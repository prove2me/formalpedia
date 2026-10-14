-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2143
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:46:24.211379+00:00
-- url     : https://prove2.me/submissions/6f7982b0-3e4e-473f-9da4-56b76d7b8e29

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 385251798 ≤ n < 385431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 385253048 1250 385251798 385251829
    0x50a03090c0e1503060606090d0b0703110d0605090718150207030215030402031b03070e060105070605040b10060201090b1614040f230904020f0f09010f091104080601090b 75
    0x4426400e010501820f00703800414901c0c820722170000464543d141c003404a5104180c000e00c444070382d6281d0381e1824240c1200404007814143e0320a503660034100411f0040c440701c450440005100e0703060008204004402806210801030384a14001c5401800c800b0ac7c000c2d01c0b008008442075400210f4103e01c0d060141c0c100035000091030500d441c800e08d400014600a61003102511045450398415012140c0f914011690603400640204007111001807480c1d0001e030185412494012107480384001c1d10b800b50740032100380c582241001514400b248125024002a20080c024000b0076100c0018001000d04252240e12000310185111406041c58660b079080c40d5082544030703940d46c0842c0c001d10340a886249008044103100100c0c3c1c84440d032020b21280c50082c004005a00d6035000e0051508001d050a90400311302e002d0303066140d50300c0a4141c000c06110001c66200f50905c2003000688002c0d0100c0e0350001820b01c014004501c020841c40d05444002c0070008005c4176200001c1c0c140d80c40e10110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 385254298 1250 385253048 385253069
    0x1e0a0c02061b0f07141002070303032c06010306292e020d03110408192f120109020102070e0c04030c090b030c010e0d080903210a0206090607050a03090c 67
    0x143c003041d10707000c5400000c4071410051022a80a003206011454041c1c404d5800140c0121a0603c00240240e104404d011401140c554004042c0300010340701000031031710100d00b684003900400c2000f14901405200395003210740d10700c0300c030040000170091200502d111882001d910400320395443d1506181e0301c7d0040e030180110800c0c590304001030745a035020741e551070010b410308000d007045c0c0c40d0b03540441d022107400348000c20000c2e20300140d841c3c91040c070034800caa0706019003500c0458800c0700c40d0142d4260074070705459019143c81e1000c00903581300396840c4903840c0e41070030030000c0581c2e00411030345d088070070f5032060b404290350340210143c0e94895500002c00c500524080400e69201580c0400c0a0038400e8080f9002d40b200d071001540c5c0d41c0da2882000750700080710001030000a40309805051800405401c4883c0e01d480103c0441e105a02030a0b00201ca0901007940303d9055410030901e5000381100e005064241000d103001412445201c000310107240c0c17500c003903208104617100d82400501c00c00c5070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 385255548 1250 385254298 385254313
    0x70804110901032a053312100b120115110d032304050616030906050a1a0108010b19030204080f0a02090109150b03062d12010e100b030f0102030403051e0a0c02061b 72
    0x300b881c6221094030310310b0300c3c0c8c04917502c0410803a0f01001103071100c408880d8026141da18010010704031800706004442009684083c40001400410490200c0141038501051400035040d040d0202d2901059000c07003001c01006100100b0008181c50350000214840c9840f01c0d10204c4007600038056418009280078580020801099102d40c8400710500d0701c0e041200c2900010302c0111540c0c40d0a005900040c20104806640c5140e0100310074401203040c04c01504241c2d0300e10b542824110204849030302034001d42891811841d10b00105400352405040400c40c001d0743e1440341a803801c041c0100907019000001049556a038000c9d050088090342420a0b0a065402c0031030407e02c6090652501408101594036a501018085c01e4403480d0304a0060550481d201e400344003902190128607054050380d00301c03540b0b140c420f00040d44128065183e0540e141d114144050350030b180031407010f403940f00500c42c04204070b600c0b00741012040c2c3c04407117191319404c3c407041c287c0b9820396a0800400c0e44c0304003603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 385256798 1250 385255548 385255567
    0xe12090402130e0a091a071e090e010902180a03081c060314010c020105150d02060a17180c040c08040204090606050a030f050c0103050c03070804110901032a0533 71
    0x30406085c030341c410320401c0100005104482c003800d4041e9642004680301103640340f880030307210301e00442c82c01183c81d01e4003403540c0e54040b0b8108814207070050130803541c00007101c46920f00284008100de8109490a28000d46103883d0340e1240d01a80305500b542c1c444180c03020703040210702d0300240c0182d6081000c103000003440742c0c0c109000380740800c0501d0255082000242140800740015124084090241240c402141c0d00300072813544213540980600c54056465a500306200c003030103100c0ea1410143c00c1c00b600d02c20100303e01d420740400e460740c499410055918120343c3e001c0c1515400c140c1c15980403400c0d42a5142a20190038250041e54001c071107110000f0920100c070301d03903081d00e40c000c4040c2c610100c0307540011008e0701c4084858010b41c0d8020008030700d54034841c1d001d00f40d10500230f00d9445844100d400014400340c0c02a4000e03924114003401003014036460b507004042200e940001181c00b47d243c4400b180c0b0703859a400c2c1106111070b800160302031260b60684d80140003116100350b00d40e00d00181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 385258048 1250 385256798 385256801
    0x9040603080f0702030c0402040b0a0c05010f02040e04053915130f090209090714070219030201020d0f021009030504180518010e0a02040f0b10120e12090402130e0a 72
    0x3c2050380b082c410004201d0b0300341003610071282070315801c1d80443c0c5007181104040d60401c11b616000c856075944c403080c11b220100c5030b2001d88081d00f000c2c44030704528105820407501c4d107550540e00c400508803003911040c101454000030301a0220200400c50000d100c1d00019062021680c035040800b400050101a03001501c607840041d201c01045d0120900c3d02c1d0748180040b80112a41d868000c841c201c0810034843c0110740c0e0a0382c0f103840c2112285401c401da8080b84181c918803c0750b80340300300002820700c2150b8042c40511100c0d4214a01a5060080e820000f90f80740082000009019070303800c42c0406162080e801c8801070904a2004001180c6014001c4020301701107032700010350114004030807440c82c2d06008842c09001170f5401881b40d0140c130b401300b2000344120140090303059901c0c01c142400e51900441036500c1d001648880c00c3e0309820000d8042a91000b10100c00241c004509139800030040b042500d0419000703442c0180c9400f1344010864940303095811554035420311104120392100e05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 385259298 1250 385258048 385258057
    0x80711070e0619050d06090c0b0706020415020d0905190b0c0303010306150f050108060a03020306160e0f030307060917030c04031a06010c14010b180412210209040603080f 75
    0x50f19890300155a000030702c41080058010954031007070030003c0101260aa8000002d6a4080c0016014584e80d0b98402c503c0d5038085101110a25004102003040030b82c0741110410b550128000740c9041442118010079481031401201c1c802c88440d200c0741c101401c80380300c4201400d071885445a4441c1074105107650f0390001d00c02141c0e01820250480c16001c0204084011111100c044a05050401b001522000310041665401c04082e041c000301581d41044564040c000005900d407001c264004001c0030006c0c01c0441074020b4268680d8141c4507140003088405039078001307100240030000c41c0307004002c03c0c4841c0b10a6013151400303c144400d0300301c048002c004503071140c01a903c0681c17805076070303030f103a40e000311078a13804100090782c90004580399207814550b402100d8000100d415000f80014262410300b0400c1d400912600100010000f044481300d51411031405c00f119551110700301c03294809510800f0400840d00420b60b00b2040d15150081c00c0903503400042941c41c3c442944010005420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 385260548 1250 385259298 385259311
    0x7031e060905160512151f03020315040605010f0509060403050105070215070f080606070c050604090f0f020405030309100201090b01240804020f0415030f050109030f020f0607080711070e 82
    0x60107500c4160f02e000c2c00031203418014101c010005580e0304242c40d2132038050700c1e020a800440c5140c1c0029070b00109088940310106a03100140c1303a0a00901c904040d00d1f1040456010360302d0310005004583c7c014a20104c4d03203480c0c4c0303402035655a00301c0c0810b82600031540300908660800080c0a5600d80208080811214030992590b003035462240071102c5111000e1100c0104141c0e00c0883c07c24202a002410100d0091410100302e07990703030002c2440356016034001c01302c072aa210109c0311000d2850050003013541c007803070f41036007403509000010342c40e4404d15811a1040707900e481c105945034001c2d000f00034211b800100703111896030755204214290109044002e2068810102c10b104640503090850050f074000d0b100c11004a000402c0c031000342101101c14400c8903480e60700000280441c1c11031039400f481040003040c984001e250141c0701d003000039220010f5400c25460402d01c8100003447c10f9200d042c4d886d0104403600d030340800752402002810311040d00c1c050808046001c00c116401c0038040c3d0f0b07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 385261798 1250 385260548 385260571
    0x2060a09140f150c0306011b03020f0d030203010f080303100501050705070801050118180507091d01020c0a170315130605040903081b0f07110f030709200c0607031e060905 75
    0xa6030070040300c12030300c01115071901254003101141014405410010001d0b0f104e030040300c4418bd0b1a181144c07402030b05042000000390008014403d20800e0500e41c070042012000850460402240ba1058103071240212070402c90081a807400381b00c400c12480c1c0c02801d0080007008156141c40b05807190002124000e00c4003030600045684001d4244940d100c842c0e0048064550b180c242a03d020141c03102c0c11103c18182c10040700c80c4a16074080c8002c045030541000104043c0a580c9407040030700c00c2c0221007004841e8148200309c01c11042c001d03514003101044684100d41c0900034002c1000349510b40180c0d4215260004900405400c082c445010b0700900c2c040070031400c1e0b080e50303a01c080e00c108154441c1048050042d00d00040e00020780c821041e0009103d01c21109640010a02c2c0c801c1d1940030306200c3c0d46480c5105c0c0d544a51000f24142d880c50409200d2428400c11102d03652850054100801c15940b0040300b160326040180d01407001d11482014001c242e82e85403040041c2c00c00740c1c0d01c41001c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 385263048 1250 385261798 385261801
    0x30807030f140a0f0818150103050d030623060f030a1e020901050901030218060c0d030606050703170604060512030c0709050919050f0d030e0115050102060a09140f15 73
    0x200b00d0090315014415560383c103030102c0b42c00d0011512001d014203c100c1c00d4410402c42c061148051014078007840f64865130080b15807443c02c1041c64200c0741321414050605e440c00030721003440c0c0c0902108a100951080010300d9800c00c022403400c1c400c01041210340076020090102403507040d0801440142010311100703552448600190491040c2050300f070204000300300070b88065010350068000f440580c21541c10001a0f00c0101e0244d40c00620394400e9500f00c0c001090740c0075014415080600101c2c50300c58140146a03a000c2e001c028091121030260f0341d488001001a601c0c0d4000c10301400740505424079111445002d10f80e2900704c1c82c40c003241070140030381c08582c05440d03104207445280380c1001001c41d0101403400c01e81010041300161401e004100110980b2041008603801240c03c55038002100c21400702c010b03084a041001581c46c9900c210f40400040c0c0e400262150040031107000007a84402c00d10780408121003191000320140208012600e46101c04140d40d14130b90026040c0c01a20b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 385264298 1250 385263048 385263077
    0x50309031c0504023a060902060d020307090f05090609250f0905010c021e0111010c120c050c06040602220f0905100803040b031b030906070e0a0e160306030807030f 72
    0x108201c95172016800b4002035114120040c2c0b14400440301400b031030002690f41116004101076602450702e090f0700540000500c103d65500c882800014400080c580783c3e56824075000649035031002c1c0005104024940100f8401903d003100810b00c683c4018600d04211807550029101200412010f80860351500d400035440d4022481e0b620b106500420b1440d42e42c180a40c00c66001d80030001c0c031410800403244c1d10315148030902c02c0065003815034480000000b0103100c440b040c3c80020801804104d030070301412100b40d80000e480c6803c01c0d4400300258442c10790325262090b40d40031600d80100c60a504400060140c80a4034000a881c80003000780482d0f40e84025480d010205440746004542c010001009408024401b854001301c41d000c1106e1440090810006243c200781c0e180c150382e40040c4203100c1841c3e00000210606101550000c1e1410b03e003d0360200d00c0700c4001c102e4899456000303003140c082480f039880f150185038001504c0c0e88981ca5410000d20740d01142000c01c010a4000300d90042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 385265548 1250 385264298 385264339
    0x604091a0907020c090406180203030a030501090f11160215040e0415020306030307111302190f020f07050103050612010e0337050a180b0a02010b10020706050309031c050402 76
    0x952083c05040320441b504c0d26901d10004113000d0b40c144204c540001692030041e079040c4000c0103044001c2c0d4000ca4a5410300d0360f40d030200d440b00003000305445e20b80305826a542c4070820994540011403d1348108002c5070340082907620ba0b4801a00540980019000c2100c1507000c4150340541e00032070741d00c0400394003d0a800100d200550340e244d410341c410b104920000b000d040040c4940c40000c0c04201760314a000c2040c00617a04140312001085285100c4040a036520980084040c0e1440c0300a10210b0240c01c0d1458070780f207080c0034a50400d0707102c60005940c0d45461054242d0303041039000801c0f1807031032400d615460f0b41043c9191001c2d40001fa103064002440c1c1c0c5034070780a0f14030548905098009040341a90964404141c1d0810701c488072031103c581c280003042030700050022420003a541d086401000f821160504401c17441065030801d510900c95000a00d1001d0b03c20f03500b42255a5141c3c40580c40c6503004204405881d501807151140342803119801c0540694400d0322410400c042119500c507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 385266798 1250 385265548 385265563
    0x801140a0606140f04270e060105090109020d06032102150c180d0f0c0518101203020a081908070302390a0c17060915060604091a090702 60
    0x100050055911039010f1203591000b0011110221200c520340f980c0e460701302003031521410200c90a618038540b02507048046000b15901e00c042c1c14060000c9604203000103e0803001030044801441e400304541400c1d110b10f0384040301441e00461306841e10580b51500100c01c4080c076000c80018040c0c00f5082220403800c0c22100d0143c3c411600305414141100300031801c00c0025189a070b44000c040b00c8680c041013030001c40be46441c0c018200d06210908240030702c00c3c0c600b42c5030003070b4101c803000c0b10802284c030541000181c203542c10360561540805045c201240381107aa1840030300b0205002650320040c002c650240e03454508640c40700d04a07661468004e50490190300c103d00201041d5418040200359401c01d1421940040032003041c4208503e0442454400001300485800743c0e180d000340103032807076035006810311200d00e0001c0ca49490031115084d107480499070903250941c0c200011840c4d0b178ac2d0307190580b4060900c0050800c46103180b411071404c000e2544d20954016490f250120740344c5440811000d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 385268048 1250 385266798 385266809
    0x1106160c0305071a0a0503060a150c050d0207031518080c100605010f020322082508010608030708070f241d120f220609120c0302090604060305070801140a06 69
    0x4138140051145d06441503403000f040b143c0e210001c0303000070903040c03100881c92920820380e0b1303258000d540e4149061031409010b60320031015903014180c20400112100342d1f003550001c0344031000c00e400e540d022200b400343c07002c81001030145401152015105400059150075402042c1c4c09001859a820066890346404000e00b001078008100302e84803e5101802d0901250749081003025070f80c0d44204143c107000800c4420403c41c82e00e03d00540c4003080441060010745811402004014a8500980d68cc0c2c452094010719003407010500000340b060382e00d0708c6408a508200281451200c1c207200301480c1a100ca800c01500d46000c10240700d0880301c03840f40c0c000016000051051400e402041d140320340060107002125581008020282e03d1110b07a000c000202e1a0070311083d140c103217440901050640d80100e014081c0c110b01c903102040510549108594045d40e0b05040b41e1180b90100700034040030341000d8802c2c450020002951041580b04d10100038481050304641d4071002c0d0003005a81103840740 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 385269298 1250 385268048 385268099
    0x30c0b130b0109021b011806061706071202090604060305010504140408030a0b0409021e0112020a0f05070302010209090c1b07050906040e28170909041106160c030507 73
    0x14004011554010a0b103250a5900d1443e40704c10100e5050070f6400c802208a0360406940c400008c1201500030003000d40f40f01d02e03000240012000a445c3d807150000e10110400a0000c950010724942d54110f2710750a00140040d96295111040640649800c0c0b00d40c901a620b420104186581c2d11103100780915480b403000c1c2d103552038104000015000c90020380703502c550380316806001a40ca407001401c13440425003151503120192400585640c55031408190450b0040003500540b95016002c01b00600480c100161550744908040f4024091254020341144850f0203001c21000317450064414040c9589119421040a4011580b181a00d11610307820614101c00b0964034546500300c07034841b210300c0f03007296218044021000c51080005098224481c042c2c03001c0414407180ea03000d9011481c483c07401700e203000c1c4c03c00089105002e00401c05480071040f0601c1034030b00e98a00088504400042c242206e0341525801c012580d6103842c80107c51512074501c00040f114001c400000207008500c06 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 385270548 1250 385269298 385269301
    0x806150432010f2a050109030f0c0827030a140c03013b03030c030603100b01020c190b0f030a060e06030601091812111e0a230109030c0b130b 62
    0x5080d509280703040f80c0000c800105a50b0356150604e01000204818003030380002c40c499603581001340c811880300081034200310980107072901145845084800440c45400000982078018141e00710b2802041d0078942e043c040c100c0702600b84080e9034015401a181c0000380d415036004001010f00300c039001203081035406580e210381181c4a050b03170031000032040d0299600c1030541d47d400e0440e003964002c495504101c80c0c0071007409418101041101484403140c030041241100900c0081d68070070300071800e6031090300150b2401600460a8030080c000305050502c41e525054520840c001c02c0c2c10854000d900e480c030701f5200041d1901c450340307402d0080d80301402820060b400c181041001c0c100744040300082d50014501344001440300307114000c0c00303400c03941d58520000c1303910402d0b8104035000070180038041d124115400d104101040d2030080c280c0c0b0501c1034240461410030981c0303007602800301400320351034411140d003810f410480706400b1520808015240e9a540d070300c00030346107440d5400030741521a00310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 385271798 1250 385270548 385270577
    0x412090f06120b0f030109031d010c0c050402031503100b0315100b031e0f04140c0114090109030f0302030c0f0105010b09010522060302090f010801030210080615043201 74
    0xd0003c1c00382d1070003803c0b403c1030004002c0424250b814001c0c0c103c0004a58100f0043d800b0715000d00d000b060075003484c00c45001040350305d5032988880c160041610660340000454006100c65902d01d43e40307003018041d01c11598403035291400a1030007595881c0280a1242c0480400c0009480b05214406401c0911049814452818420b40000b8010001e030300380100c084030055840c0e8020b601c038841d400341000f81840c05182007100c0b5450003151007555408100b141400d80c2c0c12040100418440051083e03c0d1007002004941d1704190340c1c40540022a403203555400c0c0740c1d000c80145143c00032202260442c040301c010319401c1f28024400d00114000a000c181e01642c400c000034031003102505e8a04280409605a1410160186d032080c00882e900050fa881c043c24008640b400b60b50702424000081d42c9140c000c50840300c440580f00081203644000507100b03a039609401550030036040000c4c1d8035503407100250344d6148507800084078000c0b171051100c8542181e81d03121110001040c1d5842c0c41c1403e182 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 385273048 1250 385271798 385271801
    0x80a02030d03092306071b0c06030f0f0615030518191a100f05040209090f0c0c060f0405150105240d0c050909010501051e03090102070b0412090f0612 66
    0x800049482c112140d134003020a02c40d01000540e5603004201400710350a03c424040d07c0a6240c2c990400c802041400071008106043c0402c0b04881d06410041440a04200c40c94001c1080b605002c2490b40780000105203002c091000309501e0842d500c0401c82520b41c0d1240081e0b5054900040c080380e80840c101c00c881301072050b441c0340c1e241d106071380748103204980498004100d80112032101c03183c010300c4c1041100d0000d0f0408140140300541d0110b2074400d21074049101036100134001a9580c1c03410000c659a0003005044501e44641034055036024142140f080c80b0010b81a601501d45101c4c0d850344801d03000009011a049600081c01022501e1101810b69188442c034018500043c10074442000ca107800c60191800c8091240e41c0c690741c8280403420443c8007a0181c100504000c0709019080401450034003603521002405c944507100d0362000082c0740a80302c1c01030002c017400c401a080c80204001950315003159241900c5080e07225403503003002c8149078480d11414000462850a10b208065503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 385274298 1250 385273048 385273061
    0x706081003031d0d0b1f0b040608040c0302060703050307080c090f100c060507020a02150a091e03080a0e1003052206180f0c0602060403021c0507060e1006080a02030d03 74
    0x401c0c1201110900c43c400110f01ea80c1c694401d0f928083c00b00708000240007412001c1c0d5010041001501c11181000c114494130f0003680181c00a000100d00894117008004200700c00440c0d009204a03540e007c207140080071a0001d4604601040c020030105421903400c0081d9208600d026101e441d401010600300403043c0a01048401444002403070034022031118040c0c0c44c4641c0c5181c00138110480c2520500c100c0e000d030110301d940c4160091044a48060340f148580c0201e5981034410289107c4082d008c0b43c0a0601c5e500c0106079074000140102c046400c00005109800c0c1104c200e90003240104080c1c2c140c810403200703a9140c00208114080501c4031043c402c2c9402e01030100010500c000030400c0000048054042e10b0018283c01081c0411040c121030703401501007440500010f04013540c01940d0340071406100607005040701403100d5000d1007102607807646508454103119002400781103548620005440d06000c80c10448045011803000444103402075000d4014000307000268030440c0140300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 385275548 1250 385274298 385274327
    0x240f030308040204020a05120405071a0412032706030632190f0914060307030503341b08160314070803120702190201021005100f09050108070608100303 67
    0x240708da10520440d8564440c400c0e441b07580104503142c10200050b45400c0da50071011203004d4100070501c8402a401c0207208640da041c1030031449102c072005282d07081003801043c0c18504142c000c0000390654150080c604842d00700c010588000c2a078062415000c4071042030205a00c01010301e16102e05040ad03d4412a0341c280100d40344c00c41c0c90b1032034840d03141240c3d4407c203001600e07848103003499140c242c0e0759904403008500900500d8950b80d20541c4a016807842110112810350440307030100c40d00281031504040c000c03051040041a03160090498400c4101c02d91615540000412900000a030741d210020300d0921540441b803541d650603445590818261515000300d08001803007007400c001600c415007a114056181e880d00f81c070005c0c5401c14403403076450680300c60132181c00541d0b004150034944609403540840d956845002246031403180f90702c84030402c280c03281c001a01492070340c4914180c54800c001d881c14550348600c04c072040740c015141911081841c1d0703020030010340641491600c480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 385276798 1250 385275548 385275557
    0x519060b03121b0703021e0a03020909100507031a0f040603020429040c05030a0c0c0b0a1a1917010906020d060503010b04091112030904240f030308040204020a 70
    0xd00d18042810b050840b58400001d590100701c0c03100c400800040030f1a0080d284000b080f01c2451900000c400c1c1c62904141c240035166000d68414a4840e44900b0024540141c030401c40c60501004840c0c9d110301c2d034164140102d140001240c030641c42406090300d04001526172a990503101c40c104201c0400c40c101103507019a40f07200001c010780310790185000f41c041c448821001180c080a030041c483c1d0300d00b4442c0348558a08414003a902da000070540390048003201000070f004890007001d5641007401d2802501002c050000c0112241c2290040d42c240703582c0c50300078080f000040341800181c02d075110300c02024070b43c2107400b8060016115441d811002440e800814200100d846100c01c9a01402c5512800b64480317009000c80e040901a41141d4241038604000d031024940b80d0f1030540712408020391103041e050b1341c0d003140c040081083c3c03044400d0080c402c0009004e41c0000c0e0202c00600001030348007502e401c000103040c1b14006410001c880e05621000c003950f403603508000003940321650010500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 385278048 1250 385276798 385276811
    0x5061605060703051006050a02070303140c07080303090729070c090903050a030506060306010905060307210b150c07150c0501140a050c04050609062a010501051804051906 75
    0x1a820850346006503465140043e183c00c0c4041101c05d0804950020010b2040c20004964865070008880d02241d4161400c00c0070f101c5e10a450b00080e1165520303201140c811104003240c4404040000c40c02103400000300c8140716540d10050811542404c200409552100307810414445404010701c0035500c580080120b0903142c1c1d00e15402c0310382414041d8002580410503211403030301441410382000e011900d01e41149868000200494024062140101d4000c0040307030065010b89031210700703003407640c40c440e2240d82604452030060200348407003841005960740f20b965a010034800c8406d005550005070a000c1c0c182850142441d000d030721003008110b200070071080407440030301c0b803442c000c00b007000d0500e050304024000c1030503143d0261043e00483c01c200001c100c0ea036150000c44044070700694000307403186914460040d1032402c4440034215007103c1c0806840e034038419406076060790821180004170450414039041c4070310080381c0091080d800a000340719611251100f60345e206103c1c01c00441d50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 385279298 1250 385278048 385278053
    0x3031605010608061005040c08010e0a0c03020f040b030901051b030c03041b0b0309010e16060810050d050601060f0c030822140f0618151f23011701050616 68
    0x90131800c60f0a45040040e60304103121030318107030040d40503100c01841c221840d541071000100800102400c149500b0341c0d12018000014000c0d0162041103141d0102070380c59955a02910407280c1c01114085103039460000020040311107144901c904048019689046030f0324030f00d060010b5030021300181c40ca100070b060241648062018400058114540419140c1c20100159030950381040b8002080d41c004c070040c0c40381400311346040c0048a0b102d252075007441d00c07005030401440040d81c00c5540c00600d034480c000d051000000c3d44d14100c602a584012030310f52450b10459028450b004001c1c001008080441d580400459002c20800c01c1e01c05904c04680a660b108040146c8520b80c813020364001c1601c1d100c60010600c60148c2c0080d00740344992200c0c28403103000d519140030801480b1021a80400f044401502c0c240d00700540603003444401c3c195845030360309103200040307a0310b0760580f0300089a2030b05030794070901071070403141802d0a1094090b4204020030025410552000b07a81e0110024507101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 385280548 1250 385279298 385279303
    0x60b060f07020103050703060b0901120e0d02031b0105010b030f0a0f0906060f0803070213021b010908070c0519060806030f0316020a05061804050c071b060e030a0203031605010608 79
    0xc6044120511641d4129510001d020f5480007003581c01410311700841003220482c00700413035141c0002480c0200c400a0040d14240003081c281e10001c2c203a00c90a52011a0150000300505c204e080701c98420100e01c4800c404507081e01c0e401d014040d0f80c00b005101080038200001089070304508955400301c0c410b41d605000c0030440300144030650301c06440325001c00035542d50004c09005030940c000030350302e40241038020540030311401a218101c96030000e08529194400c00540c03851800610007030062240c5401c1072031160b0403440054a8a0983c0e145c0003032507251500a507906441032418074140186000c4040c2d41c00100200742c6a0180180d11103550781e00b10030f1005041038408646070722500319150042c03007000885500064020030040181c40384401e9407417030003603514104540102d01d40d41da8510018682c041e08400030401c900f07038000c0d2074074120100201410b9490903a0b8002d025a4230030704150340d808594401a405400030030074900c4400300380401c0400c032409100003003001e503601c0d0b0710b00d0f1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 385281798 1250 385280548 385280557
    0x216050102030f0420300a0501140709080a030e040b06041e0e0f160c020a080f0105160c0f02061e04080f0615012319090801020304030509010c060b06 66
    0x4643c04411000c000030061103100b107001d180c06485109080c070302c2c81d030080b40303078a40100342013000405034010403a01070405649003000c003090301d026941020264a0700502800074040d059860300180c40005114a201b144c0c0c400c102d8188000418000304503803019151030700d04001c206d030001e4440d140340480c0d840c1c80300100011b10b0071070480c412030b0007040c120f800c8030a81c4c1c2d0043c5e05025211000c3c4001da901200c460b607003002ca0100201e00050181c04281c406420810300290018100c00f80040c01136000b064020201c08644000c0c071407640c44031160448111507031038035804100248100c0011440802280b03103014030140686240c40080c048919000382907280d084600c03a80020144050030090000c041d00d50304000042c441d80c20024a00c40381815201a458100504c925690034420003244041d0006071702644910303a11040a4100d117010448507104a002c11059a400502e6100510840c0d200d9501540c0d0182440c03100d00045406d1030902809032012500c1c2d8506007450303071b50b820040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 385283048 1250 385281798 385281811
    0x5090c060412020f09011a1309111206030705130c0507080c01091506050904060b0301150905100803070c0510020a0b1513050f040303331e1503021605010203 69
    0x540d684600b0740704000c1c03440c1d41c00b01c5460003a81c04500400c041e031404560201c100c50448591b82d00c07049040b004d8103a003140c4e82d001c146000c0c00c08204601c2c000100008001d40c50b00382080f0000785e5640b8003450341c1c5e01d40c1485415080480155040ca90240961103c046500145032613460542c42e9126002203800440702c450303299548103072900402c01c4040050034504040202449036519050000359002001032028240ca500c0f01c0101490f03950079802a44d003042700a10141d642610350b10310000400701141c48820250040b0000300c1e117400000b0546012941c8949078448580c280000e0029901410603828154480c82c04043c00052200184600c42d030051aa128204000f1a080000803031100e141044100c7c90141404041c10000081990040d01420041900c03009140500d50300b12020001000d203c00e0042c00d4813005036203803292401c41c0c10481601c19503044e40e200c03d42c6400d43c0f40c0f10704076081c24407600c04500c0c0c50087d00684004014402018081d041584a84d0f081e640116850b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 385284298 1250 385283048 385283069
    0x20a1a1003140f010506031f02070809041b0f0203070803060f0d08030705180406030302030d0b1f050706050a06210305070b0a09020315100306090c1508090c0f0108060405090c0604 79
    0x10310f4a0a4240301d240c2d88600100c00a0005080f40c000b4a06002d5184a01c1071103290006032810a10882104481d02004081c10401140c62030408402044183e16141c0000901c522410142c140c03000082d10411500903c03400c0c510740f00c0d101000a4451020041c0d40c206c00402440c00125203064080c612400c1982c90b420366603082003540b48600b10076242050b109514012080c40400c2d4000203450000c5200c48001581d000b000000440b2100084110901043c24a106034407050b07010001d46801445001c06001607101d0003c4241035030b00c540200141548001c03141616182d01c0114403a602c2d010f418010b103440c08035151b40e85a036000b100c0c3d8544040d00e816804045003000c101040481109104082941c24000198201c43c1c0052101070582c1e0345483d074000030b00c440c2400c5200200006118401a40c14058015084a0b822240342126014802d040301c0c150600000c228034200c0140d68400d02d035542c2108010003804054104403030342c40b81c00700803110b17519110b00a00141c0b801406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 385285548 1250 385284298 385284313
    0x90b0904020706090f1b050a0e070e01020f16050112092117010603140a06081c12050a060e0c03040b161211030a0c02011e0207080d051510020a1a100314 67
    0x8a402030313071000d0f074885400740c0e00342901000425101c15274a50442003a284c41e21841c40c1c1207004074a0500502d00d18030081c09800079038100c503440703105400304450302030300d0b14601c60054028442c212426001c000c1c001c4401103282141c0d01224800020022203581404801811000500303070501400740c1161000c02d58807100506004c0752165803690004007d60300344401400e08040544891034070844d000740d54010000410018003c06998030b4602a0010820007440d0002c1e240c4058456031140300000304000d40400c01c2011740d4412644107540081c06007041d9140c220001d00a01c1d0300e00081d03810420b0f20300078070050f40403a0240003143c5030309102c1262039007860030800080341c450000c1036055a250400145980d41c843c01800004010400010780742c0300c050600e03821a1085000082d80f152503c01040702d0054170307400581c0b13924019070300b80d540300d040c041d0180d9446480200c041c0c606591000079140443c2c544210a6014442c031141024480d030b00c1d500d001c44045901c000c04081d801c00d50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 385286798 1250 385285548 385285583
    0x2011b05010609050a02070c0306110d020d0f0c14040e0403050f07120e030c030606120f0d0809011407080f090c04020a02030903010506010f17100e0106020d0f090b0904020706090f 79
    0x2e10303a0444001d05c42145000308a0707544181c0d49074644001400340fa15003220849840741001516402c0c0e950f020709541c0c403c101902d90006161110304529080e1400e64052001445a88007070f5100c201180c400f8a41800e00700160103281005104030100171003001400e2040d51308801606840d0b1040c440d60b60790604210300509030181c415a601c0c0668007042d5898915903001030b100307410510a8507480520400c0c1075020b4100645640d8800c042c0c0714260541c0c41c000c1d80101001d100e0070030f00c0b00800c02920b1503102002d10101c1900c6c0c40b4002001070001c40c4005e103003035080c0e0fa0440341850031075082481c000d02080a98010700118000f5800100c2c0c0c105a5050070702401c1c2d4008030034a4121681505084050004110750103480400405500007030b220f250035038003810150003c00074034039a960751160020740d2824841511f1700010501c4007101240c3c0c1c01815501d05848a00000d40c1c1044d40e4441404002d402600c0c00f030300c1c620703180d0403501c02003150000f21440403402010721f00708040f00d46 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 385288048 1250 385286798 385286801
    0x905090705091902160816030905040c0e010807020109140307140303010e0103080a0314010b040305010e0c100f0306031a06030d021507080a090b240604150c02011b05010609 76
    0x294081800b4030842000c00c04800540e000d1101c0602107000d00503100c110074162110042c0d51a40700820305400096095400d140c0c0b0358000f1241440395880b070540310740315000d210a651b001c06a090202d9049062072000e0345c0608451a4070840720700c0006040c8540f512461034080744241107144507080045d5900520081c10303034041030010700b64011450340d40b4140c140070078914148805040d1080105254603228881d41110602c400d001c0720f684207950316080360250300d5009210403141c0750718203909400c11050228401402e99030080080d02d800d00c1101c020754100f0601d10000c0b0406554010200001e2a000b0100c078801c0e420a0703d8014501c3c000e030030315161411002800080d944844039440103002003030b0945a00200500d0306060a40369040c410707001d410441c00040c00c090664082101850000361030101004200d1903800c1071901034001d00c40700b072080c4d00900d903180702c001c11300720754840c015006020300d01e2040c0340a54200000112980081c0b000c0c0f401161141d4540d1420808880719 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 385289298 1250 385288048 385288063
    0x210b0c12042004020f1608070b040804180b0307060509131a0f0108092104030b09011407030c0207030f32011b08061e03010f050406230c0904090606090509 68
    0x1940d04603c0d00b2451712912607980520550300e000074141307003240001c003c040d1b001d450300582c5c40041e0f5001400c1078a000350403070300140909a12074142c007100c4a83e16a030b81c082c0c150705000180191420608246084600303074405580c15410441486500c00d5500301031103000224049180100360814400f010004d486214400c0241000100c50600c5182c02010541c0b02c1164541200103224000354001e0551a024560010744600740c800100180e294064101c0c664120420016100341c1c1e46800095040b41d01c200002c4006a000ca0018800107820070380d510002405200d000d002003281c000d00c0c0d03500c519035a070304050070701c0e50901940c0585424082c02100d600100c51019200710845801828000020701170303031040b002b10744001c1070580d031500785a201c40805002031042c41c100d0030342c00010300810740b0102c0301c0b10b14104640381965400b188850070701d00e01320f407840515140c0c031480d880584c2200d105140d20030303594402c1e80009041481050300611505070041881c1c6071110440e41000385 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 385290548 1250 385289298 385289363
    0x120a110402041a0d14131406090a1704080d0c050706080c0703030c090803160b1311102703030e0a0501121509060905060901210b0c1204 60
    0x180802d00444240303042c040303c8075160b03021664603950750b042408054020103070b60703130303182c55140c814070071000e1040b0382580e8124028000715000b00d103050031a070358a0408840c0d1071001d4120b1044030f00000d00250b50400c8546140420740e003003d807201e42032424104201d20003000b01e8101d00100c2d080101c00d000280040c0041d08103503c2603c9d020b03503442d85603ca050f07402002c141e42c401e000d0810a02880540740600788081c12a03403a0034034040c044051041010098072107000c0c200028891918810042c0c155540c019100d5180080034011b101e150800d07042c41c54240a05075102001000076060040c0306000c06c0c1b40d2100104e455401d0107004401602c3d1980e0041d1020701c42803003140d80141c2941080791a905c0005642d0210140c0c06141148641107148400d040002c00030b071281c0c1e140c000c3d81c040c400032144098666618001c603a0b256111041c25004222210010710100f003440031030b50350021409144500d410152110714178002e50071182120f02d40243c02c0e4015403030108407015203880d030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 385291798 1250 385290548 385290551
    0xb03030c0c09070509012102070b0106051b010207020a06030207050304031a0a0501050315070807051e0a260c090103090210090f060f0801140409021905040b0108011212030209120a1104 81
    0x545c0709000800c4440118840c05c0c580c0440070100081403443d40c1122003580d0403c25260725942c50b02c5006000ba41f043c0ea1884180d80d43c2c186c980915070040c07088840b0244e000b031800c84e00d00d141440c10707800b1350000c0000b41c1d00ba01081c040000401c0c010700744412205090404410350380307448440d01c000c80300180c2040303000350300a1781e90381d030074100011441b6041001e13811300c440301d41e658403011515442419144440e00407101d072101c84100b400006030900119607203541100c40c5010842c000d1452000305011000120070000c180b00e00340c8400101841c81e4180340205015504d500070403080301c0810034100009100542c100504803020000c0c4000d04518505036200d09001003000300903500600450003040102c90354a010f03a03441d5403100a105601138040c00c402d43d00c598101000c5001c5210f011301480c03c00104104540c400c82495042e28003500202c440440d40f0784500e104554840840703424103030300304008900c544e10024800c1840507210000c0074440918038003481503140c07896503c0d000f103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 385293048 1250 385291798 385291807
    0x12170705070f020604080f06061206160c08400501120b0d050f0a140c060a0f0905090a150b0a0905010c030c0609060203161403010501120b03030c0c090705 68
    0x1503104044600c4a03030441c1c0d04035a28105800007882500c25940034050340c2c460f000d4501584c950100e5400d00c14035041750240c18000d00c40c1c2e2119122181184d4401d165020202d50017800c4c1d001d02e100c12101d50140a1241c10301408041050300300380d8941c0b04804406c0002c01000301043e504c03c841840c0c40410076203800803458040041c0510056008a412103610360501c00030580710780302c1900150741c0050480f512a02c44499007501d070f030401e0302c0554210840c688a5008a0340000390f42d00c0580028204500d09484140100c1f22501000403180800060070300014050380d682056900540c902100010351090728100c00110b5071343e9a1008800403010f20500030090b40003600c1e031048910a007003826880080f0314040320000e0704068018080c52611564006000f0a03502942c414800928903540d0140103403020351300e503400075800500302c0d2410001807015520821404c40e03d00c0d08400c0106daa0303018a00001c2c115000300ca0341d900c1035800130886039914980300d9020360704036556050540c41e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 385294298 1250 385293048 385293061
    0x1a0c1801020f07170f0328080f13140a03020c0a09050408090603060a080a0305120c091e040b0a0936121403040f02091f2603071217 58
    0xc8003ea0300c00c1c0c090042e0102d404c804500301c148038a40341c0d20450000e42c4e03030301c103c18046000742001500c060102c844d416550100494080c0d4070480c06860f0000c110640f039950243c0042034080702d00c03401c0f03803500a00c4000b0205000d04011640d00d8034842d40141601030000814491070481a50115880c0d034107110502011680e9001117608107401034512a5980d6698400705040c0822644166000e124848140c011b042c0d00c1000382107139055000503e5925240c0101002080c040d000040e0750000032260312a904800481d11000a0030b0098030110f034001c207880014805095035844003c04648807003550503210040c000512400920707804804104c4800800c018402c9044440103061159080300c039021240900503480e4403120741d030310b025901d00c0c15140100d10103600d003000302d006d8407a88010902c4400840400c2400300c0c0126840105140713800c21420340340156049090a010f140c9440d80c010080078001810054025034441003149419a0020b0252259400060031101c0c03000030307c030701c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 385295548 1250 385294298 385294303
    0x403090e0709060e0d0f0b07030905061b030a0b0f12010f0c0c03050d1e060312020601050111031602060c030c03190504050d0305090a0b030106031d01050f01060c1a0c1801020f 77
    0x41c02e0403d907445a408401854404070281b0802c001400301c0c0034240400c1601a07050300190111407064069440c81d844000c0c04820715506c0362000c40010300103000042920582e90700455800300000c1050100500316008249108441d480c950f00a9459650f050300c0c0c00c1e600d00480085e2402e91419040e8240c02d9100200540126585c900040b92694901c0c0c4070b02401c81c030070340301008844070104005030307491401a0b20100c1c440c000030050300070301000041d298002c0d440c122001c0d6150010f949819003d59038000c40d61288170303080317900040c1401003481281d010000742c22500d40d40c00084d941c544003042e80302c40c0248001c100398108801080b00b032100d925008820147d05626060035038a07084120001800c0c90002d030000d007820100400000740440d856005a2180c0b090755042d600d105038801912030aa840071102e050f1060031010040280511501010954501424030310108000116440302004420f0b5401c8203078141c041240e0300c048801c0100313042c4c0486d00f40020158007040c2c1512a4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 385296798 1250 385295548 385295567
    0x108010b030c0405041b0201140c03060d0c03060e0a03081008070603020d022701030c0512040b0c0c03030106020c0907021609050a060905190b1c120c06050403090e070906 75
    0x45203180c0400031652a6500a0580c0c01070040200203100600c40715945088180c0001c505500660804100078090039092040038094000f2001c0360f80b540e500d410501201003d0703c40c04543d80c0f1451000000850550f200720354010610102404284c009030030018040c2c00d01030220700c00062501340c10005104009030310340442d41d040c1400760700c0f0203140d25510000c3c0a0042400c50711070580c035490741d0460784c5014200d82503a0980342040325500e0944211303103d01420700507003d400070031400b14002c200d100c0396030360340148440c80e02850200c0d2441c0040c1035030808ea1202d40543c0c408400003120740f925151383c5602100700c0c401014000344a11001d1045105440340c5000107a5400101d521a4955000716010b0011020148034070308010a00b0060040386c0030708074414501c0d00c403460700103141500b032844460600150095103448140c54548290b100710300ca0901344200700321004001902406007a1049020b0740340c500c1c03080d25103c03c030ba01c0e1500042803141046071026047c05078541114030f00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 385298048 1250 385296798 385296809
    0x20307061d03030a06031b050609060c0a140a0308010515271801081912050f1207050a020105090102030106090b0702060c011d07120f0201121d0d030614010801 70
    0x426104024000305900c201104a88076550000004201c0c10f24950b402c07100840b40b049400c20034650350000f00c400300b414240a0503520050800c00503400341b4124024254412404040d160109825550207107110422110941660400841c090505411203c2103005100555000859880d03a5410490a01c03984003042c14012007140810340d09100310901e2000003402030446050000501c40041000300248204821803040e041850070b01c00c0c0700c5950810031503004c00c800d21003048108050714140c01030140151154014010140b159084404090040046441b00303030b0b0780c00e0000310090a540c00202040d0050303004000411505601801034400c8694141216803500010300c001400d0b4854030031000310640c2061241080001c0100c0600b8241c094241161045541c58a10040091000314003174a03c90105183d00003550140180700d00907181c200d40042c0c140300c40010010440440c8240040076800080d00901c929050710524000c1c1c071030501900c5003612141d0000b00004d00c14001c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 385299298 1250 385298048 385298051
    0x506060910030b03162405030414010f1a040507090308040b07030e06070507081c1205070c020d050709141605160c0e040303110909040201050f04050310060f08070602030706 76
    0x3004206200f42d00030506440028103542854240c495031140c0c610301d0b4002d0701104e0300004026416a441d52000303640008403520b4090440c1d4903900d400314240d005894582c495526031884403d0000248124040d2028650600400710880400e00040324801803914042c040d80d18001d00218000c001540c2c02c03217240889441e80d0b4810741c1f030129500500d001100c3c0d0090b202090030300c200400071502d1400d503a080030444030384941810480b0003000382c912890000c652009404041030485400c56a404911402d02104117a1a0780c0410295143d0000a032080e4110a2050003039142a0203910240005061603420600b0600c4110a40503d0500144e0a100300083c40385051074001d26007210036074020f41070111459564140354050310302110110b000900d082c03414480c603001c25013681e00d680e002900c0641155644d60040d0740980c400c0c0d1050410880030311000a507581d080040c5950700941d03003004124540340c40320100007000c10707030003024071604880c0c0c05001180d80042541c00d01070304941e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 385300548 1250 385299298 385299319
    0xc0e0310050721020301080c0d0c05010311041d09061e0a1a0a030506070e100c030804060f110d0e010902060d0b040207080304061d010501080a080705011b021f05060609 74
    0x405843c3c80c54108110303103a86500c5803219410003000e501841c126440981514a400e04003002c025250980c000700a00c031010110040c800b42d44660301c40384d0508580c00540349400d0303e0388044a42242e8103004500800409020880c1e5000248620b81e002140010060403c031a5074032043d8412000400180c2055518844007030348007501070b46010545405000e00726103985030704100361904000c0314407501080300511040ca150401044020141000b9904d40e00c42340015a400c5511480141041d1000381d1a981020f103200424032980c0a6006070290580d5242c1d40240c3c50130039144d406480c1103069240400020143c3c4030f641c1180c071400c442c8031000503c00d100c240001c0003070180070b90262201c40040200400c00c20075038014542070310200007091440c141c1c0c4c44c11609880d400d0142007030316003102d41c4110005002c007000d4000c484c41140003040404c031549140801c0680351409a00517842445090311788040c015401a002d410403006102c1c900e8a100403a03541d200e040031070b501130900d604 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 385301798 1250 385300548 385300561
    0x305090607080a080108010b0a030804120201111e060a0e07170304090c0507031e0f050a0234090b0904030e0315070905151908180706020706030c0e031005 68
    0x8111440c203544038400c2a140c000c080b000a004e80000d0081a103150703e81728a82c4001d1030310f400010201c1c0c3d07205401b1898242000c0b01c1c003110b1403951000700c1c10701c920592440c1c8a1a001d119000c8149013822812260301e0a80041d2803400c00060714032500d042c42c009a8a180c1407005c9111303001d41794100070340c01c1e00031001c1240d10718610450f03100491240c030b00192078010319407010007001c4150081d43d61201e00035441c0010380c804060440720a0128003c0702c010120f40303005401600c03048407a8011f403290116082d0400d002c0101040c45a00645130601e802c41c00718860120f00e10107881d0698040003518210004920342c142c010704060240020104407038295642040230007c0801d1100656030f00d4203003400d01a003180c074103001e050720420324a01003413034a40c150401d46100803400030480380320714460041179544c0d003406045080312441e140c0304881da044080001000500c0c0a40c0145161031408000404540150220304100b020040030802d40741c0d8000f6a40c802101141c1d40081c00c1d03100c0c0b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 385303048 1250 385301798 385301809
    0xc081c030b090f1b0307020115170705270a0506212e021602040f0e0304030206071106040303020604061d030912030d0606180605091305090a02040207080307030606090501050403030509 81
    0x401c40c44d0742c00b400410091120342c107421070040400c426401090440d124440c1c400c0030b5021000c501c0d100d41c00f00b902003041c0e10700701409000b03102c0c1c810bd03503c40c0d00c12448441c500b02c0904803070141140d5290000c1c4552418111410302900a0035404a00521500c0c10100c0e120345101c202031700001c43c0090070002c081d03e4a040b48100425802c0115640c66600c0c0704100c0f040303c0000d00b40c1c411407402d005108114982d000301002204a580554035150540d82044803907041550281c41100d49060040040e840d4030004102441c0203400406480c03400745442000d8030440c1c68038509980361111a580c1c00d0300004180c421444c0200c843c850024400001d00b0f10303500408003071021135414113400084081e00001c0504030303030404034445407103562030b030105484610880e44182d80010550003080102202ca910494104ca440d00580d0044180c0c0d40005081e031b000340e241a54100310000034025220303018411000100300d24140079000d20f1034a0f0028140c0d015910000e000d0110002d402c0041d0f9450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 385304298 1250 385303048 385303081
    0x30c091a0907020f0607090f0b0c030f0f03010f120f0b04060f06060509010215090303040f08090409080315030703020609240307020a030909090c210c081c030b090f 72
    0x60240d8000e0320b80584025591012030010024600900d000f144a103840b0b40c0144043e00c400850080b9842e04d404541d03000c0d58416070024a40d80414050500e02810407801080c260301701280c00c944a5042480081200c0b0580c1c0c04405143c80b24600c8000049501d02e1b034140083d00800a404280e885080150240882400d80017003545071040104d032503500310010303094210080e070864242e07100507a9080c803080c40c19030b188842d69005000080000b508020040038251048c001e40707041442c0a03020130255440c520342200c24501c08810031103803001000c840450520100c00030303e031440c03841e000300b000d5100f100030840c00307107038041c44000f00354489044d00240404c02c0100d1580d20f28200c0c2d0001d4443c4a06001240040c0010f240040c0c0080d20707006100c05d0503003042c0c2e409452440c0607543c1c041607401e0110580380018000c03803100400d0b140c29507a0010090080a0b06080000006404508420001074018985481903100c9507440340e003030350380d48100408142009601c44c0038a85040010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 385305548 1250 385304298 385304351
    0x9060114130c030b0406090501060e010903020a170307080409200901081803040b0309010e0723060703140705010606030507021609020306010903020d030c031b020607150f090b090c0a030c09 83
    0x14010000307408601f650105040f241c26549480402c0181c00044a403d1910b10010754014041c110078400341c520701c58042e41e1b100407007003182e1604005030388640c9035402035405415031554610071008462030701841170070030041c846405840c201c410701c0042d11000004d40220058071302c010303890340c10010401c100d074007070020103001b0307526807900e000d120340640002c4465001d540290000010101502d0b40c02c11105080c400c00400046411424002d054110031416010400c622120f840d84403115401001c40a0003400041105c90034440061700742c03030025081d6000c550000d000d1200b580d0314801c2c0300c419100c00e1000940c0c2e0782c88801c0101c802e401590000b940c86110204401c0401d0b8220002c190510f01c41e841e02d6504103040c41d0446083c411202010790880000c022480c0024800100030411942d065000510003c0c044054011903e80d441308031241a103070b400b03210078611300700f2050305103a408a461040090071543c1d5040c80300014030401c0c021a4071200440348803507400110080100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 385306798 1250 385305548 385305551
    0x7080a0e0a08040f050a0b120a02070c0303020a1709010f0309020f1011010501060206040b16200a0c0b0f09100c0206030c0d0b01030c0519110105070809060114130c030b04 75
    0x6035a400e00e80b040e640f143c8115501c50b914124001510700b0641c0c00c11045500d10018035003450907440c0040c441c1840140510350380b9070308200c01c0c00058520083c1d00c02a60081d40100790041c900d240c101100c014102d61194411000d00400485a0340a030303421844040915005c1601c0700984085109078400011080d4030131441740b41d01c0c4c5820317400780e0318031944100b0304020b020310399030b54400b0ba844107401e85010304050300d102e000a2449001d0381200103690040e1815555491401c0c580300204505450082e8081d08581030602c04c5c0030f124103440c0b0143c400b60f07101034606844d100a01c03403940b08202d441c4c0d018801d00e41c0c500c82e856000ea00030141c0e05401808070b030740d64645010845801e9201d003020302c00d00b504e40103c448481d40300340b02d9181d0208240c0c940368906035500c4101da40000c030210400040141e050390107a01400b003801008d000b010303544c88403c3c15041501819050100582101040b42d1b103622105142c1e41da2460301c07500c00f04000364009408628880c0440140060b00312164109 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 385308048 1250 385306798 385306813
    0x31d011713030201290a0902030106050d0257072c0901020a12231302060705070806070c080d0507050405120c01020c0d0b040b0604090f06090213110307080a0e 70
    0xc07000700301c0c0c40d294505c0458843c024a5180c0038508101c1c0000c0c040d00380054420301501c0c0c00002198002d040000012501800c482868510003c81114952820780011201941102140d01d0040e91400340e00c42c0c10301d1420201030546c03545a54017410311030145003140c03580401102e040c0c48106510102940c81100b8024901100818041e512100c00da0b00044c2c05c0a00300b040a480c2c62050a400e41c039040343c400b80d8045003041d2024080c1b070260032445510f041c110b040006942c3c2d04010920188100050f180107450400054201a03001307109200380020b1324403280c00a1403581c01c0310b4981d4080240010307a5140c40000700d40d1400345404c02504250321040114525000042a0900d20426400c9600c031408a2042c0100805e0111005012a250801081c0000e07001500f081c0e0229010b0310001d041c100c651200d1802d41c00c400e1003078918a039241c0e900419402c0041402002c405841c40500071207010040d51010b41c80002c00d400f0400604802003143e141982c0c000510580c0d0707041c1120f200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 385309298 1250 385308048 385308101
    0x2512171b07030c051e0607030c29061f02030d0207170412060b030102250206091804031d09061225050102010510050303190507020d031d011713030201 66
    0x40f00303214080ca911480888844201d1450b044001032007840c8040e00480c10b0807e2035a09071541c1c440c0000480340c0c0038a4024081e809210300c10b28000081c0c0c8269004070905201084c00303c4010071503c071aa0b0344141554071042d070341d0004100c3d100450030800c010fa4038003150400b000044100306031508000e40000740007952056404118000c103004070010403a070607a040815081348140e949108404140e040101340024540c80313407002c002d00103041a840e00a05c1800140c3d64000141000890138055062005043e4048950200106000703115030940b920303640007902003800144003500c222880b4441000d00c0b1414450059845846001c0c0000700d0710700411903806040c0c83c010300b0b00547c80d040000380030030100c003206030407203d0140c0514036003640c94204c055030383d0920790444180401045020016202c110f20308088078000c0c0e41d40c10007044081d01c648a002a560f0320541001a2440512805644120b4050b080318850500200707135403d5160903800750011071500c00382000e04545c0000c0c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 385310548 1250 385309298 385309313
    0x718060518040b06030a0506061908010c0908191502070302031e030a14100e090a050d0302092e080612190203060709031109040f052512171b0703 64
    0x3540c883c9400d60382a0ba500420301d5a0784d0b55061001d8000c0d44808045460360a20080d210340c40d101c403446030107203151940d84d5182521803a4030128000340c0050820414840280210b217031508050800000955480d2070711010789907609525082a680018000101802041181c50103036050808400041040303800200b0303a082150101c0c5c03c181010b44001d0030600c071650641c400c0080082000401d8101b496400700e02c00f000344141c015104502100c00801c80410150403814030955003d0398a55542c0c003403204890311488080c20401c04401b8015500300c031480c00709000f19146c6030122090741e6030030015001d0034100c81400694001c0c00d5451541e0203490f5461a2124000d074201d64158580c05c400b03d40c2c1e5829840080c0103030340007803020915884c0488900360001c0c0105046410b540954940e541051002d00b59001000c0003281c500e501d01c01d0820404000346802640c4100a601980320341d92007400c41448401020310014802081020442d00c0f802622031070001c50380b074907131645403044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 385311798 1250 385310548 385310551
    0x7050d29040b0103020c0619090b010308190912031202040b0412022e0809100608010f050901060b07030507150606050d050906100b070c08010f02040306110c0718060518 74
    0x203006a00b4030305091103650082c001c0365808010100240205c0e40c540108000142c1074420304c0c92a99100c080c08408940500c0c03066010394080c0c94085d85e40d0624803c81111103601600e50000d01c07900000c200710f81022080c40c4120ac58250820510f04c080c00801d82d402880fa9401060052501080100c0c14080c130741120803a4a1003980e001102348100351200c103840e030301840c012001034100301084d8030b018460100c0c545c0240c51034045440200c0e010307280c4810384105401c0307150107039518117510548203694041e40b90004410002084503c0c2007200c4c4807441d100710741005d02805400500341c410004404114410f508003480d04111060f03d0b600018807a90024904014607400c1001250141d070300881c800d0300038200c25a0721348850f460040d5010964000000556407100e260b01d0015251500b8026440f5004c06d02c600107940d20b00394604441114948140104030072000d200030300d00c10000240500c07d5071280c0007040360001c00050303840e025003100e410040c0c01c281504460302e904540a05000e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 385313048 1250 385311798 385311881
    0x5040302012304121401090305070303140705030c1c06030b010510030b03190809030105090610060512010608040c03061404031b020f19030c0b2a030307050d 69
    0x5034168107949140e80d0351800c10b01401800003400b007000b00078050500f5214034845203d200960860006041e4003421100840c80c150b000c1140091503004155141c810204050305c0b4020300c0aa600305030300010114040148082c40060000600801030b40c44408001d100101d010410f108603a160314081501c0d40e828803406020300c2400c1c50900b102400b901401084100150040000001d8008102d0074506030500130f8032540c1e800c0101d10710680f0b003801841d226010354030082c1803d0402d1203044c00c540c0d00540c80503003007160501200c500715464021050450791700d46800c130015203c43c2461084900306510041c9081e241c0034009007000d0300c0004440c0718600030380710801d102c400f078000d0850701001080001c0d4088040504045540340c103d0302040760803c0d0b1003c1d94880ca49035a500000600d8541180d50f00c2a07000c07a100000380383c00070500341d030086440440c140404080940c6271303036400f001e801c2c1000d2110100e4141081c2e4104c1c0c1c841c030700c41d14170340100825105154600505031003100300304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 385314298 1250 385313048 385313057
    0x108150a03050f01050c1806031003061a01021e07090506030718060f060c0f0b0a11040b03061512041713090b040e01020901020d1209050d050d1410290a0504030201 72
    0x10810301101c0140c071f507224030002072240600282020055182c1c401040402081900b003008404a0141e104405080001c2000754007009180703070019280c01000180b0715001c0f40341c40b14129a610300418400300300d90904501081d251103010020741005e495800006c1815103d1016058a041e2600020700f111006048181450b4503000202c0700c0c041c00e0080a400300e525250302200141c2010700c444d5014000403c000f0350903015114003a440c0c0d2040d0b100e04a19103000c8248689881d0100410100c5441448010300e000702451b0714100b04d035401480a820500c445a0003800c50081000700e40307007242c15000055034261150381c0d0b0780c02019440d09182c0a6480c05030413480c06181482104c0c5041e905030005c0c51040c0848000303c403980141c52400d00c0c11038a440d00c44c000110104581140b0446545803607858803c108001c008403122004140080c401240600601074841002402541d03480780c8c0130705451180c0804040200f5040070b5038480307501c0020328210380396408030103401507a100340da5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 385315548 1250 385314298 385314301
    0x606050906010c08030a0615030b0418020d330603030f0305190b01030f0204030506040b0f0f13081e030603071a0a0522090501140904050c0108150a03050f0105 70
    0xa00c009040221a0a40401c2e0b8542201c80802d030301c4005103510541c100703808076819480e111404040022100800301103612111420600c0c07826008025480b41c42c8141114008969000699a00c3c00c005001e050980150803521184000741e0703003001d00c601c2c44500011031411088a8000800b40b0f80f0095000614407003d007912944139004c2c00740218070540034801c50f0b41d111000ca600420f0081c250505055540070304083d0f11407140007800056020f10064806840c160800b4840c1220050041765001c0244007004030250202080301c0e04040c000700004490155450810868422413150b64075511451500d01120141c0c01c00441c07140c5015016901513540c2d8071525000103038049041d00c1215410702803040024465000707030015103041e0440c0708401c400540c40c080521082c2d04034107003030381e210401440303c00d0ba1a042e4000c0c00d5420b03150761400e490701e80c403080d459070007a500c124100605400400c0929902401c580b001220040900d8911a075a281840d600c3c2c4080c03a034180a9400c200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 385316798 1250 385315548 385315559
    0x3050c09010905040506040219030b041110091d0406022106150a080c0310030b090c010e060406050304030c140f01090c0501170106141c0c0207050303030c090d1e0503070606 76
    0xb03c6008560280091026446a5080001000402004002c1da0f4642e2a0010105107007000450083c1d0207030b061000910402c206000842804100342410b020085404201a400420740c0107452442e04905404d00e4585191420187c4100302c6c000c008040300a150402641c12100d00b140543c800b03c428031004003074101c005002d40070305c1e466038000c03d00e030038006003d20403a6401141c2c4035031046044020a926a5180b10090b801036424002c1a03109141d42141943c10003600648082e088071a142032a28140006005200c0244014100003907011040108240000100008004202941e0260b201101001d00030310b180c050a40f18050040400070b800d50088100c0c0c1c881c01030446540d0016802c110083c1c030103031018422000c0c51002004020300052f440e9a515480000102003c10741c804208002480c000c0f80790410380c0309800420900003140d001008940705880c0548a80205c8a003504065080b654080031881d115510400d002e020014048001e00d280c6c0c2c07045400b04540381d01c84 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 385318048 1250 385316798 385316801
    0xe01030509030a030e0c1c030e0427020d0c061205060a0e16021023072a020301060509010308040806070806060706051807031202010e0319052203050c090109 69
    0x540e2160819001080740100341da00c40d0304003117652a00c000440320304480c07a901091010480c140c0903504081810380f003c0400d5440382d1410b000500846084c4400200030620041c80e010f8880d0000040c40c00d80c400c101152100d4020004031074100d411000d04a544900242151040356402c1400e2454540011f007180b4201328800b040e6070100c0c07070b00001c03076641e00100841000d084035960700398801d00800d000c04001500a040004c4007603c4c41c81015410148907180d480005400b400c1448080402c00402c000c0b201c2d90640d05e800b1800d4100703000368040c008607005040c01c0e0415500107a2800000c02800300920003001201c8065003103c00d145d075000b00880728a1800e880150b489881046500c01086c0c040e00710540040014445451000315a641c04c0c0c07801815601c01c44107554a54480c094964081c40361031660704460303000e940b0300f41c021400716282d003078401000c000780200803d03042601102d18030248410201310780d0707403445162241030003640c0301059401c40d4071a20f0207000108240145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 385319298 1250 385318048 385318051
    0xa0f03090b0103021005040b0307030209090a051b0d1509060f0b031005010509040b130b0a05030c13020a02070503190209060609010c0f080c0a141506010f0f020118120e010305 77
    0x10289250450f401c40c2d0800500d21080c000311420040180004100c00c0390002c0254002e0207180c42c0140d41e4918101803060010004054080380d910f082c0030002c444000c3c500781716898150b0303c2215600c030801000b810090590b80c10070024042201c90114071000c07558840d07016034401c0007071207034000d5444081030100e10041700c1c40c8a0903800d0050400155009001914069100800100f44414110003042400d074520030200790032038480d00b6409803402c00e074081e00082c00c0c2c16000b0f000916001c402241040384000e4610301100d900240742490780f03109211440c01fa10004040d25001c0c2140c00c10b0182d503102090081c0d00c9608002d0100b1103c0ca030600c21250103402c1070711900080300443c0c8071003505001c60201510000410403111120304e03014080014110701c512031031944d801c0314040040c6800e20404481081404a40074001140e802442c071328145a620300c6c0c1440d4110401c07000b02d004d0400d1142c03034583c405404040750200081b41400e1000004590303100342c48050028011003d0307650 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 385320548 1250 385319298 385319303
    0x50c0d09051302031012030c080304060b0a14031b061306020609010c020d0f050a02070803160c0801060302030c19080303160e0312190203070c0b0307080901020918070c0b0c0a0f0309 80
    0x701d0000400c1150300c031b1240140e500c2d000b42000c40314012243c4981300554001c940480c1d601e903455004584a25000c8107080140082200380c1481d010003102080d95142c40750380b22100468041016030f000c3e507490341160410041c5526489419603a844082d5640ca029039400d19207508100821200500c0020400c0c0741d01c1c00c2d99104101c441c4000303c03d540b9584220210800c60040701c0c0c000c1403407a0100020280021186a109510480c030300780480c40040c65000220a42d06144042000d40c2d0001b4001c11920707011103002460040b00001c842c4007801550028009000100030400c00d00c0d4403420718540e030003164554040042c50441010340b60181d058080c0140300d020f0100c95008915852003500480c5540112850000c05071101c1014a40940c080d486a90340001000602c0d03a1201c40b4540149184000754209540c01000603180d140f820301e03800c105061000012859441040200e00c0340f50001e50441d043e0610740c010304165401490b100e008030f00101d0036201914842d03c6244181038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 385321798 1250 385320548 385320571
    0x7030314070c0311061308250b030a0e07030c06030506120c030a060e150c0403030f2c1305070305060f0a081e0c060c01060806150f010f050c0d0905130203 68
    0x1410341e9038441350089501c40f03c980080703040c48660400300c00c4860a4000e00b510030b0013448a40340000462000300505090a549405008000c1001003c2d05054907004442240003041d103242600b5182e107407a90704d13800038204159500c4001484d64256000b24001d84054130103400280303541a805585403e211f92481c0c03d50300c9150210080341041c2d00c0b103101c1e40c0e04e00c0152954a0700d0000c4680501c10b0540c4d0b05480300c07000003400c008054000c6502a00901300f402c20000041054202011140b40c03c8515110101000b07a034010381d0350b8594a05007145101d0b50200014108010028014401106d420b4010440c3c0004440740c0d15184140004540b0701c0700003018200c860342015040307410103030640340c03252044001680c03542c2c1d02c03c0b028100c0f94219100010b951072030410141d00d05100500721004010006840407420348840340441804603007820000000368080d07004851500c94003500c800c1c0c0d40111a0751070380c4030340e00444080071908100c840b0740403001d04142181c03c91105031011040b80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 385323048 1250 385321798 385321823
    0x21204090c0e0d021e010201061e05090a15030f02011206060c050f1f020c0a0c06020a0b060405040f020f0d0606090c03110c1e0f0a060e250506070f12020703031407 72
    0x105104002a00c05c80010320010584590f0740c41e00c0d08405581024100606101c071400b8001800c00350400c50740904101c00a0100080e1a5884101031b0250b0001820f010790301d01840e015039001322403141d44034076001030801a031b5030741e45402821210035480071113850058254401c020000040c03d000c0440d44180c01100590480010070029400340c140095103004210601c0e001c9040d40c544000201074940180202840350720303013844140001040184600d24085c1440080307413581003000c9015078152000301c01519210300003200710966002c001c160a0400341e0201d015403242e0841b40b40c801c043e403030600618041c0d01c4118954005c0d8200002c1d964440c03c1e203001c034200c07402c200411540e00303081611207050030f641d5118184800c00c84144d03003103922a5003000350510100042108403003262440403a12401c01c2c000304034030072079101c4c13244511004544041800100b07040c402a1551000c2d2080b060552480d0103502c0340c41a20050700480c01c841d84102c00c21f06c5c024121044140e001815001c2d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 385324298 1250 385323048 385323079
    0x606080114040605030105090607021c140307020f061f05010518040b060d0903030911010e031e030c190308010f0b030601083c07020102070b060d0201021204090c0e0d02 74
    0x3810401c80307115030007525558000380a0300c003840365900070580b46028107407a1030007810280c1380075505260408400c190042003a0a2540485402c50340c1410f03c070095900e4885000491812136900a0052030340a40f905000000a802e015000310100d00c10b1180c0030550380e2001543c0600800c01d800c0f0301580d070000040c4144c0740640c45226181401403015050400326440b030720071900c44002c22004640d4460300710b0103000440c2400c60000d4404d1a01240790707211200071035100c01d5000c4e007080c60480e403039050080303d5000f8400d980e1140d480c60f0403255120000c03401498074482040c01940810399a6001107a66000242010103583c1640c944074516151140111408800100040c003046040c02d02d00c6282030280310002c0c0e803c005180a032529800502140066020180c00e41f800e583c4104035220000d20b04503500c940c85041120043d200d034009000513428a1103184100310203040000d00410011410340c000340c500c9140b40c0e150348500310f40d8018400750a552100c040d41c45100294040c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 385325548 1250 385324298 385324319
    0xc0a0e060702030102070f0b010932100503030d050a0506010206010819051006030b0402012c0d150219020708120306041d010204090b120601030b070c03140f04050f0406060801 77
    0x184940b025000501e008010303192210700c090a003900310303180c071561401044850110f0043c0c0c0707810344c0000e41001c2c0303000700c4000c564201c5441ea18007540442c0c503240010000c44a4042e22402000041c01b80d80d542d904410300c0100428088407030001c1e0700d240402040c1c0075480005c11605030b402c651300600c980d0b00c1c211080e00c0640c002d10710868051207a0750482205d04414040e080040d44503102c88517090400c1d100140150003022041400c1448a07001c20003039241c6c00b0003000c0444010ba515072409044e9040451076540e1140c6007810403400000d4569074100f00f11a00500364006a003903d02c0e650b2585d01c52612281c40981650810390180003103505413515501643c42085a5890000e040c8802e000043c02da0300aa444480c40c0f95036911407198504240040d802d20a509202420b855030441e030740c1c2d544004000d05124100300c0074851403010135000301e1008070b02440b00c6910b65260200d40c4440d08ac2940316000303160141080401c400304070b003081e005400a644e01600c6280e02c0ea800e00b902040e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 385326798 1250 385325548 385325557
    0x10806090601031410020d0906180206250b0702060405160503070e060d020a06051e09030d0806010507050303010909020f0301051504020d0f110d0b06030c07170c010e0706080c0a0e06 80
    0x91307400b461801d07521182c102d2000300760311101035901107584443c41c24050212020350704140d40b025180c1c0901801a9500821903000002c0d1411200c00011104410151103400c2c071001804681c1d50340034440155000201c444c400e07482102121341c0380c03108040510410a42e44105901640a40d80500c600031003480210340c00f80e0050400c001440c101e030001768039100140d0284000ca40005504d140130f64407d910301400b0b401182d030481c0307420781c403401199442d00410910350400c035030300f004034040e81e11400443d43c4643e0454112503d82d6150b840b80b03802080142403c0b48a0664450000d03a1814113026492040ca072103109072225800003024007000c1d5002a80c0302c429107654040da0b41b03c201c0284941ca81041a881415454460102842e021070380d000c116070b40306513028004c00c413511698034101c40341540c0c0102c0400c0ba80c070804d0a841d000b4052000e0120742542030412103c841c140004455045038040d596011880e220010b820001c0d11031100164001171003810419440e081540040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 385328048 1250 385326798 385326833
    0x50306010314042f01090306021305091f1401021c02160e0a0507020a050a08130302090403020309030c1f05030c070501020a0f02150f1911031e01080609060103 70
    0x8524035607000c0901c0340c9410b04840445100c00300b4224041d0702c4800d02c01c01c48445074900100d0a01110000010303261003000d2000412180e00065403048841e808841c0307100031701c03001d051610f0500b04412445074003900541d1142091075104000140200300310202d00e08510181c025120420701c0340e0302240c9442c00603031f00c0c90541c400c80032030070034000f60300ba4038030010314403407062040328240b041c034039803d455002e0982d60440d440400240041200130840c1100e41c0e601400c9940e94100090f0030903102c00300b5602c007942c04200c11081100b13060b0040014010070b05d080b0240c0e94150890802c008001d1140155154030030010038001659070b012720000d5400411680d84581170920700c4d6682800d980c00704428800142112001c030040640400c0149141170901000340b42c0e51401e242c27110b40d5520000e080d001c19506e00621143c052919a22407458008503001c411307078038540720f4111000110790b84544030704418007400019460300c022400e1401100c15a024141d00d0340b031b58545103060048080c0b01d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 385329298 1250 385328048 385328051
    0x304030201140a210207050111040302011e020a020607030302090102100603170c0f070f03020a06020a05060c160c0801050613050c1b10231e0118140109090506060307150503060103 79
    0x40660401e40644c0035054100c0810026a50b0078940c03400c0c83c00e4540b540d0600080321410300013840180e8003d02201d9080104900f140102410094124504000a04043d41040000906005043d0b0540003001036000c280c0841d0303412600d60425000b22030b01803201500300810503040003490341100d0700404060b201c5508071200e9030707000c449140c14a6a1030303010b40052070000300708008604090139590001c014a0015264006203038481d1900c40b80000d040391004000040d15407400881100e03403404e929081003a01041c16211543c0a000709800c4d90050b10924020f802422000e0030742c0542881005021140c60034030049440103c1c2e0025200c1c500151801000d18402000103548100f8a280c150404048800300800b000c070300c1c1c2c00102401302d040402440300951071480048100f0b90441e0b160b46040d180c3e80d030603074243d08014103040c9807603684006100000a04004260440b264079401a03042c1c0e001034a401040556a142e42e1248204140030700412004190140000e5584490103050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 385330548 1250 385329298 385329317
    0x90a020d030807090b030906010302040b0915040c09170f010e0a050c0907050403152003130f0212010e2a1309020303042c07020105060a030212070902130e090304030201140a 76
    0x1440e02c103038200f1524491f00d0341c440c4004206524041c041c005d4800001d442c01681c50904031407940d4800200000c1e6401147c917551800c0c610f07441180304800030300345003d171100e80d000344511580d1102910700c044000796080000d02c103800c14011032514107103503100f801401e8880c02a01030200384800100340b8024400c00b44400001b007001d0629172a9001e0320244001004900c198030303111401100062007190075814000c0085102c1005401144185c2000c0966201c1d403840c400100c6010b270054520229508050702a00404400144080c3c40312486684070554003e1018021541050b401450f500651f0308401840090b220341c442041a40090f003500d142584402c548866444024050500407940c000c0804262450303014a9421100c5440244082c2c01c0c502c0009154400600000e4810403601040440080c400c03c00d400040000010654884138030211a4050648600c5401400038642c03002820340b0340040119070a07294161201d42d6000203a1090101a0700420740031410300c50b0003071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 385331798 1250 385330548 385330559
    0x703090807080a062004060f2d0c020d05030d1a150f1602090c090918030a050c07080106080c011e02100f150b0d06050301090b13170301031a090a020d03080709 70
    0x506c0a0030280c0c46d03038101e042425400600401060700001040400c0040b510384040b050942c40d1200e203010f10301004103003150f00000d10680034046009065100000d0307030724149030654110723840d2006000c0e008924000013009000c030204215062040b0b0340b01c208028800c0d800740303d01800000ca004080398901c1003050380400d030703c4c5000362811825010b001c00d40c0e0301c1d207190103491158043e04070020840b81d4642e40204958902030b40c01e20b10140180450440036128003000040020178401009000c02e0303694034142c54886040402d0640002c03520040d0039121490361035246107014071070303004240c6080803000000042c21170068424419031a00c00485920701300c154900041e22070315034419074482100b0741040440e1348070360001e800780e4140245407001c01e00300102e860307004d111240755184c840c0d140d00c0d01345a00b004001107174042400110000c000c0c0b100281c0710f8248a83c401400c2e00940c0c40f82e11032303d5640d003c4050700951010071720131024000f034418204c10340c20414500f811141c41e51200c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 385333048 1250 385331798 385331861
    0x919080f0409020318010e07060521010e1b12040f080705011b020f1f0209030f190b07030908030612070810140a0c230d020309030703090807080a06 65
    0x10b6101e15202c54000c01803100081e2444c04c081c005050240080010b00f01491600e6100c02180c07140205000d0301145036115441c4000030b0609000b0507207015000c540c1c41d42018081d100b0240d40c450003080801c58207c000281900480b1075a01e200404000d850f0703a2580c95401400d91244106d030301d608244a0800041d600b4000c0b1041c0c00340107d6000c2d00e8051051000349419a6800402001c0d0300882944a1260b00c0c11030001154504210259441503e030010a1400c030780100445a076100da080d20400091014807501010351145021218544038250106c0680f005418050301c0d6010420104034149018110140140c4850041c3c41d1001c1e51a01c1907420090320441e00c0c2d00c40c5444804009911110035141e56110030170b00c504003c0408007840c0206040c03136204040303400506880032480320510400a55403800045c050556803468000140342d12a00426001c0b0301046070318002280805000c00c0c0c0c00207481140d00142100361507511080040e21004980c1409000f10400740201241003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 385334298 1250 385333048 385333057
    0x9050c09060901180b1f020c1e042301120c05031c1b0204150303030f05090d0c051507050c010f0506090a020a09050d080c0706081605030c120a0501061103030919080f 73
    0x4449200750080e85200d0103420008030602c614850151015421082c0d0007171054412904800daa00007605c10303140c2f5412507202c008110b201200409000009031b99001030030400f0317041c0d100380701142046035900c0134155120644101101440c02001b00301008520600c61000300959104820079150f109402041c121502d845d01d40e60351a549440c1802030541500030720005c0860741008102904d02140c5080d1541d004d2050702c03040001902d004800d002d000c0041da081b907012414005598109413502400035480b0f207004e4401c9500f42032050004951612a1920510025106150a50340c08080b50021350102c5104010b0140d0040003043d29114062a900c01c58846c03114a5580d540600e826454861140d00400801c0f401000b00a0400c081c011840b1002205040c50343d02c940341c5c8004210503001c0c412108400520b0329081001c0310300c0903003205040719820b40b80d507402c03100e46515050716480120356001e600da1183d50f210507264204295000b086d4021039081d4100b80c2d054200e010f06a20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 385335548 1250 385334298 385334329
    0xf030901090608271c09030c1a0f040b0405010f0206060306150301090c0e0405010516050f0304061427070f0e04020102070317090306160c06051801020a0309050c09060901180b 77
    0x4180b00145007031070031284140f2505e0203070070104032080c41c0d5581d070525600306000345892280c01c403803214600412003041e16060210300364068ac5a9899622040b4103401c5441150b0004080503620440e15001103140b40c0144400f030003410080c2d40300d081e543d4060000c54000794040d0368844d0000e001c1100c20080d0005007644000e03c01aa003800c6c1046800d44101400117003900c0c10b070320401e04400d5004412281000ca0404815450340e407241085d50041c070300b154a583c00d08082c4c204001032901e500d204820b014880c242c080490100702c405440da01d000500035801703000700c0000c0c10710802a4241206178424814412102d05542700c0e03031544800e40486c04082e502c414041440c0c021454144005544660600c00348114900301d04001000410020700107408559030f100440d02400380e010040d48850100c0000750342d20144044000d0081c04c2c11103068541c0d0082d400c048800c2c3c6801c031000c500800000b0141c184a900b0075401150b50b039101c841041c00c0550b2100000c501e511a455203031181d41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 385336798 1250 385335548 385335553
    0x5090a03060504060501080105090a0b04060204030b01030b0403230d151e0e06100e01030b030a020a1805090d05070201081315060501080604091e050703020d080c0f03090109060827 79
    0x415140c1354050714410f80010f10264180b00c04c10030800e40015800b550140c000b10310800d15207890070700c07000034415604042c240180400000c814031941c00e1400340210302ca561015072400c043e81d4412004000006800fa000c1c208003ca0712070048550040703400920052844911696034205800300a00c0c54101222240001300082210746480090303c0c0d48502c050310030070480c3c1066800248030421208005050554900c1194000e403802c01c00c032046254050100d100c80c07030b2245507000c0c00f00e1031001c0d10140305081000040c500540031030000c4218400d40c40701030038000135600640e060788004100105130240803c80030041265185d2a0160020a9a0006805091100041c0403148c000c11081c003860400d400d0000103580640d0496030222191000440403600e450084e040210036030000c1d510002c92866030080c424100000c0c10550000b0f4112141c607046411115228090040902d0200d04410010840c07035000b00c2e2115071250074043c1c90345181c4403001050b0b06642220810240c560f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 385338048 1250 385336798 385336801
    0x40806071101050702190f02040c0203030a0b0d08070609080d0612030306051e190302031f0606020a2a0503010207030306051c021e18130203211905090a030605 70
    0x94114880712101200031000b40110300d0242d80284d52070b451840e101260707400952a0074140072581403019030310750b8010010320601325005c400954a40064809050403450641c00c262a850064807203000c20764030060050804440d5112000100b61500068918050400030700c40940b540748681c00140161141044d400c1415080c000d00f124480d4006a000b0030030403207041070350400d81600407801c1c00102c50388145103204045c00380086509030b100075018818002c01c8036550381138060b021111001c000041090702d0303a50504a0f591803c90034054810090b48800d82003096010020124000302d107505818459a1440443c0c2241e20210742a80040c0d9140c3d020301051409150340e42e1040c60000b00c1300625111500020803090107080c0010798035a8001c0c00c0720481c0c503080d027000c80307003079910284010600e0071810154441d0320400d0100e1007030040c0f03100394880356a6210807200d0802c0301c02d0f0540c104001c0c0c0e840c6003072036200030800009000b01407001012130342e2a0100d05020b0751180c030011409 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 385339298 1250 385338048 385338061
    0x18160305010f02090915030c04140402040c02011b030c20010504031806050427050f1b1303121202040807051302070201051210122901061409060f040806 67
    0x311032412080c44400360040015000036a5912003e80c0c102c4c8103240c0107202d00541b0000645440070381c3c418543c1141c20440e4185074003c840503540c0c0f255000366010300c42c8241c8000f0403800c80b5424414945800800400c80101a100b5844080600458104280c001e1104070304d01491204401d9500e803160f4440d810041050b6000e50099000012541c1c421400c0341800350190940c00b07140150ba0344c0384181c04249035410204154501d210b031701e004d01000982400c401481440304115150f02d04d5103101c1d0f0040d904005200201c40b84030800d41100540d82d07040da5100040d5070300d156812010018007242e00001c0d98002e00c0144018182000141211403601060040d00541041c001302094414400040582d800078100c5200c0e01c1000c030601d41c1c1c1d580e640b40c000e05149994000381c2190246003108400c02120b00080107015070b403410214903101100d0b100d840280d009014107000074040c541c0400341d0001c000054003824000030034141c20109a03540100756500140e104804562045090110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 385340548 1250 385339298 385339301
    0x906040f111c1214040b0f161a070c170313051507020708060417130f0605040303140306032d0115051c0809010e12031204020a0803130e1816030501 65
    0x7694200d041c80303511000c9021204926021724482c8549100c00041d107803483e8100030007120000b807103da100601458081c10207101d2150209a031a1501075000c011400e15405042c4403007000d980b000c0e400041c0116071048126680025002c250200c40c40e11420000030010300c00010818179101421405283c402c03402854060707550301102c2250442000d000100c0d0f050440d5180281012042d540d50f24944d10144034402580e40c41303081c1d5100040760106d0488d9020000f0002c0328003a68a900d880000b14130801403d11041d80c00c01c1d0b055020b024514615002c0d5005090f42500c00ca1101c40c0c2d00d000c901c11542074603401070035100003070314842d41070100340780011f082541c80450750a451040b01d1180e6560480e403290000c224144503181c0703003901d40d0350b03941d031001d8601c0902d80064903190f00201040711585002a035040b449050315001c00303d40000008165014000a800e60f0602985440000804600003408c104010000c07072401030f82c0403800300003142a02299812840c1c015240d0300f0482d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 385341798 1250 385340548 385340573
    0x110112180528110114040e0901060b03070e0919110c011a031b0310061509060f05040b130801021303050606090f150a0905090a02030f03030906040f111c 67
    0x41e004502c1c2d054080c001411070406039402540442440e88907169100181d4440c1c40c071030000c008054000078041000741d10081050700403c0104001c1c010207480700116651400704554580004034841d0580c45a440c01c0710720550020220010f12040307850a031031940c2a1154508411040200040c00c202121803d02ca01c0481c0784a89584100101da51303000a41c4030844a841105404101801d0f0004c5a07000d00500031041c2d05040c040142564418020410124060140700407811484002070800d00403c043d841c0d00c2d007540e88a42c41c16007000c00268a5070400c1140b944803044150001c50340400900c02007009510400030900745038990f05d8003a2030030301c004005c98003400c2810144a84160340c8503000342c101d0000c10182c0086510307440807030000354181d484a41050f00340f80601483c081c5c04035905070340e41d00075401d5800985000000d0b43e901d00c02503d034041a544400000f5002c40c1001c80d400002a121b18404869103c0c80d9002078450134aa004030044411002c4200040201c00c031480c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 385343048 1250 385341798 385341823
    0xf1e06060801080615100504090c0c050607020d0230070503030615040b120601170a051608040804060e130603151a150903070e01031506211101121805 66
    0x4190500d8a00040c02c07a08171508540c0d80950710403d190f0401c0d0780200143d80180c4103598080010720a07402006107141c0b62140305682c240030708004200e410344081082c1c00407004d180c00030403802d15907440d0540d200d03840c00c155140202da41c2800700b100c00c0c00c2800601646018a00558a0f400c01504011560f2254a09007540f45c07010041000301514507800c0d502002c11520b964005543d40c200140d8524000d807118081100303e0380b0421a1440342544003a0280903c607030b5501c0c3c4400c08800c2074034441d4003514041d0502c841400100541c9104483d00825054050300503070794002c580c000f040940d03070a600111000091110000c110314654403078108000700d900c0004640e0049080450300800000c3c0d00c10012040c001031603e8039031010005180100018095812690b03501d041c008100703100d42c00b00c0703035070700b410500005441e44440c40801142d01029030050900d02143e42c5245a4484528075503040c0030343d00401d20741ea0348180c4500c6017071030900c14446429504a00e8020309108095541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 385344298 1250 385343048 385343053
    0x15030a0e0a0525180905061f03060b06040506040609180b0f090a021306050405040c0309051f110a02010b010e01180603021602100c050708010504020609040f1e0606080108 75
    0x141c004a40c0000e0401c41800c0d15010080020f42d100c4210101d107440d039084184130080002d02d01440c062254049525a80100107865803512440000041c07016424219009002c10342c40030300205034640c2c4240b90500c0020041484c040e030b18004502160003a078081030210f10000e10800620140c040c0308100880007500030000300c1d103490001644008040b40345030040140c0000112640d046604481d0900e400c0b900c0d44540541d40c07503008203180d0140c01203a0045041c00450800640280a4070008952040c094034000c0c0c5d8541300e0b0351910214446851490f41c0b070b94144151000404000c00ca00000d66002081c100d50300c40c0054002c82401104d507042080c3d4401c5c44150040c2e0b404560300342d031200e14001d0fa07507070146e5404c254400360501019510510038211005807503040340301d100141d403084c000d80d000160fa0300441c0b42241e0084902a40200c810030044205283c568001181e40a48070390003d18070066403100b002c641d0b0f81c2e140803040507980c2e030740903c10309410451003801850242c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 385345548 1250 385344298 385344313
    0x403050a1b080a0f330c0e0a0e041709040207060b21060a020c100507020c01180303020303040f1a01150914030a020d02010c05010f050103201f020c15030a0e 69
    0x11a203d440000c80e002800058585951042c0c5da620f074a40072056000c0b10309052101c024040004d0020240101100045098001c40c0f54103814600c0c556400c65180080b060348648e42c9491b5241101d00709c0b0341c0305402c43d400304403d41c00c5a9480c030180450130701175400024441c10b41d4003480441c0b86094500c031241100c00c907002440040010b04d00d940300c21240c0c005070721804c0101516180900700e01c0350349280e038200000c100c203643c0d0010b0410101c030740980e03c4030100c41131002c850502c0d6449000190044e0820400100840e03004048600c0b13940c81810344280c1c005094544a000b4070382030308894407400050820b94032880d4490000720162280201c0705032800c45000009590310b076030000090003031855440c104150380c05041c1400300c054202001303020240400d011040140802d0004907102d240034284855031503801001d1040d400700141c0000909030240002ca9032010390403103200c0c00c40c815110244500d89442c12a0241d03c0314070760469440c0d003495112401030740c1c00150041c15580c000c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 385346798 1250 385345548 385345553
    0x30b01050922031b1403031005010c0c060f170702010c030b010e01020a022e030203090d0504030b060103050c04090212040510110301180b0607080904060b04141201020403050a1b080a 80
    0x186600c400c6075044c24041d403000c40054400000d450f1301c00015113140113040e110090340350003000840c0f00b48041c0c0710014005440308015519103c0318840500105d5402030306000341d60055281c5900d000c240d00740140640007040d1211401002182ca24006075116024a10102c0c0c250150074030982c02402e089000c0d50003000001d660303030400040644502c040d1001c20320610390414207940c5c524560254400e4101041c00007502941c0282d032440034501c41c019001c840c243c8150140e40c15030360300c41d2030310340701ea1185801100030b4400680ba0b00e01c090410030000412103000e200030700e41920401080c4201d1b182c0b60070411b0a1032504540581c0203400c00079500f46665500d401c8905584200f903c0c00350303000c0311017600c100510740c030781545422500000b0f60101f8409403070041e003800d42046070107010b07868072640500514040c920525551512101d038261041c94140301c2c0300c003488504030005041a95036200c8502d8908100e80a072002009516016582005280080c1c064012034005024003413456 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 385348048 1250 385346798 385346851
    0xc081012030c020f03060f010806010f0b0a0c050c0402160b0a020a08130501150303080a05090c03281505010e0109020301080a030c031e03050114220b130204030b010509 74
    0x50000808100b503070340c0039004659070960f8a82a801018040f00c0d260316152030401b01000080c0201d1105210b4a40005070001e418214007003903c2c66603107040c2c00c161009070f00f6500e44d1001d110450340d80c040c080001d8419201d61026003032100b150b24844000301620300300705100d080040c2089100030b00403c10942015000300303500780c00118145102c80c845644d428000d0041c1202a03845440301c00c00301d400014954809a004e0044003031600801482c0c03514496036644025400c00b007501900308514820740c54500d40a4490215a03d20804030701c0c00084d5644144817400020401006940c1e2005100c0c3d000c101e05214003410184e01c04624650400d05074517520300c1c041e58010100003910100c0e008040c03181d40d07114680c251803400da12540c215140f002d009401d09009a84804030750091180c1580380c10000165043d00400741030741c1c80407001caa150b000d042d0356400c003504080c1c0039250300c00800480c80200300031401003008a156505040401c81142800f9202201c100e401d20600080c51600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 385349298 1250 385348048 385348079
    0xb1005190e01090305060103080a1103310f0b0d0e06090601181407080402280902071a01030302071805060f1e0301020c03090f0d030503070e040b040f0c0810 69
    0x20381c103003901c5a015440049900901c0f94100404a00860000000300175a0744040c02a1031001d46801141c4202402519964050b94018502894407c540e031303004001448034289071051f81c521914071030b640710315050300d058490f584050400380000a00f2070300c00b00641f151600103210386020744240d003021074007246c0d21201806140441c0380c200604520088042d480b1880069000c400300c0c845107070070300b00070f40b050380c044800788d002c1c089191031003500e51502156000c51401e102ca0010850703013807a8084009420402c42115540300d07102c607040c5c2100d05000c0490007140f0a038000d11a07181809c0c0210119804400134034110b44c100400d1110554485640d1512250240c0d040d8001c010b0420b01d0044140c105801c240d059440021641000c0d034000c001800442803d403002d4150b01c02400a1100741908200003800085040c1b000c86c0c2c55904c1001030f80b08564004202203000d4480c81c1c001411107901d1080c0389501c5a5a0041415035a009108181d001001034924111240b800e0b403c0c00701030a5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 385350548 1250 385349298 385349347
    0x301030c06050a21090b060604051302070501090c0803040312090f0506070327031a0601020c09040501061d01090b1906050a1710030b01080606060403020d0f0f03030b1005 75
    0x14003041c68120180301c3d00800300007040301003130015885075441c90240104400c0d0f100341e400d1484c020019190341003000860741194030207400c0604e04214519420001d40207a20210340c9552145181d0380454000c09014000e8810180075655031482c51410b80758141c079045c0f12406111503a1810450310b201c400303841d01120b0003034400c1c980e1090b040c90112440c0d182c50911600c080d00c41d031090500e84841d00c04c0001a644680b5401610603c00d140c4070080308002c5454030b0060f4003009440d215420700e14889908144a0000402c07800d4032805121007480813048140290091400100038214030342c001d1642080e01a0f1741000130745002041524107103168003444040c4800024080d10b014401d0800c4511a904903c881c000350401210258403541c1c1d0744420303203003210088000b0035050320225000e4002c0000a191900e032900c1c50742480800c0d04440c60644884024260b084086640e00c1d040c002c526200b640c0000381c043c0540704200315071202c0381401040101c14410385413412405088400070a2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 385351798 1250 385350548 385350557
    0x190f08180f010c09090606090b1e070602070b060a050904020d080c07050d060605010f080c1207090305030a110d11100b19090e010c1b030807270e060102030301030c06 73
    0x10504454614010045001074825864074250024459010041600f694030080d01071000a540e01c00440b00c145c2140a100c0c08450f0400186240d041c0d40c0700c2415203014003140d00e504110072501c035032040344c1100c801070b2500842c0c8400c000c854170b01605010003601c800c54040103281030940100b02100703084c92004000090010312180e1020041040e1002000700816640c0541458a481000381c40c651242034081001eaa1417202c4650281160f00d2081d2081e01005061407080d5014018980c0090803010034403a0310800171002c55014001004000219143c80c40088100c6079442d143c041c1d1940040100800802c01c0c904051002c00c00741100e20b604480070425011200005116001d841c00c4d865807602500000615a03d03581c01000420070b004008101201e0121030513030b4070340c00031211003031000c520300403000c0005d01980946e0382100551900116080b5200310541c3c0090a121964103d08501202000404125405030b54407402c06e1014500790351442c0d60b440f510844a016600600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 385353048 1250 385351798 385351831
    0x2060a05040206040906030804030204051e0c090117011409010b0a020a03050702150304030c12020706170a0906051024020309010c030c06060e06090a0b220e030d02190f08 75
    0x650380d920549000c3c103481207041190700c2c1e47c0d180c843c4030751307025120490285041900240803880921990310702840155600000b40d0398590603010b141d8860791a140c1800a81940c2c1c0031001c0229504901802c80120823a15061f20306003002101c0b981640103040c12142080120b04095002c2a1060341c2581810107503103900d800c0c4002003064480d20344541c10844040108424140c2c40308440b07142c103000b90b03400340ca00b81e40f6400890b204e440030701810b0082042441e03113102c1c0c0601c030b80386070b64400c48080e00040d203401113646650980300b09458502c009012408d061040e000d040c004c00301680202c141c18414004086800782d2a80915640c05040c0210b1144e44802e150241d40445400c6a000c281000903580700e042510300c200054544038040d82c4c80300300051401c4040c2c030074a14202002409143d8a880140c4112048040320500c032a600d519001540303010103040002e0103650000540140c2c80310400100941618104030600007004210344001c00030380d400040345500288811104c0625 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 385354298 1250 385353048 385353053
    0x4110d0510020d14010f0302011b032003130b030f010506131802040e0c13090203091905030307030506090411040b0d02120c01022505090a09050d030507180602060a0504 74
    0xa0420500c02401c41074000030701c071800410b46034005103610301d01903103201403a6200c12255031180700b940070003800710b030844500c1e1010701c0c1e0300c00682e90003920a02d043c50701d009540e50481c05400710040351100503031000c910a41411071403011003003d80304030240f0034110f03d05502d40d00c00403007043c0b040a004020001e100000325000311695005044811082201c1e0b0f0f00d8600c0c01c2e0025405485100702c42c4100c803000c01c020f804a501207584181e030314106001035509003034101000390310241c00d0b2907061003140000d03000c0301c0000c1b04280909028030040d64407850f00390f0303003c6d00f65900100510b2150150100b0000011070a510214584406440020b4144a00c4000c25064611450042e51100041100e884a010005204d801148081e400d440110103103a0f00c45400c198503202954246405007010b010500749501c14544c0302800110104544d800354840c41d00741100080d0300030010740c444003048162074100c0307019401005034002c440c2e00b42c0c0c501103000707481d038401408443c0c1c034589a4011070b06 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 385355548 1250 385354298 385354303
    0xa0b0c03030402041d1b0f01080103051c020c0315011503090c120201210906060e0603100b03070b07030518010f1d30010b06090d1401060b0301090c02100504110d05 72
    0x10300356a480880704000040a00c1500d8401408641c40c81f5100c81c8403096071a52080d021541241e40c40001070803050800c081e81c0050440d01905070007140704004811049a40030402911480c0c00c925103554103504281500c10032000f00a8458140f6003400605000905100002002c550400740b01c500500343c80c4c401210080070b102c4c500034250814855100e01510664440035170107104881c1086407903615540e6580401040725016071580007022140490140c58004081c8444001c00780c881258658110064a402c0354005600140d4041410400ba201002001d000001c0c02d013000045500b01e141c00820300e100c11003140508520b010b50041103a151090300407483c041c003407032489483e104180b070716040018101c000c1c0099828043c4a18040c2041d00c1150b81044000d000e84e13021911584a142440036060f01c200304540d03a80d60001030703000b00000518083c05217200c0c080f4a0402680d0001c0ca040c81500030640c00c1490300081c00000b44542d4070419070b03130200b07607105d03400b06000341420303030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 385356798 1250 385355548 385355591
    0x2090105012106061d0409080405040903170403091a04030b0c09120a1b1a190c0b04060b09062707180905040c08282d020a0b0c0303040204 61
    0x61801c0030f40c04036255402842c5007604014030442d88151800c0e440400c03054950125015020010401c0140014100343e00800c2c00310b40a41401740c20744500701c200c0c0755541811070301a40090b03418441401948015041d502c0000c0c00356440d01c1c10241140c0b10030101d8880035120f040210000690034000351a1080521071070080a03003550355400e02d60038a100c3c000c2882d04030001d28003440d100803a1070116052943c88038400d042d0201c2c2401c00d0800c4c195103000ba00a561818410581c0750040020003800d0301600c141d1003a0301c0840d01e4a000410303c80d809002501043c03052168035140d940c40041d00e000d400e0801c40b664000d80980d10b50754030968254480e42101125911130780790101d408a4a0741110340514400c07002640996a81c0e035010781c841d050425420401c10440c146084116900e6120764007890180e001e0f88680038081e02c420b41d0101c030101c1042800c0c441c1c0e220a200f0352800c50901d4008110380000f440ca0010481042d988a1000600003807196a4800e15001c0380801580c60700d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 385358048 1250 385356798 385356857
    0x20306040902030a0c090e03040b040b07030329030d0813230109030e0f030a0201230f070b06040e0610051909060b07050f0d050f07210c0203010b030a0209010501 71
    0x2560780300304d1800d04802c1e803402401840400b5041c03040201d030071800081124112040200b006003000d0404d907000820360b00021055013016194190100c0c00c2d01d007000340c481c48018000a200d0240c1080b030a1500f054680d113442c00030702102d0345c200100c05442c122005220790f4001c001c082500001c202c0c034140504030318100c00d40c640c60021203100b015007207611a0b8120004491ba03c0b4522041001c055442c42203d400030300007164041c4d948004100d00740b1446c88050b1700700d0244d081c005551885607aa4000300801c0d03441c2000c510501219003083e200b04100520b21001a080c0c501d030800b46210700c40303041e105642c0907280c44142c0b00b075403c0d40c91480c00050824200148542a074403c1030b04481d4001180a491070302400781000200c1a00061100c1290a1525510304181c1c0d50800b40c0340340e4000003c00e8851910318a911541c0c0f410a00d201c000a000c5515885650b5800d8010705086500c0360b0b007035038000e501c10854440980d40e00c281ca141180c5091038100d81250801d6503085401202c02c001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 385359298 1250 385358048 385358053
    0x909022a0a05070e010305031213060f0b1008010308031b070b010608040311010603051513050d02010f0b060c1209010219031e030c0c26160c08060403021002030604090203 75
    0xa1599031001103101d010180c080c00c201c821190300c3d0414498541004e00c40205641d00c10040300c100404c4505590394400da034465903081d87c991549403542038840c58031701e410a046d515941c081c070b20700d0302403101c803140d043c580b8003150f0179030559594079074503c0301922904c0b00c8a041d0700c201c45c3e06244882269080f5502000c1c409155075540c03406031520300c040e14103d010a0300d046514403402414490a02182d40150092041c10b05005158407500c902030f000440841044c2c1100010420800c0606100c064a40c00014004081187c00e400c0700d1051270000d1141004000130040c544001841184a40f03a00c4030300d695078118940140e1130072050360300d00c400304942d00c1e441d41c080c95040484120500c45400c0e40c5006a000d19908800301c504902143c40070038845403503103000c02d010305840c8210b038401c1c0c00cd02c440d00180104048681d0404140000b1090005c500d4500700310b01c0141c001c4c0100000c80003416541459600a91500d0904030340401c0300743d0200001341c0c5030384c82c1c0c1c0000103065006000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 385360548 1250 385359298 385359367
    0x30606030b062b03140d05040b010807060c030206010e070302160521030f0403080405070f08010501051905060714011803020a030207050307050a052211040612020a090902 75
    0x401100d400002c90361a48608107400c0c42c5150038801d62100e4100b101c00524021840c80a69025100005c040900d00c00e03241d01030118005414040c400d0f140141d000d01349003040d81d0700d03002880c2d103441500c0e0813480c200038074242502c0000c3e800061403810f549200c013050000760f8518034100c2c000e000d4038031100d000c0300e11038260506105001c00c0801010700311001a0f809180d1001d008842480300303a03076004800c215400001c0120b0b1240c070607a074001f4070440555410035504c501070000e1a0312608034181c6a590740004224a24082452440703514114024428842c030341000103e04d801101806070045800c2c00f100c4501000a60003150129002c50b0a1414070b410b07400c0c000d50360700c440030003200907100d40c0c50042507034500020716100319a0005c041d4441d00781084248081421019401c0d1742000d101100310844440314041e429203a81100d11042c0c0f9146031003401040c0b50704100440c14514410440380005c15401351940c41540c132101000360340c6850304000c10107440c0039408112010b0b12000e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 385361798 1250 385360548 385360553
    0x15090f1214030f0711100c09080609120f0d18032a0213020d0e0114060a0f05090109021602040c080a110c100e2103180c010e0906040603060603 63
    0x304140103426656000090101044a0240c0744020340b1010401c030a4000000c6150303205070111854101d00806903240d0303485a81d29201501c1641c40d444000c03e400c61070900000344200a00b513440b0120b00000c00c129140c1d40202500c52144d0141c607140414001048000100941c00070010460611101d007001c0d00c041c1001022019460600b00b0101c11440c00c0c0c4a007800882460324840d500103104800d030020524085009511450554006d55164400001c0141c0300303200d640b103a030007010420041841e103001000b5080c403050b04403000304490110b00380001e480300c1c108603041d28190f42c40160741b0342d0342e00d5503240b802d020070034025401400d00411f10200f56010104600400d5200001e114a0303c6070b40e2401c85034003c1c1c03100310000350b00600e000b0a810509401103d4800e00817000e07180601800e0103d48500c80d181c85030300c1d91200b0300000344551900d000500508190070a40a01101c15019000800d01c03551440c0301407060402001150480d561940981c0003150b1000040000c96640e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 385363048 1250 385361798 385361813
    0xf0b090a38010f031a090a090206030c0a030506030f0d140c1b040b01021b0f0612090d080601031103070c03110307150e0a020d060c0c14032208070315090f 68
    0x108441400a240000200090343c040e004031180b01d9405c0042c0f580c020440404d001d06580002c140040d45501c911800000da00c90200450049d54403440301c554580104e1710150aa480103404c0e24084d50048864503121280881e8260181304180740c40c1c4010401074100c3c4010b800703130b00744264180c0140d90040c240000c5100600ca003c0805072400c0c0071840803100166102c0300b14403506c4142a1000c1220b290a107021170250008960051900c0d0400c0094a100011490111922000d56006004103109550170540c00c0e40e214809103000d2100d03000f41131480700715020140000b4284910501a242094050503480400010042c11070b900c0f13481d103040448040c100501c420001a00c2c1504e48034030030001245168009402410050036034504d56509401840e0b800c00386010002d40d042e5250000d11684001c2c0a44007a040c01161035141002c4207011076000c02c400545c84c810300b4001041b481c04082510001c40780c11400b00680803e80024142c00340c003d071200100700600b4103000d0810071111 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 385364298 1250 385363048 385363151
    0x6030218040f05180106180905010219050d05160c03110a0b10180b0306010b0f07020a09090506060a050907110109080406020d0f08130210020a0c0b0d0f0b090a 70
    0x20100009291340c05105042c200c980f1402281d80c03401c07031103104100306020f40d003141000912800006107040050390210041e80c141d00840000144002403c2c10750310024000d90340c00201c140000b14600c0c11440001c0c001820320100282441a5040c203040e980c0c009009402c400d54110204044503d040203131410494668003500c10a282444060320710b095440c420641c0450b4083c0c000c102e5a42000e6110013180c110690400914108000b0400103071681181c5d84001e0460380e41c0852520b13154a40382d402d03c0c80c002d02c501c0c000c01118000704110358402074280d82043d0f603410011004003601d180300e4054900c415015200c0c0344002000118140e002500e0480c6001036035500141d00c07048901120b903031783c0c1070b605416000c2210b1881c5000d45010200c580c0d8108042c012980502560b0f0341d2000458060b41c804079000d000490703070f54624201e90042080c02c0a0962040003110104400501040809400f6a86007503440408800030f000349100c0d01000510791030304100b21494a100b00c04481e49 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 385365548 1250 385364298 385364311
    0x60d0204091202070812040f031b0f060e010f170406051b0f0310120c41090114130e0f06150103110304021305070e130203010f06110706030218040f05 66
    0xc0e05c03600e141c8681117441a02c040e136080050018620345552200c562003000404e854161082e404ac000940c01c6010117000000d09983d280c0780311404608001402910031604014180f281c44096840e10380c0c844450a980310343d118000081d0781d12030782c0800e620351203c82c3c110b17031a00500160f0082400d2009000e036200c1c004000090311225103075900b100c019100f17070030001d10151030305006004d8050a20840b140c0520740c17030000b10981c00300c1c0341081c48a4010201d072844000c81c41c443c8008074200800650301420003054180040c050540100740700c0141405020411551030011305a948000d205088444001004407612818080e00041042c02c0c2e041460b408240f4006595420f42441004c0c1c038812600104501624200c8195100103080c00030103a8040210241048000d59268240024441c2503078100684a41c1004001800800103030001c1060041c2034241029070700340002c4110669a1624000d6100c5c0c07480f00d400c2d030504204000300d1b0b42c0241440ea8090210350300390302c03443c400c50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 385366798 1250 385365548 385365553
    0xe300307060509070f030809041401030f050f01050942161b0201080402010e0325080303100519051c05010c080705030105040b0f090705131d060d02040912020708 71
    0x845041e2003c0d030b50b0b0700174468085029046401040810b001c00003601c0140c80c080e1010440d240784c080307035640d890f00076003040b616108214100002d02104205068a071150715000300014200040743d203907503214021b107100100074a50b20380340c1c50310807906200228208107010106c07a183d6400038407018130012900004960385015665141602c1514907a07266403a05030400d03a0038081c0c5c0c0044a100c00001c5c81a4180460315101c3c1d1026181000405030a100c2e180403106500007011403e151500282d2000c0101d9000344184040100400d400030101d400848192510f15400782d041200c88400340d01c6158006c210341d5030341150715010480009040e105100800c0300f82c4041000380c40d41001518880006002400140b0450500754041c103a002c400078209079204240c1000148a404120382c8200000d4021590b04960313400443c00e1005820303183d0101c0304001604005005030a070040c1150301c00c80c04020004150740742c95001180312600304441990400791414041c0d550003a600c500d00b89071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 385368048 1250 385366798 385366801
    0x140708061f0b030604020304081b0102091002060408090405040c0e0106030b0a1d0f09010f0f0603020108160f030c0903120e030c010e150c010e0d1701090c0e3003070605 74
    0x1a100c079001001690100c914060031911041c052000079000203008650300c080800c076010840342e5000d850003032207902000250f80c44031020b051000020559400c14155030015050100080e880c809483e0081015640003440d50740c0d03410441100304141e070003424a40b0460001080c11585500100069001074078903003011a0360b41140e04110380841d6092001a41c0d10f004545042c5510070400d4212803c400045030303107070703260420400311000186018122603886008200319600801c885600c4207483e00c107d82c662401007006880030000c0c805610030150760703000c0c1041950251101c8405540c000c004206413281c0712001400244049907402d1182c42541303c0f49209600c1100300210041000c0c03c500346407244a411030740341e80c01c064803000141d503c134010380600707010820602014100907550082c1003032182080740709201c01030700660801c03814001c40d0000240c01041c074814054040d104040e58440907206000d05107400484035046290803a00c000d91100c000010b01111070044600700705d00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 385369298 1250 385368048 385368091
    0x2031e030916180e280b01050303040b0a0e01021606110114060f0103020c03040518040c0e0606121905010603060f150c0f061503120305102114070806 66
    0x1100e152050106100842c000e0f1080721840350018030403250307010101c0304c04201500f46500e0201240104280075112000401c0500984c3c440140c0140030070380c0a14a4182030490746c0759144209154030080c0700d0300d928400708592013000400c1d00003a401368a40081512407100030000060340940005560800c40981160041030300b00c0c2c3d0180740028a04a8501d40c14401500650840414203487d404240301c00695515402d4100e030b02c8010b9803c903003d45142624101340788c0780d0180c00c8004594403140c10000305840b42c02c1100e020004644252469030b0310312801c080e42001110301c0002960500d03000188554040e0420021b80302a690b0b25141d02c0c1d1650303850494540c0c04040381c0e0001e8180e80428001c5444610640200c1e401401d002c248842404071b41541c418507588102c45848640790b001c22072551500c10301e40c120001d2290b0960317091a1814928000601c440c0c8601d8440903020603100304a44456001c0c01c840c100000c2d174807042d558240d0152500d80490b080800c1d510042d0f00e0021 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 385370548 1250 385369298 385369333
    0xf090a030809120105010b04061809091103060a11030a021c09060515030f0601060f14071506060302030f0408032206050610050403050601180f0e060403120902060306090702031e0309 80
    0x187d80040c03091904062426904541c24040e09505000081c4010004100d082890080741c0c3da15020300b03800d002c0500f020003403524000f4000c0126004c113207000441d040e01842c4c541225045074070301c0c60140c0c0b20041f280d120010103103002e03044129103162000c6c003030400c034490300301502c83c080e801d500300a90100402456219541d071900340035590840001031010178014000029185618a001343d01805141c0010751a680202c0c4140c5401d00460700c041030000c068011040905814502542181000c1c404504803000140c8010b1440102000145061051400b042d807004c44084e05200e07250007031b0034003000408054400502501f48410300700c2d1968052000c917000c40364880b0050581340c0c03800d500030820346500050b40981c180c903030821100c400031a02984c1790400c0800007800d018105840c019100010b0103540e03407040c43c100800310703025075545001d4030391100003034481c24110f0350b0784801281980300d06040300700102030202c071384c031040b108007000381d8030520030316048500140346a0392202 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 385371798 1250 385370548 385370551
    0x607080f010b04032d050709140105150a030c2a060b0d0507062609030903070602071208030c04080601081b09040b04320f0705040908030c0f090a030809120105 70
    0x20b01d00700c0040100300102c440b80607150440303145c000d00c44484c011207035940c03410542a41e01c82c51455440b4a034402054480b120500d0042004441d80818619001c156001a0149500c11001e065950070b000e40030a0089038401c420b000d400040d03c25001442c0341030802100142c2007a10041d24001c804419401d1041c002455550828010420a454540225450b4200034042c2050740e03c07840ca03103102d210303e129071540500759090285480c0e56600f000c0c1803401625070b100380210340c0220010040e0042d4281405c1c0407980044146503299070741000c00e2224401c2c2c0d842200c0500c2900000100c010300811502c0c0f030a030b40c034410001c0010580c010400214000d030340140c07480c1402c101040000d000c8443c4030b07141414130300103011544814074120548107424010200c1c1904000b03941001d0360003e1222b40c003d440d00f260b0070042e00d41d0f0758a62680c01e01004000d40515130000070701c409a11381c210151104200000c0240100c15202d02c1c00c411550401c0b00000d008002171034003036580000c10301465 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 385373048 1250 385371798 385371803
    0x4241506050a0905040c1b11031002040e0f060901140a0803040609060807050906270907021c0c0809011b0f0c033003020a0306080106080331090c110607080f010b0403 73
    0x50f44444010310300e14003041c82d4112307600d9940c054090904d0301d09001070301008003000c100584851501440c00380030000185814888544072080003025a1148541c5040d508044e0b807a408841189c00491000d440a030400030306880081000140180c0c00040c1c0b50985500340e0354041c440d16110802d80749809210289a842071007030000340d00300c0e80c01520300b01104100110b0350710301403040f1300800e505480c2510b81100503041640d00300d591807030010541c0d014100925250b01e480806441c0e00d00c4500801150504000d040825000403000c1118000c56447d003044520610403003901d40f403848174055101c100d0300007142c0410510518400d1041c00d004100280760500d80912040c4101c0003540603c00f50808d02d44e4031134010540741000d1042c040a411400000d5550746074504100501c0c080e43c0222240740481d4900200b229000c49210030700311030135020080f03604a00d6800c1514134482500d803090091254204110000b603000c00c0d018042c034020710042105980302d04001d4510300c12400301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 385374298 1250 385373048 385373057
    0x3060308070b152d0103020d1506110c01080f130b150406090e0a0b0a23221205030702100e061005040c05070f080d02070b1e04241506050a0905040c 65
    0x7a00c4000304c40c030343d069001051400524020048004104407040640042034a888841050041640181d40511021070000044c51703004510350008000d841c005102c10f000d5040724010a805599030911204420340c00b1703074510003d180900004400130810b0801900c02ea081c40400202c0034860f00c1800ca1009554000d00312500c5503858090181034064240c040c041c0d554094102400c40900b03030218070a03d00b02540d905402d0841c40f80002401c200b48440343c0015010a101c00070f4010101240381003060b01385140ca940d242032040c0c3c02c00000401c2203640b10f0520340c0345165880701203901032007503160111140e00242c9500600c000c0f00c07100c41e010408602e08115040210710300743c0c8403000480c4911006858000e601c0c00c403d06a80001d0021a40c4003020414030425940641c1008518801d641040e0f0b00c0c2e18142d00c46940c3d0603010aa01c910300e1551221619000354160003070301400307038a100070004036699a80002e100341d12810700980092403c0c0d03c00720700c40c6060301a1800c4401e0340d944 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 385375548 1250 385374298 385374349
    0x915110313031b060c0909270308070309210807030e0607030209130c02071809030c03051606060b090102011118060c07150305010e15030a0605060103060308070b15 72
    0x30265810701d20201d4002d000108449140c0004203d40101007040e1721a035a00c0d10020715100e403034401d5507501b4810403c03d901d0806420710151807a541e0301c01c030980615000d009501d562000740c005001c80c00c00684403a0321050f00c00003090300ea04d103007101e40d80d055a4101c1c00e903a822204404484e20070300c01c003045800000c080f42540c0e20940140500650091008805455041c0c5c0c04080318034170b01c04400960499201000100c200e0b03050401502c68003001407210360a00d68000380120801e101c0181071240104a13071040e51180d4400e140801e61081e401c00c481e0f61100201200ca0708000f18140c015824000c0c034012107880c02040d1040290798004401d441003061081041c6604445084000ca201340440000c0103da0791180100680413074500151950500c4500310061600801404030845090140c0c50f451320002240b2046a80143d40043c040d02d650380102c004e040c0070341c40902103400101b1070714103100c0443c40c428001e900340000f00c0d0a400c800802d20030241c1400040c1c0ca4000d080b0744 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 385376798 1250 385375548 385375553
    0x12060709051e040e0708011107030e01030903030209030609070305011a0307030b18030f04140406062c0d0b061309020105030705070809040c0309050708032502040b040915110313 78
    0x1102c11120410700c035007901c0e840540e40e010404680c00805110401e50107250100308501d020f02c6503a4169520040c5580b41045540740606000d03c120130b400d040598a54070700c4107040c401e60544c0c0f455200101555481d00304041710b40d41e90302040c0016039280d46402d0792448003088002d90043c2b07241021780a442c8040c555122a0840ba800400d654401103c0812144000710305200400c40c4921031004140c0365400e04045641c9030160f0316159005030b00d000c60501002e40c01c0f6020030302c601c0d81d2000d04203010071804032456a81c0f0601c01d0490f000100c48a14a0801500301ca140e44600c20a56000303000902c50000c10080d181c01c8a000303804200100003240e0302074030603402090002d0040a00b83c0c94540048003003400c58050400420001e9910819442000014041c3c0d00040c102d0800450601c000504013160400e0030654103000e040f0f9142444085445540208400c5000280200320308650750510440c640006100c0079080c031714101d40310402408800a803400394111000d007940c2d440380d0703a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 385378048 1250 385376798 385376809
    0x703091e0302040e100e210a090e09251e03020f100903170d0c0215010909060b0a03060501320405090109170408010b030703051b011202070606051206070905 69
    0x70000c01e010300174640c5006020150703010701c414610b0444001c14041c010101080a620451580e52032160300800c00c110300e05a000c0c109106031101071700c8260031501e0391100e03a40750608001d004000301c41c03d914200b101100003a1060100c50f145407800c101100f08000c4522044840d0200035408800301c078900f5043e06010180c13042d10203d6060503807900d85c407038172403020a41c4003070b40300c1e40e42030000502d0a60000c1c6a0041c0140c509441c0018400b030340711214800005501402601c20341175503101002d041c0704154000b8030310b1100240c01c03402c807135031241082000b0341300c24006d02e00d00c00040d82d00f0700003111300008045080b4071f071460303d03007882150181000090700c0d000c0c003050100d40d00d4101c403501041042908180e412410105a40d13554a0054450300391510204614072a400003507040000c19804140c8140804801c03000c0ad2441c15400016903a086030302416086192012901c4030070840c2586c440d0f4262078086a915000001d60700180d40c3c0c5450498190300000d691400070005802c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 385379298 1250 385378048 385378061
    0x305150a050a0e100b191b020d290c04141507020405060d021c02030d091a03040c0e0406020409050c09060706110f070f110109030b0f06061c020703091e030204 70
    0x440300c118217aa00c8840020301d400042c0c02c0d0104101e600310300d4001c45d0b041040076460300d200c1320a20400001e00e030006940e00121603000743c440e0b4481c1c0e40e01002007101c0d90300102016103010403110305003811703042c0140d180c01502420704401d0072030342c100c803035031030708400080000341c500b000903240001c40d40c00d000c007601001c0c0135250042030b2900e01d2001641c50700c00403406400c2005480740908035900415260005030a414414400e901c00b0500803036104a040044006040b004165251a06d01d400110009a540300c4078040b84030005100c1003002c1d42d0000d00880354a5a020b02981c1c40798441201c5510030710034400d40c407403410811180002d03203540201021881626595042039103282c3c1c0d10003260b003c0c8408a4403044000e034854100100498000e100450a180c250280b5095a07200004e490307003c2c4c004081c0d800c480d00081d43c1903a07000308807503600303c8101050030364011140e502c0c4083c3d00002c00840c045200b500700400c03045446240851120041e207841d42115180d9020700c4000c040c1e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 385380548 1250 385379298 385379311
    0x613020d020612040201080f060d020d0507031b0602060901060b0a030b0102010912031e0501030b071d2e0809120c0106050901031b0902030c07030e030c0d030305150a050a0e 76
    0x10000090340159945001400d03560462104000040c0b400344001442c1c034000904906491850109100540c1c03901684041d06540c1550007041440c0766090051402d41c10342d10051806000150b4030070104400f074828011034620b03400700c5a41d42c981c01e0615090b5480340c0100c0ca4000c0040c40030507041d0388030f070b0003070889a6018000054900544d484144c0d450a10541070340109480e2580c00030450b0101000c4220040e520030100415419503568101d0800c000e8800301c20482c282094199050145c9413565160600034404c0c0303400d09440403615000311402d556154445078445070780da91240a4501c0500c180e07200d402802c0086a034101038442d54224a0f016130350356580384000300365a1510000240a5800740d0301c1e1024460ba4407561b9440815141c2200b54054011310074001c60f4412101034800680c0e140c1070184441d00d02c0c4010038034100e46085ca10340e002c0e914000758000c0c141c00d0b40c0164003c0b0300e408511a080000903052240c000703114410356400200d0201c080024a0459060942080c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 385381798 1250 385380548 385380559
    0x1002040e04320c100e06041208040905090c0406060806010909021b010908090a0605040f0b1e030703140106140f03150a0306060816030503090409030513060e0918061302 74
    0x8814501001a5a0800344400b01e6a220784034001c403a00d40140c181294558a242494242c440900803d100c1c1c042c034440c602c1242d003100c245000300581c400a0700c0c05400030100c00c0203a0f140c10614140d450091141c040d0242d481d150300410828450b813030320b078071071141038440044845c40c00420100941c010070f03070340c03e152241c8200748002c1b000c280103443d4036500032803460391039407407440400c40910348580c0840e0503ca81000200080d5941e040084100d0786d400d040c43c0e4a41c801e240446025880c22103c17118221800003c0100481d09075003c540c1c00c0700d846440d11320383ea0301c0d5072003035030305120180c240001c9100912051407a0f4807040001c5501041130022041d8003003031140410b440f0b0140d0f40003180c0d065120302040c8104c6008004005180e1000c0c80c1203044989141c84854581c4203282c46d05000d1034994070401d007454040d00403642c4400e051500514250b9962030010301001c40103081500c01c045510120f03880c00d0b21600d1b101400341d441c1010300b2603900c0e03500d22040d0b0074102800c103d800c070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 385383048 1250 385381798 385381853
    0x108061207060c05060702061b09060904060b03040c0b1e0d1107080d0b0402130605090406030c09060602060c030903040608071b060516090b030a0902130c030b01021002040e04 77
    0x5800921514004084640f1903030095030b00f07407030b105081020080c580c004640c01241003009000c2e1310080b03940a0700b18900d41583d40e04c1320101080862003400c44443c0c0003810310600041c7c42981c8030003035120340d008a1380c0000e49a181d1021070b2a070b200740115010b10f04601040c00200c40f440d00c00500200400e00ca0000d03091a40320b10345503158102031820b071841100407410380412000350060300001c02003102e0861410b48900c412950140c4d550180d8820000049000012511250301450142d908001c1d00e02d4200d40e40d00703041c40030305032901075880140980d10214a62010701002c0c2da009408000103107041c142803071f000b01c0707000600034901c00400c420200e40c00e50b500c13410004201c1142c0240c0c80890140707054080700410901c040032070b400300021024200032120040e400c0d26007209040d02d0100f2100ba850001a8450003c00d900300342492802580c0008107070035601c00d4034840ca080e020748030700090b014114400c81c000c1e44184951199600005000221604010100c100402c0d00d010441c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 385384298 1250 385383048 385383079
    0x610120204030b0f090607020f060f09100f0b13110301050402090a170601060906020a030f0e04060317041406120114181f08031c0203090c030316060b0f0f010806 71
    0x1d86044e51101800001d24042c40810401031010541c840da0500040c008030512950307071543e8502c0103015220303115611020941c10f0b80103018410601705140000e014805280240e08014203005412603c102007424003144042e03105d018050b1341c01c4070b00101b80d06681c41c20b420b21000e544490103256101c4000d500204910000019540d9150002801407a031036040102c058500e0405800810640d8000100d410002c2e40c4030040c02410801c80c40c0c100e0103601010b011401070702c0300b9000204691030051284210002c2c00e8050b104982980783d41000441280060011506c103007140207d11404070001803010046408542c48190385c0607000f1f000221040500f15032105007035841c004804120101000071002d0728010b03c016282e13540140d8900980a64914401e1225200c001c2e0010707000f10024401e0001440b11402c0c03004040c0075a5582d45506d01d0b0f050454035280401c8580b64985000598141000d081c14501c810004c1c01900000c1c10020040d00c4c8504010140c0e0741c08420159806103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 385385548 1250 385384298 385384313
    0x80301030c050301050c0c102007080c0d0f0c140304030f061b03020a050a08060a0302091e160815040e010219110604020d240501060804031106061012020403 69
    0x254041c00140c0d05480c02c00c01014299040540038900726601441060405c54021450151240c1c0e02800007600c55040000d0403803d001d4507201e008142404103c03903051100c0e880050070208001000e65003862001c030015a51150400c42e000d000807103001e00d400001d5809071b16242d0001000080300c1c189581d9640300101d0080c0c1c000308861854071140c04100000282d102c030050510941025400c01d414240010180d0041c00c242c9810802c440000c26016103502d9100c101858000d82402041d00d0000094614042d90207983c0c0408040c80c0c000032411001ea100c4640021016502c0402a4484a0403010101d489002c0181e000307a841020b1341c00d02c0000d00c010300010304065201c23414484003071006080041a000c10390b255402283c10000140e54858006c401a0703480401d450320b9251210fa2090351001c051382e602c0b041c0f0710345800030a040d50082901072140e4806da444641c200d107620006030300c80b0b0303007610b241d60807070142918096181d028508260000c00405130050816545e07171510b60 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 385386798 1250 385385548 385385551
    0x2010e120f033439020d12051b03070510020a020c030a03080a0c0c0c0e0c0c070e1803120105091306090606141008060d0309031a01050102010c0e0303070f0804030803 73
    0x6000002100301e220305a080041014500343c0c28000800850583c0c05130301c810909160141c2080000c0500c0004550300c4007401701495070054180350b241c3d030740e61001415550215001c1d0000f1010a144d8a01c0300300c00208440c04a94020b018100c2c060b90390110601940100c21610194041c4604070b8020351410040d00ca00540a603581940608100300141f084a54110004040001c83d5091201180482254004a4a0320840c40340e16070354005100c01d030307802002140d00240c014140300103841c010074a41540078410244410b620b201d4000072050307880c0300d010070140c804440d520042001c0d18040018541c4012802c091400303101d4a0307500c0307108559844108581c02607640509015041c02c007102400c0000c0291140989089000000b404181c4005c1034940300354a00c103203034020144117458081c0103643c042160340072002c0881c45040b05a01c00d00900340150328142943c946180718081900c2400c0b00540558079141c00d42d2200003484c42249010785400d1000c10001000486550055 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 385388048 1250 385386798 385386871
    0x1502090d051c180f180207020d050610091a150c030d0f050907050a120201051903050a0e07060e190305030a0f1403010b040b070516140102010e120f03 66
    0x41011007030b1100040d00d0700c043c00e000f1084101c0364641c00d00110707682d03510070401c2c0d40e440710481000b07098409000c0081d03c00c52500070342100038584c0503005c04c100007800600031040482c019140585420101c0110740081545d048003241c103c43c524460b0400812500308520001c0b20b69241034011800b03180345901862540200698500b058800000d06110300c58102e0804006080710b140343c000007940c030f650540a0051190070f0940c1300801c5a00950031601c50392003403010401012800480a0001c01003120191032290410f0810704c9441000308000c015655161201c1101c20810002c0c070003880701401c0b40d46000c8400356804404140204080c2420780760b90740e981007042040f2403005100c5c1310300a0414841600900050010254410030340f801e441044840c00c2e10381d8400d0a006190054000042c0601c0e8506a0301150030200352085240091003038000384104010105420b603211011103109041070000e109201c0250381d00d000843c2c00c40002c80300fa15200d81e841c0e40c030b6001d441040b0481e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 385389298 1250 385388048 385388083
    0x5040c15050a03051608040305030903090d060605090a0605060a0e03190c0602073002060d1a041107050604030c08070506070f0305011e05060a031808031506071502090d05 75
    0x5194029a06000e51380e80310703980b80c01400300700c0c035400009046040003a100405110020001a0741600104191641150014819005540103041000040819010700c1d80034041440000e440304596024460031101c0240c082d03450400526001c5a900700c03601c458a904d405880c121442000040c00e602c0303030250040b004c0304d89192404501901c0e1181641c813280b06e442601341c1802040c0c05003100e4040b044000441030f0350203010fa10014000c0e12413054802e115620300881414840c2d111006401040425a02040b07043e40c19000008140500040107100e41e001c00b00050000307101d81307502d50f680c40c8203c4d00981005070f1555040c1c24100111980000284079a410074400c550500419004004818a07100035241c0c481001040b10800d00859008100000301d052086100c2d5200e00c00075081039101d00380714211071400c41c49079401a41c40b1942040000c10102291401008035021140c2c0300b100c0c80c1100c0060700d1200d000e90406450107902c0f03030703411917080c000c10021b200c000c0704d10107107548 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 385390548 1250 385389298 385389307
    0x50c120607050a1b02031b01020607051c02070201030618090303050609040201230c1204090605060a0207120f0204050c27010903151b0512060103150905040c1505 71
    0x6124000954518100003a4010014070a8041e0800308440482010380b03411a8401204a00c18060000100001b03415114070403034541c2c60342d144030510100003802d900340c40c499124040d0881c0c0c20701404a0158500341506804c1c2c00a100c286d009103907052042c10080780c0d007581c1b41000078200c0e01d1001032442103519034204100705030703140c802c41358484411903869001c3c1c01c054000925000c10321219803200d0a0385141038107800c50702030640313803030300302c00800c80e1180b0b810f04006100070b402506c6081c0c8058180000030869217402001e07107941c01d082e0350003842120f04d01210348580b140090030544401d0f00844412025071242d0240d148680c40a4041c0d40d44c600340c01c2c410089245074240d0f2280ea10b4a42402a20320b6a40038000108030303500701412980c84622a08240024004041e000c03c4000698840f00300c8641c006001d040c0c424007540c2c1014840e0f607590300541c241c3e05a1030340e00440c01c60f6400e05110400ca01da00683d082806042e9002d041c036202c90700c4030070a003490500e10000c5500481d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 385391798 1250 385390548 385390573
    0x132c01140a0e060d0512070c0608040c030206090d050304121104050432010c050703170105211e0d0f030203091c052208010e07051806011b03050a1b1122020705 70
    0x23096000800551809141618117501e03581740d100d840340002482140005010002179940d00198442c02d90440f055903a40c540c2d5203481c0402c03035030f11a01141c02c8084140768814504e490b1081600c107940001344004281030501c1c40000e1a1110354100e040c2c0354418003292000202403054802c8503c007900c0b842c0d82e4115908010f004114510b41c1000580c3c901b00041c0407544511160056003d95409031040811019800c14101610300c10701000074400d40d103042c17032014000640c9108011040d1905440b41e00141e200714164801240c0203282507000c41010540c0400c50b159a03440207103180f07004c606107041e9410041c0030008811048124030041c0b03405203c440028454070300701c840322400a00000e0b10b00000b06407041d007085140b010501c110700014481349d00580e66080d04100e0002075904144480c540508207801c030f500b6680003d80300f41703ca0340c41304501c4002450550703048084020383c0030442e802c0102c0041c03402d01c055003400040c85c41601d9030503240007409035076110300041c0c4640702008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 385393048 1250 385391798 385391813
    0x307030509150705102310050906060a021b06040902030703060501030e01020a02100506220203040c1a031801060b040807090c180902132c01140a0e060d051207 70
    0x181d4280384030508001040020b04005400103150382d02800c0420b901c540801b2581c0030044017410200301c425907a042100e0b1014080d40002591421a040880794499100740140c42c01112540809640b140306d4010340d120f81501114020a0020401c0e884c00b622000504142d030402d48605020075240d0505005968042c0581c40b600c40380c0d503000f141004824a0000c2d81c07144200d141c100e4075603880340030480f0740c0c9030100c0b580c003001400518070401600300340500000754000c50301511683e4900c180480c00810030509000940704413201c0c20304545903a010100e0045020aa034600f40d90703960000142c50311018058001800604080d1030035600d85103201059881170a03120040215001082d1000c81c0034100c1842036402020b40140c4408080c182d00144207140e400c001c4044c0d04442c1c0d200c4a449803c24161165034000800300b005076610504940040c4420f640c00b80c0c000325034a801c1c0880896100003950000c0c00500380002c1902ca5203a050901404d488000d13845140040d1040c14841d80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 385394298 1250 385393048 385393069
    0x3020105040215031509040809090106021b0f01050a08100e010807050307080312042310020702031b010f0309020102070e0f040506011502070b030a0b0414070207050301020310050108040c080307030509 88
    0xf211442c81c51802c1069800507150400700944034070740701008902400051020b40d924503201800e03005003540c413601c003c0c1d91101c0000000178185006401c500060030094004088407406850346814200c070305406031480d01004041d0050119045000641c44184d07000700e034000c04c078ac1c50241404605000c1450300f01a15074001401582c0208105003848201000e6554000e0700261126403001e010070704040e8507011241042c00510508030a0120b0942c19801044040d03c200d045414294501d000c1107219114044d400c0c0c0070640d581d90102003240a030b00000c0c5218414419180d085465804a89401900b641d004400013204810001080001c000586c05490901d86680101d41c0d8440000c0d41c4209601420391481c0021010442c880380700e41003503000f0704c0700074414400c01121520012405204a810030010b1140250006083c01c06100312809004603010440c1803505200040d202c00001810842e90b0040003130340003540c0001800038184203032017940e4050741c4001801c00c102c0325110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 385395548 1250 385394298 385394329
    0x309080d0c051903020a0b09100b04140105090c07080301090b010315080d0f050c1e010c1b02040209061c090c05120607110f070605030a0c14070618020409030201050402 74
    0xa00c8078aa0020650008030440c40803050120340005800c01d160490605091040c0208441d0b03010f418080d01078030100d2510b00280c2500d901300001c0060034200000d44480300178810303150020754014012804d01c0d50700640d00909404003e40f41009039512280980d000741e01035010540c0c2ca0b0001e0b000c0d50f030b150043c0e840c0482c3e0601c0103480c860808050503110480e040200083c81801180491014001c0d01a140da403c14001650746407042032000c1160b4200901c0308c0c00303165180034900c09005004813080c0708580500b0b154920703140c807140d0174070009501211500e54000740c10305c1161300d880f0080c0d070503c151341c6001102280000440c68403000071344564002078401c03d00c11005d50550f440010b010b560011480c40c1c107181041800080720700300314a41640f034445001d103c0d0f000c9405a0130800440c040d8501c0c041c00c0002100c041800c40e00c8280c0c2c2d40002c800308008120140118405410107030848134aa1108144004d0a50011f81182c0504a0840241c0d45903000c01041d850305019501c100fa9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 385396798 1250 385395548 385395557
    0xb19080a170403080d0b03010f0c0507030206070f050a0302090a03171209010207080906070606051f0e03070506040b03072a05060601020c1c050a0c080f1615050904180309080d 77
    0x900f1560303000882c5c010401e41405940c0c1d0380c00c030804207a5003504450203d0ba08103200f00410034038030200078113036401b10000394058440c11010444691240c40c15810500041d80c92900300000500120b02951000c0c48095000440341004408200e00e25111000d80c240d0070022666444588414061024000e00001c902d9206004a0010901c00412550380d25812201c59940c0d09080c80c01500610154010350307001103220341e10b00801e1502e40071605c0d008680b0b4035800300b4011240c081590301c02250003a41e8200030301344030420003810000042c41d08a01c560a0a07440c01c1300114000c8080c1c00641840400140d2001c1c0382800e210080c4051600329030b082c03010380980112080420082c00d40407400c1070741c00b244110003105004d4184142500307643c3c09000010741035551120266141c0540030401c00341c2c005d0324070002e85441814000001c0340c811184a1040d04503222059481e5088400c0c4241c0080d1120a411015040e110100007130510035102c003c0d4090034281000d1408904201078801d22 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 385398048 1250 385396798 385396807
    0x31317040320040e011103070225030f050709020d02070605060103052403030f1303020a05060c070e0601033207030614101e030902310b19080a17 64
    0x914020aa806540010300d0441a036039400c1e0200f00180454180c0c0142540f03004030ba100c0b0440480c2c02180102d095500b201d900f01213154040d04201d000c004c161444820040d02040050641c0c20041003076400340c026100119a01c0c40a94140e078451002c860030190300003517034420001e0038842c80b07030044020300c0e0030489032804d002d0103481c460510102c0c0c030007407041c1e0100380c0c103a070b50070011070706104940e2080540b9032200985228202d102030100302c3c8503440010740070415080c0401a501146441d030028403103140f03041c007107481c600c40c0903181c28101034030340602104102980c00000d41d00c610b514205000d12800e02494529180c014003c3e06c00c050400108010300155035440000d4003504a442c5000d4905c980300035206046d102203080d115102d545e0159010541503401000440c0c002c0e00c849200245100929031606241c0003000080e801000040007015000d45c0100400c0c40c0c00707415901c07562000d54914000c503000c3d0b0312051a950140301060304001c00c05404148500094103242d040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 385399298 1250 385398048 385398053
    0x311150115030b1309080408030a030617192603090a2105090906131104140108042307080f0c040612030e091b030f0114010e090112020301020f0313170403 68
    0xe5141c15561031940320741383d00b4070b0f401b80703c0b102040b900142182404c90303907506216003010700501031501c602000000200955480c00c400850b841c00f016041815292044695a0ba0300440c0c3d000e050307450308d051110115021551580c00021400b50440d0b40003400ca8070901e203080c000802e002d0070046c03100d5603003003408000c6981040550700c2c200811a200035080d654000802c58402251501c0c44405041449900491145d040100141c440041c2d48215a03e81c820054a180f0800e46004006000801100140d00c01c5404504075140200080d078903495540d480e0180fa0030059a240d1203185c2050001c0c05079480d003481080000c00300700000c400c4920103510043e00c203440d180c86084c019019100000c450b0200c114484286071917401d1116104c0c10b0001b01441a5a02406280f481c070311407500d02425036006401c1c0041041c002403c001d85a803c02c901c00803503081d4618100d230599000d20800303040700304c040091481603d19110000d00c1c0c2d00e80341000c0c090a90302c0030403400080000c2200344003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 385400548 1250 385399298 385399309
    0x303030b121f091106030a1d010203041a06030a050a05060907050a1505090102030d0905060f0609041101110c06031501080601050c0d03020318061e0a140406090311150115030b 77
    0x74401007440c400600c0558505203191685940c0e5880d80d1701c160000208012107110ba404000c41c8142084520000040b0030f01083c203d110964010b000d51410300e03042518400301d01400d56204102070242c0d08641d04980d2418a000700d48002126150051020417406450070050540208000c48294541525102c4242c3c000c0208111302d0003082800510309081341d00030001c031030303a60f00e940d01c0c10415080c6506200740c84200907592100c3c0e488804003c03403000e250402d42d0300d01891b08010741c14801c070803c40064400a29040c03c01c100760142c070079002d085951300030143d481040c00790305e007110061710b04000400c17410000b02a01c1c1848000d202800c0e0401d000640804441da8900380140c1d41c3d205c48407100c100305104c6810403610312488041040c6104035504655401c41c0d1028100c84980b1408050015110071448458100018200003804a0803d4220041213806030070700341120080c111425003400900040d18480c0f642841c010090448450107101c400c0300c441c0790070084c1707044d030303000150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 385401798 1250 385400548 385400593
    0x30c0904020402280804110904030f0305191503060e0f060a0b030a0c03200102010c02190804030516060e0402160b040c0b040f081002191412010303030b12 68
    0x1c0c01280e000c60100c59644040507108070880c0c16511385021841d82181c024490b1004807411a582c40700e8014552541c200280107900450b072648a002c2c181c10300800481c024080100400c0011031080442240040e15105a20f840b4503400c0500800e18107508001e0b060322150707040c0200c9503008407540d0b016040040750603034008201c2c02d404a036800388000040e261100055000e00440b841c0ca1001040151029425240d1104a0800d40c030280012005900701c41c0d5020382140036030400107140382c0d6006207a01303c6020900c00e1503014145510303600ca13203190023008820302e0340410a45034103005560b0003092400c8051011141989084d4440c2000c80c00340f03640a0004080421003400b06041100d86c00e5100050705030340760381d42c0c0c44d00d607a82c8045102681c0c502c030344900c0b03000b1410400f40e001ea0364021203003605d08580c080b040325450980d0407a0a8040348071000702c1c1c14800d0080c14000302003640d405000310b01980e0046055540041000f8088503c1444902554041140303000031408000124 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 385403048 1250 385401798 385401803
    0x506121009020a05030105100903030816050f070b012108090105070515090c121b06210907091b0818071e060f02032b0f0504060614030c0904 62
    0x551140e11240c844040c018415085102050b0012950001e074581c4600514100c131401c031940840000da195068901c3c6141d800302a0005810000150804d240351894034260f000030315095180c6001c0340c1c2469119001100200c42d1401c2e03ca004001c2020641d40c16140b2201540b40c44101080e0f40e50384480912a05031420f050200100d025402d118050149400c05806580c10780b19600d03207003042d1521042c1d00207005101c0c01c80b803415810540d200050308050003130130328518410031540344204180d0b0f401c50700802846448500140043c0000170000ba4041c03645103000744411414120b80105035040040d507000c0c0381c4221211000010303805040c458000c80c003190121503110b8090340302800e00c0000e4005400b44404890120250586644007008481d1070b1f030344000c0d400110b81801c0341c40f803180042c00410300301c10203002c0c0c1510640e682401146100c0344400a0502c1c4400d015206039402210141c039483c0d6962000c0020000d1503c0c0601e181c1e00490250a00c092a400083d04803240608003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 385404298 1250 385403048 385403077
    0x1303090803031519090f05070306080d0912260c0c1804110105040504061706070201020a090b03060a0f0602100c09080a110d0209090d0f0f0c0602131802220506 70
    0x4035481010070207042c2e00135001c036017800d100c0f42c00e9010b803200c05040c06540392000240303040340000d9405004038003811040550350300c85039440d26045201d8580801c00d0025208401c884000240c42030ba00d80003c06140403202d2180d8845000e24000390818813a0b054080c018448050030265050302e0000c81d0382d000ba4070507102516184d070100106c0c0c2038001c0da00060341107032030800c020585203640e140450a0140700b00c01c8440940d50740c1012801d1b4002da144000110301402ca051007500321002c041e542c1304001501e2070407016501c2c40b60102c0005c5652007500581c0110800c20318604d80350185055030070143c00c141e00101e01e031010282d40c1e003900200150070a0a10310110009540d141c0c4e040d95000d07001001d40c015406c190341e03840d0311410a0301c00d42022500c003501c0800e801d400781c1603910320328901e5140c0884018060300c1e00750180d4840000d6a071180803161000c00c200c80f4507007140000c0101481d0041c0c64080c12100110340001c01f10b0710710070189040d0020041a5248030854240c111f00480703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 385405548 1250 385404298 385404319
    0x20a03030b1f032c0a0209060a03052802180702060a1a0d0804030b0c12090c150a12061710020405030d180803030703090c051002060406020307140313030908030315 72
    0x10448008003201e684d0541300701c44900e42c09016000010704a02c1c0c07034001c98140b2101c3c2c503000c0812410503000d11004191341c02c40d803140310786881d0704140094200e00352203900d6501e00e26907000035103c021110065204030103100500000e00d504212003a40700c1042d00040020540d440320b40c8807040060401984600780b00a4100708101e40b440980d00110341c0318072500c80364100170b4070041094000547c40b41032205440002070b400e0200041240c030300034014220407074144103c1c42e00d404a070310200342c000510414010940c2912841e00c5190000d2245001a140300380305646494100300102d020000f106006010034811a640454951006246803c00482d003040200e54241000c0300e035030141449000100c20480d4490305a000100e81a1156003100c0c60701e91520104100e100d82c1c2c030614401a40301900050000b10290300554014800e8144001c504000c42c031001c02650045445140380c464440510040640108000c4094408000510f04624085c8556000d40160b120118401c40054a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 385406798 1250 385405548 385405571
    0x30318050618070b030a020909070f05030f0a02090303070321151509030b161b0b04030c020a0504020a0c050d0206011a0a03110706020c0c310b090403020a03030b1f03 73
    0xb2a81006001c0a2280c58172403a1504640d40290040d40585000e000d0b4800042c01040c426456024002c2031030700d40750300310344806c65502001c1c0e20003030030980c266038204012540c0355401c10192142d1842a610107083e80204010320a08000105960f0b41d02810420701c961031a440b00f40280070340d4a115000d072016400303000200d5884a45901c06421003034070350188036210708542d4100000707181a84425203404002807a8a50125000704040d010f800000e01140000b032296001030303081c6000800700548587c9503400281241d00105602c000300780001403c00c1089003c1c0001890303804c0c41e001a20301036146c440900c070071481c3c114102210b1000020140d03d0207000c0d45c0324080741300300c0814240c0c071000d01d850034100070761010a0310441032143c030b21150602d150098101c24143c0d81ca02e000b03801001001c40d03500e21815082d0614540c2500c4403004403054840d0354019100e58000c3e0700503c10360b8440e040180407601c40c01456030140e03924a1381250103504514182c1c0d15a04c032440c0000b007000303049 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 385408048 1250 385406798 385406803
    0x1b0903070b07111008041b0b0901030e010b031207212001090b01060e01021005190b03010207060c090314012714060405030a030e0a02030a030302030c040b030c0304030318050618 78
    0x1c014a55001500f45041c0d07880316481003c0c1791189114503088452100c501420b0380c0303442801c1c4110b0580313510400ca108410b500ca030700400d11207c400000401c103c1d0000300001d003440d6070030700b404058400c007180050178401840200030244103000e49400c26031101c1c900c02004d20312491242e2154860141c01d095504000354496407a89400598200d51561a900002c1101401204c002d00501c509810007910741810b10440703001d17038145500f05881901400e03162002d031611809142d4555030038080600812842d0042100d040c400b42c3e41c09840c030f030440c5403110510f03510300a1010390b03a141c0514203144041d041c01c00c410350509801d0b401035268a034505040c0c0c04903000e9070580c03640181c0d424007081000000c060150425203481c2884034154480040b6601c450018020f94075038007806581d00420302139402160424610a03603a481c140d10b500100c0c681c2e92065404500d8500000204410301da0306108002c0050f01402d04007450710000e03243d2a98980024142030a4080c0c146010007604004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 385409298 1250 385408048 385408073
    0x92a0504031403090f010f020a02010e190b13080d020d03150b1207020f0a020603060d030311070c1a031e060604051c0506070516030e0d020a09051b0903070b07 70
    0x1280318040031580d5580b0707034222900303ca000742d10402c51509150702410b00e40c1c0d07c40c100c5034001c01000009d5001101c07001c0700d030fa200300c0d0000028504c0b02076540c0682003400280000d164070302c1da00c203003100d81c0e00e207000d0f810b41c000c070f20940144079100512a070200d04829600c44070720300840d501a0030040d8465000a40d0f1110316040c0d000100d41890740050b405503403145e8266001d481300b03494980d040540700c105400000707510000800000d801894410041e0f51618040d15000412202d25a40c2d074686a000f010141c443c402c02c54420804640030040c5929101800c00c8085d0545c2000d14802e10000003104000716030002e0980014010340300d0805071401000000c0815414407071001010000014042c415596402008002070707205014004481c407141603010008080c198544040740c01c508150f00e07540d4810700b07062210300541c0d41c00d1462030142400000000300c90400e1041c210b00765076001c1242c96071349000d224503001680c01003009403c07039910403102c0d5640ca02501e42242d24504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 385410548 1250 385409298 385409303
    0x2f090f0903040b220306050a1a030a021c060e0f0d09061b1b091a120a030f0314010f08010f0e07050f030c060f03040b0a050f15181807092a050403 64
    0x222502d0002c20301c070941d00301f03074019021120b08100da20060110120b0424140c1200303501640640e40da1001414581248450b80100681c0d00a200b840343c0c5d41d503002c0c2c0c0e001602d150016403101100e070041e02014007004031307446844e0030402130507854100041c1c404054600000711682c1c011040c01c05024428820485480e00c81c22120021629808054018240c5100c40d040e01081007807400150b0800c0640700b82110080c41c0180300c01080d50f0b5045034510030605480042580b50680700b6460425100300c58040e180b0008151091400d0148090858044c280380c1c2c6101801c000f5003011960002c00e011041d03503802d55084846040d2403000c213251042900c00306800030000141107904401c40c101460045126206224403034442d40d5222080c0c840540d41c0300002c403403c801240c00c060000b20488000c40e00608082c1c0b50202c5000c08800e100030172102d1036080c17502060564075070320302804981c000d01302104041042d00700400c40c0702c1040b4481540318025245030064840c28a01402c107079030080d603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 385411798 1250 385410548 385410607
    0x90b010602061501050c07030204050c040b07030309020108070e0d170c030403150605190509041a04060f0b0303040b04090209280501022b0c2f090f0903040b 69
    0x5940d035000a607a10800c65001c107680340010f1080720700c0e611500458164034044030090410b5400e5808001c005c3c000a85014400701c800c2000203a034910802c09031809078042e4600082c160781c6800007500d010bc00400b610200203508080710250b80e6004450f960050300258a014000100402d24485100d0081c014150b440b0110f40041041160030b15404074081c800020b0004607907400501540d09540781e00040800d2602c4400c0c030642c00d0021000340d206024100300390620200c0103403507903210810f66003540c0280d02c034200ca5000282c0d50160ba068404142c008601d42460300e900034920b1b0085009141e01c1a40005010406a550f0f402c0800703014200c0c9590800e880b41e08400328050300003031250703e0240c020042002003103516141c100e0013203034001000202030707020000304a07442c07400480e08603a1026481e443d544222580c04c1243c104082402504250008010800100c1da200a150841c001b646404100d103551011003a6012554008a2951550700286502c81100070314404c03619400b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 385413048 1250 385411798 385411801
    0xe0a11041e080f0105060306071809020406181401120f1d030d1107020a0302060d0617010905071505092202031e060d0521040509040302010207052815090b 68
    0x10641c4481003021184007608480d5a0304942e00c400e42614011180c1ca81d16820280014450a018481c09180c00300d07162254030756641c0b60303101c0104036082900140000303000c0103400f801c80144c1a0384c0c000544100940d480044160328002002c100048445c01003154070340307500c01e0107050190400c08800b1110320000d2044d0000c0000103940f500981055809141800140101c1e60500030841e4890750300a082a0111401e5801344215039100c19040b1f107000c1e80d61800020b12114132a0841800c151040c00410001651700742a86005a10340101084540b125850b401d015001421691518802ea400d14001c00c3c601c2d0b00c1d540c10254141341c501e0103500004c104501c0360450311802d0190182e06607580170989540c000d00c92000004040104164040c207119001d030300154504640310f144100c0080c3c9480d4650010410700315040d502140035070f4010420b44100441400706e050304610046a86d1240c0800e44080c0c50400d0300c406004c0d103170b51120950001490340d15000651190342042101c00c85 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 385414298 1250 385413048 385413089
    0xe1f030b0316030503030a020c1006080102041a0f031803040b0d05011d0f0708060f030f03031012080702100507050607020c01090f0b180d0212060a0b09010e0a1104 72
    0x29060311451144240103440501e07000358984003128003035039003040007141075994038201000298400b9014044600c0f030040b40406140160140c04040d0807084009a11a4500300100d004100e0001c50b681060b0020b00c840d528050820058aa00458403e1003e441001ca000054190b1207580c101040500c4000303002c5a543c150303900500c0c100c0d060012071107a40d80c40b040c0d031603000e0a41a03c0604440d000003001c82e054a2107040f490343c100c54000c0400801e40400c0c000240f0b48501c1d9107480642d6080801081074040f003080c80e12005040801b4000030411050b07903401c52510840784003c1c401c5031482d07000364019120301c00750343c0082c1d0b109040716128184101c1c041d6031000019080c50018550303400118072005180c041d1001c8403014441d11b410408030b208075040c1000542802504092000040300160b0ba40140c10f08510390400e0243c00c1d1401e05403001000c0e60b42c60b0250031f000e200c003040100700d04206910010360210940b04005203050b4082c0c03c8403001e114680c024031a080451007410003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 385415548 1250 385414298 385414301
    0x13090f1410062904030f06090b01090227030f0d021c050a0c030c050a02090f0a0509030c0706080c120c04060f090e060103020919090c260f09010f0612060e011b0e1f03 73
    0xd00500803c2d403c00356072fa035010078400340d2058030403511140c200100300e1100f04603101003412034808001d0540b030030742000700700007460600300e09424401030388901403801c800704420b00078803200034039131618a00d418004140584141c507100c40082c20000d0340c2e4a00018007000b40410101a9030042c0082e001c2d060007054801501002d84015001c11300d890081184560004112a048c06d83e200152441600d00001501d01e404024045d51100301d08212005e4400e031490742081c807610610941a49031400c084008114002c52150765041c440c25000502c035054a0344103140c2d0095092a000d65999441c8000c1460041d02e400c21a5440c0848036000c180c608880d00200c1814001d43c1d01c1c1e100040d0301b0003a44414400c03061600a60010342c201003031492180c01c50941c0d11000c0500041401003804200d00d0071500307243d1101820070101082d001c2002968081c0c01c0301403284000a02108012044015400714250089428407030020310300005078032002c0141c1e20501222122710b5008522980180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 385416798 1250 385415548 385415561
    0x4170f120d0510030b0112080c0307030804030f020a170313050a1202100212060f030a1e02010e01030e0c0f040b0a090f140106080613090f1410062904030f06 69
    0x1c160501000030309155a8110740d0301202d8000001e60302d5a481c0960001d5107105054041d100e0400c10880d01d6a0404104024941c0030310075540c0041c07502d082d0a000b4185e860100c1d4840840d08000c0c0d0010202d0424481c80c4408071045900301e0340c83d00d6050149214540001000b0250300404107845c041c0050118003030070f82c540e01e4081d10904600c81e020b10f0100d21a540e40c06c1070600a600c04141c66042c404544541154090700b00c500d2201c0c00c2d166100050210054030b001c0014ec600e4042c11941d2043e103100b20725900303003010700c149000c0b108141d4865443c200c5460046a400b2401201079039503800c2045440405821040b03010340319042e0001030500801d031001c0300c0b03081140c1300c0e0051a46c0801503049039425901c908244c0c41e94020003424644600c0c401c00d07102d485003800004201e4150507090311364450301c03404205810418440c0d060411090b0003d000d2490460100580010b00c02540d521b009580c0c00c4d0b5145034003405078001c1c3c41c0110340015181c6981c0d031580c0320801c43e0b070340d0184 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 385418048 1250 385416798 385416817
    0x30f050d080105030a0c12020303090a03050d0e04020c060f0910020705060a0522030e13020a0f02100b0f1c05030c06010f0b040f0b090d0b1905090a0804170f12 70
    0xd011a0b0303d4070305256454407134880043c90140c0555080100e518080407101c1c00e00c3c07000341501c1c50560001f0001e0744442040d04143d865801419a1806c40b0742c2180c3c1d083d08a43e410b441c00e50034600500c06054490000030015030302c0d0480c000000324100400d0107030904000d00f520045440d028281400d40ea2020100c40018246280c40045407000e003001800003d554440c6130080c4a410180c3d03403c40d140000c50a401d44c11480c50800c0c00281c2c1c045001030400503030740c0d41d5503052142500000034500412a6821307141c0504d00140714640d42c41d2444c1c81018014155114000915051440910441201c002a0507404003080b164800c86e0003250060494240700d901400c0c1580b02d41c9580c6542c0300358420818409190201005400c0310403020f0f00052200801c910031441c602e0702d60540e000001c80340c4a24a094200c0305034103003d4184503564120303146000030040d1030500e99428800384030300d00501020514842010510041c2002201044140f1300305482c1151101e500041241e040300603a0f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 385419298 1250 385418048 385418057
    0x11070b01080f03030718081b01030b040608030d020702060705030d05070f0206070203030f0606090411040f0902070c1716030309150503060d1212180203010b0d110105030709030f050d 80
    0x6800700d00062082254500700300550f155842c0c08400340c6000d0036944001c071191000d00f5001503491300522103841404580c0341c00c07200c10440900010100c41c92076552610561a00034140100c40c000410307103802c00040391005a41ba1f1144c0001000350007040d100a00c070780300001e0181e8803110310790001303800703034503a0340b90000b065403940000c0e600c2e03200c22201d9000590040c4000399404004514660300544041e003440d140032501000304040d1095008549440f510002d001c0040d600c001d80030030010010410118103011880c8d4a40c10030a90510907076200702c0e80742040442c0400b0502491240c1c0143c5e030150350740183c0c2c03441c010b040c09000d44500341040e180010040340980c01181283c0c491034006240d21603e00e1690b07140304060f0700500345002084511003424902d400301c0e100303200c803541c01010468411841032040609580c0c03440d600502032340d0b5180403000020949200201001400d0130110313140e0b902c0c104100d480304010741c800f4240c08551868038083c0040440c00407440900d540c0d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 385420548 1250 385419298 385419301
    0x120a022b0201050c0a0f180503030a021c02120702040218090a05010801150312120e0717010c0201090f0809040f2409050601050406051b010509100b0f0906090403030f11070b 76
    0x40c03050017078038505000b0500080000120900c181504a112240d000808a40c00d07202c4020a240d900701c5405840940c1c0282d501355107403110965004c03d2800da910050a2401004c82c050300705025074034000b8044c940100d040603121081c0081c00c51000c6000d070058a4501d084400900600303003e00c04d100083d440c1c41e2000e6412602400c01e4000c0e00e40294100340c210010480454413041107103e02d000e203039034903030104c0c904d0309003405260020705408025010a00141c0442403c46029600300029680340c01042e000080c014800040c005030050034043c2c03190122404100540f07085000e1484441c0380044039829800408845840b5080a031514994a600c41c510042101ca05594640c0440c0b014001002228840d1004200c60b1011400e402d4802000369a140e00750780c4280d604160941090b51740c460208010311442d200b00c0360440c1c09900c5020ba000206400c444041e04940c02403801c140002c05041c02600024803c0c40548001c0004041144010b00b50390410b40003102c3c222031420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 385421798 1250 385420548 385420561
    0x70219090f020405060a0806030a150e07240f051e07060b090105131109040c0503090d0f0906030b010309150e0d030b10030504020a03290117120a022b020105 69
    0xb00759000d03507001420740b500d8160404030a4036500300c0104400d034140b0511004600050101c104050202c4441c0e41c0400c425030245403aa04100654008414007240d0800550340705d4250064580b40c1940341c1003000030200001000c458501c610815840d0803410420384034801350000008280007405100b0800c00340c1000e200308000940284076248d440082e41c068540a0b180304e6200208000c512101203283c282004003107401c0c3d1f803441e0b00360320100d88084200050150b0034001d0050344803c0c0d140c000d2002804a0014040c00c00c5801070701d040565075021240503134043c0d803014440c95008846258102c0c0d4000700310001d008400070180040c02003203002d107461400b900039002c2074039008007907403c0c2c0080380c0801c80092400801c20381c1e000c3c0900b4000400701e040011082c0000320f01e5541c0d0507a081e440740d2403060000e0182e1200c010a10301018010000c480466802030142840c1940c81d9502d0410800b2417424070030b000c4516004050901c21590320503842222403103402035400030f100594902 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 385423048 1250 385421798 385421801
    0x203070f11071505541005041d0108060601020601030b0705030a06170c040b060a1b0c030f0302010b0a140f0907030b03010f0f0e010b01050418020f0304030503041b15030f02070219090f 81
    0x100c00c4000c110005c000d10315051030302d0412520003c0c00c6e45000d40c1041c2e0b55104141a03540480e008080341503400d0010702c5030000a00445034010801c2c00208070715407442d0780301404408024684001c00c01c01002090050250303400400040c00c2e0b180520140c5440c0250003030310382d10501140303440783d03180c84410920341c00c00c102130340c43e00040f80d1680c201c40c501c0300b4540d400b0703407040c1c1c00102ca001c03180c10001300014407654142d600003030081c0d0000134107c080c1018405540760b20340159060318200042c04010740e076040140341c2c03405402d45e0410510f417201402580070307003003842c0c0312540f47d42032200084418510358401b6202203c03000701408006c030071314011401c0311034000240d07000030800c01c01030011540907881c0c0c01e0361007604403005142c11810090190250802d0307400300c001075800000d100921400102c4c4000c0f08400040e40c03142245494904d1064000c9c0854a40600d42c94140d0000d41e40080d5054800e01a0068000d09042c40c1c0d28818240e0501c45000d429801c0e0301d000700078604490715 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 385424298 1250 385423048 385423177
    0xd050906100b0d090c0e0103150e280c08010e0a0201090906050f0d0804030204090303051801061401200a0c0e0901050c0d0e0316060203070f11071505 66
    0x2002402440c080108030755a01400220034241c1700450300303c0f0300141c003c28800c000341c02140140302040358203038041000c6e42690144502100301d40d1006415131071298100824a404c8a80d0424425108071189000340f94500964489200c5519060380e03841480b02c0403450300c0c45507201340c0e1070148142d03c5640a104440040c014503030082c48840d01016142010306640342500d0003200701908181d6658009030650308014030480010b074441e010f100391401c00c507114219200720040244086410b02400d018000d0324000014104100420030720008024080407907480c180c08c0c0251540c9540f6070400c012910034900c2461094880d52001615141040c41200c0c06240c042c5105031410745e104240da03010300b941d290f109841c1d00042142040d4401d11782da00340034040c41383d58090f89030701c0c0007203002c0e024204400420082c0030600d00309020607000802c1070000e43e201d6914400310032007804001c9565000351521807000800141d410100b031210f140041c00c8094005078902c1481c01103004103a003402d032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 385425548 1250 385424298 385424309
    0x4140d051806070515090a020117040b0402061b030c030a02160612020f040e1006080a0209180417120103110a0503100e010e0a06090c05040b06030c0315060d05090610 73
    0x201607001c030894607001c0000e040c814050f00c12500c0d4451041180180581d007500d501c6d040354018070f4800219600030042e40c0e124180c004020b0460f02d89034403040c44d8254001c100920a000010741010050b001520910384c0c91808000c890304c980800f92031aa980d40a540d5800151080440d00714000040040c6001540c4041d40c1d4400b02661000800002e90072210390b01d40510b20601c0007203041040401102d1003813000e600b040382410f00c1c010002d8034250700540810030b118010085400e541c3c40f10344502d8282c4808500d241d64940e90381c10014500d88810540c000c41c1070300010422040e43c41c410985060364000c003007005880e8240410025000301c10722403107406400c5900f020001e01803c0d4012680000c000c00040b6100d60755088640c01c001c1c002404507541569480e4180034001142c150343e01411090741c081020800101c0064801d000c010100d036071f0f024002000903507000d0107141040303180038080c141507121a143c140c05005448200c503481e6040c0700d00000111071262469500c0c08644 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 385426798 1250 385425548 385425577
    0x7050909070513020c03120f070f090807050f04060306110403200f04020306031219080916120c0b0301090905190309090b01232701021009110904140d05 67
    0xd651401d0140a0341054807515601c1c0000c0c0300350f80c110314611f1162482203403411114111898036400c0600b40c101078000c0300040007502d800510600c600081c114060f503001f10307030007644900804005400752006406c001c00d42410140c0c091130f1680170303001400550348a01d90040508840448102c100d038444d0740340c144e004950710304044050409500554103c0c030050240c5815189494600754907603c00d600007002e1009034a614040960f0104840341c00803103500142c0882254062429030407441070003114040c042c81c001d108108103801d41401c00030807214144503201e680d1520020001c00750b401094540c3d006209403103803000383c644204040c1a603d40c03500c169960400254200415612816034148811040320720720911111400d000e000d014252584da40d030700c200b80b540740403c540c1c200c2000c140501c000310200740e82e004070310900310300d80361500001c01019034103101c81d0107010b000301c80ba00070410000344011b01c03103942203c061170440700c0c044940284407180200d50300e100d048100131030403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 385428048 1250 385426798 385426819
    0xf0c0d0e100c0f0501110c1501030f17040f0303180b030f15121b0f030a0b041e02130b01090609030b0f0903070803010f05010905010305160c030201021308070509090705 74
    0x803401054804045402900c81c0a5a211644c1e6580d007140d140343c0160101100104049a06041c20854580101020a100d0207a94516910703081c5030107580768020002c070300742c0500e0a080040d01082e40c00402082481c1c041c0c40b69a4200604007494012881c1200c3c42e07034100c040b990300d070b2800459004442400d920038066954006880100380030002d140d501c50b0300d01181541824040100b404540d404151201a101800e020004045241e88425001b500000c403288040307203030999615407090304040d07034880b80000c161000c0301c4186a400003d61080400710154a1050280c0c803c24420800780ca40002d4103880d10802e840150070fa100003403407404c1c07480018183d54089080c860700b214a00003141d061101030350f20388a00e5042608a00188810207000700001c1d030f8071034070010081c242030038100030a00303041c411640003d43c0c6000e10820301840100901c01c25100b541140c040000d4908850407090701c404221f9240c0b10548a010711920080001c00c0800d038022461780121880141010080c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 385429298 1250 385428048 385428079
    0x507050301260c0d0305030a0b090402011b03020c0d0b0907080712060905070b04080d080f040b1f150908011d0d0c0602160308091b1e060706020f0c0d0e 67
    0x548165014402c03034007640400e00380c5612154a08503103d44241c603182d44034602060501c00712500401c501d807046030304905000250340c20a100454410020742c0c0e0b10511079035800d0680c0342640f0365000c0c035004405881c00b00306000744c4101680c022031182c41583c0c1041d50f0b403ca4140d0320389180c0a1201c1d454890380350400020b6096000c688a40d20501c00d9038a296030312031140c9419003241d07004030025040001619000b42e88840b046500c0b841c01000700200e820143c40313110406100801209041d180f00f600d059800000c0d80b4000010080c000030788003903820b040c0005204440034802c6104c0c640c28501f0941142002e8000c0c5403440f801c2d02c0040841c248601d07022110400c24680c241c5401d47d003008000341c45652107240b003400318000e844030a21410403100740c500d86146501e80d01d910880161002b0b50a5455071040b20303101400403000180341c1a028000340e0cc0e07118080000300388610004400c0440f0031180301400407241c08900f41c0301d07245407900d401d50300c2e805604940e952013044501c01e5400c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 385430548 1250 385429298 385429349
    0x60f090c1e09040809150315040e1c030c020f0303011212050705100203101410050d0f020c010c11120f1803100b04060b090a0e370507050301 62
    0xe0800740248030307010003075280c0818040d0109903030035105410000b401040728240140c0e91324048a80e001c250340f41d850289116680d009100782c0d2140b0460f19010321014070103040055040d00c500c004040c00840080c000082c009043c0035130001c0143c014101c0d030b540781803004800d03241211440d1014154a1150307070b4130100111740b100100780030300c0400e10010f00890010011014045211030300140d90342070048038140401155070240104c0e002c00791003404140c5a03035100000e203640d00c0c00c0030707920b5420350388040d4040c0c824146000c0c1002c0c40414a071340c040300150086070318124180c13224002c40c1c0d0121000c903241c1440301071886103404c00b0071203024210010402010059000400d4002074924800060b052226142d1a050340c29201c81c0110140c0ca414424003004042d00b0000c103182c540410045600c0c001c092158921418070b0b0300000316101040d080c0d094a10a181c05c00c42160049401d1b140c0b010901c090500301410719010014a100703001d030044030f0581e0b10041e1101106402c041883e80b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 385431654 1106 385430548 385430569
    0x30120070b01230f030106120c0e07080705070b041704090c08011e0b0711030a050d0314061e13020307110c1e060d1103040311060f090c 60
    0x180c3c030f1090340801100b015502e07401c0702e04c150340002c0c2c0101501e501580b0000c0b40b80b41c5000405c00810003403400d481405140036919194208101c1c1c00441c100d030010b000c00e8080199902041040d5021940b103886416441d6203001e00d004101e01340d410680c0070a40968884a14011554018260074090600e07500002c5400895105441420380c070f501c00c4507451800003414805100ea0803401c00803e030405070866204010501d001e42c2d884521221900000e4504403881c0c0c2d20401c42d859032802020001d1403068224400c1e1b4103850748600a0005c03581c00b04810f0800e114034011030002d144a14015200c021840d0281e100050501c100ea04001f4030910503600070b80688242100d205002400a54246461f000120000e0000707000402d84030208140100030401050341c0070b82d40d08800030070070040c0c4503907480d12010069101802d55014881c1d4001007040040c03402c105580c503 = true := by decide +kernel

theorem cover : BRFrame.Cov 385251798 385431654 := by
  have h0 := BRFrame.cov_init 385251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 385251798 ≤ n) (h2 : n < 385431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
