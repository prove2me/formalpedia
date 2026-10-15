-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4289
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:08:09.477231+00:00
-- url     : https://prove2.me/submissions/c75aa9f5-0c2e-421f-8d35-865e3c7f336f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 771223021 ≤ n < 771402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 771224271 1250 771223021 771223031
    0xd0608010c0c0602070f020a0308030a0513020a050f030c120c0a090902090c451e0607080706060f1e140411070b15101701051219032d0e04 61
    0x30400e40c51b503c1e034455000713410051102c0c01000340142c180285200d011818002d002c0355a078100251032a52040100a401580d80071090040c1d181c074104280c1390b0700016003143e400100510020341740074400b41c3c810380716401902254900c0d0400d02070038405448102002c0c070811001d58046455408010184206e02402203025070155000d0b0f1407105a41c440003110001c0c0707003039464080c3c0118128a80c25410001607800c004a5810810400541103403076404642180351880203000e0781d0342c0704000440305d80904106e81000200c16108500241811068685e2107508021604610709003103040c030b030611110800c00300081600941100c10180781528042110001e202c0c1d44203440c01a080d00424080b01041008441e1640241d00c40400340704550340f5040a507c0003096803840310a5500d03007094164a001440b0606019045083c100040d01c100ea20903050890811241c2082640450000f030150030032709141144441803081d4010303480030145545464407030180072808203485050099032071b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 771225521 1250 771224271 771224273
    0x203030d0506011407060b13290609030604110f06070503041e080604060b0901052202030702160b04060f050406021b0f15120a062111060408030d0608010c0c060207 72
    0x107109060004d8038007900e520b840e8040c514000c0302600c02020325900078035840008040205160240003110410105052a1501d14480411542c2030300341016400280c00c0254508a03107080220b244a90300440070584009106010031800c0c20903040001e105540c24405d05021030701c08002c40381211000f40000d003201e030168100d0580e6030000c0d03000d5401406480108030070b00451f50008549502c00311030102d201d82e01c920400078030f03462034214001a0000217107c404100c05503802075070171100f00c0c0100d40044640b1100787c041422180c01038030407400302050411805802c180405850081d60134020300700b50500d08029510481c17020f4080988011100200194984c0d00303404004080284c420500118404181040395003c80d15000001c0007010018003a45074a00c111000e40303140807408004000c0700f030b118018070002e0324420b94030071a54404940c040da8035540103100070b02080700034640b40d102681c0d00d441250b04560214645074103000540070b9895202c00c401105541c030120043e140c144c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 771226771 1250 771225521 771225527
    0x1211120c0105160f170c0606061e03060a03080a050a0e030109030816140f09030c040209010c021e0604150815061b1501170f01060f09231906080303040203030d050601 73
    0x98409014020810304017500515044000d20396000184203d4805846e1300041c800c0318469110342e101803442400b9010000d03501100103580251307004007001c2c01d01c1d03140e45440716030f03600c0440d011000c10f800140c0039035615003060603c103100d00c046000700000c0d0403c0d1405000e10300020718004121030000b0007001054082d00c03a060300201000400398036a011100302c99044da010400d082e01c40c0c41040301d00c0203d86094000c4583c03401e010703510b000c0c40b00e0b010b03030070301c060b44000045d2101521002820861079840d10005030004045002800310030081c138240c0a4020b12000d0584080e4200c0c2640c0e41056842c2c9000306c0d8401c0b004180c1c44282c9030300c0034001c02d0401e42e070550780288140c42c10000103000100c6410707440200620a0550b00480080c1e01d0050072142c0341d21a40146248100c0100310910440e40610381d554214501049407540040c40e01401e40b03c115000c11001c00c289004003c514040c0c400c107000b809a40009620b03500b8203030006075880c0100150b03140c0464a1b000041c0d600c4e48 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 771228021 1250 771226771 771226793
    0x415050306031e01051e010b12040f121d0306150f03011409101b0f180b0a1d030d02031b1501080102070b100b09191211120c010516 58
    0x7034070004040f550991501c081c06458250360050104401e00f44001d2254260701801d81252450b482403460030700324407005c41003580d0042c4182c91108408000002040284100c5104035000b540c61a03200302c0301c0d083d00d80c1003014545d00c0d540643d110204100141d40600c2950842c40c004a940d95001b00e00700000038094002020345003407034a210400d110702004005100c0c4a041c40f1450706000c4113442180008004140a610340b0000303500007858070714280940c03140c00341503004404d00d9420940398904201c45d03500c406008000901c044905410310900303041d0040045804030080e04010034000002583d0f8004c24016002012240701d068801c00010031040000c0804a4041c0e140c669441d800d040c000d4000000560703500c50241c00160070070030307a80d90180030303102000c06139400d0003000c2050149940b00110211b500c000403410204800070130315240103405108862a50101c0e03e11f00510034111101503240c01c00b9400410340d80b8140c0e07080f20507905615144408544020359a0a00031a144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 771229271 1250 771228021 771228043
    0xb04060f0e0f12010207111206070f03060f2601050105060706020c0f19050f0604020612040c0806160207080601061e03110706020301050405070e0a17011e050714041505030603 77
    0x4010b44200d0f1051501034002e450902c0c000d200d020000c8000000703100000b03e44d03030807442161b00036000041501d400350b145802440301a2a00141c1d1035110300c1c032180002640e40245841d00d0041079054a1000c076070401c00e100d04940c400a2100c0e514000c08070b0f40500608800800706034021a05001064042110f02503a00e640c008030380800d87c2507d0380540305884002c003999039000b20300c0e0220038070000082c3c06020701c1d8054400b0b4540030407107004202100010b082110015070540b40002c101b030f01000b545000d4a55000d940c004c001c80208040c1c50840d496012543d66042600100003468216410f00c40541c3e46036a5030101c8450084101c00403c10003441011125000c203120007405025400340d411386006607020020b5403102642550282d54402c3d840b54410903406051210000380070042c80b00095032000420401e15100c48045a58110703d22101d216075154104060594480840008050b0b40320b50385151a04141c80c0070328030251b41c0700c0d41c424840f00001150341902c0801804180c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 771230521 1250 771229271 771229279
    0x213150b0d090b040803010e09070f03020d1e03050d0606030e0c06210a0207110111250e0c030907050607030507060b0609040504050114070e03071208040f060210060b04060f0e0f 78
    0x1031805140403001a0004c0c0140d04000c030004c0d0001d00340b5027002843e50300755800c1c041080e10003491355003003000d08042e58104031031020540b0300f10090400e060450412183c400c0d25882d449107004004102100c83d85d030311190030581090b0320030796084400301c0c0d0100d4103a02900c49540e07c902d101610380030740d0304205010100501410400007407154540c058103110b4841c800515101ca03040004450108020014158941010a80000084425404000102c038052800420300d40e10155031406100884a01082080000400c102541b061018a024100c2160168280003458800600358003654400401440c2c0c1d0b8148a203440e600c3c0300c19030300100341c004d1046c051441d2918096001e0706203140b00394401c1c0070403404244280e001ea0039204007d140034000380b10f914940034000d4658100f6440c1500c0c508010003010568001c42c5080f4005071134650010704050b01d40301c07012800c8601e10b60152040560034002801f1460b440702c0c0480c1c10780103a1502d007030280c0d44d5400080b400d154000c2c1040d40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 771231771 1250 771230521 771230543
    0x1a0a0c140c04060504090b1302130e0609010509010e0706030213090c02100c1412100905070f08130308010e09160f0503150c030412140d090213150b0d09 67
    0x412000107540c4079519015a418481903540d8001e100c1070b18103240b4000c000c0019040094070704641070301034000341400100740c100d44031110800d2030101c40d0308850b41000398001d031040000718502402181e800c0907510000700500f01e07011001c80d407908128081e031000c0540010320840101142c49480c00900f00d1076204206201e6080710280d078444030b00881c8038840f030608801201c0c407070003060600421030f65425014a82510403807400d07981341004129150201c04028049203003805849054031810b10382d20b84800c044c4c00c4010242000300002e200d801000465091400043e6000b40e80368111072000410304810744860701d40b2814081e64043c40c0741d41e191a44400202c503d02d00d190f61040351016410748000c501c8144007e0b000c1c0300125009201c040341000840c000514007400d030768503a00e03245401a10308816070340c4d0a0003a4006161900030307030340b90401402907207459800000368144504080240030400081000d812003140b040415490001c40d604010083e26040900d03415031000380f80342 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 771233021 1250 771231771 771231803
    0x6050d030e06072d0b0709060516030306080d03060e0901020f070305090d02030607200303010f060804030239061303020103110705160603050c0c0a0209060406050402160302010c02071a0a0c 83
    0x340d20769084e040e541c168610000c949154001c40b802010b480040d56000c0c03034a100e1880c5a41c07905880c0104800701a41c80380009803603a07040c08603e448909560b008994107141092140701035a0290011340c1591041203c8000310140804403862542d060500ca40c40700b00b864000f0b209407a4000000e0f415011750402c00c0800c1d540208031070000010380010b0320719260282e503100e03030300d00090013880d20101c0581e80c14005240600201507200c0d129104079003070f00301030544003c068041c1c1c480b458103400e5105420f19012950700e84845003a101076031042c6c00c1010140c1040445022480040d040c10b46d40c1001d401000c90200440f84001c0d00b000464076244d0b107201c0c00070042082c40c829800043e250401003840c0b1401d08080304d201d50100f900812220b003842d001c00655120103084183d2060b960386002505072140d0014190780711080320050505480380c1806800d682e41c04d007a90003150402c0c032080c0000c020030112108540100b0000b151180e51110003039464000c0400080e2500071040b017455 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 771234271 1250 771233021 771233093
    0x170601030f210e10030b153615090120070b0703020a02030717060a111b01020705010f0e0d1b02060301290304080d020711190906050d030e0607 63
    0x120b54124103076420401c43c8111300c0c00b00e049804a0603401d82c4030f600f4281c13600e6001c47c580040c004a1102c0d8808813045c0d84c000c01b80c0c482c489040308454103c07060084100c4c103a8a80041241816101400501d00e00300c840c50000344105002c42c007040000c03000c0d10800c443c10404012541c050148c0c000c55550311103560074040d40d1a62001c3d012071091040359400701d5a0111091501e01c0d1145410040071640c03201c1001c5005414480b87c1c0702c424000501c81c03450780b00303a44413454802c601c2000006a94601d41d0a2060940d0f045000480f802814441d0b03405417000c0010b22000000143e140c00c0a81d00601c1c5d020700c5103080c0c003d001a52003540032001140c150382801c0014803003010034500c042e6000c1211b04a4207517010855000d0000402800002c0550185800070000715205004410346c80028200013646400c03200c02080e0114510070b4140480003491123000080c01c01180c9101200c5805e13580144003200103040305020362070100d10481081304003100072a422080d07841c000b0000520071040703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 771235521 1250 771234271 771234287
    0x230405070e03060123060307021504030f02210a0e0102010603080c0304060219030c0b180105070320120a150b1206150901081f030b0f040c170601030f21 67
    0x1e0310038016040002456800030303000101034008440d4000310501e08004001842e0402000e09003580510581448181032060300c86d8030951007a103514845e00300040e0000e00d4418814034040d990b1080c003140501c042e22890568a90044924207408000603d07030040740500300507800201009804111043d40900c00b00203002510016400c03694160445010448d50f0100b0b19400360100b114032011401003581484065400174041c8003289580d000b0b03110450840c5c00c211021000655291000c0c000d2900122107810001c0e91510414181b5059108034442c0c0300c0050240d1180594400c49440e1480d0480d00381d074006e080240c5020b840d05080c040f09030164400311581881001801107410042c1c0002054803240c2c50103a5414880e55186010300001142400320f1041001203000300000141c0841c401621807a28213000c2907487c2010318100042401c05d4004800c0613025501c07225040c0740c000361286c1100d80118081d000c3c1c0700b03907041034084101c50a0600010b440c64900002503140c03c15a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 771236771 1250 771235521 771235547
    0x2d0b1503070902072a0909020609030316050d020a0b0a0b1c0303140f010b091e030f0f0c060f0a030c1808060609180c0105390f1623040507 61
    0x140b004200b5403441c0da40004c0c50814020342d501c041c005000c211051390140b40700c248049c109510348102030700040e2943c0c00410840c020140111048000c009003400041c0030034000c0c4c00100001c000c0c4c0e0b40c40103640f00e40100402a115130780c80e2841c4540d500c0a0034010a045e040001200444031420010060300304400070302100402d0401042d547c181e004001c60480e041d40600078101404601045520300761080d110101c2d81c610204a5081e960a000544555982074002c01c1440c2014a1250038820340580e002d100385c0050020301c542c8441e013002c480c0503407044c0c0b030300144001076030a050f28020200c03003401c0c03400030303910704040b0741c0b40d0b40054907601031801103503500b82035516070604481609040c0c1d00020039400c4986541c407194010409801c4e02420716818200703050019400141d0a4400d1a0040141103d03030045020207409200061802401c0c1c000f800d0b48040c1d41c00001040040da2080d806941d403c2e014010885141841250b50440003d000f807143e8149550010424600781c0741c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 771238021 1250 771236771 771236783
    0x20c0f0d0c0e0f0106090308040b031b270925050c0105010303123c090605090307031202040302030606060f2208071e121a04030503042d0b150307090207 67
    0x40003080140c0610074507170459030b0040c0c0e050b09c2c2508001840700c407a0030252450049803940c2d881c11945401b0130002e003403c000b4080600c01065140303c0c0c0064400e28207091217000d09241020f1264110302c48402509110300e4090585140b03481c0c44e000c903003d101e071261443d0701c0d5103454004030415070320031706180a903100c03484140014045800c1000030092000c0f0740a41c03031811200594003c070080d001040c01a00800070010f80001035449940c203962085444002c1d5420000f86401015000700c49040b03004400c1d6421400c080c02d5501185d1399000c06010310b841594003081d03064041c4035003401c032060b10040c1e4400325a2004400088070b0302030b04600510015005480020a407034500d4000c01c1225003514003044031041c9080100032510450b643c056401d503500c1001010429514070506005038425581d1594901d01030a1020061a080040c00c140b20b1290601110b403030460b12030400c02da6001410440c641c0c9858100d41d1081c0e01c200f0140e83c150061881c0011010201e90241044c1e0340100f03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 771239271 1250 771238021 771238051
    0x62b020906030c0a03110f0a081027020108060402160308040302120a0512061c0803011404020a080a0e03040801151505090603041e08121501020706020c0f0d0c0e 71
    0x1c0205601c911201041a4000f45071440c00c001148142131078441c45800500b001500329810004198411640c1d00410010742c000003222200080c81d1050540c400b1400700c0d00800d00040b852880c404802003000070b1b04000c83c40f00441c00c00c0da0341381c9c111a4540381c00000e55005880c50700d80075100c0e140494007030b00940a940100e49502c2000360071a0f00e80c072443c2d40d41d1440d268640302c2c3c02120100241c101034110701c1c1d0070034211046000d420200300690080c00b840d501d07989003220203401d03040f044030f10f03e001320300510448605580200c4402c3c0c20001c5190045030440464690030302e58011907000c02c01541c00d1190b0030844d074085600c108259150840200901c0c94414400c2d03c051042e90361709604010100005000700300555503410800750000d40e016200b0200d42c450042582000d03014040b002041410f121258450514801703040b4001c1c00603290341494000c0203501d0701035416055000707000c032031030428540c2c2e545071301c10101540c890348140c6101e4940c1d182022808040350041c0d00303441c4817 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 771240521 1250 771239271 771239281
    0x110111030a0507030309111909050112080d241502060a060302180414030a11011a0913080f0d1d1c05070812090c040606030b0d0b062b0209 61
    0x44200e40700d41d400394694501d42440e0782d4086005084c4c90350b09a0b140e40340000040425591003840e09203101180310205406401d01030318104842040c0c0c0240003090065062a00140d001d8003621040307000301e070340001c4007411004440143c0c10100c20780c004081d0030f58404100c90055500880814159900310307040d81d9611441c2104903030a90001942c09550818041c01c038800d0144002c1e802442500b048500e00c90481015103142c1010340c9050108203113034541c691000e400d01c606a4400100d0846888880505003c15401036000d000070b09449030442a5000f4080842d040364244003401a01c80d03641da80407c99440200b2001040b90040103000e0000c40c20520001580e80502c1380d40e24410100c94142c060680b120f901451007214a080280b181c0240c0400d89070745244645070600140100420754000c02003220070f1b9401041c240340c0740440d0600152900d010340403040703038004801c1c40076486200002c0c03207507254a40f84c1c442e015080b8481000c140022031034960402d10980350012540c1381c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 771241771 1250 771240521 771240523
    0x7090605040b090105040b15030f04030f1e120209222003060103050a06080105040c17070e060d02010e0a06050c06070504060c060902120f060103120c0c09020c01020d0504110111 78
    0x90160b0742588a100640140858685039010000503a0020b050007054522090303c1d00481e001103c0034425107800300200002c2c5074000c007184503888040d103030540ca08022000d00c0300682080c0b002500401491600804040301d555044580c1c0040040c66009040202e1540c030740c0100100310300c2d40c5040d0809044141c000e41d0b0424083c890b90545159a095585200c0110010400100102505030311503000140441080c410341c0d01580c0500d01040255003030541400080752002c101c1c2c4d62961014904000c0340162000311074008508a90440a400c503600040320490003864946a00c62b080a400203016504031000f424020107400681b901c580d40c40070141c45900a40c0b00c1c1c1c2012442e00b1040f100061100d5104a54640c402400c002040003034040c000c1ca0030b6880410280c2c00c3e40b000d00140300b4003150740302c03507100b030f50503890102401d2010b55561145038926200f00005550081443c1d4081d9401b90103070b41e51140c1e4040204024034090801058140340440308d20b000c190742c980c9102502c18 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 771243021 1250 771241771 771241781
    0x4090f0e0c0901060f0e0d030e031203010f03020d05070e072604030e0d061104140f030d1704050106091509050601020604170a051903061d06090a0b0f120709060504 72
    0x700245a6092030b0300c0d240b015902e056400b202c240c1084071510f1448455a554450000c046000c1d554100c0c4140103a070a05103030a041a280403070f101402d0004000c042d01620f091819a9810344d4407613455200c2d45032007868100070f50440d04131480400100000740768440d101d80c5141102c114121110766201d0780030310310302109a40103070028032070b141401e4403428616000303129503228400000c3c2d8072012040c0050b1b550000d400c81d114410740c00540092500e04001b21505a00c0110302030542c4002400c00035042d640d1030b00b4080c2da55595040040d060040c00e51041d0700901b035204041c400083c04041448a0007014040c08440b00e2624000c03920703135440041d05510070395219280480c0900d00c83e001401941011101c2d40c20040100640d29600003a90340040e15000c00e170720003281440c280502c5c050720140c9040c0f1030980845c04001c10860756924080e054006481850014440313107003101080113008200a082e80000c00d900c1184072003040002c0d09012610958010441c2071744810070001074078 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 771244271 1250 771243021 771243043
    0x100c0c141003020a3504320a0201200708030a1d0102061b13090e0f0d020c010e01090b070b01090605040908091522050915180c0f04090f0e 61
    0x900c0d1415075503c4500340d00040b0345c50001c81008000805100c1c10020710180301103034200d60301c1d01c4d0300c480c60249158201c02c071489810350003944420b00642600c600d5841e1210b520182c1000040810507460208000c90a44484804810383d40180d4480c455a50380b03070b0000394520000b556203400f02c5400d10000c90080324800e0141d01502207622041c400c0c140079100c2030f4803821161020040d01c05c1c4c403902c1079542401419942c0740400c2e040c165020b030031706000401c807041507141c03c01144150907030790115401082c08000d09242c8018804000100c0f00541d10341c04c84032090703000156003024044407044083c1241c40d012020f0001903158001d00c0141c90703034040002c0007080d0a22501c0c2e003c2c0340c101c4a40740c0386404034441609000d0602c00030032240115012950145240311400d00050509000705c550103130194078a0304000e011040030038204580c031b00624009982c0e500c042000040003401705c8122940d40e41a8540340d0380c80d850290010702c69246001c08451410200605075080070900d11440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 771245521 1250 771244271 771244277
    0x2030c010c241b0201060f1208070b0903070b150f010906091818081c181103070302060c0d08090703050604081c0912022109100c0c141003020a 63
    0x110000c0300401d804110701000c40e10742c0c203454803507100d150149002040c00380792040e8000725400b8070b04a005171042c0c0761382d00700b06811281905140c011a005200711107003150301000702282a611021400c0c2940201400103045840308400e001540b444034201d05107443c81110400311030321b0850010340d0040001d22502d4042980700c80108540802800301d07111505070791902003841c0c0346000c2000ca16030300c54030003200c21701d2002c6080740c1c00314822101c103011071130041c80401000e501e81c031414a41d8410110001d0190026203602002030301c0900030386000b10ba01818894441035a03008058071604c0c1e03511400b0000780c0100c001400030400262a000301d030f0700300d0701504040c2c0b25520780501503441800310709410505c0380d8070b40700d40e03c02a10078525554041c03640d030040d81c119041c00905246605801251081803a07075080b0070845240222006000b08441c1e0071172490f805181621075000364500030700074690426000443d188081c210f040c081d801102d081600d50110101030701207014010f01c40e000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 771246771 1250 771245521 771245543
    0xa0308040315151e120b16141902100c0503060310090f08031b0a02010609180507052205010b04080c090420010903060e10050c0c190c0f06050702030c010c 68
    0x80d6050300c64040000c0c40394044c0321300b846440c0c84da01c850341a0541000c54805c1070070800c00c0260003811441101038809443c20140041d02c8503000501030140d002e40a120810039003e00150301d00070028400c1c080c82400082c480000c2c0550050303c2a08110748050107030090034101428110544100e01402d9840241000030481a03180c1040300d8100410300b5030220000d0428260002d240c034050701c01411586c0c0042070b2141006000f4050b1100f8024900380040c64004c1c1c100003402c08034030101070392819280b01004540c440c142da10032602c00d4400350002d03032900001081c56401c450007801a0303020f80040782c80000081c030910811400446026002030000d0f00d205580b0400c080c40d0390310a190524280344690b031a80c888108884c1d40e07480089a55100b0841b00c0800c007800d00909a02a804150003418000020342d81500c07644244c4041094000000501e42000304129800c0003904880c0e403409242070320b0f441c0107030003544140c50582c1b0a00c1905c954114641c490000d40d2003142d401008005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 771248021 1250 771246771 771246779
    0x1050405011808180406051203210f060405041b06050c06060a0303080f0a060905091b0102030901020a1412162f0409060e010e21031519050a030804031515 68
    0x2130149007409a4403984848000940741e0720070ba11941d070070504030091969002c0000300303680000d01910085d0880c103500b4003080001c82e00d900010740d1012007958007144a0340c4601d4045c03e00c41c811a540380c40c400d00c0410100304958014090603c184a0904441454540c034082040001c900c2c40020700082400002964034136040030740e00e1b00504940f00114600c0d454142490a4601c00c035411a1664441030503400d059005442c900c225103000c3c0065031400540000007900c611112101030b25600051711503e80c003030030070001c0d826003500344814580c45e6100059a01d0b440e9801500a40340d0048150305961101d03405010100c0d03482c20318006c030f503030b4400c01c10500000e00010302041c3d400300ea5644030261920800c1c020310000010a2000c0c0c118034a8034400c0c100c00100601c01b101120b5010b0041103c0d40340c3c80d91420740d41c000101c40030f081da003501000c001407103d0703140c200940203281e2400000800007d0780141c001d980c441c075441400311080c07541d44411507882500011210403000c3d4208 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 771249271 1250 771248021 771248047
    0x60c17010e0f0115180306090b1509060609030c090a0504051b0a1403100e011e0902210a05030a09050f040b2b0c0b03061c120f170901050405011808 65
    0x1a603403500c6824044060721030b803e1859007404e01782c0d000f80e4029440b0f062403400c01004601856010701031100c0e0703c0e52092444003141c00804010540760103042c002407408115a010468000c3d10781000304040304600d080080c00014040558080710940f2500a004046402032540013080d01c001900d0703038103268500840011011000d041d85a01270007032600001107054036008254050b0800c000100e5401d80d214070340420100c80d8460005900e2500000720b00507641c1f00344100030318007040c0e10289a00b0743c14100358145410b071000103060340310025007000150340000e40364040381c0d030441e03038415450b130002c0c00d20003691810300c1c00c568050100c1007050403194002c40714001c0300c2c200c1c410000040e54141d50b9a0408103140d000018070600100030407010303140c0002400d860420041a0000c690ba003941c803c03910030b010261640a004415440320516846100c00292150b80c02882c60401e080c62842a8000c100944080c0c44c01c0d400e02d064804650400d064800e002541300100900e002d125030180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 771250521 1250 771249271 771249299
    0x1107051b090c22080f07050a050105040b040308030408190207090b0f2101060503070f0306050c070804032406060c171801050d020c070605030a060e0c0403120c060c17010e0f01 77
    0x40f01409014042222107040181c000d10025500c001c1040c0750a160402255008942c04241041420001441680c4030b81303054904481d4801000368481c0c840740b4010480c0d00581c664410b1507110846148192039000a03c54122b0302c0100e400c00001c0305041c1800900c4c40555620b81c0c21030f0ba4100c20f40200258141c1c4034030b0200414000003091b54680700040c0c00d000705680509071088035614203005000452003041e40180544120310701e0800d05a940302c04901840c0300242203e0f842d40d482105070455501408010310100c0310401401b91501c002409414086800351010780401202440c41044ca00c112040e101001c283d40d120507905000445e0107500030100181099024040c05008480c2004400c000d03001c540c54441d113a02d0701c1c00c440d904481c900d901c15500c00303022506002c40501881c007101c007940e4000604e807695902250058136081d9001c1c40c01402149051003d02d5829808603880307003007820814414405981c1c45651207907209090300c030980e02c051a90010010000542aa = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 771251771 1250 771250521 771250567
    0x3030e120c0604090e0c24030c0d02040f15030b06191b0302060118060605090f01170108010c0e060309070b070312021216180302040506041107051b090c 67
    0x11201c00c8041a008039145820640c4440100c03a11510703441c246400900ca1066401c0007034075400075050041d0700d44c1c0500602d546a50006003000004034800c00300d10002c840701c80d171802c1c07015540c0b1681c6030344a1a0f099003c1c46000300190084034140c041c40d100c1d000e45181144000d080c07508103c000700280721031940d011150303424010700f080f81e10345000ca884400b11000f40681c01800c030b01c0d0300d0800790041078910b400c2e2140e041d030b00d050700602c80c040e04507054a11280066a4065907103035481c006071030280b54203421400740942c0354000241480c054010301c8040d0b83c566034158241ea4204140b01c1e4901054500303080c190030050080c803c001c3c0c800040c2c210580245041e0481c0280a01010103c1c1e01101e40b14001564803020884007000c132643e803600e0700303080c1d140c54900030f40d4a2070007240b52805030100034419903c80010859941d43c50700080031600060111954030340741d628003103554030b038020039460380c079103141384d1108442c6030901444d403291140030f070464035002480038860240006206 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 771253021 1250 771251771 771251773
    0x130b01080f180f03031015050f16050118230309060903030f222c0601050d1a0a05180f0a090c080a05011103130f0804030611030a06060903030e12 64
    0x65000000c2da0412440080710340102c081c5580e801c03c41c1000a2226050700f001503a2540c5403101d0040f607500c042140d80b6a501000e815455000810000150505640c8090015800c1503002c298842104001c074460034450351030350220400c88080011b52481102040c00d00f40c1041c0300c0900700342000c80003000a1200201a01d2600c40341003050301c2e003504040c10301d11000060b480348603440c400001c0442c3c080c0c031005036050501414400c01c500701c0c9000e21100260203c00c0d0010070045e07400b902c1030744d00aa0a0340c0060004080f10b40441e0503145c0c054503060b10079481c01c900024a130801c2d00028002245441414846943d0321459103c40704001d040250b01c0703a42e8070b0442c0c0115229a05420107004524054903c8a43c40d041050a59a0480301c62211a20800c14806070000000041407076039401070f04c41a142c0014288440107009542c00509100c0c10404004910f800c3c1e040218826801080708008a42e1a0841202c1d000281d01000f80850510100f03001c142c50101c5e282c10a90344504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 771254271 1250 771253021 771253051
    0x1090f05090a020706110a020105010b1603180504020a0f08420303070b0106081e1f09140709080a080f09061b0d031409060720060c0702130b01080f 65
    0x50b0b80c0c601207581b40c0420700080030f40480c003206101d9082c02442d00604080101038101005030541946a442103c0b008081c030040c1400280c2ca0b80d02c4107011070003031000070030071516404002c00141c428030f035a241c1d00c00000c9034000010000b071189082404031440c60300d00140300c1d0301d040340300c4044d02201400f195a4040c94880c0c00d015070b601040200380c0c5611419801c01d883d454054040c010f46400352196141c07a054000121283c84002e25290b4802d00540c4910b408031041c6042c0b5988a02c15045410100d0901010420441d5101d8886014200729911491080d80d00d030310f500e82301c1030301c21070041001000304007055000e01404041c0c111140300074080c925201074a2104c5110703658000d095030542c2c2000300f440e1040c0da098481c4480c40441404456070b40d20b0081c00c031a8a51500400c0031040c4480c1c9280c2d40c1c08801c9000c134038081d02c1c080d90116002c80c1060350f909030450704030040407489446207520701401e81065010b00c0c1604c5006031146903490b1244034074001002c8005010482d810080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 771255521 1250 771254271 771254273
    0x90c011106071b122a170901111b150f0d0f0b0607030201050406241509080d02101a01020c0409030e13020414040915020705011104061106010501090f05090a0207 71
    0x111300f807544403071100c0d21414035202c00380c82001c040c4100f50218014108600c0040c5010800c03406025404d403050302d020559482c0d1180060b20101c28520301081c4511584003c00d0007900340585400c403205084402440504401000d9031091040002e210300076602030107049418100b640060f01c0035480c20300045524942d0a004c1081c03500010070550040c1e454106110600040c5e02c1186402000d2009070700c9520380f000500322208505220740c40c00c84111000c106402842504c0450181203150181c915521550000079913a142d003514020a441c81e110207280c40c501140c007174a403481d1041c0c0180000780903038801c010041c100e128098050191031906c25515540f0b142c2000c4072408210001038840d402e020030b0440100d0751000d22801145001c8619001c10b00658003030002c20a50100503a44040c10300d802c601502d407920f0310300d000600106010070200d8100e500c020b8003001c030104640907680d0b960011509152684521382c2640b00c40324042c0101d040400582d0f40c41842c40704050b242c4046 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 771256771 1250 771255521 771255533
    0x30e01023c30090a03030903030f0207031a040213050c07030e090105061605011509020a0f031104061808030406031407090e0a090302010b1305090c011106071b 70
    0x44400360031690801c580500403107020304442200040c50500a114035803140b041c06000c0b003081e048440340b8802140b140148086603104a41624401402492102d6607034540078088900a000880115601904030028a880003c650048079000100b0321101c984d6008115080740011308182d030412144429641140f40c41e028160050074001c0410f959026107040082004c10301402051081c410a0010042907580d4070503185e9032405a250141c81030400d1030300750700404c003174011005008181100042d011200360f02174541c00700c8507150942c9080000c207046044030340320311400c500d049046c0010712406110ba441c00d4584e200502100c29803070f8907520000c0c5550003e5100c0e40000751500405418003101030040c6070018040d04091078050709003074150500c11001403a402c03005507200d0303200040c903100b500702e10074600f0301812882803000740409038009020112200030a51084000c1501e15502c02c604244d6040b440902621880c2c8600300c8c00c40d68102a04041c8150b45d500781301c04404551 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 771258021 1250 771256771 771256813
    0x92101060e180a08221e060305010e0f0606040e070801050a08011806020912010527030307080c0703260103020411071a070c0203031903050c0903100f021c0203060901150c030e0102 79
    0x341c03101c824016205030325200c01d507146c640000302050308000040006030910000707150860760310441060240c0d55100421a43d01035a0711001e0808148020300c10b06582000e0082e041c1d0301c1c140c6042001c00d448104050a0300d001c030282c2113132040d0848006010a0455016008104c8000c0900800c211481714003400d445040c0e403195078a0021940c0b45c0d00a60304160700a51002645014604500c0c10041c0945400402403e50421500c00600c99081520a070841d18030300c040503404d4018074001c80d04c0321680316400d000072800742c0e15008040b69983c000d00d0640f03006545c02190b0019004864004030005e05001d01340c481030221000341d002c016076052014140080e1400c1e46503802c040b44820023030a0b03c2018244502c1c9110802c005211078a0100d08041e40310718000c00864154142c00000c40240310312840255810341d240140400d111491300110300803007080341d0707416150b40c07600031040004404070340001c041030000031110002405912030410280050059410264140b002894004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 771259271 1250 771258021 771258029
    0xe060d02010e0120070f140108040506010e0901060b0f190203040b16170412201315090c020304090b0906061e0705030a0c03021504051002092101060e180a0822 70
    0xb50b11ba4000d000c03070380c00d058000700d2100007403801001c0c609083e2151901c4400600441046088140015130401030940240b0300501302000c0c030701d40d6800c0c0c00031074400c1c070b411041c10030b2071a03a4010f992881c014800010743d8141e60305100010b140c4104030646121401d00c0074011a0f02d0039212070003a4403a801c88019000400c20781c40f1120310440c003458404094000000d000031041b4a020982038151940c2c0e550f4200313109410000240855500d951300c91403629a444903004031305044034280c54507804000340088034000035040c010b00944000b0001c01d003100315051070b08034905111451001c1e551100301c8001b03d242c842d00341d1030020341d5251681540c0c408030307600c0c02140c4140745600401d40d04200517415104c140e000c0444a092a036505911040140c1035040b030b040c0c0214808a1555446c840b01c403e2401c0103154090700da6204080601803e094411005488075000004045114000586249010303c1015002c40c24150345d0f400c000e03411100703a600009840c40142140a080062150003034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 771260521 1250 771259271 771259289
    0x4e0207091505090702010b0111030a121a040606020c010908060f060415150507020a050301020c0a14070f08060702011803050901140f070b0114120703120507080f040e060d02010e012007 81
    0x44607d1320014000b22081c180c40001caa1003008032492265100107005d01406e141403022802003242824000185260b8881c194810701c0c081000607540e4000589080d080c80030780718903140c0e59648951648480c02110b5450b804140040012300b03d10b4135909c040440c20807220043d015588030034184068a200313a0300d00700414400a2100e0035854040c0c820340091004400942c81c052035040c0e21038540a03440300042605100c45c0b654844164180f0a80c0060011100080106995103041c02e55624081d40c40f80e025505c1c00ca200da89440c075400f900004240c00d5103c07207240031400c00044600c41183c98061030020002d0100075405d498140080580d14000c800d49c0160b54103110543c041c0c4000e04081c103105888801c0f081000f860080368000032660440c1b00078591801c0018140c40d01d02c902d180c000c1201c04001a5807100500d400c000e04250385441c102d13504142d503480140095040a660081e000c12044a045000c80d849804024501c949201c3c4103807103460050001842c1c14000e800a10034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 771261771 1250 771260521 771260531
    0x10020702041505030a11151c0501050103091e1a0c0a0206090106050a090e0c040e100e03040b1c1508010c02100b1c4e020709150509070201 61
    0xe6160600684401626030070205403001d180c01d000a0340ca900324000100007030040800c00603541d41c0c48a02c01d00c9001c402c405039607a15072141c0c0ea08c0c0e80801084040103403500d01000414154841d00c200c0314680c0d4000e084c01ca0031105d06204440c601007084017150340c103141c10214414417090300c1070710780a004031101c0c8a071294909680681010001440c180945c2e26000e0100800e540392120030b0100e80c40040c002413804109640d0307a040c1103040c81e40941150405400940c842000900710305451140d1604201303d01e0f140b809241c81e4440c6100ba1400a0014010b004c130b07181c5118400c442c86074040c03500003807612520440e020170750344c0c0d54030090a6035994100902d0490701800138000001110100304544422000082e07181c102c9910340c0140103443c07106000802000740c0c8403481200514407021001c0d03e17a440d0b818030700c5003100d4085503901755540300425100c0107041070011900558005d07120751400c01194400420300b40c411003000c90b90104000600d5190102000e0080d20b0303507400410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 771263021 1250 771261771 771261773
    0x12050d061a03091b090621150610140a050c2b1b080406050a0903060515040c111507050d1d07060906090b03040c08010516030e0a020108040b100305100207 68
    0x20601000390355820020007604068800c17a03403180a401c3e4003280458a5841150560001c407840c03031502e0b00540f8981c07195001943c020081d170400c4622a56048030840204102079004480700f01e004894802054418440c0c145601e0041024201d1070f00d0f08411141d01d07100990b800c0701038400e07604840e519444032800b44c00c000341e400403443d11400e24007102c201190b8010f0352030501074450741c40741c201040400f250b00e00b004d52040503040e004580082d001d000354141500610a0700c0c0c07907540054842d07031522403c41c141500841d0103c0c40008500041e01200100d980704030b54002c1d0003010303e41004010028602c000c880ca04c503095112100642c00046510054102490801c0c0b035007041c420f110200404016469109054006556280080d29100c0d1900e240440301d00000e50800d08840d42000c040140c00b05042050101204d101d0b501804107041800101342c0302ca220f54400790014440310002404a520700d1121a001100700f21031240e00760381c0b61946800c00085004901d079103500016514 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 771264271 1250 771263021 771263023
    0x6050c102007060b010f0212040b0304050f0a0c141c15110d090b1b1902030702060c0d0201050601030516200114011d07050405010e0a0302100c02120a12050d061a0309 73
    0x100c1b244a1030006024851405041c40070f0f9000758425002101800000101000740501003906c00d425000210b580c01c030080d181444100e101c40c0184a02405940030300700c003514141107c88164161280e60300202402500d80001680f140c1181944c000d444003d0000454a0203000b0200b86000b60400182e1007034614000c00b4920700a0700d14810711424082100741401100112000d048100500d014003415540040e4114096180040c1d0300c8040424019282e22002c00d1440300d200360359000700010b13552000158101c400642d40b0010165113080c0c80c0c0f0031980150901e0324254405001200c4d00180b2115041c01e4811184907107640c5d080e1b1000411082c1c601d000e82d01c0e014082400a90480c3c54040401041c1c0e0160b44540b0341009142c0300d40810b552140d0b404100550f4000e0003444c100e00907517502401c407036182c44c0200d00501e00851003110303998000c40d250420329400340618403d6021140121040d40140340740070384069a40500068549a402203004080d4105d04280d0320b9140800000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 771265521 1250 771264271 771264287
    0x301050109020909070f030e150103150516030903030603060203091608030f0909060d050f0c0111070b1e0c0a03030b091503070e0a060b04090e0706050c102007060b01 73
    0x30064079801803161880b16074840080c154004c02529117003c40d0046240200c01500309001c0c100b040e030203044100704000410405d07046c140d07800b41c214101c00f01300b1021020708a4504641c85480f42e244102c0044006110350031610259000740703400b040851304c030703100d2000307d2340103035004101e95010103203040700b001c1704008900041c2040000b65042041e2600e5042042c0716042515100300700500010f205a40d036000f403900d071290000c084480c4640c001154607514201180b55501140b0410101f409551001408a0036035203000c01c2d42d400d10b48540c0c9400d584580030f00340040240e2003030041c00680c8104105060410b4003942e004503010310000c042c0408004042c101c60b403201a411040001500c000900c101100d803050b4030510075070b0b55041c4030401041e80e0b4002255a44001900181003400341d00b00311115803c0d1415600c442c3e0b075412041d185d601c0740d042022150740103a403440d00d050394194000c900d000841107201c1200041c12038028100d50280b60111403444e9604071a5400396486986 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 771266771 1250 771265521 771265529
    0x13090b060a08010306022110050a0f1d070207120c1505030408160501110409054201020109020a0e040611030603190206070c06020703170a0801091d060709030203010501 74
    0x9291601e0300c410001802d200050002400c03840e00000c06441c050300b0040d03040507613814507184641c0307418aa2080b4074089240d02c1854030035170115901091540704264507000b00c4a2102c4038a52148101e0041d10f004940208110294000c170040020403060701c00080000d40d21400280e03000e0303414103502c0682c1c3c0e02c0031115041004007d108200c00a40d8070005c80307081e0140080d4020b0310f0491071409901400b00142c12440b5902d01090000d4910800e42040d0300851901d100320032841c1503032030030b0000111030340043c0131061000b400040d0a0303c1d000e0700070404414188000700d00303201e540d0085048541c1c503901c6a000b1019110401c800c3c40698440c291880501d0050749255080ca50000307903440075010745051500810307411000071540c910080301d0b8a5503005107244500c41d41d80c680651201c030188000c0d03c0c0c40d054130714000740d84071b4800f0845020a001d0748440c55684d0034910a0700007400c040c0001c460702d03260301d4041c0004040c1000003512400155880e40035007802d41c4140f5007502c0060b44 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 771268021 1250 771266771 771266779
    0xc060301151103090a0306020711040f060608011505070f0503130f090c0c051c030f050a0e060c091e030115080f0c090c07021504181d0f0c121213090b 66
    0xc0c400c1310381d86075102d10307084070340100c00980c442c0d105041001407003a8580c1034650003860a21800c01c0d099094000d08121031035501c0d40304240c6c0e60346481426890300040d0043c006002009003500160b2101d03440c84c2031900543c12241002c01c0342104581240c1160080340c071030b61b5a8181000b902c9041d00820303015507035510b001c40c00b055441d0781d225a112040808920010400c52404200a120342e20002450142d401c05100038104180c2000003018492004580c5005040010300d0183c42d07401102c0d00104d026007030040301c0c18040351085071040c1485074150706540311605d0f401203201594440c805403a404015102c9008070080b000d00d003001484a0b1405903525008200044e4115030650300916015130b4100e5002c240c40c15104a54801c5407c110204e1900501e5034500020a5000c02040090301d0780c0e070b18203107050b6000c3d0303a601d011000503028140d0050410921906200000d86d851140320340440c0c107000001521001c4640101041c2c034403001030410b00b007046850f01e00441442c3c244c252 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 771269271 1250 771268021 771268027
    0xc080a03020601031e03021005070216030803010e0601091410030b04091101090f03030503060f0102011e0903092102010c050709090302100f1104090e1507031a0109060c03030504050c060301151103 86
    0x90340180d280ea10481e400231250790b9640018403e2402480803051544c0c8c4440065071642c2c403441c0109164100f801a0550103503084001070380c1f0350003103610f0400d0301c00504130001d0290b2070303000708001c40701039039100010151203942420b5648c4950080c2c01b01207100b00710200320400ad04000401c0e03031555034407075400150741071410004640c001088a810902c140c0d9810081206480140c0c05054000500d900b903020760180c502500100b980100c441a2107941c5488003241d03995401140394001110049401031609400c000541c05855035100462088040e2030307000c0d036208240310444e010307040c1c1600035130411403181050400600c240382164840310300400950408070711803250350149000300300c07105603140e87c40107003203404005007030284200513130707402141c905000e004010303114600100f0740742c128200c800d480c0c640c001e149690070f80300c0b00d40e10f443c0304201548003203014100240c0181c42078024603401d107605484200085010300a41d000c60001104c1240006101519140f040c40c00743d0828 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 771270521 1250 771269271 771269273
    0x408031e0408070e090c54041e0c140d1703060d050106091a0a0e04021207030b0a0b2e0e0f1512011401021e0c090108010b040c0e15070c080a03020601031e 68
    0x811641d5143d003c1c4054901100c0d23031140740c0700c0409a428600c0364403d084012080701041928100141a189404010a00480304ea0140802003405000050003040103c40481300e50114034040c542c03207000200200c5a095007925141d084542c00d40281c584161074255960741441c86a104804405042c3c4258400b18501050310903580d0300544006d01c18042d440d410559660704100e03a101654011301c850b1000e0030060400c000415180b40080d016402d50405950800517001500c4500c1c2613288407402c143c6200c200c1191500705003005241c1c05040c41d0300381c40c1c80d61a0a6003100c45004241078160380c0c0c1c2110f0410501e8100140d105a41c60281440b80d01900c2c1d81c0031407003010b05542d20340040002c01450740e005040c001104800e581014850000283c5010150030038604040d00303a40820960703c0403d0225910201011038070740120410640c6901203402200401e095400307000c1080340701751181c0b0340c2030610f081c846040d00140d024900500520020582031800010b43d200d840c8950101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 771271771 1250 771270521 771270649
    0x10c0e1f05070804120b01122102030706050103080409060506040b180f09090a0209090706080103140a0803131a06010804061a060408031e0408070e090c 67
    0x80c0d04110050380c00e030002111054081e0040c0d401140d8404405500c0340d4441e02c2c142d041ca419200c0580c4e20303c8041c000050301c40030700540c14004ca904201c503011048083e0055003208001ca403101811444100820004900c143c03103154082c5d8840c0703001c0f503665450711040300d0a503074854005a200c1c0108220422907019142c0c11601081154054a036074112920300240d2201070003252141c10a203407004001c8a10301c045081e040461007290301100c070f038503410400d40e9180c441d80911400300703400b00010700214050340184e00300400306508071911100307680d6601c15103800c1640d034640c1e440c1c0030151180070003440c4002c4e59102e1100d80c541e40d41a10f04400024040d07103000d0000342016594882140144180305110390a001e40980b100d90b8035580e031501c4c1a643c9d40014803c100310840c40c41c2e050b504000380c008035021902c02d0070052030b242c1e040c10209240150040d21241d080c0c4a860011a01511407003c0e050138901c4604400090382c84842010710409088200c21210b43c5070307402142d2000c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 771273021 1250 771271771 771271789
    0x6100207050315061c06020d0f151e030503280f05030708060d060204270b010804030f030b0913030806010f092606040b0907060c020604030303021612050408010c0e 72
    0x710103103c104181e10f8240208211560226000d100d060101d009802400300940003412410540d810810010780f2603e4850101c03445580c406507042a101000c01071600a03d4110f00600c00001c42418600d58035519141b03940d20804017907120402020013800400c03c12000344d04c454140381400224032050f01c03401000c0348402002e210502880c24040758107902c03100c0803040f01d59030107a0215511500c4550403000500b082481031803151120489072145005406526640303401038540720281d842c0e540d001d4030f580820b4580a4101941c520544900350b0b618050140a501d03100d03d416a200840d0038021b001290040a032410322a484000410740c80c1c1c081c0302e0a048070800e1000440070030f00041c01c44088114100c2081076803213103c050009011995002c01d00951820003140e400594a007026035180901e000c1c06580310700b00f4001040803d000303400901041b89000b6407800c0d0845079175142c440401c03e40281d1070005201140502c179568092103400c2450f10b003402c000743e80060310700001e60500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 771274271 1250 771273021 771273043
    0x3060a050403081b0706060905150402190c0503070f0c0302120f0d03020f070807110a1d1911070303090b0a0e070312090b0c01200a0e1e030a0b061002070503 69
    0x9504d000b1062202c84100301500d05040d4000703028000c0030703942c140501c060b050039035064040071030000fa8114140b929208a81c105020012510b0920110710425a228416100103a8490004000303030000501d800014124162190040c01f01c10780c10341c014003264a0108100d00c04549c4841100400001c0005110001414030700d00076955246c00300c0c1808990090800040142c480401c01804215040100030f904241c10b55050710030650740c03161903602041c3c5088204c0002c3d44c140104500c6240101096032b6100805004038207413000304200040f503409410180c000035030b90f100500c00c04c04032000381038003c0202704081c810010503040c4103482e180d081c0700040208102642412485004955080c001d184544505488080d0030354a640a00585960006c0c0c3c01c1c540360780034000d03031030043c150350b8612082e030b5480001c1980041407000021070180c4e02001100e40c180501026034080144c012518481c0810301c13100d08094060164586130f0107007010654200c1031040c001a00d0002c0d1802d0b600c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 771275521 1250 771274271 771274291
    0x709030b150a08030414040e03030613150510110d0809070501030e0f060c0a2a020907030b03030d0603061d150a09150c12150b0703050f041403060a05040308 69
    0x1000c0c1c540d0006206100550040080c0e00000c140090403410181c3c0d104092503082d170742407003018200e080c85c1e51603200440d2034690182c282c0726003100c40c1c0c000c0c0d4004546142c0003024000010788544c000391003001e08104240029414410081034031405001d44520400d0b1407d00705850300f04840090b4030f42080e80038050405603114108500040c2c1000070002c40d8220a05680e464100500070a140c2e60082c400300021500206c040d00c042d0729080041078500300390440c0031080200390b034200301d11198040e100104240c2c943c4541011750745e003030005024040c8810800640750b8558600002607842d40d8204452a442516041c00c150b000481c900104a14880502c50301c0c0c1e4505400300010005020003070981740041070340c0d9252541d95401b4403011013040d00c682e440440847c00810680344c48d4602030b100403418140800184c2d2404029250a81c401e040190170004803c20f41e0201b500294029003081c0311203004441030341024800c0d550000d420080030300407440d054801070007910016001c0012 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 771276771 1250 771275521 771275551
    0x14010b09010e0f0a2402120301050d150f2004150309140a030512010b070f0b0c040e0c130503030c03031506070b0702010f06230f0609120102070b0709030b 68
    0x1860b43c940c0c1c904100f64000802090700c05841c3c0000c104140484194008400d4490022070800c9000246540c2d03589410b103d142d01d50b82c01e02e001d11031001c8102c80101c0b03080120299402c246111401891822807a2007400503002e949544135000c101941c02d8000a0403000b004203201400100c40591541d02c9181404070380754000b07280440c07071801ca140440074107000d600201c02c205a80320009159811149150101c20b03601c406605806210300d4130010000078155801e5030000c0da000c0c000940c0b02c0090310945040a42c0d440f4036828040c402c58828168101c005454542c3c10b48000303095010348030540040d8104806440000c0d40c910010b0314800c030200e41104031039416a0f50400f15618203a20181d00001c5003080c4101038080c0880381c00309010356080910210f082d1100e52020419506c196950307031402500c0e6001c0c40440030325811403d800a504220082071a00d485200302c1d034091040000581d02c41c201e080c60181840090710740010000340220410100b104e800410350455503582040b40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 771278021 1250 771276771 771276797
    0x140a06050604030f0f051c110706140a080903160f1403030708180319050903071703040e0604022503090f0e0703020a11101e020a02031c0204090614010314010b0901 72
    0x445d0840a1440c424202c101e618800105542301c1083e1601010f60001c4a00c910f4441100340c449100c214036928107102c0512a034440340f4030500d00c0c06e40201a09054038a80f10040c1c5000200c0c12420000351225104211100c04002902d428803c0c1c42c0000343c059030440c01c0400d401042900098038101c55142d5026070020412403c1c0115580a0003140070618500000003014240c2c1d04003411081c4a07000380362000a00b102c1d480e4595425140b41c4028501d064240040d51041c2a03004d803200da0030036803c2c094010031080b241d6144507059074111070340b601d03c0400d00e00101181d1050b0000c00c10b003c0409800c2003128200e510540d080025403c0c050f858403030003402141e00302e03984900c000c0c2070301c5005810920303507291b9401402c2c25207410220300d003030280200721503060b84141281c05006a004000100e10b084604c082c020385400f18600162034550350b9103910042d156a078100c0e080301e0082403981c2c000d56800d4403500680c0c00c40aa2100b006614088403d40c0b2401200346060600140c419610 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 771279271 1250 771278021 771278023
    0x270b091810020f1b011811190509061c0803010b071704050307060503062d010201140906010504090f05030304080901030c0309020a0501032007081206030703050727140a06050604030f0f05 82
    0x10301815420550f00800c003400c10040c1d04a60b1007c2a002e1001c115003410555080346138942520300c09030480040e81c58140034040101041800c4404403080d036035880300040c40400046001b040054112030310707008182403041002480842d1200c1080741040b0800c000c0e00c001c40e19000b00c50361800d0450b183d956610124481c0c08046441c452842d5104010030b0004c3c88906141900c00d2003a4002c00034100720618902d001d907800c0d21082d00903441030b001000300d4a0550840034a5034800c030107100d4203600341c1d0740d81407440e0400d440c01c5802c00c00c0414103031441d50f41442211380c6000d191074180f1034160310b6000304401c1106401414100754450052060121082d0322014146c02207c504903a280d11904004c1c0702a0030118150710900c0003003000c10301c11f141c00158202030300e030010701801c11185440881c1403825124158240e1042640304900c143c40c0c0c0c54801c0020840d02d40d0140c6840b842d1400000046508580229204400902c42032011940d03000b0030345d1613690b000c140d10f200c0074a1403c0c22 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 771280521 1250 771279271 771279281
    0xb0c071106070c06020105070207140904050114040b060108060d02061e0405150702130501030b0f1b03010e04030908120d020702040f020c030d0501050a270b091810020f1b01 76
    0x39801c6880000e12004002c0b81d550081c080703407069402003180740c4600804a84401140c0301d1428660350660034426180791400301d00360401e100e0000026061070110041490307071001c4805440c000c214104100095030000c0803075a03c88000c0b914403041091560000e8010300608925007502d030031304070498016503d90b2040700c02902c00207000c030040f5080c440800c007965102000490050303c0c06040d44030001064008c00d4141c2c1c0c0d002c14824241d9032400811400746100412084c110f00e45022840d030440c08035002107018140c90715a0003090b01c1c01c0d00700940543d000340c1c07100e400c0d0303884240c0c289000e03044041030302c0c9020043e40025a0b507406c0c078000a80501079106a000c00e00d4800100c0110810002000704091015007900788006d0782e8900400034540b007103102c0c2c60320318174403040e55500750444944030b03210000d12660000344d01980c02021031301e0f07002c04851a80c14074000c050607001e060030070064404840040d260030351030240540760b0f80240c1e000f804600d50000e1100d074541c240030030080d080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 771281771 1250 771280521 771280553
    0x100c02030a1b03031409011b0309050402040306020304021215270609011b020d170c16050606010e2d0a03120f0e180403050c030706090501090516030b0c07 68
    0x10b1031804110501c072040034540512044000c00d0000c03680035000c10015082d250418016150080348140849818412a510b00c3c021000c2256008000c501070355184003400107980034480041c1c803403074144140081c110726203800003107950295501840140390701080550208400402c000201d0703c400307101c100614005030b00040f50244004000240350158001080c41c00140420560604504000e0b078454a4046516000420301d242c4400c80750907414165420502c0d460704c40e80703409007070110800d000740564011150340d041f4005122142d0790205541c428500d0072115452101c1102c252070104610410309031000600c03920180320242d4550480d0741c01550403000800c180d40107000d009001d18000043d020118042040b88911800c00e211006150b46072074850340b4064403103403421f6600c1c2d006481e0030f8045120800c0b0715000a22a13001d4501c01a1144002146050300f81c40c0250500a5001c29441030482154041010603c0400615040317000c07003001c030340c0e01c0155040101c404018104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 771283021 1250 771281771 771281783
    0xb0c100212090111040303052203020d0605060a05041406090a090f0c15090b22080d0e090a23090703021f080c0408070306112215020c100c02030a 64
    0x500380c104008000c6003510407001d440003000b001300e088840206501541c040030300000c80512900701035902101003e40841904500509136564a07800510000c2c1c841400321051504e80041c4441820810811000303498116000d000480442808107100d1b2001840c1c541f1541c0d400b800724118a51aa010052094025038030307011440507418106182e10031480f45440c0041d5003800380400d644201042c0060301c2c040350401c1c0c90083c00303491811a0340b8012510507041c3c011804001048442000620781c2c01c03150f0b80382c002071540c0000400413003001c000c4c10450301608221001c20714100001441c5005085c0110034106519170300300161400101e40c00c0207401c4114208030080701c0d031800746512601345141d5240100d07540d80b152011814000e521482425138400708041c4005001604000030001c082925281000d80303400e401e00c1c43d41840041d10a0401e260101808507000c00440420402e625000034400b12446602007000e044170307214120200304105042408540e82031102c280001e8000b5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 771284271 1250 771283021 771283027
    0xa090c0308190509181806010f0e1008060f0a0f0203010b19020d0206190213090506011407030905090a15030305031911190207080708071508060a0b0c1002 68
    0x4a0111002d0340030151408240300c01600d080180b0307204008a0f480d000c8003505044240450304104400c450b4094040300450314001c08901140340b0812540b8003c1c11040501d03000f203441d000f000c0055000241170302001c9060f18005200001000031607580044496011000a41c0c03161034000041c0342d0303800b0f01c2032040c3c00000002900d90365100903104140c1c641d001e0007080e0302c45150603683d8142146030100540c108400049401c2c4400c600e0f4083c00440c42005445c003000d07000440c00c081c40c5904803242040c2d889061081c10750748012034140388101000c001d45010541d8030003600d0841c0e1445104c1c40389903913000103400c414880d00000240107803090814a015140c0c90b01400d02d800403600803541200344980b0300f060210600564041e103004414003403424600ea0110305800340461800803c0d4450440c0008805904002c0c8000030034180020303145103418503e81030125042c14082c5820442c4017401e000d020f66a000b141001c03601e0111810340c2e43c009030b0f82c40a003132541d140910301c20740d0701c08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 771285521 1250 771284271 771284273
    0x60c031801050423040b010e03071404090803010914011203091809080c010b090603071a070c0806090a060f2d2004080c0102121b0a0b010b07030e01030c0e090a090c03 73
    0xa00c44522a134001c0303509200350030f54600115a15043c800b03e0300d07490350052204100322000300a0070302c02040c0c060030100e9011100d4440e004d1035442070b400007095640c3c450714000d100007403010083c0501800582420803607001d45008000101c5c501404034116102c4003000d240c100d00c1c4e4410400c0c550721054440c0c03a8080503403214001d00f01d03400e07002d00895a00700061610f01c3c010030007605071907120646201c0c201c07030032440c9040b80e00004002ca50050658602094400c0204002c600c6044100000c01c804482072400809440c0200a108403540c240303548107040403132114010f00c0f203030b00a40c1c2c100050f90721524944058440c0c0740503070160100281c140e031000d43e8400000c0080e54003c40032150039602d43c600490f92141031680e0090051010700504411210740382007070028260b04011030340c0c0f02c812a16001170800e0207901590031403100144940c2015000b00c2101d0f0344c01d0302402c04010005904501074028805400880d10502045000421007611a4021034003103030414912580c168807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 771286771 1250 771285521 771285569
    0x70e180108060a0e0127060902210d09030308040b0430020708030c0a0f050c03010f02091801081c090b030a0905060a0c0c06020f07121805060c0318010504 68
    0x2c2a14042d14150070300c80b548980007414012950041244189078150240f818604001c0d0f1283c04400c030740070760700c03500c059000d60340c1c6020082040400c3da81c00a181c24084500c00d00e8807040c144001c06010000404002298019140320f50068220b1061840c0780d5451a200490400e1003c0290103100070f07084051030f0085090654a450407a134088500143d25091295624000c40c20030700b14130752050720300000041344034580075000d5110300100c1d454450541c000a0940d040c0e081d1004041c0c3e8042040c0c0428902100500804881c0e1940010107506055881c2d0b200c0c2601c0500c405800c00700304d00301c500c80f441041d1400041c02e440e103410747c0b00e0031301e0801d043c00f6140d111000e99451282c2030100303401000610501d40c44114036201d5002c084604c0c0c0c0d03120040d40184d41c1081d0200700900c002000304000c1100e00e8407030142c03030f0394100c0f1031820f0320b00c0e10400c00041d070440d90185c68140800d440042e0000111000e032121110601c80c03d01e82003004845a2245401500015080d03010b00703000120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 771288021 1250 771286771 771286783
    0x22a130c020a0c2309090705010f020a0510140f04020904030f0e0a1701060807060c110d050a1a070903030e0603370c0305091504060b060705060a060803030708070e180108 75
    0x4001500304c0c0d00501304000f000f8100d0340507034019030540c0205d8000c101c80d40c040c0484501040ba140145c1780c102c00382d80c4034581030110031a00c0c002c031103407550098408014070309019035010344544529400c6041c11340103c0e481040c0200000d042c40320180c2405c20700350055840920b803043c000c02001c902621801c0300115030304543d580100035804c002e004180b141020650009441450795000c41d0102240c0760220540c80a50020b41c0255000c0002c00c08aa010b10005100f280039203061090a94002915405410020448010808001000c0c40040d070320580c03004100008807403194a80d00d0314001001402100a0703200c80303509910b04c80e0001e0140d4a109a04444000102089a20041d0f101a0b0503103004840c01c10382030704404000ca0019840120300350f000703030141000046164610380231480c03641c020130066525500c110b0802441411602464018142500c00743d030460518440180507040003520580510a007241d402d5000c1d01e0348a04c0c0142030642360101681541d4510616452715 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 771289271 1250 771288021 771288059
    0x606071109070e2e0207061b02010504090f0902011d0307060302030c0d1d01060509010605030c0a02010e0708031e070807200d0c090e060f0133022a130c020a0c 70
    0x203003482d80280c4c4101d0020490b6401c43e031064a0713a050108546035000c190000c070f0f00049040c1306050001040401c0d240c40744400c0b40300c14041c00108a00c0f20700014104c0503084401407501c40c541380d1500c0c6961808601501283c030f0505015880c1d0b00e6445460301240906c40c80d80c0c55807480d007840c12034214805820404007041c500000c0041540f18401e1140c80c200034054100410300c10004a074003c001040241801e4800b8400000c0c0406980b00003800d018155010003500d074004542a4041e00000e22465514107140c9205460994142e4030500c00b4014481d001e44803851120341c5038a0744858240c1c40010b00401004604c0480851515050f940c08a0041d100032600d072840001c040040080c40900030030110000703082607071805441011511011045942c0c050099a00741c103460302025640711805200c1d005019030352448103111284031001c000d1522032030401c1050741ea182c3c940054070400c403808000081420150b40310180e10300850048020464a800040014051050a9002c01503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 771290521 1250 771289271 771289339
    0xc03150f0a060e0402060703050c0105090c04240306020901180f0e0c03090c0f03070b070803040b09071503020313020603090d03110f0301290c0606090606071109070e 73
    0x7511003484100c00c6402600403c04a5400a804200036251a50241010318801d04d4410702e4002402030390303403e4401c1a141c081036a07114040400c1c0342e140500030300f030034501040e0245504006a01c0c0c2c03200501c0144c40003a08059000404c02c0146c1d10600031100007900e0008808801c903941c001c55000c229407449200c031102218000701c3e49407141001200d000c0e8a90758020581c1a40d40c0042000560103180000c3c1d06110b81c0e080054078080c04800b07402000d02409440b9103a2525081c0316400040c0285a80c6460304041e4040c07140394642550a41c04400a2600680306c0c2d56074454411044070210b400fa500000202c10001c004000140f4142e50b4001640c05010350305441d00c244055000381c1c107410841520500051185820000c0ca203020800300c400210390707202c00c013410410b03a540f00d645103030032070b410803070810600b070605003000751f00100c00781d030650f01d0130103161a1040100100140e0506c105040d01c08200f0351441000d48640e180307001001c1d22580104041400080140307106c17181e0003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 771291771 1250 771290521 771290551
    0x3040f0b07020c0123090919060602150901150b030910020f09040b010e010e0402030a0b06130918080304150e100f0b1e10030e0604030c020315190e0c0315 68
    0x21700c0da00c1d01501d00d0a10841182d460034000030108211030702c80020040000c3d503000808050751400c560103107100401309a00a00320418010807174060b03a03a00145034280340e0f8181b0b000345814410400c0b05200311030086440e207440303860ba008100c0c2407091307800d000c3c00302d0b40c00400d140d00c80d02c507064002c2c0701110084600308182549c584c0150b0715980c501d1400e6000c11050306607000141402d400540d401008148000381d0086483c0005480c0d40001000548041d14880d040c40715000c54860035074010b0625290407030841c520f81e1000254800108001d080c01045403108850180640143e040035a0396030a032000041080c004100402d000012803d105007807100c4051f250901a0300c2c0980052061203100c10100b448081c400ca20244040035020141e40300d048007000071040c0b01940c011807280c2d84040200c003450041601d45a5134007043c103000250042030141c0a43c003c0003005206401810214280650804007030408641000c000e0301400740c044030800e000440c03c90a4490401d004103000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 771293021 1250 771291771 771291797
    0x5090a1401020d170118060e07030207050607020c1c14120310270209061201120228060311090a030c15050403080f030408040510120b01110c0603040f0b07020c01 71
    0xd00a1401107416040d0b0030f60801841030b20b6042e844000f1000c8080c1b40420020b036101e10400480b441100c048000907404185c000400805010301508640031f840102007411100b000280c031a0300700200c029610501c001e8540c200700410201900032400182560446010360440804580c0211101d80300d50308040d00104075201d541d82c0c840100b94003900c200395900d040801c1500203600c102d00840e8802030a000c02c02183e0440d0b8241c9010306444407075441007800780d1040c02060007580b00580b140440091070140c041e06540c181d00304440f000e00c1c0108034206030480d101c00760b1203a278030380301d400500120002c024444004500012980c94031502c41d01c4114203131040364603004034040149070b04000c0004c0c26250407040061074105000f41c94040c03405a544002628a003480380b00c035004190940440140c4031b800e40f0490300030030001c0c24105a000c2c03070030800c56200d202c0100c001388500c4010000c1818000303c80445413200c2c0c1d01109184641c100108040d43d941c00140140d40054020540d0314 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 771294271 1250 771293021 771293027
    0x1e0b120411151215031209030d05030105241c1506020f070b0a09090e01091716030c150c230f0307030c11030d090c08030c030703050a05090a1401020d 66
    0x5603030707541d089000750800c01068035060f59a03201400441015602c08041d01c0580e605005001c890410b1034006139484840310b00745414080010100300600400b40010400f640710b0807850012185180c1000009210340280c000b1036010300ba1b0080a0140314080d400d4814000d40c1c841140095041d00f0181b089940307a60899503440c5000c52020540c004c0c80041103503c0d46503000e0900507180e41802001e681e00c1d0214207003101d41408100e80385030344480a0b1000c0c00b681103114210b20740e0039600e481c90301c03518400b07000540380030060003401c00040c00600c2003844000c8040001d040840c03034052054055085009102101d54107403072130358a03c218000d0428581c018102c80d164040b56000c0c40c1141d84c0ea51080d8010102c101e03242091102500c1c032001c0000301480200070311150b1741d000295a020a0400b11001101a00b0401c9030794010020f612180300008140e032079841c0e05141c03032a07841c00300e0f690071030780e030b024101101e600070b03400290115040254300f00d0340160b00402c0c0d00300c80c8240c444000803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 771295521 1250 771294271 771294289
    0x20d0219510c0c030c0c1a070b150f121005010305011b021612030210060b031f0b03130f12030506040e030306090114030106030b0c13120503041e0b120411 68
    0x14074007050350f440e05440080c2c01010074101d0356005040c801031080d51402c10301e84a54070003516004100e00041c1c9001040f00c0c602d550740d0000449028604114070700c2002c10765815180600520484406d444580817080810800c0c0345524468000e01c9956980e20b000350282444080703003040c90528102405c2d259100264041d001c40c02c40110840781450a8080c000100302d03810142c2c114020040b08100200460043c0401800004081c55407490710000b04e16101c440c038091190416000e070780401c03450004800340d075041048818082d0144007145080d680d03051503494010a0702c801c0d074070030402c202d40541c40f00744182020340d0248058144452030075120720003140d000f648603040c000140001055104090003041c6e024000203801600d90302e03091150305044415200d5108002040e0341c03110310300080c440007044124008441d6400036562030341c07070740214012411644140d94002c0403140d1010b45903402170450190450740c0d501c0e0784185018200c02103030150390b0811b13918251035060500c2108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 771296771 1250 771295521 771295541
    0x405032a10091a07020607200303071a060604050307060e040b06031e1503101b0c0b0a0c140d090b0108120a0e04021315020d021951 58
    0x403110300b40d04000a43c0f98014a503c50490240f50500c006001a2034400c010300085000705ca01040e4401140700640c060f0002c0c0c40017502030740080c41801c00052504410400485503040d0490955580c203010400310700a0303512540d410720641c1340c000744058000c9028400054203480500c00601c903203003407044910081c5c80a10482d03046a01ea110140b40314007407550004486403200030200904400280f505110820b00c0d00c180f5580c44410713280242980c20040c85640701d0a001511560540360303184030440080c80005081d8030307041d21041c22841244900c103000c1c01d80c0b080c0360302c421500d810b10340100100c0c541280d044440000118a03024000f41003050004407141c503902d403002c0d403003044900e01413504905400c582c00b40b009641c2400801684000760800702901c825460310210000d143c0030f04201c03914250740103c06901c107252040308a0100003900300700384074100d41110219007100d401c1c1040340c00301c01c03209548071120032584d0410781012042c0070741c02c03030f04648201940300d0466001103d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 771298021 1250 771296771 771296777
    0x51806130e0406060b040f05040605090601020601120305070b040803180f03181318021305151c05100f0e0718051b070503030406050a0e100e01020405032a10 69
    0x1010003050700031900c40c5500c0b0b4440e150100e000c694601030318010340c00c03a03003081c0f20402c41100c091140e41002d11400c0c7c000d02c400c0718028154204800045c3d04c904040c085e64031142d916040301428035010f6002c40300d00c10360120002465141a00305010541c2058544916006014205911a080000b442c6151201e403d000c0c2d8a08010015200c80c0141d02100d03050300108015010003031a44c5620171410040381441d10320000800c0ca02c1000050a40c3c0c0c0814040e451500e01401a0b1000052141e442c520068900f0712801d40100d8041240c04805100201288139201c44019a8074a540014624104d40e020501c50b140408007420b480d800e82c2e019008540611030340c2c0203007058064106540264821800341007100b145521446203510068003a07605a09c000240700801445201d03141c0d004074050003c01403841d85c144074036150f8214070501d5060780d0b222912117440010030b5044030000c3c0340007000c440b0000d00e0f00c009402104404c00d80d5090060b40303800c0d50040f40c20040349210300500c00d69 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 771299271 1250 771298021 771298057
    0xb041d0d110f0a0501050105090c0408060402060702060f0c0a030e0a08060c1e070308150a06050a08190e0f060a0b060307050c010908071b091a09130210051806 70
    0x100101c40a05008490709881c1c40b89845a01c07100a05112002c1c04034060030003c1055030603c420b000f20301d400a40070301c0b00c50004020800c010540031941941042d030403103c00380c0e00c403100d0000400501400145c2141c510380020541c0b4a09000103260b503001d880398882c40040d0000604004040825200b000703a2038110070001056813080b00e0080c04540c03c11001580e00300c98a00b06040350350044081200400d48a5050100c51052080368000c2004200d82001000e82405c10040c494001d1000340d1b41405001d501041451607000040540e0251003d42000518500010035503030380d550701c10b2180940104004244000f0507400381e4020050f001e40030a05c0c40c1c0320390104444507400f2010f50007a555840c200c0500180328640100342c014003e6004280e0707041288481250080c00d94007031604079191030040c04003c000110701400c4038408640324000ca5544081ca1002c400000d4002940068803280320501160428043c20400c5420300320007044d0010344081c8410ba203d0300b0f051040c0341c0c03000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 771300521 1250 771299271 771299293
    0x11071208150f030703170c01061e090921200a110112090b0109050a0e010e0d05070c050901060c030206160206131a01090b0f151204020307080d030b041d 67
    0x1c030030030008140010b411152201c0d0345c3d40310f0b2040c40400c05518692290006205031640300c00b4020480604070400e90301c0c2e040354252415114030003141c42130340c103c1515a01220184400c400c6d0000215983c40c1c40108a80c0404000900f80207068a25945426200010a40800c800079130070340102e911000b0f030744001c1e10800c01174440f5001101c10f400300715280c0890708005a640c90000b4020400d8110128030390414003101d00681d408404a0781d81d81e8904440100b070b0200008042ca06040e09052160b41d0750050b090011b4101041e400154001354403000001c0c2d900c0d409014208014000d41c03e88983d40c64094022840812131184600180d0261012841409210140c02040e6108a8140f5400000c602000300000c03800d9015003801a0f840c160100c59040548100c4801ca40c12074502c001d50303d403609102d604e80150482c110190340044005411510308028403405003101d5422148400c005680c0200580803030342c686070081d0304040d60524060205400701031080340389009032841c0058 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 771301771 1250 771300521 771300529
    0x1c1701080d0806120f061005180604020a090911040306060815010e07090503061503010608031215010201150b190c0b06040b01181d01050904020105040312030f1107120815 75
    0x43c005a50060681c005070440c00703c10400035040c1c3d0050409004e280c6807621300e5070a00c000f61391000c0d001d400c101d603c0c8849a0035900c807107980004121030040c0c0b14140b01c40e007260704102c0d0b40c22132a00c0d40c0c604032502501c2454507015200301c130704c20707002804601d031030300c0003292100c2c00c0c074082d00c032a00a0007005010850844407825886030712803400c05482507441d40000c1c41c041060310344111f50541c582402d10b4a0400780104006844158011441e0840c40b0554041c3c0e43c600400e4005854003103010b41c0384681c800e4005040380141e4007403184020b0307201c0c0300d0351420784d01c807068103d4100080c200c1c14a05c2c41c02550200ca00d150010ba0301a0369641e8281400007a0004101060408c10103504140454107000840c10241c414204a10607040c0c0101e8608800c0e0010f030031082c0704070741e41403c210041c1e90050071107054960140d00100081d100c004280c014104c12182030940340d0034000040d0710500c41e840030700700c1c850042080544510f403249098501000039a1812868174001140c0d81c29410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 771303021 1250 771301771 771301787
    0x41103011208210702120307020c0105070c08011104090c0206060907080406060b16030305060d0206070320061303020607032a020c040908120c090102150601030e1c1701080d 76
    0x409014068a00b0481c00da10340c120035504824260449030703c4052180a0364100411032046000c00401451400d02c00c3c80a907503440041c04481c10050006083e03401c01406580c1a002000c07400b00a0000301c9120351009116001801b50444044c81d2002c040b02180c03000507070740d00400e0040e0103030a8036121540111889100240143c4031940c031110001001d00060b001807541845201da69001002241380090a85802800b09445102150600005641e40000302d0f0401075150804844d2040ca5480c0e0002ca40381c12400105140a40d404108015803100c5001d01d0f01c80c805d5007503801d00d5580030030940c121a089580e604054a11001d40703052800c80e42001c14050901d80105c81b00d490131200080c09541c10f4420171990440046001d40c0d40b100b89003105600515070068042c107003040c210000303660702c0c811a0307000c500c92011808100035034000d40c0002c0000c01e044094a41c0c58556202a540c210b02443e0340000044002101c040e0065a4812840c141c1c0d0106000d02040100c0082c200d81c10742c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 771304271 1250 771303021 771303023
    0x70e01050910120f05010b03060409050f12040504110c120f0c071202030616050d020d061203080709060f02030909150d0c0302181504110d0903110c0411030112 70
    0x18080050409035601c030904101a54802e03510000543c009001e2032055614002e0070280c140d04240060103004129410760303034421000d0314009000321090801501d00158440c8242c11402400558509680c805000f802503502c1520103210080c840c9040d00c000d80710315480240306800c40744c800059203032060020407800c41032140c1c0e18107002ca0002c00505003005507001041c641102006a0308504040c4070a070381c0003a107450001c50038171020002a01c2031080308201404107900103010014880d50342d00801c0034191030402180c0c02709032807034080d040542c1a03a0346400f1a00301c4c0c0c8005092032007031010034aa041e1070b5010798100b402401c1408113200000c1c00c818000b010100c00d003101601d66800d0745208a01450300e10621620794010702c0380c01b900303a203180b50b04801902c003005500c04d180709032800020380a4900040f580e2031488036500c5e6004520142c011682404001c4e01855070006c3c8200301130742c0d0136003030341c00107031205e000c02044035205a003c0004c1101800108008412000301e0340000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 771305521 1250 771304271 771304277
    0x70c02010519050309150903040303050702180106021f150302150d02130f0b090609060c1524030606090f130f1208150307050409020315180d0305040b070e01 69
    0x45000458540b61240704000c030080000e1002c820019114130412440c254107040c581451b03c00c0c101100140d0f2030344503500000c2c1c14420001000000c5454148120031803115150040c4000e5840710300080d110b0b440c042e442d61401c802c105903100d108406120381602e400c0c0420400ba500ca1540d400d1002103542d0303034050401c0d6001480003984140403400203003241c141c60f40440d2000307818030800d14000c051313540252952410611554600e42c48000440b6000702040720b1294450000e00782c3c01d031a00108580800840c41c1510500195000555494180c202d0400100c1800190042491b648502c00c440c03044e8030020003404a56070b03800d01500343d43c200f2240f482000d1080100c2d283c5d410b030103480103002c407000d910b0702c44842d490990020b1900c0d0080d04d001c480d0300111481d01c0020381d51f401c160203418819030341c6400d41340441d0f030200000050071048030007007042c80c40c0442d40035100900207a51192a40136504015281c1c40c030030710500c5d10844e8083e02072010f5468015081399102e00b80b001403414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 771306771 1250 771305521 771305527
    0x16030510050a091109090103030c14032511030d03022d03070318140d0806031902120c0d050312070f020d0f09080a0b06010905031f0c0c080a02100510030308070c020105 74
    0x303d072203128056002c0c5002b51106140c00d0072038070700150078210345a40140c8941060000703500528281c5103d48500707204807075080050b5446d0402800c48400c2403182ea41c1880f508841c444020340680242c207500c003c0b6020074120206012001c0a02c04504104d40000041000061000c0e4001d5000c180c82c0b52804a240b02c1140d802e03510b0b411121305000e07103000183e016403003171440070340d001c54070a0748070800303402404480844d000c3e0100b00c03810f1000e00a1265100c1442401c0c103080400c0850089440184005000c60b11400c1c11602c1741d00c0860404650039213040090b111703030b008401414030380149500a0034030590710785089418003015503e500c00c00281c0b0380e001518000400c01803c00c14050903c5000604041001400500096105500039000000c5c3c15030302d2068403039200c800b0140e030180820080f1030300000f114602d02d01440141200c001041c0111180d5001810711b0301080201d20400032500e8624100c82030000620000300002c03000070018004602c100c41d440f420038418101030b41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 771308021 1250 771306771 771306787
    0x3180705090a0219090e0612032514210304060906020304080904060608010b1206030708030a09030b0105011814030a0204062c01030c0b180916030510050a0911 70
    0x904000342c4a0440321034021034002e80186094100c4145440d803414404801807620a9181e5008401414188500381c1400342d0300d0f4580007801220000d034500010343c0c00850140160107403800b00346030240c41d11054540110f02c01c0c44000740e00c85d2400c0d1400200b0000082004494152350f10042084905940b5048640700050890025501852242c0b100d140c40d80501c006000c101c5070703133038880e900300b0240c480100500a000421141d0142580c1e010002d1540d6a00c082032400c40181d0044055210010313042120961100000c01a01e216180c0d1070800d0345d9403401100c451104610045005c00c10100c1001041702803500710460040c054155102c0c2d02281c0c00040c11994980e0101140030380c940046600c0c406881da0100400001c054406090350454955500d032200502455410000020b10a443d00d0b19509482d040610000c148048524000003090f001c9500340c00c0340b0011038140008508180c0502c25608240d0700c0240c201c85071145421105400350211001014110a0404c07842d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 771309271 1250 771308021 771308029
    0x31b21130f0303030204050301050a2703030e12040e180d0e0d0f1103010c080f04110a0801020403210507050c090a020909181218010f050d020c011505010306030803180705 75
    0x50001d50003600e0040c2c840b86404140b41c2901c40c014071402d00e107454480700400501c181d1a8073300310070351140c1c07401440c42d140303107401e80045c840c085098240344071b00b0724092520900305c0c00500c143c5161a4600e12140c403100d41014140c290310020a089821107888549201e10031b0390851420203000f01000307490b150356203c4a44052030440150b07440016054a544a41803d01071450303c0200c500c0d083e203140c070304011040306400c0041d0006098140702c00da5100241e41e0840101d0103402110021980d0715980d1401502c00260381c030106980722402400303861003500036000c0e11005a00003010b4a00300000904101e2500c100401d041e1005909100c40c41c4240ca5003202c0512503d0518444400d0a04e40b10300e041c5090200e042c400c000000c200300308005c21502c194416036404080c01c0c01d84204440f0201070b601030044111400c2c4140c801f0804100120054101c60681743ca0383c4111051261520011001c1d01c00d10701002d003620030200041000314001c11001c40c0d0990301442515039550700c0b10005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 771310521 1250 771309271 771309299
    0xc03030f0b0d030309020307050105090d0b310323120601020f070b0c010f0501181e1a090c0a0207060c020d020904050d3e07080f031b2113 61
    0x40d0b00007076a4604117002c50904000900241c0002d081980c10312500c8400110f039024150f0000b80105030f000081140700703255000020b0b010080550200c1003080001e0b0010081d801c0080030707000203d0010107502d8011034100300d84518400b0451030751910a44140e032409030140501158114402d0540107071155a0900203800a8490075001503619220011400d09440072200405605840c0400412001140450341d60070103401450110309409800c0d00059a44a0301c085400c0c043e00301a40002000300c0821048150071b021100f041c02d50300d40400812640c003880b1a49809640b1030003050003014090352040ba50a840100492250452540031481c40c410940e0100c583e6441200740c044d005030070061010b40001e203d00c50505040ca03108443d40340d03c0348032556002085983c99820040f4905104c8840030b0803400c0115145c901d0b000030310b030350b5942c000383c2550f0000c09201c6a81650b03007404117100480700c3d0a0301c4961888403810102c1119580310114101c42a5442003001848220349559 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 771311771 1250 771310521 771310523
    0xe1807030b091b09070c12030609020310320f12010e0f0723091e150f0f15030705070b0901050412020c090a02030a02090306011701060f060c03030f0b0d 67
    0x2802e00550f81052015140d40e110060368801c010741800c02c10107990184c0b0201070741d500a001029170750f034003070002d9004003d00d41010300742d54000000c000c56078003c0b22101044403841400900f4074080300400308024015000035459404000c0303400002d40c5412180002c04401c014440c1410903c0191084e08480d0b00c03d1005185410800010540c1241400f9180052200c43c050005100e40c0c525030f12940c610648400e8892105074000c01c19228816002c0b0750b502010722549902400c0106401134030400460300e40c0d10490500e01c074100581031503400214180d2010305611800c01c2580b6440e60907410041504042110500040c4c010609032312102d4003500246000207140e040a09000d01180340000d04101558086940d412144d2901501e0310b074407002d0100f005803a900c2c0c0405560191080850b416030510400c0c00104240c094921850900c807404d100030040980d942000813203080382c0d0b20640c004609144507070303030100c7c5c040c1d00013400d004a052400a2003988050000348003d0030914 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 771313021 1250 771311771 771311773
    0x3090123040201020d0f080c030a1805060901050109091703060d0206120f0106090b0a0c050c03010c031409062a0904090305190e03030405130621110603010e1807030b09 74
    0x81c0015941c0610080710324003514a445002c4c001c5850000d80500405040c200d662040040084c454020941c0490150161414000320314061404c0c02a03590ba0240d594007440d5207450000110041c013841848103240e8050048219107414594140300342d003005094030f030416241d04290300140e9880c2c3c0101039600e0780aa21468174100100100395828050b00880180803911100707000c1c0e43c1d49030003900c49070700d01440c00e40301d9a15030b840d001d4148140b00f24115015030800d0051b83c1e016815401c004001e0205003114001641d034502c1e45555000281c859800d000c2c0710200100c03240e240c1c0c000e00e10415049410551070000b40e0800b040845011110036000184042607980803240028480711000c500c5141015058060100080d12071150340b00e0f0510801031511000c4001445400000091801c1e0031046080c140c4012101c0030030640403011105000c000010f07405030300e0901e060b40d041c1c9005c005003030b0403640d0340400000842119a05010103100c0e1070700000c0000e402e02201841481c12038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 771314271 1250 771313021 771313091
    0x70c0e010303030f090f020f01020c04020c03090108090c01081b0702060f0c0c0301051015020703081209070b03010f0308070212060a0f0e0c0607260d091e02010e0402030901 76
    0x2c20b00a0883e00c3e0404000d006a041c00320704c1004c6080c00342843c846c02c0c3c0407a100703602d1303018200040c0d02c0c2c805511b010319045400800c9003e00c1d03003004806400004820f03200d45506940e101c00558980d003102030b03070300c3c003160441e030101c2c0b180c03003881c0680955500d642003420700d402c00380e400040d529044815141c00c1d4503030008021150741018030003c004140c0a800a00441c2425a03183c900740d1110701a480c07200c0c0840b03910a0069100b044014003c640240340b150fa80d41c00005c900302444401c6400c0c0d5441c0c424048001021112102140c3c100e40c2143c80e8203204030706507940c000450f030010b0701c140e0f401000491609500c0c10300b0701c0464081d500e040c40c0060603e03022414001901c3d4540907064481e00044402070298981c0c0c0201d450240e80641a4030005200d060419046006400861464007010541c05114a176a50010034254001d8120800d218103000d0088510044c10200900050446444104500b044d40296420070458400490750702d500c0061000455452120b44ac01d0154403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 771315521 1250 771314271 771314273
    0x301150806061b160f03030e09270a0c09051b070309090209010905040e0106090f09150906060314030403031404140111010b15040906090615050c07050d0b04050105060f030d03020906070c0e0103 85
    0x20300b07150050506a84e1244c0c103180200240c0440760320440c02a070308050901c0703210f0502c0014406031580581c802433241e10144c0f11a50000140800c40c1e92050448035103a400500c1c0c0914401c1e201c0f4168560780b44400c0c541088100381c046c0d0002401541486450500424640c4e0707a4040e84860310048000003481301e1134403141c4c005403071445002d04001703032415401c04041800a00c1c9141d41501220022810051038076082c4014032041d84050401c848000d400041c0d000e0100061084900991301c0d217680701d141500e010100e12a03841184585800074010468550280301c00c2e065050400e000014140032140c040740e00c4101504294080c024001401e0202603030600c40d40020f00f4030b5600030000300b414402240e441150301d4584400303100c03011661948454040105101410001d440c0c00c0000e40d50345032403550b109080d5811103403542000c000ae0018203184200d00c4d480e540040c014401c0f100012070940c002d40c8203000d02c036003050080240d0004521000001401030080c08a408565891 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 771316771 1250 771315521 771315527
    0x102070c27060e190b010c0303020f0f13030b07020606011b020d0b0106090504061403030301050d14010c0e040f0b0616061d0a0b09060415021602150301150806061b160f0303 76
    0x1c940741103070260b240c2030540c001641d00c41c03040050548d0508006a1350015a0b2241281d4000e503101440301d10380001c1c038038028046204007003048900c01c800084160b00c03601026600c50320f044409500107111914600c144280d42c071411880c080c009040080b07500f0107070b214001490002d8210700007140c0708040401140c107041c07050000030031103002076000c44004c0400098482c4818450300b4410206000d00301b0a008001c0c940d4850150544000c002480c4426006891a03c207590b155100f00c3c40c1612151050120703002d624041040140020b146c00b90725440c089900c6041e0b1820346000d40e954a0400381c4200030900e86503004200c6005048000c014a080d4400f901c0041c08031440740c000b4824007000030f40c01500b5141c4104607080c0507031241c001a40090304d0316240680030750f0100c1c0d20050302c90708803003c10042d41642d2809605800741c1a009100b0740d841c100960702150002420000e000c4039101c0c5a03e000303040c42e042e5064034a820061040c4401001c4103402440170000203000401c20150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 771318021 1250 771316771 771316801
    0x80f0903160512032a030d0c030b090f070c0303020a0e030f0309041506080114061c0f0608030f0f090f0a0617070801080309040c051b0c040507020102070c27060e 71
    0x50381000031441c00b15089454040e400c075030410140d0000c1c0058641c0700c801014000c0d0f8440c4070700301c107013041040c98034200100a00f800e074422b9405440004007060b558504800c2185c8a040302d51200310091400303036011002503100d44001d104000c01508103d040799030070300c400c0ca02410010019920758803c04100401c545003002c02445400e00c00504000329600161568111100c03507200380398601c00304010600c82c0c07046130b10140d000d0000001d074900390b50466114a0b1524514941044030704c2d200c41d140d80e624811080d4481003580148410040a1800001096032000140144001444110114442c00115003060001c00e11080d56046044484086560b02c034905140800c0c4a5140140040d142d1040d0300d21540140c0e22141c18203192400f84c000c44442c01c4000b40039240615140119903118084540303104e1256040c01c01260500d0301c14000c0d1a1019002920074500c6443d0a1400185028903c1004075001c003281c0070560103c19885076000134002e41481710168904510701c2c1482072 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 771319271 1250 771318021 771318049
    0x60c06180703121206030812090c03060c070602030604060e0f0a0509060c0901050c1c021011090108010e070e04090303090303180c1404020d240b040b0304080f09031605 74
    0x1501c00300c01080802c602c0d14a0031224406400d01040260903402c1000180c0700070741000d0451800001e0500c442154012840d202e0040102502c5d1280311500401d0b407a9071007998401c050702000c0c0b280d07801068942e40215007180d00200002507080c0d9410b1880034480084901c0400710603003208101c0841d180f0b00689900402000190115190082c5040c8050051020355410410041440c20b9200010032024030701d283c1e0108048040040038400a6640740599a8020203500749004401181c8000c0150b80c81c03610140c44e4070a49a09140720420b9040c0c005024400700100703011032001a4889114440307026019544c0856401d81074103003e400e4840d0303101d05c07008002c550030021020413410340e541d2066401d0134012001170300e00f00000030080d000b882d4020300c001e4a800384440300c02e4898518814602c1d00b00c01c0c0440300d1541d40c0050501c50007648900c5000042c10000100052201c0340200452680e105140b8106009400440d1403c04040d8007240024074100c8140028580441900d100b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 771320521 1250 771319271 771319273
    0xa02040503060403050c010b0a0b130812070303110d0c08040b160806010f0e03030f180109030c05040504020a033e0f100e120102031515070b15060c0618 67
    0xa19020110b50798003802400501003090108800c02d01c0c41013900700b00c0c2d100d03400818120100c0d4650000ca1400d03404034804203c0c90000a100007400440410010800c4504c4444141041c0303041d10240e01811a034000c0c202c809504210500c0c9810861268040480c100e5651009501c1c0500d0720b8a54105e019000300c4082d0040c0c920103c102d9070000051303a00c91400c3c6031601904030400c0341699a03856000c002907040c0004560b00e1005e00103030000c1c100c20300c0c1d4403044c000c0e00c8452500558680b074160101070840c0008420500c03c40c2001c1c2c00045e0400d101600511480782c0c1c0b40c44803005000030341e082465012036110151881c0c1c0701c0c0c0360110302c802a81a81101c0d106628000a0b04542e0020502c60050351a903104030762940c02900d00407907044001c0e004421000c00005400c0c000d5000322569601e8001000710204a41070007510b054120040806940c5003290039151820b020000600c42d184550031503415030075644454000d400d0003240c1c3c01c021b0855007880041c2c1101046216255051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 771321771 1250 771320521 771320527
    0x4090f05010509070c1118060a05100801030602180a0b0915130e04020a08030f0d0c17010303110c041109150711060a03020d091415150613090603080a080a02 69
    0xc83d50303c0d40219a00015142010850702085103000d2001c1c040d202c0a40e40e00890710704803c002e0144d20410140308210807110790314015194020031070b20030b401e498444001a218001840021481d6005024016454001802031744203d0000303100003520360002e2080340404154035003507060508080701c441d080200724604050081000710700c130005c240700c0c0055012941c804502951504024003020b09030400035a6981d100d501c1c07100d07a080e884000b6000c6114500703c450f4400718460813160005d04141441085903906e162421610000c541102000300d0007640c03d40c01007503803070f8460340612400301c052294a59800d001040316122490300610b45003803003003080301c0014480d000124500901103818507101c05103403200324000d0261030030030034407039140c15081c80a20500005031030904601c041210705170000c468103584010000e5581588905d44d05110092600d04280644809962003500c000c810340d49044c1a02910740e03039401541c071444002400e85020754459501544510100d409500e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 771323021 1250 771321771 771321779
    0x6030326090c2101020a1e05040302220e0d09080f1b1207090906060504050601030c09031101121d060603070e0f040303090f1110030b0d0b0405070806070504090f0501 73
    0x1840340308441c2c1c4180b007048420030000c0c00001404108240c0c200350f00086403541080f20300070341407903c010000440d0741012134040160174840c004842c1941c1d400713415940604035aa00f8000c1d992135a24800801c1600d449120144450400c010120f50040b5618401c0d65441d0200b858204070648290340b0031030300b00401500522401100c0c05000300d40070b0b0b8400e405921584401800c0a41e50b422440f2600d00300007600c2e003400312980080c4c0c15a00215010070240d2107000040d802c61b10300700540b201040a1510400104059909070200c04c04c0605001c0103d00b500c0000301d04465002c0303901420fa628200000b10010030070465030f40c2c8980140d000309109410304180544000c00100103058442d06000010708240c801c0d040300c425035502c0380602e10140c043d071400481c03442e248020039014102640600c051688039008541c2d0012000e4001e001c13044207511615440c0400620a5030284201d41002070440010800d0034400d402540e01e0940740d508010903441076422256081118600389070041c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 771324271 1250 771323021 771323023
    0xc1e050601030b0403050c07090606082809061b02030c0628020a0504091d15150d020415031a01050406031101050a031409010605041512020907020f010603032609 71
    0x90541e9004140b003d00c6698629080705e0600c80c54184c03c031140242400020f480046030405001d80c0c207183c8a4050544e074542034100c2c83d00d404c8120140c0a0081d1808503098081e0b0390001e01c4981c0602d0020071043d00030743c100e000314000900040d0041c0e000150358003e80000380180390300401010a900f1127950b03410000c1804141d140142d0001d50b030700184c00e80405018800f210300a110070b4000b8440c207400c5051402008800c0c00d0aa10b1034054401e4440b0b001c0399003203046116155412030345458080c140180704007560501801c80e0059940c5080007420000ca0422400540c404c00f450544400c3c0400006114141a0f0280d0300940c00c144c01800003507446603035140c52400a190480c0c941e0507010044002d0241c039094403004c0c50751031041c072a00540c19041602595411359062004c68a1303144030082402d540d2207200b0100c01b82507004401440c0940d4100e0b081080d6104031a85041c0200360f560844030658400c03008180110b282e0200c145080141043d80302090f075002e4240d00d000b660311 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 771325521 1250 771324271 771324283
    0x907050c1e0307200d0f0b06010e010f0309031407050109032304030f03180e0105030d050f220e090d08061804120c062f041419050409030c1e05 63
    0xd101065034580d8104640484103809600c00c40201880b400407024100484801c076882007e450388410017001402550003100b091000e510181c0d254018210400d104800816060030f08604002150030b151024030254805005005e000304000030b0060300030b1501030300801c144208081ea6102e01100341341804500001d07682100c1d0006515030302c000a03450200d40107400452800f50401010303401188014a108216042c7c03a0107400300c2c0e400782d8900a0a0740c42d40901c005e03080540c01c04100941c2c1c0c104801041e8020194107116840c001e907200c642c1600100300448a00c1d00715489009036070070301a03208070b04607000388082d5180d40b080c1c0032160400c1e19607013000700094110344c5d8802d0b80d1a0b0152040c0294850507411100030041240000140450802c0c13492a004113180c1c0b5a00d00c8200d140ca1100b03d60031034000031911280380d01c038a418000c41f055485c0c0114500e07406482c1c0007030603460710b001300820148a035481111b80806840c0514144030409040b2100c068100d0241000074030002d41 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 771326771 1250 771325521 771325523
    0x16021c080c090d0605090d0e0105041a0901090506070305030a0b010c1203091506061e03270501090c090212090303012108090a0b04080f0102090907110c0907050c1e0307 74
    0x16580e525160002c00c08120f807114000b461107240400300002e6010100e034220071100d59907640420f0728044c070b00448031801180158288003000e400e2074800c10382030718010141c0400605003c440ca035941c0c0c6c0007850a400c1810182c0120340000204484480b0501c10b03d20541030900300950307030381c0301915040e24019408100b02c00741070707a40c0300240a02040c012582d0703040d503a400b014403240d6242d84000f810b008103501d00d03800000035a10080300312400780c0910f902d01c100000d400b484540c81c41c0095005034050307074002c3d10b40c1d55841ca50400424205005800980041c51000d40e590104030465180c6400090610310550014001800b000c91921104198142130301202d071040111401c0c0806541709094185a110340124000102988520080d0045490343c10549070310000424085080c0d119401c62154408280c000042c0c0982c000e180c1c00036000105003c403040e100300761001c034054030000d0703450202007070003c00d0b00c80444104110301252680b101d0003090b1a080e003210015601d0003507002c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 771328021 1250 771326771 771326791
    0x61507030f0918060311090f0f040c0e010f150c0203030306040b190e0103021011120a0507170c07050409052116030305190b030d1d0916021c08 63
    0x60032a4118031070102d61000c0c0403080b09081080c40c00500c0f910003003c1c580700c1158a04e501c0a4aa0110303e8100c09031441060440c0240001d50b03200c40105049490040c011210840f040d100130074070602004159001c0d002000d0031104603400d0803181c41c1d240c94a1300e000010002e0407100c100c01a2000700c2070340c0c0c01080550300840e04c100c10380002180700c108050304004030451484005803030040e6031100c6040302d00035108850318518031042100c2e030b41f601c150080c2182d44444500055114124020550380c10130342307401400c203100c03599410701c61058100a10441c2c5c0e000300b1210024113040c410074000302000c032000c000d0321030315942e59600e0f800c420140e0300603144030340c4001d41050a45421a03181001c10008440c2e0000c46180182c0109410340b03043c600b401001000c801030914034440c403c00350000078001c1890700d00c852401c41d14198010181c4161086604980e01281c4850300f0301c500540240c0e0b60807400e0006100d0091600c40744d00ca00a00c5440403411020f0144d400c0a41309401440b048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 771329271 1250 771328021 771328037
    0x51f050703140402240c0a0f0314030103050a02060304022e0809030a1b0c030b0a0c08150d0f031b0803090f030a05160c0b0f090a080606030d0c060e0a03020d0806150703 74
    0x4103102d00900440c0040d41b441d00607048a1000c2103403480309240080d2207034654444192800e0403070009030009020041003070780002801c8003d4601140519403162009064a201c0099400e00c0f620554100000f101c900642901d8007050a4102c61a0341d441403800004506040c081d9000a141280014004c0d80c5c0f11000781200091158544084010750342110400e10316051104201c0700409601603030000141c03001c5c2c01301e90384c1c16008052121181000f03040081c500c0c0a03403604082c0443e085821020321180c0791113012100f0144100b400085d014a03403260f12071802610090410300e80b400003425a0700100316940047c1c5e00081941e40004c0c002903d410f2110880c030f04180b4000903a0044c10311b009003c20b854203140c0c101c00007080401c0c41640c80f0304480e5640c10140740d881c2c80c1079900340e6140e040714645001d090310585001e074103940581070201c0c0d00c0700070401050424038001c1c41540160007600e0b40c1800f407604035044d250000c0e025550410b81c072942003c3c1080b6030007685002010821342c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 771330521 1250 771329271 771329329
    0x501110709090305040f12030c02130f050106050c010e0f070e0a150b04211205070809060a08040318150f0e03010f06050a080325051f050703140402 65
    0x20050003001e0520084204410400340c103000c0e0003a0450322074029165803480b0003203803414404d015035920720381c50f0b1940d42e18080d480c0c0c00c1201108400c01003861040e65102d084000c40c01c18000c65000300002d0b04e507140c1d0b94445104403030948407030f40742000c0c0c40d904c40d040c02c000c00d00d0000303150f00465010100841c026110343e6081000303800640319883c03020102005c08242608030000400c00c9441c40d484140c10068040502c0d8610440c0ca1805001826a5101a07207664014801003001900c614401468a04070381c1c0024405c0d04030161030b200041450040100701a00044030382000b401403031000051a280c503d01d85005113201410f8800c1154404100309001e020b08144140e4003c005c00038005460800c3c1135000401161188038802e40d11002e000038484070100c06c88110305066150262040480f44104141350000b0360104c42501c1002103c00b40304002280704c3c50420310b0300e20f0225050510b030708014140d661840307c0d16080349802d414070006a0310f0b04c40c4521841c4070802203001d00e00d89 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 771331771 1250 771330521 771330523
    0x5010201110310064a03150f0702011508010906050603070f140d0209070215070906091e0312080108011d0a15060803371b0609060e010902030d0e0109050111 69
    0x1040e04c03004045091005c41401c0c505075078a148010346000700003030f0301c51080c008040d5504042a440000f989400c00410001c0b00841c20842e4802018000480c46003044d61840c200c0d41b100e0390003017081d079654680c0798042204901a85410007005c800902072541804005449c400d45440f808404c010400000c86050b181c180700120040d400800c81d004500d02040e010f501d034046030216a038900d01400000383e040c1d003d10004000e507640c50b500d10500701d04000300d08011180e80340403800395510074400000020013600b42c0c44d408101b16601c205d0309504d801c2200e802d50340b43c00c01d0140c031030000200c452443c08001901030111908070b14010381002e030070303819000100095000400c0a01000818191000605215001e0856280032400b45025010808200c00345030089003000500070f000c02e0441980184c0e980c2406c1802100f000412609a544900442c1c1c0451403400c0703665100c078540010340c5414002c1501c0400306082c210b000041c4440001c0007840781d8081d00c0c2c1071040a0880d040b880720 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 771333021 1250 771331771 771331817
    0x10902070c0f1205010f1a0108040501020705010e10061d041e0c090e070914040b04080909130201110c0604090f0906021602090114150a270501020111031006 69
    0xb590140d045881910749030300c0d11400440510a036442d600b401c0311a1800d440724880e4001c1e105030300352031039512102074004640400010f4005e580351b41d02480010003103039084c4165000c1281d104010704411155540420a540c001d0380100e0f07060100001c8000c00202c0011825030195101038103071342c4c030340c1d040040f02d4808411207800340460341c900c6008074403001203600502e407040910781210b698541d100780c402d090f2090007203016424203001010070000b80c1c0d04400c143d00a4440d4504504021648010484064007102e41c4114170403560700c07030000d550b08040d40b0312401400c4006401e2040b240400700d0340d28401c030701c100600d0694841901c2000c4c65143d029165071540000300b5075455507a0101c0c50b910584420040e0312443d034034000002c2c1800c00700f003c0e800c12000500340280300340a081940605800107000902844801c0400460094050020105081d0700d10b4654040c0350034440020308495015110000c3c0082c02c0081c0442c1058083c0307058100c0b0460f140000702100c80b070540031070f110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 771334271 1250 771333021 771333029
    0xc010e010c0b010e0a0f05010b04090902060c0d0f0f020d0f1101090c0b0d050c0a0c1b03020904140106081216050304050a0b031b030403080a1109030a150501090c08010902070c 77
    0x14503000e001040013100242014020214040300380309200807100c20314222003081c8203103c20742d8000c10081103100750301e8000c000d00c90700040c003850030300e400320740142d052903151005c48001440400a01d4600ea4000c61040400221840100b0b110059a400504182c0f0380d803609100780a00c103072519242040035040f661070507601c0407113188010f42ea4190354a054202001040720070f818000002c0350100c041090307443c0c100c500ea5520b010b0820907180c6124103403016503078004a40812002002689500b040d541c0074900c0b690701950b110180803c2c00f400c5580035044031009802c0004a90041d2001e42c06990300402400d005604582103031030420b286104030340c405034009107140e000103501d16041c4080c510491103070410703644425829208401d14401190028042a0888c021402c09400c580c40074401c582c1280d0000d03d031000c910300081c81c0901030041220f5034240c2603d11200945240961030040c100d13650b0520800000c80c40103000d51105000b100d60181d408619103040c030080010f02c0b0020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 771335521 1250 771334271 771334283
    0x30d0809100212180609071205120307020c0901050406060c200319051c080a05130215220e0c03100f0b030103120914040b120d030b01081006020c010e010c 68
    0xf07800c9260340d0020f40c0c203040300c21061000040d80d011032501c1010540501c11280e031805020813604020800002400000c000d80e02403090030110300084640100440c0100b010381c00411040200c801040101034058000078091070605c40b00b081181d8000314500042e903401a1780522011049007690301010b40c0c044402d5052094030080380c1080f01010a807400c0300d004d0320070784103a0411540d25000290b40fa999100001d426240021046031169200c076400410324000345d40d4100c0980c0008041d0840c00c030509040c0c000014040b070342c070181c424002ca071009190070024041e914200494000200041c1056020280040041c2081a103e107459003d8140060300003010398441401905942003400101c503c010004a581803042c040c00b03800007101e0301c2482540301d89800d20305110182000744111034000e616a642110b9108052280c5103046103190740016549021034001003001c0c0307001c3c0580c0107600007641c09020559000c240350800400c2030818074000360f03603100100d600c0d0741c9010000e005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 771336771 1250 771335521 771335527
    0x60d03180312181212050c070603020c07050103060b1213140114091f0b0409020411130b0c0319110d1e0302090904110621060907030506030d08091002 66
    0x41049400c869000d080a0f980c0741203820ba0034070000000d290190080c01c4130810031040300d50000741500084640d02440d880e200b801c200561480364544440b80e00203401090300804ca61290721010000340009000c2443c1c180415440d00c10911004d20401c82c0781d400016081d000506e01c4500d00c507400c03036100d0f0b209500b440c5402050101c03034000d00103010200d80242c0d0707800104482c45030011314000c55454800d002c800e00515105100c00900d6410405500280c480c1a079001513500d03445290001e44410350b00660b0340c65440c640d003100001744d40210074000c5081c00040100741000040e06e0720202c0064504404a0380c60505075509440000c0460040c070600d5401c9a1440d07002014105a20b18102210511112281c055003a402030710142070b000b02d641000200800c0030038000c51411003018107500c1c82c02080c642042200e02c0c03101014519004040c007800464204180c0c0703075074403802a280400150030302e030303002a45885502e0310301402c06c0f403a140440c1c440d04090140002000c4207042c00c540d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 771338021 1250 771336771 771336773
    0x403060c090608040b07110c031603020906151801021e0d03052a09120307050a0c060503060904150b04050a06180603050304060818011518090803060d031803 69
    0x16210340d04a0400003400d40d140015042d00656003540510f40c0014400195541c040c0111480540c00b00040c4e114851010a4046601e05004060451804244c0007410344d0850040c028200360180085000b00403840c0c10031240c1d203151041d5130846802e1a06002190754503030040345000d212086800d01c60190103a107e501708800039410b40d01c522191814400c40c0da0305200d0624008980100c04860b0075a202c5580381003000d18010070300f0b548018112030a03103203420b101c14610341051108495960010403101c051040c0c0b0401c110092089107880c6145140c0080450600c80740078100a00050200c84034214001039604065011900a00100864a0b00c0c03400701e000343c2514810030009c4c6511000c10800e0204501442043d00c2d0804011403800d45001411618890300030700d04a0030181c4034442081150003802603400700c0e41c8164958154030300342039505404a9038000c8040d6841e141a08003000500c022080c0c03944028201c500210301880c2c1c0c2015500c800540740284c558803207040000c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 771339271 1250 771338021 771338033
    0xf16050c0f010f0f0b030105090d26010602061f05010f080603030715061403031305150d0906200a0c120903140f0c0604030f0f08072f01090b0306090612030403 70
    0x82da84c0c101c800c0c0140300510301d14081c54201c89054415035103541082c140c21004030302030803118000d09011001103c1035850210307109034002c7d0a0704813000580141050ac80040320304901140700e015028060601c9524000007c0c1040000c1c0704144148200000010aa035030181b0139184050307000200c1901c10300320001007a0040a8a001354211048070391240011403c3c00002c0d14040c0e031282c102d2440e01400c000400a4810060800c0a002c4204100b00649000c00e070260484045c07144c81c010451a44840325030035091010700310740840f902c00307114011a9035407000010b1704440d0049e86580401e00c14280c2128540e6107500081c0400002030700007010b041e000140e480070380c1d03110360581d050050b1950030440d0610851002500440e440780b810345c0400c00c1740b41d0040146100711401c0340b5124065542c02c0d0380780d600090700b00c10410100c04902c0f00034000700d0200003d0800746040002c1c5d47c113005801324213010243c801409081c179240003a500792110303680d064210307242720201c03911a80da03481c00d9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 771340521 1250 771339271 771339281
    0x1b090a14180d0509090408070203030c0a080702150304211206081513020a09050a1d1605010810060e0307091506030e06071b051510030b0f16050c0f010f 67
    0x8071100d104040d01c0048043c454015503400101c02000000c550719207413915800764000003410f0342e050104119403207041c00b0400c42005a1881000e9a0b82c959026004018014404100c0501881c10070400c0000080c1010405003441c9208032080302c000501c0e000407140030203907080402c1c50030300d0128080341c1c0910019084e800d12601d203000048650b100c13010700e40e840035141c1340250069241d040901c80d02186400959200b40c5400340001d1826951022400c010080f102000742c0380c101c1d001c1160a0781d4407441c2140500020f00f0440298240019400b6041e0f9041c4190010000700b804030420707030794041c00904000c0c803040c0030502019280c8440b05000d0600c622602020030701d0712113100e019510206100d44119099100c500d22900324802c03290984092040c1100c06000d611030031b010185440c04800c0c0144052504001000d0561408a0340c0440180038503510038014130810004026021114a549a0078a0640d0f1500703035100169240c000e1201012699500b03055449900c04929408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 771341771 1250 771340521 771340561
    0xb0a090e0606040207030903143903011b0f14040b1309180f11030d020f280201050c0a0605010b0307031a0307210f231b090a14 56
    0x1a51502d44400080200300d1203241001000f03d9007801d400c1020030100102c05003007a80c02d0003600e000344500034000768400302c0c016401844c20300e44080c010031180401e5120f07000d280b054000300103103441d60b076030f482000c1d051004140c1000188100c101c10584203801c0e40342049081c3c0c0003d610717252a0024602c49400680d01008030440311800020071022900442140010100c003044040c10300303454410400303000a4041e601c0311040c0480c5045a14100b28002c0900d0340b5a01030102504044009400d00070419801100000c3c2001010460030021607140c0c5030703d0782400c02ca66034070710801c0b24504104068a0240031546451b00014103150b68000031442a00740759001c02c0b00101c0d0a1404680156400b120340c1c040d4040d81c0103001d1110540d4041512201b960500d074480c81681c0c2c0e445102c00100d41c411100d0780e6520800c0026020040d420548180da00c10191000103400c03904124480c00041100e0720902c00d0380702080000034954402400315000ca803104d405032401070342c1403403040d440c03c0c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 771343021 1250 771341771 771341773
    0x4020c06190507140a0e060c030a032405031c030b030d03050103121d0d14030c1f14160306091a190609090b120a20040216020402030a0b0a090e 63
    0x81c0380c2e288a0300e0700c82031130303100a038a09041c5a802e0078200c07039104114211070381010b0100840000c4407010000360032030b549142e5010400070341d200c0480d6400c014565408801c510038000c10701141c1d0340424162061a8510340501050307003191400ca0107049c50000564240c010203070303c9020079500d5088141603030f000310085050724000d003d0840320030050310808841a130f1007801020a074513000e952000c0082c02800c1ca1100ca4514a03900b5003194815030b841c4c1003561258554002d42003c82e0b1803844039441c6480704016640800881c0d9180203c010304e046010000e101c11140f10602a6009034098071003100200000d2254541d4000f1a010504140d031003040043c3e0100303040200440300c01300b0f8a10310303620750700f01516000c1240701901010402c954018040040481d51460810203c51a1030250030500d0041c148031305401500112010300a02481c01085104400b484a2501c0c00f00b20fa0705840042c0e0341d98804401c040200011084180d00c0b850400002800030a00d8122150004c8450 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 771344271 1250 771343021 771343031
    0x5180414131106090a150212030129040602030f03042d0b060904230f030a020703120c050a02010c050a0b071e020609191502040605071401051e0604020c0619 69
    0x20445075006403000c4175406900001d080c00070742d00040e241140800385004545024a24409503607058100b60070a017001c414500140d060600c101c24852041010340302003500cad007810850020340b40e204096040742159400004030b4200a00c0c400040444a810242d800c0800000d106603d0300f42d8060700242c0312251007074081004c0d45040d000c5c0c540219401243c103c000340c40c0d942c2c0c0141d150103243d901c625074040d81d080010070f01801d00081003941055800307403160790305601d0201c2400a007110402c080080d000c100c0b0000910014104a485809017040841003550f454914035050341540e0003408041c1d89410b0124040d00001c40042881a0b800090f030712400100d03040b030b52010111000d20441d440740110304101c2505030428110381d4020110780300a11404070f070b1801640d00c0755001400290000605000b0b12612043c01e14207031a1a4000f44000c0c21721013440911641d6a448054031410014081810303950746a0454410a0048065600615054040340c0c02403040400d0403075058245 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 771345521 1250 771344271 771344303
    0x2d0f01020403061424030111030a0603140f0607030f09060e0a150b0d020607030314040b0f01060f1e030605030d0302030a1103040b04030f030b06030a020a020d0504060518041413 78
    0x5400910321171004050311070300464800d0080c0c6600d500d071041081d0035542c0c541e65085c41c00c0e031810085220303082c0b2820104209107180303130034240035852040321002600a203150005407100030030f20940020591a010980703071036400548000f403d0354240184210f19140c1c0c903800d880804a402c24110780100281c40c040104a00f44900352026400d1056011048103071580051030f001029158440c000d140008910131201d807590848642030710f00381e490f079649804000400328041e0400f0b0140502e03140965071569840b00c0a081203501000d44040c0c1c3d14021140d01000e803195102d4001886c006088070740d0740dc031107540900294426242052100d0a1890100c8801d12110480707000d01e92008140140342d9036624201c1d64a041d80142030101a1100540c5c0200e0399494003030340c054031a4030001030340c645241d40f0280c6006645000c4505022041c4420007110f500101501e00c0c1405200540d10202184000200201051107005820050071010f12103084404201603074420711551910401c030502d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 771346771 1250 771345521 771345551
    0x607030504021f03140c09030304090203040627060e0d1704150f0204090b04050105030703240903050c19030e060c0c0a0303020c0909071a09061c0b041503052d0f0102040306 76
    0x504203c00303415509c1000308108000c4030740d006643c07050280360006004c8510410740740d075103654117006c0210000300c1401d21007448014461004051480401820b00000001e009084646075840904122844900040600c814141785281440c107801c2e00b000000c861414190094115001e0390b042e0303c0c50003003400c0c6642814800c140c10b98400400820b580c5185558070507154042c00d0098143c400c00d107405810200c01401445006846070300c2d059114841d4660052908010509908810304400c42c42c8000ca6000030000418a0040c0d48950f030702d003207410002d8a040c80c1100e4140c5c106281e610300005241e80480c200e00504011224600b15880c0d4146140c0c0d51001401030140c007001200a009510360b00b00010a50550040d20380c0d0309141c7d44810348072000500494103604140c032502002d0345490b03d40b0503420008a810480c5d500c0c03a003107031600380e6194043c03a0385d034092080140c410710106041c0e80c03442140e080b105044034030090700d9a08131800307900b191008944140c02d04441d00f1800034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 771348021 1250 771346771 771346777
    0xc09050603011809030504030f050a060b030c0906060a03020717030402010818100903170f0a0e0f06270d02010e0c0d050d03050709181407050c0607030504021f03140c 73
    0x108044190318142d4084100f88000c14400d07030201c0070302508200000c00984603540c1070b02164040e20213000320340078a091503001d1b10980342c44180700b508455500540e0350380c1d001e00c058000600b0303540c03552600c01d0710324207800a01c902c00000c0e114101803501c0c02170104401000314403540c0f0030790780d402094451640d0106403a80d6142c2141c859080002c120803c07160300e90107091001c3c003a286c08941d41f5200c590700e81d0078240903101005254240d10421196982901038403040820b000f00401c101046840007546907440078000c0c0e800ea17604203003844039007135800012042c08515001601d0503000b00e42000ba000302100100c516880c05000ca02d0300192070140d540b9210260020050060200000b008400401008018406110389444086180b10403092000d1082d0b04d87d040005244851030800006042c0c010100020444204009401040d01184c40c54008105c0e0a02162940755840000c4c03490514030200c881c0100542103803450680d1640010a01c40b010008030181030710340d0701135152944 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 771349271 1250 771348021 771348029
    0x1111b100314070509010504031707051b0a0509040203030f0c030703030b01020a1211010635060106090b1308010f0212060a05030d14130b31030201111f0c0905060301 73
    0x582502c0025003254080c40044c0b212150500d0716518158590751100d10810140742c0c90000d800303011414104020080202c00d072607240300310f940c074580991003001070400746043c002c2c140214800f0010500315201001612442113400c207105858800c070301400350307887e084031100350006400c11241d44000d50011400c845038a811140c00120b80800d00340640380411410070710035540d0f51b201b9000541114005002c1ca0040c4400c00c828559205569407180100034a40140c0c0150450750042000c1500800184100c4070104003054070b84e40000f03008160704c130381648180d04a500b883e2403030001c450b2070b500a1600004d0f1821001d25620b0b680c042c484115080e010b4190181d0002100083d61409248441c0504102000c0942b8201060002c02118000c03944243e1494038040b482d40442040c0104008204158060820714100001030b01e014007851480040d0511864000070010741c581400702100c80d40d040b515a06035031140d0000200142600c091400020790450030110b41d42c0f50480c1241d040f0b0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 771350521 1250 771349271 771349301
    0xc030d0213090212010509180a05030a14131e030b01030b0f070c050a060f11040e0108010b010503090705090606041d0411061612021501060207080105280b01111b1003 73
    0x2030b0301b440c0502003034aa01500c882e000031040d80711540c80c40340800111400c10703c100083d50711412100005040d204110b20000d071039140030700c40129081135440c00e01c000c1301c0f14014018100740c041c085c8113100252981014104c1c51405001009100c40d00701d04a00680d070102c0c0314800d91380d480c3c0b000c80b1040f2280100a295410014095010400c140c005401403480c05d240054059800c001188040e48242e00c0440712520060041080b24004c2c4941c2d6100e10702828140d2035440e1074102a601da03002801071504c207a4441010881c162111820745001c2c0010090030a04070710040c0640c062600100c80032118010070070316586440c01e150701550505140e13440c6182004001d641c0302020304a8200c1c070101144200841c0f10030030001c001c1082e0003070002d6005400d1003410b01c4203ca0940300c3c01451000a03035400107200c00000c0b02c0b40d034082010360051000041c44014540100c820a070103010340406031040c0080700442c1180340d11a40c1000100300e8074030964125501381a001c6e16000c42c040400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 771351771 1250 771350521 771350557
    0x211911100603050c09150423090a0503160c050a031103010606030204060912060b0423060a060c14070f081015141c0b0f0f0609010b0307140c030d02130902 68
    0x350805c0403919802104411b039501145540c200894203d41c0302d40c817040c064003a2031901149081d900c1c0d1140341c02810381d90207007080701c9054440a50700d1007140c1c2c600da80041c00400d96800d00c20404c000101505008213220f50f410364a040098002d00102d0f180c81c4654640900015254041d00c00c45046030040d407070301c0d08070134034003004e03103946c081124026a100b649400144c0304d542e50714421580c2c2485265400040c05800d007607400c00d0b00307100524030740c0100843c201c10b001ca90b400c0008680303c581d00100f220410101005000d08042c2150301440c50200001408900003c0102d43d40710612000081040001a4140c44c8403440340c030f504c106a16811603200008660030604640380c1440c1c0c128210006901c000d5030340c0f9851007812104003230442445c50034060f4801080804c940c010700200c401465a5050941415080c840540740c0300510104075010200b000100303050b583e03543da4a074262900e6500d1511000c02950000103032610011194001007101210792082d110700c0e8001c0380c150382c3c1d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 771353021 1250 771351771 771351793
    0x14070e070e0303040b120405120715020a170108030315010918110f03040803071b03020c010e03120315030c10020303070305130506070c1502040821191110060305 71
    0x994150614201e58040c0030801000c1034040c0801c00900514402842c010551725050414a0408810007803c0220300e10801c5210003207074455a0190240c421100c00680d680085081a0307450104641e00c0c0d0b850f441c1241c0002098032020025501c0b8101455000c0b61211402e80119900031031782c006c80780403400c4000e41941e040001d42c0f01001380c1d80041c5a0300c5c82c0c81c01482c801c0da0103810480d01221003139400010461000ea0140c83c506920780840d01c0710404441035500079444200508049041110100c0d06c810b16942c204231035130108030084019036585c00c200801c12510130319540b00354000c3c46031000c04010350420311016811041250302035801d5840e01c00d0110040c01c0c0282000c24510042c03464040802c1081c42114000d650300e031134056130403881d0704d00390544814001c409564036105000070081804040f0742c40005512a0f01d641040308101c60821200740aa40b01d00d010802141c58281116038108200001c41030490044030250003440341440140c6071640070041080e00326120f00c503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 771354271 1250 771353021 771353027
    0xc02030601030f1e080403050d05071a0406020906070507081209010207140a050a0e0a0605120d0c14061608061f050a02012009040e030a080103021e0306070c14070e07 73
    0x140c5451050b452080c201203044c19140e030700701002c041602c141c540002c0070410032030200120b0030403150a0516904101c01511508080070900060b6011901c400000a04200240c0d048603003036030b001403102d42c8818843c1086680c4459500031402e040c0716418a40e990001070788280c4614510590040005608080b07a903410341d6020703c06642c021f19520001300ea40e5540321802c001400001c0310001103450031400c0602a10034540c09103006100130048400c0400c0041000c03a450a09403c141e0786620701c614010006003440c902c02c241c680039400501c118050003441c0340c2003c0403a0344d511030044c4c03120410842e0310100d050b04410400444140c41c00424090006030625444500000901d0059034071182200c040c0c031100060300440c0082c1b1404545814419600414180d40085040c8045a00098440c4906010282c4078030342c40d44039050040130702d10803081a80380c09801d0303400508205402900c6580c05400495007952450001d072140080021a00c0458003407148050340c54032404400e03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 771355521 1250 771354271 771354293
    0x30b06060c070b031e130302030a05071106030f180613021e04090302010c0f0c171309060308041706150105030c070503041509051504090b0406081f0b010c0203060103 73
    0xc0507140150000051902c0f40706003c0c601c1000d00b00c051346907a44210801540d041e100030718034040809541130181c08a80d000068176081c1c0d01508004e60b440c211410502282c40407149000d5110000008004905a8180480340a584442c0d06400c002d2091011252184021502000f1100e8294560307000361400c1000c11281030302442089007109447d8010078151240303201c1c180c1c0940c0d151200892003d030300000c81c032410707425440c00c1c020080d02c0d5078404180c280a00915860340c4c0b0302107050500400c6c09280c02000f010b01c00020082e1a649150000725038001d446a1640a00300b80d1800038441d030049040d901c070300100101d418100f00007000650700c07504080d12840c40c00c0002d000410000314100000c00c00b07003041107200c0b620800b01c0d040c010084000c3c0c0c0c0000d03000e00c035160301039030445144030141c1e0151096a4000f04204001d1b80100e002003c696202001d140b003410072860100b0b03002500f05031926083c00e814071506482e200107640c11122103800a4041c0e20400c010804900d8000364 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 771356771 1250 771355521 771355537
    0x70c200609030f0609160302010914060c15040210030501030b060405180106120506100b031305031306031d010c021203130c06020f0f0c06030c0a2a02030115030b0606 73
    0x4260a01c0c1d2a040402c0c40c200c034003c0911400da00c00c0c0140820044100300710f2986c009410300007a4028103640c0020142683c030302c10180054141a6140d416542e9401520b045008403022115142e402c0224840c050301c0554059000d0041c25140c5140300e4481c2c0112416260031854041c00340d00c0e000c09000040600a2071a041100a5440e044d4030f1002801803000030302c840e4220baa005441070a240707050100240c01c00c812540030340e00070440c085049041e80d40c005000c2841031a0b122080c10f14a040d440752416040d200300132100d010848a4241e40826000000c100046403000301040340b030380c00c07207100a400e800580d00c8841c5418071849904019a4407084c2480d003034000c1200c9a03208103e14003d40c0241c800f50700143c04000d0700b48401c101040d001c2030817100409219111801240d494800501458000d10001841008071030003441c480c0c10f0408050080324031741100400c001804452200224400d5003001c00044070705118020716000d607604041c101c01583c80340c004205140d403041c12 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 771358021 1250 771356771 771356779
    0xd0f050a0c0807090f05090c011115040312050a0e25080d050913050115050702062106040609051b0313051504060c0c0c030602030a0216110306070c20 66
    0x114500018032401d100d20007000d80724024210325041144d07078030550b0540c0c4081d0044905d00420464080400100c000280c0420308028100140c2440341c0c40c00e10703404101c1c1020b00710058080c00200b40e44103031074113525030204d0b200300419100e0304c002100341c1d42d00c1408203c20741d0041c0030218001200b6690b1480702642c040760008010b50361100903040c1000641c910b00414004698061039091801030300b4034030212a00100000d42c10020f40311106c00098042c6000c0100c007203481c40841d1a02c800700d442d080085c050f050412480307119041443c6000315131081c082c45c2040c50018100300036000d01d40c060103035051085007201440e0707001307196904000c01000b2043d4044408001042e418030007244141230b1080800703c00d01e0b00e41020000c1e40c0141c96000100002c100342680814891804032040d40d52021002d6a2901d4142c1c0b44c40103030040035075128582c2030043c0420f04003c2c1c0d01d4440d000201069050300c16941e698901569007276002140a040503a50b0146201c41e02c911740c000000c4000020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 771359271 1250 771358021 771358033
    0x6091e01180618050a0b01180b0f070203100e0d0306063603121d010203030609040c0801060f090f0203160516081b0c040b0f0d061404050604030f0804020d0f05 70
    0x845410707002403c190014207015a50307018800e004030301c1c1c06540c56408087c20320440140e038610610741c00b038215128000503440041250002e02c1c0ca4001125011500141210000300f81d44d64210002d103a090001c1205120301040c0e500340d20b000e4040e0b80201e03281c0e40c9426200c90f0510301d000c00b600010808008180b00b0f00c00c0400c65400440c1c904001850080804004604032054054a2510f454400300c4041001320b03800c1ca03481e81d00008817070f40001c0946420328142ca4514103400c0f0040c00e0703003012001d13508150b40401c0c40c0301960321240442c0c13442e800500c4144d12a482d840201c1c8030503100b20548040302c803180c521460050005081e141c02c4030100e844850441e8035100c11320340120900c1100c0e690000e04080355003004106c07185d500d0343c08440800500314114006010000e41059090203201e10745c2604003801090b0b800114182141030f8504010301d0640f4205031121012a13041b80402e14480302c0840c480e1182c0d0030248159030161510040624940740e069103141d2400b000c841c148100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 771360521 1250 771359271 771359279
    0x50a05060f15041a221401051201050103020706091e03020c0603010e1303022505012705190e0103050102030601080f0c030106031e060b1b01090b16050403080a020606091e011806 78
    0x4c0b083e0580b498175040300e2042518203015000e01c0066400d41c865040160078082d5040810988002904564007401c00582d52851454800701500d5891400b50003001e040e0200e002c811414503820b0f0249120741e0a40c1d0a0b400042d0800207603000070301801814800d400e002074456001d5040428110303000c1d004a96111201045020080200740c001c1043c20744040c804120030350b044a0312094603480f13224040b0161a05001c0c0200c040c025219061050910a40d40087c160b54442c28a01405510103134a030b0715a142e0078900c2c0030794019a4814001244480007891400444038440c3c02a032415401c45d2030f59283c00030490251207a071003040c2c05640c113034900c4001c03541e59108102c01484814452902c0301140322014440c01600c200351440c0380d04181c415000149101e071003603488540b00e120303658000081c035000c42e0b242c042c40d0001880600f0005074006075940009050f44181d10840b900070f0707160749440060440010f4541e00301840c0d1304881c0180801050748403840412040079100003001591 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 771361771 1250 771360521 771360547
    0x2318010207112e03020f070501060f17060405060103060b060d0c0207090e01200f0906031008070906060503070e03250f050d02030d05090d0204050a05060f15041a 71
    0x3069008680501d00c0620403070b07a6007401030301c0b03c0300811440b4046041c034410000c060f0101d001003410104265001904411a0603104241c035480d41e0000020410207480701c0e1189095202800342842d9400d1040c044030744640c00041040c0300315803283c003621860f445d580e5200701402c2100301d620780c005800d00a0240802d03c0b4854031504000d6a0300625400c3d1030804400120780c3c0c3c844040c1616410101001401d00c0d9008104034441da242d60240d03640d003480e0428042c503005464200d40c0c0720400000f4804041002d9040000340c2d1000c8003601c0310300360ba4090f100c0031500c0034820b04020800900002d03a0081c000e0301c2c95510001d01906460306c0701c81a005c085038400000f0345299820303407903000901101260b21004d40152409032a01d00070500c0603000030780e558280082c0c000410000188a20b46070301c41180703109016601030418030440c10007900c0b80000c1c1c0f0b011902e06018007015045901c003850660f0181d0200341c10005510b251900744034000c0c4468662108960038030408100b400f0500d24 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 771363021 1250 771361771 771361777
    0x90c060d05220f020f030d020c0f12030c0708250e090a050d02030c0708120430060905061003080306150c0f0d02160617090a0f030e040b0423180102 65
    0x11082c25495650b000a20401040c0c0129080e000e021f43d01c00380c6402ca01c0c980001d030695083c0c500319460313091107403100300140309041399104240441c003022442c0c03180110300003001419100187e098802c0d48880c60081020744012030109550441c00780c0b8104800380183c0000f64002802c030b8151000c001198494601c0c3c601d1147d0400c0041e40b00049a8405627810f024030405051064013034110701405040042c200e010304e00488003403030b55503039020013040c446180c02445d460001000c40c0c0400d2060400320020290800141c45030b0244c680040d00114102d201e440550f94081e0b4103d0458880b0b0092240c0349001c00b56903088800e0401c1040482801040364124190601d401043c1c5c4000b81c0c5802810300f0b4410500c58410340c060135061094a800400003c944014607075806503a42c0d0b000307512441c144900c071018103d81e1251001d00c0901d80e000300c190100440c191828004440d5450030303c421551300c841c05403451154411200e590a15140d8959080700d0401e03515454920b4400d200d6089034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 771364271 1250 771363021 771363023
    0xb0a0207260d0e030c0c040b06161110022116020d081e031510091d0106030606110a02040504050307020a0b07030e010c0506060108190207060f05090c060d0522 70
    0x4607032003082c00d0450042000c43d840d001d02440c280042e6280d8a82c1e100309400c10f044c0b0076500ca12441e01c03151078890981d1720f0494848100c6125a0042c00d110320380c0e284c0c4801e550302680c95103d940081500004050007003809080440c01030301c140d8540c10b0125000041001d2440c13003909450800350361407040750201c5902461960742d81c0c01c0c0e0745803030883c18101c0150720032011206100700566a000c1c03403400c04000b8402da6507081040901c0304106d80c1254241c00121000c45811550b88074078801604c444d06842841c0c5080203420345560064400d90303100401e0001552040c0003210041c202a04180d4220744140d0440c1d0a0095590000e44a100103070409401103c000c00c0060a06a1009005007807030400e007090b4140e4a100d44403d41c48010061465041c400450b010420a6445107400390003641920350440d19a903c501d000c0c405000c0c41c00c5403803d03150416000c1981c0c004081824100008010541440c0c00100c02800000c0d060007459109070a41e0f501c5000072007a2a84c041610203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 771365521 1250 771364271 771364343
    0x5041a0907091d0c030a120c050705120c0a1406070201140c01020313120f050412020109030b0a090b0603070b03070f02031905070b0f01051c06091b210b0a0207 70
    0x20f80b01c02002140740c0340c101000f041c844d80c03024028201250164495170a0705039986880f400041503414103615154190740400e030804111403035040908804240400741400031100c01d40c480c0d960781104400b0403c4600001e074404800c214085c0158040d4509441007002020054140122a074074142240c0084510f1002d01d19420120400c001284480c49070000440c245040480e070f00040c01071003405280100d450748100d0054103002d5a0041c0d00d43d900440d07008a108085180c1001284050001400c08641b1250314601282d120310300800da031010b664520f002d1500b561341d82c0d10106c4115094030382001c01d42c0001c1007416445641c01c02685262005a224a55104030501c0c11480303101008001440e03010b5007a005114695646408411000c0d60389240421352141341804001402c141c40001e094481d006584c984401014040720101e5015000c0d0700f15980c103d0f511096004804ea00c010030f08064a000140c4440c01e40e406071440f14000c601c0e907804005840074280980101c11080440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 771366771 1250 771365521 771365561
    0x30b0d02090f0912160303020a03150609080c0117060108060a0810060f05091303081e040b06031207081603120c2001060e0406020a0c02030a0303050411010305041a090709 75
    0x5450400c0450361a01300380c16554900240ca0300e01d00e54000f040d00e0010100b54000983c5d4000c41d200307400c210240c12610300c5101d502c80d610b0201074030f680c0c4a44070759070700c9010340c01d81c400c02907000b0f444541c96110301403449030303041d6a804011903e04100410840d8070a00400d00802e5550042003101c900f080e0484000034041c1c1050790001440c012984064816602c0c0c00400c14490004480101c5c1c1c1a418102940d0310348035000d641100e601d410002000c2c0071401d0080000f807203842c592060041c10305400303640c0110f14904100041e880b9180000d003550800304079000c03071900c0c000c9c482c65040b4002d02c2c2c1303040c3d1010300c0d000c0b0505440040d9074800004008030040043c0284800e107005142448100801c18185000c000c1004540010006403180d64046000c010143c000e0a195401540c020240d60b0201002d10f4003400a1000381c4069031100701c1c1400e910b4081d4024440c0a00031a04100451545190628206200706c1c008081c0003050080c4000002c80c1700560103841e501182c0c000c00186 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 771368021 1250 771366771 771366781
    0xc031b0210050a1107030c200102030d0509071a0d05090a21090b030c03100f061202311419030b070315080a0b0c07030906050c0705100f12091101030b0d02090f 70
    0x288000080d18003c03240307007400231001480d030f0f000421183c000c810b03a1408076040d901d840c5110300740f610603841882941e0f0200118000038107048001c000042449200304003640707640780c80c0741e0360f4200448010302d13400e00e080150f40ca903030448500d50209030302854400503154585102010581064901100c2d000001c802d02055060b04c00256001c0d04071255550092480d040700280f043c41e43c444082182c543c009400c40a80719011150740801381c2c05c41c408650210122903242c4800d03558032a0203051b508848190441749000f501c281c440003001501d441525013181c5036030381c9041014022500b4190380e000c1030001c8480d00000c8000505140c40549031241070360914224181004109000c500d40c100500e070002070304642e420042d41c1c0940390841d198070314100c0051405029810199000c084c10b045121103581c821400407060303885640703031003000400d0010380c1c1c00c6e83c80c080c90082150500c1c00050744207503c01d40c4804400c01004180704d01e610905d4000c00c00404050703031828288004c6204200c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 771369271 1250 771368021 771368033
    0xd0605030109231b100c1a010f0b030423011503080d110c0d0318050709021c0b010905130209130504020117040c120204020c01020c010c031b0210050a1107030c 70
    0x500c40c92680005010b00d03130700b18030300c00b0003050001204030311844010301c010f140e1a102d0b19000d25601e521054040b0b034044100c108512280e030074444d0540942000318040740d84c0820340c003a20300556001500764103045169480b190081c8102040607019035807009085001184400d04100441c014501c840e66074140c03410764410f135070310942010742020b810000102d00ea40002010103264043c0e00d000140703841010b003040307040e030b4070b100c0060000d208188010039403e00a078010016000310885030f00712a44990031500640c5c850341122404200161070800650801805003095101100c0d4014581b0002000160b194541100c00340b0440341d40c0c008210031941c00140d10a0f040f814143c0c0743d0800c0c6843ea455903441106800f6203650103101c183d20300d0071912180c06580d41d0030174960007903403240b00c9240040d000700190704000c4e00203410032040303000014203608407862120080d8064410100440c01e02406000d02600c2440260340e280d0a00e0420300d2810040e0184902c00c2d51101e00c2c050041c00d00e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 771370521 1250 771369271 771369323
    0x909250f0f0311030c0c07122d030807140c0313140108010302240f04062d091406040f0608010603060905010f060e0a0305010501080a20010203040302060d0605030109 73
    0x1c8003031518200400800030011801e59501200b03610032150b40f11311891010303041c90215804074004544051104c0d0030410340c140c1d148544200046a00826007008000f0390311100d440c40c010b8040b8a08074003013400b0622038143d1f10032042c010f094091800d100b03200e0b460318613800b00e504481c0032500c1100034003040c1d0708004504801102440c1104841d415600020510080712014465240c0c0c40d683c10a02c0014250940e4110350130030a50726100c40d62584090f04000310200118100b140101c10808d10340008413114903802034035038a2003102c070704120702c0c4540c2c6403007a215550b00c42410f0000140010610040380060403265440701115494040701400f0350b02c281e0072411003641094018880c910071901044112000c5160901441c40e403803010071040d20003600090899400d1200204901038001035000c1c21910480498402c0e10311000c1074528a015071f100d19006802c10031041001d8a4440d001c0d107040e507101c1200203485640d0368002070031036407062000c84080070041e6071600030418000032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 771371771 1250 771370521 771370547
    0xc050f030405150309120433020607140f07060b030f03070f020d03120504140c0109080a080c160806061f0921020303070b2502030909250f 61
    0x9505090420b000100e20182603004900c06640100004403c03607801c004141d000c07060380002ea40d59640f615030740510742e803041c046080340b000b000c1c84001d8025413440f0b50304502d802590260138140c54240041b00c8030025100320b20032144041c4800c0d90b8184d116001090000c2c03180750000b0381e10495000f07240c2004031017615404150000e0044070080381c00610b150b844254111040c1080312a1460142e40c1b0000c507100c40d801305c51518040100704214517030031503a411002811281d00e00424001150182110f00a42003180c10514110300050355010141419503003c100751801c0e034841854003882480f4960001c00540c0c450403e0040509185003047d20394034000c1550762080d40380e0200502400820300ca406c0b4420041294880700300070210281c8086a402401c0c2c0e035031456142414541840b064400041c241004098295000055172000480311440d4000d075040907220010800c840ea402441110701d80c480e414180d284118079401689443c3d900e0320750901ea10481c810003030042c071055203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 771373021 1250 771371771 771371773
    0x13030201051b030c0a0507060f0603020307120510050a1d0c0a09091e02040609020d02090a0e040203070612022505070f0506160503160b0a050a0513030521070c050f 72
    0xc0040b0960300c0b041140e07070203e5810b039010f5556540b044112440d220300c14010b443c03140b800704440290940f54001e441102d00071002c8074651500c07049034080c200001607009203a548500420400401d00b9001030303a0115000341d000440c01c0c5003821404c07403c8441800c00141d60403144140d0b03174502d0035001120140140c0c0c0c0c010006401166100055603410113104240b034411480042c0455071a40c00c40ca0107407044032400e544551078040102c010703410550419116a0601c0c0d80484c0d40480c0340d525522443c0c009000300780c0c40d454410141c50441d40703880d44070400c580801001c00d0b0201891007a000c00a51000e0003102203a540c109942031070102c1d084440c1c00c070f419810811055640105949080f2401c440e94044a092840e1807841c6105010305501c1b5050080840814042c201c42014072400001d881807010f551100851412070710120f40074046110078610340000f12340b14070b0103044440b20780ca207a07011004a011070040e800340d04031138060008860f0900c04c02003020511101c210864050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 771374271 1250 771373021 771373051
    0x10501061d040504050703240b0d2f1504061808061603020c01060b041509030305030a0b030f0708030d1503080405060a12060b1e030f0408031e1303020105 68
    0x14007881c09000d110000c1031040d42c80d0307804030b4180601070102c03a00541e804400034440e19280000308080c05100c219070110f00d0b10340450040c00b42024140c695640d40c2c000f0f550901e0203016604244804480c2941510310042500f41100684800f10755110303240340030880d140c80d02e01e00080100340b10701503100c00e0b098408000c420041f60200085154001000c4580d03544070394080314003207000340280c1c50202c0280d800e0900c0065942f00601c028001d076090741c05520104502c800054556650038070006001440400000714108030680c401098685d004041d10360b20121099803030700d03200c080d8010074030720303040002d0050b844103a91103007035200080600c202d00711b146981c48a0226001c0c80c030444e8011500081e04001c40c5105100000341d24100d0f01c41000040c2d22161800d0700b6400600b400d00700e004850b800c0e015801004070980b03219501c4a012807010340d6444c0e842d4092500040e000807000305000c00a5042c154001490520034000300f80a5401d903041c0742030003402e5900c09044445108000c2e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 771375521 1250 771374271 771374297
    0xc06060a0621020a0302070602070c06080705122a1201170c130b06090a060801180209061b03090a030303090b06300a080c0a150b1804020f1207060201050106 69
    0x140905895034002c000c0103803502800101076010b0f201d41c01000b058140300003100000c000c9400c6826054075100ea4851200d55501074091320144102102000807121950000e80c0c2040342078242d00300310005000c440f44003c6640395101144c2c2045005103241800b42d001401901d403a00c0fa42d0301c29102d20303401440301d03014000100c6c450f030741c08403400100652500031003490f0b41c40b500304503551001c0142011403207035a20306000b0302c0807100380201103000d40340da606180e01030300c580203844243c1d4004103010701d0601d100064010b400f00e250749003121404107012905c2c203603171100740c8680103602a45001c41c1c88240d502c1d0250741020b00500d038921801020314000b04040300000b841c2051f40ea0100343c2408260f80e91445031a160703502d00b00602c8150001541840b0030001700b800401303d172054a8056082c02e02c0303550382083d40d02051103260000602d00a940040c0040201c01d5041400900f0501c042c3c84030038082000ca1003450390813412036000c1402000b220f582403040380e00600262404100400c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 771376771 1250 771375521 771375557
    0x71a062812020a15020303070e01021629220504020a051611040c0507110a0e070c1e0c030c08030f030103020d060b09071d010801050d0605070908030c06060a06 70
    0x1036802181c9415041c0a503010440d29242c03001c5015003401030703221404681c8818003d5603980304441c4040014400140000c05500005076011080610045046154284001030017105090444140c03a0100300c1440403c5400850080074500806070385c51100c00000b03510b00b01112483d40c811070050344104400880780c0e40c072000303482d402404002058801096410100131403c20400000c0e0f01030300d4480b000806a40000007440e0071440740900903141c485a00401c00b07016a00c1c411204005050360000c0e003503c1c1304440d4900e000384074406286944030005a0343c0c0c22103c0000085490050390003041c0240300c501c8031004020300b9601d00071031070300303505010040d420300040c03100900440d00c400c1200b04001c0c060304009494100641203d83c240341030b080040408019800740500400d15082d40d103010b52085007003d058a6010380030000402032540d0380c4008000082c07007070302008001680410448020700003482180c070454000c02c028200141008041507640d031004050181d807a031401c0701184 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 771378021 1250 771376771 771376849
    0x607081b1e1f09170d0c0806090906010e06030a0c03080a0216210f02060315040501050a0e0c0901020f060f0103120c020f0409061d010603050d080c030a050903071a06 73
    0x4070341c1202258088051801c0108413844626030254070001080b001c0344203180781c3c4a0b0400b96619910190355803611014040404016522444607402803801400b1402031502c5403030300300710058111000003a00740c6075000d0030398840e0012141ca001c00140c404e410303a070400503904a085110b1601ca441c501c2c005817200c0341031144902c0000c048800c42500c0500205001075100e854000d00359564910700008944800f42d8440c2059108500d07100021a843c10035110038800d07210075a2440d5030b641c482c0141403c0640001e040507045100300c80340100c20386070500001e80601044800a10305506518100503018003000c01d0318100003501c0b42c0e40d805a681c03050b84a515a1068030005600001401c000f00a40011201546900340000058040340760540c0444222800b0707606443c510091309004844860041e1a0000711950500100b600e102c940ea000a400c498a842183c0c5445840e580e542c0d186a442143c82210003190070810245040070054541e010301b00030b00c00030760344c1880208014011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 771379271 1250 771378021 771378073
    0x609110c0d0c050a17070507060816030f022b20070609030e060406121a06041719031e02061b090301060816030302120405030a020607081b1e 62
    0x45200b058400a00030144640d590603078006005982c512082090b0002039402588215050b00c10668001240703440750064070701a0140c5100c03d1044400c50740110040c1c8144504400441e9082199440340b02c81a07203424000c80c40121040c10400081c4501070449070b0070914021804c0901c007480300000964400c6400003544014001942c2e2a0f038141100c0c40030b014007182d504002c0002340400d1503504402221b807003a11004040c000d440035020340301010240c190360b0680101041c4002c0c03180903205400a1030081121040710042504100b20000614802c8410b401081d040908040d84c0110208000b003801081e0004290600b80040620380707440c01184c070300140e040f01048140542d0b9081d008203004250060031940409412085003040e210340d440300b01c01500c603034040030075407082e01d1003500c0c212030b4010040c0050380c1054003813180300d0f884a4801c6a80f00010011030440110b801c000b0b045080c09040145804540c0745030010002d60540031150083d800710211340c94882c200222000c0d03078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 771380521 1250 771379271 771379277
    0x3020108071710080f0304050307030f1506060e041134080c03030a0e280305071a0f070212031b0903070b030601081509070f050d06090609110c0d 64
    0x6698a100444803211401003402c42c031100c060620062248010f40c000075031302c1072426602d1180900000607070780d02c070314481c0380e030160000501080814007001c003a00e50140580384800c0c4042c00000b0071300850310280c00050100c3c404952003502810940718403640600e40c101e0325490302d0350061902c0c01d080040b0340c5d80c4003191000351401090700c03402000c030104298000e10705622500c2407100380e9102d400468606142c50310f05442c0228014000642080d05820501c840b46d002d1642c40418038ae50116841c01e509010b003c01200300080ca100d407000c00d506805c800a00641d0a1064043d444010054550811035101d10607c140594a04080701d0300150300e0220b07000005c0400811340058029115400d40c1400359900018019100000451007010f0982c0c451615907980d40c4c1042c402199034240f40d420603001400901c12a004041c05511081a801d240c1d08040c605441d24040d10300c590402d50306c1c5e6032210400c01c01280103002d205003403480704030103c0c24250214036070b41e910403c002c0c0100030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 771381771 1250 771380521 771380537
    0x1d01020a021e0d0311190c09050421050a1202040612150503010c020615010c08030a0b150d20122706011706130b01050d0312050a05060a0b040f030201 66
    0x614401002c01c510380c1d00107040402000e801e07003009409180c0120200300365008103201200d40300340340d02c5911130080d07004d1200c0585905100c0210014a00140100d0303284031500070aa030f482c0340322105450548601e0341d419030b94049c0f000d4000c0c0003280d80c2150740d1b800e5006110500285802c014040d1701001ca03604001288010400c3c118055920382c2e00480c0c05510b021406000c039a8041111407143c0307220003081c001f41c1650401103c00c462002d0010700612418004150181c14581141864200c002d00a41d5101c1e43e2030380d100144c1d440342d840403000360350fa03640120588007030066900d1482409083e85040600b41034940201100c002e00b810314080740301c030002d42c11100103540080380ca102a4102c503c40c0da103500080c010b00e040c407070340c4508a205000006407107800c0c0740031740040c0030b51100000d4516443d0409004800e07980d40400c90034031411400100110a00e88a50307031085080c0c90000c04d01c2c0c1005001d004150555420002c1c81d810300f000184410403960805030200c03076083c0703002c1d90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 771383021 1250 771381771 771381799
    0x40510050d050a09140c010509040b01021c080106110708030d0e030f03090304030c08010227150309060a110a050306010807031811010305060402070201021e01110a0f1d01020a02 78
    0x81901c548052150356034507280a12110740d04075440b0081c081d100312561101240200c40055807601c036000000e0010704108035107056828039400c460038042042c0121380704030b070064031072080310f02204800800080001004101d02c54ac0a5810ba0807030034070074042e20fa1982001a4a9280e1007030f014240724142c3c8840ca44040d9020410403a504400140c0a030750b140c1c1810303010f0b103803030381e12a00c02510300348103281010420820600c22210144003c000140c0207004840e85240410b005509807076010010070442c103a03507130030503008510807804c0d5000380c61249402209841110525548500b03268000e01c8400c09c2c2c141c0003003c49400c10002d00b003d060a9039641011000313840810300500e84125080000002c000c10b8003d41074586000742c03424003195440c4018003080b030040c42c10107401039011500a40d99111180441d40829042c1000400c01552500c072109050b4003041100000800c40c0c1d605116050780b1114201c000c81a1101c0e090b03c10a01ea00000c2d611360019002030b200e039855a41e081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 771384271 1250 771383021 771383027
    0x602120c070b030103060e070504140f04060b0301020a03021905030c03071107050d060c080601031104230603270d0f05221503050f070c080307091a03041202010e03040510 75
    0x250081581c840000d03640e60312071401b20060004489010340304e20400b04085142d02c5c0034080c03c80c00d0700c0c0c4405440e1440c4e80b0308001002d5000080c2003600c11550f641c2c901340346a14280000c1000030042d03240541e42e600d0030905c4032003003024941c03200200303c003e00a00034880b01100840b82c00020614000b55448141040c040c00c0461030381c001d6500a4020360200e04200c41500800041309450725040d8459492400540c19030301c05040724060b9480c1003006211900344a058455625a80c09800c0144e02e000408120301e0b502c191007488842041c441c030301c0b91000038604050f14103803000d00980440d520800c401f070412038101c4581c000b40800492a24692080c40010011a01d1802c283c0321030a5651483c01c540d200880442d20006800d28001a00416020911a0040042ba5559180d03c1c40c20349405002d0f4001802007010403016410000d0703100d81500713106000381a0741d001140c0d6803e15148c2950401c422075408400c0d64104109c2d00010315001c820744040740c0080c0d801203081d9641c40030403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 771385521 1250 771384271 771384283
    0x304030212031006030e07051c1509050a150c0f0e1309030806010210060f0b070f05060a0501060e0414060f180c0a0f021c030f1d0f0c04060602120c 65
    0x10441c0ea020210070000c503440820f078502c00726503058030100035010252000c9516060305010f5a60807080c066910b0000b040b6110342c550b1124042e018441269002c00c0886017a1900202d050324950f00c00e90245080c04034a80d00008082900981001169074040f4007421100c600d0a0380001d1041c1c85400381c01170349030307446421044150381d42e04004d83d401a00d4003801040c8140c42c550700500c031302e0071210096031b180c1c81128150b4041114103d190782c5070070141400b81c0c0c006c05081741e440398802c16410016034200306542c00746130300103000304196040c030310002c24072241d200503280b00d41d0500c0032742c04104003603550f04c40d08a5404d40d0100d08050300003000c035085000c01900494541200c500f0081c220801c00d014250060241e500ca0910381d41c0d00b00100d9a60396800c962125104115048010960080d4070921480b10103540101c0d40000a031030741e42c120f9140140040288d000790210350b0540d00e0178000c0c5800104121010412a4280a00250f42d04492900401500030000d40f1a003c24410810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 771386771 1250 771385521 771385543
    0x60f072c041814031e0c1608060730090501180605040b010512030d02070609060c0e01081b070f020f22140f06010c0606030503041403060c0901050f03040302 69
    0x144549032074492002c800860000301500e048685030b001c0c000c0c03240e000c070841c0c0e15000c5a41241810040d4503201d90440c0e40021034204040c812544a00c5e18403030302c1100400140001c401030b018030f15210b0030103800c4419501d00d0000c1200c1c442c0702c550207420000d108624108045038009031507403443c6422401061380440704500701d02c0c00e907840f604100c5a900b115124620400d00c0345c0d641d0741daa10920414003402d8440c014503400c24004e0040c0d540055000d0401c0c0d80c0038220102d602c003c03585604007180c1801e00d42c800003c038401c0e82c3c00d9407542c0004101d500a018605c480b2003800d42401d80744024003480e60020700100d00084a042995503141e40c10300207600c0241002c000c1424101c00a104801c40c0070303400001d501b0119034403849002225903901c201880e0407100d10a0b03544030011926030f40d000e0403c0710103550301d03800070001c120704001400117054403180c6003d065505108141c603100008003a101c06040801c80d0a00c0359034000181c4e005603403000d04241d200d440780c0c90164205944814 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 771388021 1250 771386771 771386779
    0x60203010801060303091d16181403160b0a03020a053f011203050a0c17090103061712030408070f08090f030105151504170f060f072c 59
    0x2002003a86441980400c085910030340754060001d0f82c9654075500f20384100c102c2e00b0485040c900040c3e007902000014510200245419101c01207114207020304240a0b41194420001010b00113059040401a800c00c0064075081c07154254507004403c2d00e07a00c5403000e454101500400c0d1500c200e40540d06440458034541c0c0c10441414007422041c60440d00c0904d2040c086260080040081c4204450f41d4160b92503002031a42000a82d181906d6a5114070004000c008800446c40301003142e0307142481c91002050151a174980050b03000505803142d5070400c48450006048207168040c00285900c00075810003442522a956410500030311302546c2005031840045030341460070402910300805201608440006070701030700b5000d140c2280d0701100d4031100e80c0345c090311241030707031400d079000070821207004461a10b000d03190000800c244070900306015407540409015200d4800911145600c8008600f90b44194545848010103400284801d041c3d40d01c400a410212903a613400391032200384000d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 771389271 1250 771388021 771388027
    0x1101090f030609050601060503090304030602070206160302060414160905070509030a05072306120c040807080a0204061a041a09091e1015030203060a0e0702150c070c150c0602 77
    0x20a2038000f6100c40241180c060140d41c002060342d81c01002030324040d4034000003c45c00c05086541c0c3c0d80096008140990b40400306210403090708020451000c6910300c81c1d070191100741024580425003000c0d12a02c540c01c1e0b0019110309101001c8030040350116041e04201056a40722050285c4051044a450329014055034034403c0511100007113410031a180c0707140070741500c0041d03050902120901801d655103c542040b43c4625284030842c1180c0100745040103d1030140e8406075549030016030350180b411500f00101030b00c294a41032183c10700410100e000d412002c041000c01102e548124054140c4000400d00c2c803501154072a42036490394076018012070384504002000f003010f54030320141042201107540009140200d1546450100c0b4040140d041d844140390a09034044d410090040ba0010b0119600084445000004030700511560300905a4800a034082c002d8001d4000d0004061040070080350300080c6881c2e0584040352810751942045040183c0c0481c2c089a100d20040c009038004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 771390521 1250 771389271 771389273
    0xd0503090d0c0c030c06181d0c0a0e090a06090b06070b01050607080f131701111b1009141006050906060d0f060f060f09121b080307120311070f1101090f03 68
    0x8260000031f2442920300703070601c1c00d6a5010200300c40d044112140e02c0030a242001c07900e916410310140c0900011420309900340c10842001c119010022a40580615250001004002103d20450900c0142a107885140c102107448036000f008040c8035080c050240061442d00380b200010039201d00060030040c00f5a51b550014018071382d0207650080201e00314942d840c5040008052041d02c480e0565400301e64144580340d8500d04008180c2212084c8074015a281d10030701d0010b078402c05021031300c2404410a00b03100c501e54030380341040d0700e0b5030113164900c1e081c014400e913900c2502480c0c6c400320031610385680f400301003518400b42c2126800c10322110b042c1034011071090302c1382c0d031310340b0640c0c6a60b6201c10207c54001e00c125183d1129200f80d419204158105001150708003480108039855103e05085c85a5581903892441c0d001440a4031080f010109409072186d060103a00500300c075044995080c101d164860040c05d00d03813964001c1c030b143c440703680801d1f40c1c2e405885100014400c1c4842030400a0b0b403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 771391771 1250 771390521 771390527
    0x103061a072406030b0106170105040c0221070b010e0403020a06020f04051011211c06050a0311090a0204240e0307030302011d06280212180d0503090d0c0c030c06 71
    0x3d20f000880d0303101a594004114244071b9150030010f044402d0300d0f01c60503440d2000744001030960030744030b00841c000e6410301c603079084002145410030188000400c0c1c1d00c611030308200d00c1d02c080603003214481c44408814480402e0b4001030165159820800c01660746800c4c8610803403d110365444507401600b44003085442503000140301c0550062401941c810404414404894000c44224019680780500c460034642c01c010310ba0190800204000181d0241c40d400003802040380c0b13a104461240d44980902050b0801588064002d8412042541480e0604240440c8084010070402844100603641d50400b842014010400d201c06015030740c440f6124207000703028000365950340d01c0140901042041804000459501c00e2400342585020303488000d10042120920144140b0340070340034001100c12888100d03009000d401c100410300e030f4052840c541c060a040c6468440000e1100510411881890116154060304d6451078056080041850f00780e070b40000d59040501030b442d10000104003560 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 771393021 1250 771391771 771391781
    0x31906051e01120c140f0c060f07140403020a140406051c060e0a0f020d030201150603020403020913020f061c0c050c06010e0907170a14010204050f0103061a0724 71
    0x4020b03616542004030500f5204162001e0350500070000c0c003e210300c0419040744801030b0954005510742c0c0c078a040140e00d21585824419184120038110700c0c0c0a212416401100c1140101818051203003818039580000b18011941e03c9100c404032444002801c943c2d40b036034040005480c0c0200b02910701d0360030300101e15101680c04030440703210b480c0000b0001941c0300001c0e00c07440725510400503032640000e5030a0007580c000218085081d9900c0708101d40f0111901600e400c041c04040d500185c9891540c01000480400038180203030081c40c2c4040040940c440505040706120165081d82d0b503503540e01910001c91140340010301b0f2071482c1c040700210107980035004121038041d810844060740d0f00d5410700d520b48802501e00c4100359010250030000c0e0b072446402d40c0210384d001070540d1079041136038580b0f18040c01d280c6000d000f0f99500060510442c41d0852809605600c02c2c41d0030055941000020041207071280c0c100009003001041010401100c444504c006422035a50108150181101d00001d01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 771394271 1250 771393021 771393079
    0x1030e010f150b12071b17070b0c03190c020337050c0a030c03030e061006021b010504140a0302120c0103140609150303040503070803042903190605 65
    0x2014040b000105907001c0d90075030300f11000d10b20840e002621070803019156a441e82040c0402c0b144062150340201d101040480c02c03000341865003d80d202e80d14a0032420303209004090052070354040c010b00c08180d52450340f034800c41103a000001003001c6440700030f07481c2d07020b0309140300d41001681003440c1c14002038020362040203031106103a0000000c8040300340c465001c1c40c45070342840d42c040b482c0c03840401d00c242540c11f429402810300284030520002402d0415404581d21248041021000c202c1154100704000410300420342010486040700c00080891241c2e102c0c03a1400422000b0720415503072040c281100466006155010402d852940b55460b0000d41c000140860b203000301c40e01c03441c0b80414141e0320600c2c0042c816000e5603100c11081c03410014900030f00303030588414440420b59803020071401001d002040010340c0c4452400d400300c84070707164031300311222034100c95680640e600384950145d0390030518166005c10041c559000352801460113038055548041c201403075580c00100c0070f403042104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 771395521 1250 771394271 771394301
    0x8190c031e06030302030f0d02040b07030f08070212040302010818010207050a110a0b1c0f020a02101d060f130503040905010e070c020603060d050a023006010e0f0601030e010f 77
    0x1901c800c800358088a00760b11001d40982c10410070745407850041d000500d50a00746450050400c0d40703510703081c0e0301c1e80c01c8444110041024007001402c05500040032036400b207041d10040100140c016003032a21401103110003418840c1c042e0100d0540c01c0c2c0101440f1408403004000c544a01c1e490400c1a5591040301c1d0a0380c0ca5802503061440302d043c081003500039101d000d80320b1440c1003c580802500303d010704100f03100e00d81d80e070800820240d085000420b241407030341d0b000742044005156000125940c00c0000713103a41c841010910020107001c1800c0e03a120b0071540d10700c00f9940c0c030f0a401d00480c04007100000c0c10750000240100701c00059500c207a041c0c072040c00c2c1c02d0700c0d50360360480c050392207090344a80a5800740c01840042e81d180344c0000c80580441c442c2c0d06440e2104029030100e0a425070301030401c05d0103003a401819902c00d14881c1e40c0030300c1d18413590041c038465245ca881c90680c144081c00d00c029104181c0001000d6902a801c421500405000208042e010207139040e0011300904040700c0b02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 771396771 1250 771395521 771395561
    0x151606090f1511040b09010e0d0b221101050c0a0f06140c090a0314160801021b24180a0302010b010306080321041b0803092d0108190c03 60
    0x120401c1442800f80d030303c1c860310541340380c00c0c20320441024681002400c941046041500380140b61a094400f411062249100c40c200d8140403594404907a6206070030300d02400e240036083c02240a803100c00480c000c080c20140d5503186441c00040c03c101c03c28402038803604c4147d04400030000c46500400c4081c5113070100c943d20740c88184031a05075104101505520000410781807011802007000401c41d030810703000300c41c0d01d510804100342c1102200d40c030070111030f540450482e083c0e1011415802c8007111400c05458600000208150005054050f1019500c1d82100140c04000041c608240c08070802d82121852800c45c13070b00a020b8650b007003040e4002801d00500084003980041941c00b000d403038000203500209140380422078001c0051003030b64001d140c4480c0410f90410030324403c010300405006999a032a41c4414405061505008415001d040d0b1901c07030303030042c80c50403100c120142c00d01e0304804945503812014505003005441d0041c20380f0b4007001c41c11507501940034644c0c0e141c010000141e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 771398021 1250 771396771 771396803
    0x903030906010905070c06050a0f1505151218030d051501030e0f03070605060f040e0706140f07081e16030207080303071e03091502040501081005151606090f 69
    0x35604240c908801140e80d51b031544002a01c075812040c0e02420303001000400c0d00000d1805030588034941d5417114102c1440d042800a03080c4500d5101d2441c00c290449403420029814200d40d84030020020ba6034500070606000b40b0342002c2c000c44481501c07e00c0c0a00203807c140350280c000341c02100099010030300e0085800d010a001040c04103041000202450410640362204406420f00800d15544000420f08d401c0c0581d50310720a04005d0300002c4002d1000b207041c140050700600140500325613848080c0240446030114070b04480a46500032042030b2240050103481010f15003807481c0b00728103200400d21a1602e08252100d018250195080362207461b40c404c68103840c0c1c401981c2e00000152150302c081580095410010502c040074a8001101c1540e9103411041621030031010340741680009003002150390103111990010304010700003007542e150400107040401e02440c241c00e40103011400240040b4032403040388415401c102c05111120756882c1a05d289820b18501f00da1007010021002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 771399271 1250 771398021 771398039
    0x903081b010c0201090b07300204151d041e0e061b0c0601030209060a15050a0e031911010302040b16060c090f0b0721020d09120c0b030915090303090601 67
    0x2203000342c1003021306c00a40c036882c0c02240c640302e02802c2a10715401801d102025080b5080202c0102907404030010388903400d09040024411081480e0010003d2480fa182400302c942110030412140464000900c4003c01c00901c05480d8041c000c03e54041c41d0000546c40403a000c0b0b149803060132680c404100f1252152130009850080c1804a03005a01540050005041400245030400c2004040c13410561343c071440c003c5070120380c69018001402c0480e01c00da1240d0460a6900c1590f000c4005d00040d42d10f00e61182c10b00c04c003c05015060a41a500405159000e64121f40203002401202039480f01c0384100749840041140d0103c40d03240c40c1031034011050744280d14030010b5401c2ca820200070700e0300d005121465a00304590649085841010320f0281480002c03680c1540308068020740313501c4800c640d018088042507446601110b915a080d900040c052090200075100d203800041e0710ba403030342d803586845c041ca00b0750310b45d103810500d005100355880c0c0000594400d0070354070112800f680c1c8816440b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 771400521 1250 771399271 771399281
    0xb130c080c12011a04030212030a0806010f2705060705150106030e10050a1103150109091e1104080a0b2e030b090c030d0504030302010e01050105100f0903081b010c0201 74
    0x1038400a060900601400000780d844850041d4810ba030071782025246d40021700001d42c105440d8140d51b0000030240c66150300f0003401c0741e000600b400c004110b05c10090014201041e108d52280ca403d0040c40c4006000707000e04007100280601500581c1c0380d015034505242d6a0802010141c89016039400000e1603030301c40d002e84002c090402020744260041d10f2550341c05490302030800301040c1c0d02c0324000103844440c81c0196220308044842204036880300700c0050401d0025070001c504250074484014103080f5411208100003c00440000e104030102442d403d45000796001b03c0e00a010307843c6030034103000411141c0350140240c546010034640c02c1080124a5081c408551a0080a2800c0030008500d6588085903c541500140c0740d01420903000241040c0d00300d03403580003250003c1400c0c014994248102d5160500c054001c0106506210002c0c100f240c0c24040f02e01000300661050601d9880b92000da802907600840450301c40a014410004590304400140c4056107009852642d141c814000c4d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 771401771 1250 771400521 771400537
    0x80c0901020c120a06020d09020f011812021c03021e0f0705151204030908101a15040306050f010513090f1106040314010f060510020316060b130c080c 66
    0xc00c0024088414400a540880c0041d5041e000380d90307907400442d54074002807c1c6042c0e140340c005096610703403040000044602c401da9042103d50510700c483c1e00000c5998100f520725008101d101801141b0001c1c4980070003500e01207280c01d83c20850340070140c0028500005004d8051301d021a00001c0c0c0c481c40c3c2d2071100039a02100f69004910410403800e0080a0240218161508a00d41100e0310103500ea00302c0141c9040b0001a0003040400032142c040c040e444450291020038045011380c8042103260a802106d101e1140801d60204802c204800049030000c5520100a0000307180c05009211001c0d003d01c81d01e0700030f07181602c600d01d052110344510b0400c1c650102072075501c200c2645640c0e48000084207011b822080800c03021000c5114007602440e4844d1a200100340d00555201045c10f075545980f00f01d005902507000895403540101c1582c00c014480320040c41c0e40c0030582015070107001000a0550801850101550416010b0b0403114807481d1944914046031948612006181310707a84e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 771402877 1106 771401771 771401773
    0x120e030a08071206030b010302060c19140c0108041a04080f04030f0c0911040b0c100914251208040902030708040b07090302060708071b0b0406080c090102 68
    0x1c0c3e8140315420f14024401c0901d180c0c0c41c4c10030103506000c02489201c020481614071001048000c441c2c61007a4482804501c00b03040206450b058101c9142d00c41c022100301c80800d501841040c0e0085501c100201a20800060500123b12018000316450702082201452455104002e4030265006610040c00c9800c185003100c0d04809582c060b40d4000d080a1300c01c2840c13840742c8195070071160029007499a031851002080d060030a0220224101031030b200100d17041c091000e48420303094407203c0482e90340d40080094410a0600803201c0040c5440c250410b0000409800b840041ca0f072088000c2c9d410103468103045010381c0c10480303000340041c00c03080410007807142040c0302c07540160660400000340b600719000300715103200d060b90180034500001240820481045d0310801000c120b940340683c095141c00d082c0c20b046c0d000c3d1060000143c4101d021030007051b404c104684807504160 = true := by decide +kernel

theorem cover : BRFrame.Cov 771223021 771402877 := by
  have h0 := BRFrame.cov_init 771223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 771223021 ≤ n) (h2 : n < 771402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
