-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1161
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:31:30.05312+00:00
-- url     : https://prove2.me/submissions/93f103e2-8e66-4fe1-90c9-b850ac742e89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 208633093 ≤ n < 208812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 208634343 1250 208633093 208633097
    0x905060a051e04020a11030d06060305010602010506031509011409010504110306150f1c0521070c051e06040303120b060a0f120e1006150903051009060b0405010602030a080601 77
    0x162103002000300070140c0c0c2a400074151400760722217400d0013058aa42c0f64043d4214114000000c024181d48116030011083e600a074500300302c03907600c48404900300da400b1903245405038881351424480788481040c003580050a1000032820000340014100710500a80716120180e440710300380410091407820002807640c09600500d80d501d4481c2c000300400007031500450081d05654250500c54544020f141403070217000b04000030103400d0307142040c0d84480e800748400921207401b84080c03000302540e08441059400c840d50031001c41c14882044020410700e1440a090410818400c00e191184000f42001354040d840da600300218013868401540c04e1889150700c58541080200c1d003e5070058516038001815140c0361010b9403078412180018410528111070a1042d4a80d802e0800d0882e040023096880130f026041080c1151360303040c0c40d4000f440c00018400d401420440d45844800e03409544e8960144102240490304640850b08a0350280c000c03070016040000c030000007980080c0d0b800c3c1c000c4402c5c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 208635593 1250 208634343 208634359
    0x1050307080a0209060702092e050d08090607210e01090b04090504030e03010e1b04090b0c0309010204090f020301050118060e0f0307030506010b2709040215130905060a05 75
    0x4110081c4040001041c162041c0ea02107001d19a98031000d05851043e980944003803110f060008050010b141d400248018640d01c0004a1a520780c00d40c005030708540700502070640d900c4240e55641110b422034143c00360403030001d0140f0804241d13901c00d98224203a9482b03544c07030701e80c002500c0245040c0198800303505000d0310040400c281551101180c0803207901003400105510345180403995a001c111901d070f4075600b03003c2d4003410304002083e0010b4014400458081201e820780c180419249082805842100000006008014032600035640b10490200052526854000880485100715405445507502000601003035800c01404420002c10324035500d103181c0340920040ca9190840740c014020926400007104e2501e08200e5800a158000182e507a00d41e1280a08040382e007180030070592405814034007800c00010031141800246010740004516a100c3e002d20a40100d103180001e600b5004203c1488007400440200d005170640d10340204250502c601040107003402a00103074032500c50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 208636843 1250 208635593 208635601
    0x12070b0a18052101090624090b0d0b0402150a050307030c0507050c0f04020405030a080a350402220b0a08010209061602060c030d020d050f010b1c2711010503 69
    0xa400440d10f81d4400403500c80c940031101566880c050003840701300415050903d5980c0d8441a803051205001502c00c4501480a55854244009523281c2c80c2c00c440d0030942040307a03c800328140805459102d80043c0485146100d11068009a07502c00100705c00040e0303001c01840810795140c011040140078525009051402c903480e1591100d118840c489d11607914414080300039100c0760103a03001054020241c4e10909078500701581c00b0350100c21504002040310103000101003107508085070040e4050300001c0f0300501080d41403c0c8007c0035100340c0e0302800035090400d13448421420134400d4a191440850440360500030300c1015443e9410240c0c0990041c000301d000c03601c4003c160f405520241d003181c080402d40380049812441400344032411030200081c45029902c558008028074030102a0030041c03690b40f420800701c0040280101c8410207004c101400004003803020000500c048050001501303018840c00c0303d16002c96103510700c0241848a10903050080304544030308190000e00b807035803561070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 208638093 1250 208636843 208636849
    0x310060903051c12060603060302040507080405030a0807020c09011d01080f0c060304060b0303030c180301050709091d0d020c0102100b060a14090406060507050d0c020603060d0212070b0a1805 84
    0x140c4941d18540100c600144010544e00c5824003000041025004004103602c0e1a4014050801350000703170b006a05000120301c40b07911030311300c040c030468200e005141407008c2480215940314010701020218407030020903400c03940e038600c00c007030003450700315500700202c0e040c040403803940d581c16401340026401651856003020300101d041030b2582c80441c0c400382e5981d80d074074044000300f40440c90f660b01848040f04000c58110084010100b40c04444080c4030082c150030201401c0e1581207561100040c1264010000841280c011480440c000482200d03070440142e52030b458081e10202c900010b9014424414a035601445040da48071030f038000902010300001c011801703500ca503044410402c242c08403180048244942a1402d080b4001c0c4140000fa641e60001080c0d030b0410401510705000c0e064181e12000e0180d0003c840d00c9502030191401c558400040100620641c0405d03600103030420000303038050005014100290104005440d111860503200910f60b40c00d1030f410f0b64480208141c1400195 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 208639343 1250 208638093 208638103
    0x9060e03071e0c03061422051902010203040906141e030c010c020409061e0e06160503090304090606020307030905010c0c06140c0f03180307120b0c090405040302070501030e0c180c1c02031006090305 87
    0x700b080c80ca03009e81030000341300403491441250310089565281c1800400c642c0e420442040d8001800c031580c640040c010000d642000e8800d1281d03d5250f800107043c036803603500404442c00d46900003840000c143c0103e0711588103540144040b500000303500d52596a031158540700d06166210280001d09aa2a10744030281803028212042000e0180101c0060f4240b50204202e030007511840b1001d00620b942d0b05030182d43d030b40041c2400c4000c10240080410303194410b0380d00d0b01071540c20002804d5202d113096010355800703410004080c07803030404222084c4021010007900d4101550f003030085581d04600107004001c000389109461080c1c11010301041100118204240566040b600001700e640f45c0144549241c4524120705070000e09110070001490b4008c242441110000c0e00e044c0000c1c0301582c0400e483e40c4503000d00320b520114800f40720b03800b140c4050503117a005815408031490102034550034200c42c5d00c8110344c041d0f2a50000100a404c00300c404c0c805000749514104481c0c610300f1603603015195 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 208640593 1250 208639343 208639363
    0x3020c0c0904050a1a15040903120b03030f0432210709090f0303060b0f0f0f220f0801020909070e01021203090109060e03071e0c0306142205 62
    0x40c03881c06000c1803d0003000d028160340c0a5000c170044410206200003240d0803441107494002c124241851000d0301c0c2442e02403001000e50503540d1001621a00601c00004c1c07a90501d02a091300c0140300f0150300b060b440006002800e01401042d1103a40119100d0b810503006035003a58112815451070040c503240c0b60b5a0000388040a00480030010541219034030b80703101c0d40d0000c801c190030b1001040501612910440c01c490190b42c0070700035552560a0310080d4461288900e469003030402c0b0501000d14044058598620345006c824541160640025a1064103d10300d01032050b6508003007090001690b245002010fa04e0300a504101903407000848466000701b08105202c0710050b5007496038030034090858000304508800e5101e040c029012402405894012120140340842c0c2c1602200004140c403039956218040401030107240c1d017484940322201d0400c1303409100348400803001070258040c0d8074001d0b285150044103854a09100030070f2a45c0c000c0805102081c4204240100b0408a401c40e28 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 208641843 1250 208640593 208640599
    0x151a0d0608010b010f0807050706050708060102100515010509030a0515060a0f080d030e010209040507082a07080a110109081201060e0a09020a050f0f04030201020c01020d02281209090c03020c0c 85
    0x101c7d506ea100554952040d00802842c091400d0100115142c0001d140760082c0d10a900b211006102100e40c0000c40c1d40547d084c100c1c41c248011950410362143c40208446500601920301c10032003a0f48492a100d0b10b407417030030b5003102d07480100485820002c6821703005003d00800d440c50300346490040c42d15400341e04140303820540c491050b8811038000b50100d5203200d034090000c00c0103241030000244245419204444825000040f00d442003030085070301e201c24691161104c0c41e0000568840030301d64171401c070107000d0114404034400e00280a01c10301e00326034000c81c083c0b0b41d203014445040341c2489050b00940d062161040340121181c82c0d558211003a102c200741c0061740d664000c00203440074003411545d0034401c000000c09103425542103002c1c00c1221720070b808031a244201807005a0303d41001504940c0107900c41d54079102090580700d2042011000300050304115140c503142c0442c07400448441034081500f03076008002d810207500c00c4141c070900520701141042880c03103e8645813040b014041d48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 208643093 1250 208641843 208641857
    0xc010c0b0106080606040302090703140c311716170613080915070b0c030c0a30050f06010207140603040503040e040c0905090303060d0303151a0d0608010b010f 70
    0xf0082e10307031700100c501039600188418502d00d400c040082c0548034440c5d42c10045c0000a003c07452203440e94081d0392a0b0010200180d142c603c00d09642d1821540641c1385105240c0786071000034041d2401d81a0505090410018110300640301405003002401c40c0c1c45001c40d611040c0c52a010045c0c0460b03483c0c1c00282c000701c1c00700390b020b6504200b9228020140f1144c0e002c14031400629813034842c8401840018801c1416a540d81e4404000c91a180000c60f19080d505900708009181c562189030304044103402080d950411342e0200c00c58689915445483c4413030700da0b41d142030048111307111800640c0700009200815444d41440d00790040510564440c90003610080041010003c00744240d4000d0300e0500f8010280d40b0742030034500c808071401e21450780b0161230308020614403c0044212480b428014081c015810000d6800b240103001c141c21040b00049015070200d03079110f082107070443d211303010340080f034a45401c11985811a1420380c004101d6a140600c100c5150360440398480d003400642c10520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 208644343 1250 208643093 208643101
    0x1707020f0f07090e060f0606210109090b06240f09060d0606080a060f1a22080c030a0b0a0506010504090204030501021c1e021602060309010b01020c010c0b010608 71
    0x280c40d0980c403520182040c040d0101c0391105400000d0400d0840d50b9000040c00844822800703151604401e80d050680c00461500260035030904034020700754802141d4041e1000100b2011407000c103602038018440181c1c59418000510210540241e08000119403140c038844171105106405200605600d170200300c04141c0e1640b0701d041101392210b141016044594600306c110785030300101618000d0001040285c0c0100e0380341c850a07c00c04003a1285003402d4800e160428542e44544030400c201d03644010001c00203144070154140340c5070190000c0d118001c1503103041460a60800c41540c1c841d9010b980031942480100383c1c0b555100360884405280043c131500d0300001200c01c2c0c03045400032103400d80005800020458152b00811300720160f52002c40568284070035490581e002c0700140c04500c00e00310f0000100200c141d0040103d07808407422802184107075400306190b5002121050340a964440743d50040e942c060001c08140c00e400d207081d01442c138155655030200b40d0180240b90410482c84002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 208645593 1250 208644343 208644347
    0x206190b12151b0a031d162102010203030604240815060d050c0906061b0708010609050603030301030b1012060f0f0612060b060d051023011707 63
    0x403000d1484054005000c08a00e5070049035240d020310340001c0720241c4480001c03101954480507605000d000c5030050f00c0c016104400301c01500403154034030a644445e500e601c0184e1410445280003016005030080303500e00d080042d11711003c820506120881c000540140140e074040201c80d070104040740c000596600b0a02d40d43c85140c2c02200c15190b82800138804201f0103030005000c4010400325043c032581daa00c3d04140507550300c89490043c00c0e50b0116080b03500c1d17441c08541480e48100080c1805003404000301e03d204615143d0054003503180c11000c0c051140136400c3c06198040d00c40300a00388001d04140c400300355a0b1005200291a00c003260010034961512544110001e1034028501030b440c2c43c40d402c0920040c9a1080e9090708146441c0c0500c03590701050007210708441c981d40c0c03060b0f505880c98840c3c1c070180c075620401540c8845e040200d00d00d0105030307100340d0f401195281190701e4518100100c501444042002011020394210b50441c103603a880040e0421071540303402008401d4a4125007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 208646843 1250 208645593 208645601
    0xb030106170c1603020f0d031b080912040b070209060306042f040207061b0207030b0106030c03021603050919030c03030e03011508010c091a030c070219030303020304061b020619 78
    0x603949420114081c45024140d00040b21011b00d00030320107031070581102501c294121800c8002415210301e140303107003a42c003d0041c94440d9001e0203003c1a9010554410131218440c0d0280d004907200d10310214281c410344c01d0081442c0d070b21043c150004c00b85401e0644030380d81c0381c0c459038550b80b4040d03507890400c5840065000e002c030071059000d8402c0d5214142854964098441110b0f2036a41c60301000d0181c135568400668081281d802c0268110142d091890032005442d07120320050a168082051000660030390310006c01550007680c1d95a1141010003c01100180f0100002070132031a030141400407545040c054411280d060800f5504142c2d4200400e01500348840303c460b0501110500140151041d00f060301500c01555507403c01944510941c2190b503607082c41540c1c0c1f408180001210014290018000a07000034038040740703031941465050a144040c3c000b100003c2c1c0100074082005414066540c290306440c5890700003100310310000b50f6076400140344000303208888901c82104501940 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 208648093 1250 208646843 208646857
    0x130306060909020f01020c09160e0307030b090c030319050a090902160b0106020a03020a020409170301080d0f030903020a060b01030b04020d05093a0306090c03090303060b030106170c 80
    0x4003803014903a100414002446002c100ba4050010071040010a61010400e41c1c1c010b0401064124692104100f0700095201c5c0003012042c0483d07844030300c032203076810402e0740e005510944003031070103140c11640305003040c8051410034081d500038028119540340074000c0c6120301d100c5240ca55100c0c0080b4004540c0d40c9115444401000e01c005882030035080320040d510001e9000d00c0c0e85880c03690361408102d07900c210501020f801030300111054030040c0303420b0f04140361031800395004071186c40207079060761210f078000e91114415600854036a008660032104a28041c0d409080400010100c0d1b1000381d16844104002003000360359000b81610f50703009034054004031314050700031034580c00d803011880c000300002e6455030080d10454501c1894209003828440c40b484082841400191580d01002d80b0218681c41c5042490303201d0102140d02000ca100b4a10001c2080d039010030030980c0c0d4240941114200d0300a4140041e003000113102c2243c11201e001c550b0203017118054180d0782c5044d5000341502a000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 208649343 1250 208648093 208648103
    0x90f030518041803020c010e061e0403020907050a03060522050a1d01060807051207050607052a18010303050406050c03130305030405090907050a0b0304110a030813090501080a0204021303 82
    0x101c1c07403120800036521401c260602c25021181c0036442c86005540c230140800815900240400025030141042c030094042101e8455290b03040c40d0f100d50025008031822100480000c01c08101d8030511503141c01500b00030701741903507200310013a00d200035070001070708500c1700c007035000c3d1208040307452070b00b030b90b80149001e003041c0b41c00320041d0080c1c5403040d01030a407038860908103101d48000441d0501d04144602c6024086100922610345008140801500606000d0300c7d1400781600001404d6a8044103103d5292048601d0407070405a00801100c00c19103107041d404207000400620000380c02908803000d5072403e0400e00c0d1205a4240c074686103100308000c2500d00410041c0c00002c1040010103402034079011101c1d052541d03107210340c2695501c95803142c02d17400441d1480400024042c2c0c001182c21a02440313a03000810840c2c2d0214085a0450b80b00311484540021003d092145086144010b0300307140034240525450501d926664900d02107002e442258001010b1a80e08142100c00300155401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 208650593 1250 208649343 208649351
    0xd050618061813140106090f180303180b0f180d0c23030d06210f031214100504051014090720070f050d030f080402030c030a06090203010b0301090f03051804 69
    0x130f124650203040f0a22400010b58207140d1911301070300340340c020301241040b1240307070150080310364078102c020b8450046100b51107098283c0010104a404110030300c01c5000c4241d03c2080d0900d0f410f46001020b040640211540220402419140e40401d810303030035681000b00c0c20b940702000024459500307070540203a8064031000608030441c803103135003043d4211442420803481200c030040b00840c8111181c9001010020110300740e000007030203502c10302e0500c1881c0b400000e07900c0c1d403005113030405941907a00c5286a914000300700801d10b40307400340b00c1d40b10400344186415540b62410001d40d00b00300c2d603e414841c6044c8800250168440c00c48840041e11000603803521403040d12038592682124090342029031342150740840d041c00d10b1090806c00315859940c0a000440d40013040721400c90207082282e050080c4041003080c0c0d507080000b0090940148030004010712148101400c40d010014a903002e40d06045020340424004d002600126405040455a0300c5c5055143d800d86110803821a40c020301e8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 208651843 1250 208650593 208650623
    0x60f06012c1c05010e0607141c0e0109050d0518010c060f0606170705040311010e040e030309030a1206030c050d06090209010e0a0e0c0f0f01030b060d050618061813 72
    0x4802c0103070180c601400003000b0f00399a100c021500c1d02d03c01c031292000315816040340e80d984580c0320001c0100c40900d454101040004101220680e0800401107540e691600303806401d20400b4010007580038071504002d0301e40242000a1141e540400c174560f41888002d654000c00d100700c1c0e400480c035149113030a04202060302c648014019205501d5481f52120074a0005400c15010340b0813181900e402000e0070f03185070380c10310044906d1038480d82c07895045620f41d0200c01c03041000300090350240301c0c0300300510f499031582580282060800302004171090704080b0b04201041c0035202e4601651815104140c400b51179081200142c00c10b28402500f022041e03000258100d0440c072424050301801c003052041b140741c60740c180da807031505400141e4450511115040300e4a00000540300b50101810041004041c2000242407a0440485030300c4036912041040f5580ca0415440000300b940041ea92032b84d82002e0002c6807080542e40406490f001500c40030a0b051041030401c0500294410044000820 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 208653093 1250 208651843 208651879
    0xd111201030b090a030c061a041d0d020102040b0403020103090c0e0a05160518130608010608070302010906090308030f060a122103090f0b0709050307030311060f06012c 74
    0x1d1205075008103035240400d800802c01320301404910340680d40c802c480c1c0840d840f00e2000b0120403003031007170741452840d40d100c06840c0da00440220034858010039546c01844071116041c0b060032050b0034210392041006021f405014401c0d142681d0302881c0000e11648a4a001880700d03010390440d20030094002e0411100c43d00640005105190181407c6480d00a1200c1900c2e680a0f8100c1c00385c404000f40209034640c100341030852031000c0c4caa840070075020b81c1d85030054211000c6402900007500a0b903414070039560001401c000030180307468503280092454865030120300018080003510082d500104001d81e958060700342c00307800300a400e030003021072500c0c059541c1c00c01c00d01c41200210300701e29904595402031240d07100340c2d41c01c5004801c50000300d99800400d004010122002d11410000202e010340b002c02060001d1446500d40400e5451101d46192410000038a840c1521070002c08101c200d0341c0c84440640d0315a035001d15031181611041599000c80b00030040c0a801000c841d0f13014001034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 208654343 1250 208653093 208653127
    0x13020d0b0106120902090426040609030b0106170c0f07080a030c030605040b010509010e0414010e01030303050c03010f0314070b030c04230d0b0a11030a0903120506010f050d11 77
    0x107419601d6a00442c0080310f42e000c03d0b0340c1004c6010b5440030941c8006004240010014281d1051684030000628035610420351190000d40085002650440c0c09000300148103030140d0140c03c0b6424601000a024410b000d02006c00500000e400000860010303c021540c01c19515982d44c03014101e61640d034181801401003c507a2050030000741041d00001d0141001e2180340141e00040c0d5170b0900e0803c0c80c030f0041d9100e80e180a01c1503003180d03907207120b45440131080088a02902040380850680c0d4035500b8010180d800103004580c440904200400074181e030480c0c16411030340d001c0303808840201d0040045003000c84036480401c1c800400010080b0f07442c1080f000b030060741c1a80d0020880d4480050349480003004501e05039400c807a120550a001c01c481c0c00b480e980c00008242d0104aa80c0c811894403516001900e460030180e440c2d403500820075411100084a1100402c8104003a16115000030011700300340304640c0500030002000800821582c20100d04a11006017582d602c40725007612500031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 208655593 1250 208654343 208654349
    0x903060117210f0703090e070203030f07050c071412100b010f02070b090d050a0c0303050a0e010806011403070203040509090a0b0f1b09060903060703060e100b03040b13020d0b01 78
    0x3409000310342d5042121040c20b44034608180e88060341400180920004940e00540040c0c2c148401444000b8512041c0360445200c0c210560245460b424003803540c1402032409441c440900c0b600b4005e64143c2c0c1000100b400888040c940072003481d0f201900890b500300c919502d404c025002d100043c00295000b500030341400072080c2c0c0d8944012950f020102d071074401038080c11b84110020803080d42c051410409410406004406035482e4031081e540b805002002070b48100d000c98408074200e01c81d84e400c8036050281540a007000300c1949004000206030103210103c0c0c885090012002c100018800c200341d07000f030718000c1c15008050070094455581c40d4114941242c40e002d2043c005400003245800c1d89000311502e90401004144101c018a40364100510443e00030400b481964581e0b42c0c10800d0a0050102d5200000e20f2030422202401a5400408024100c001c007a820810783d0500e80c11a5449500901500b08a480b0b0120003080d984083d50b0107544801c0f01714203001800a103c09607412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 208656843 1250 208655593 208655639
    0x203070810080102210403090506130e100b0304231204170c0102030d0f1e0b0301050601030e1209030a0c0e010609050d02150c070306020c0109050c0402280509030601 73
    0x4001c0d40ca00042c0e0a078840c4500755040c40c000d95152403004040030300f00c03a401034800d08002c08502e4546000c02e0264000703041c54050341940c0700c0700b0020136000708541c54100c9000c04040c3e0200341000603508092001902c01001c3e215a81c07243d1120380b0240a54068a58120003aa044100490300c00081900a80103c2c500c003196045580461040002c0c03040344100181c01450410400052401c01801c01d001582416611880c0000e40c6131806c964040c04040803850005110a20905043c02c4070740007071605050501e00000700c10210343c00610f249410082d1070b1500c1e83c40d001c00c400300303040075090345005240054100c00880e1403400c0c000c140b4141d80c4507a86080120f6600c40810210880c60080a900900d042403101c0c0d00c0034100c0c000340080d43ca48022a01060f590343c1c1d441089034071480c8804100e0350b54000300c004226092002106620040b2000d40c24200d11408104000c550b001c40301138429100c50801103610300a00c11382e0000007005050f1070541d030b0b442e400e500c90518a0005807403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 208658093 1250 208656843 208656871
    0x73206090304080d0f11120304030f080108061305010f0204060e091b07030c030512151302090a050f130c03060509070c2103020903010e0307060b0123071502030708 72
    0x40c02000069404464010005100c8064050000d44044c41c22011781d004120204114051007101004984400c800b40c1d04207a9886c81c0c0b904005102d203000c040c0300d0040120840040150400003d94607810407507032080860214050b1a225004203149c2d02c003c01c10b9400410f0014200e50802210100c80b00c2c107503030340741c0d2603620040d42d403980b0000086540240102031182c9000320384180c0800c030a240c07007420010714040040f81c102088030f0080765080c96108410240389400e0410303c0c0340040020065400b03500313010b0b0f0840004c8185060f806a02e00038042e0402640c119a200e401150021000a8081060704107410005025080304d0240e640034103524008079149520540c0c1391001d56802c0880c0c0342c0001c1c42120585034001e034080700d1108041c1c00780070010040d40d080c0b08821010168070300075583e59640f4a058400d460003920300605010407011702440307803040d0907501a41481d24161240d03480da51031030041c0b100304c488884054218404020416140d821120407401440e80304c40c1070f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 208659343 1250 208658093 208658101
    0x306050c070503040b0307050d1d070609081b04140109020c0607050403020612041b06020105090f0706170901060e010311011d03030d0905030d050405060f060402090901030305073206 80
    0x200e18401c0101c0140241e0040104100446104000d10741040c41880e00317918020260003401c041d101240103586002030b5014074400c0d80501000300f03000402060500d10b4040746032201290b158a100c0c0286040b8144003417008165030395a0b84802c2d0a0400382c4a44c80b8103584034078003a0020f400511a11455104131310210b000a40141e09031012242d0042c41940303400108100482e00c668042c20403a00240d18610f10008811288003900283c16070354000500c0b0b10300303411f0f0741d80b408110b07444103009900b02d5001400280d078402e401074115240c040c0c480300c09031141100e480c01420140d018045000300312001004100c0600d0b06101039030700903a650b9100c40a00d50604044209a402d6254590300c10008038503103035155000380391214060f0095030705185180f0b1403501a100300301c03000c075503541000003082295001d41d6140b542190050300e04504001c04100440d0010300d043c0406003c0c0701c0007240302d208108401441d10320300204480210001c00c00268043e410002c02d898079026800790000007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 208660593 1250 208659343 208659361
    0x1a0c0a02010b010c12050903120324040b01080c070828030b0a0e1308040302150403021503090304030602090f13020a1d030604020f030f07410118170106030605 70
    0xb1361801d504010f5082c0d0401e196842a03d1951091800503014028000d0302800c07a01c0300380146204620307442c2c1035503484100444201c94400300c0a0854404d510b0480e94100507603101380042d80c000c0e010204e0715542c1c0c0c82420a1324040c02958000d10001541c40602c64030030f40f591501c40c4505103a614140712044485081103241c107010f0260345811195800000c241d8001081114a0103004440f018641502c2e81c000c900c950a04034001d0a034000002000c03c07c509040301407003050000484030b03a00f903040403c441c94a0348900e00c40a0813850300405c2003900c030390701d032310031100c1c04000145000300c0900400886400794100030340751004146004c035660507004031031201550710b50004008d0462580c0e2039007001485081d0b5000c0ca605131061001c0c009564104200100c080c05030200d03036003243c0d000840c484008002c1607055031410f200078020300034105c034041203d6121a0007403c101c450f00001700341600c0a4101640401032a01c200092900040810350054094a0007a4420b01c00d5039211551 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 208661843 1250 208660593 208660607
    0xb0106080f07052113050c0a03030c030c0201030b030a0c0906060203040f1e0302090109090203100e30042303160902070206040306060b18030c0a03020603041a0c0a02010b01 76
    0x50808600c5103030000b0310703600d11a0b00141610030250460314000009455081d811540464031a940244c001010b0000d2001c200a042c0010404a491100d6241075540052070502c401c0c0340142440484011034045a0107a002010041d0b0003400721600b081c0c20741403030090088030b84510861945001000f1600510100c2110280c030300001da02c046d5903180c0310964100b0b0381440070482400ca80c0540210050340d854400c075000302040c81c80407401020b280105402e20b600d840f03818010502d04035000b155410041121300c01c007101c0d040e040048035480000740500c0c06040070303038032105e2200280220b8440c801c40d910503c0c240c5010041e01124956000f45a51031b0070b040c1d01400a038402139002c000c2580c0d543c00410301c051020b0412410941c0e20740d00c240981d44c868120748030350315011036558a46902c01c011040111002c4005091001d89680460b0400b0154003002e401400000001000e10114015190748490080d001843c0d074509074a8014030340d0400c800c0c54005500300030982c0c1032988901e030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 208663093 1250 208661843 208661851
    0x151a03010b03030f13050a08031c0207030c0b100503060c0a090b0309150a0603050d26041e060908030703060501110d050a050a1806050301050a170c010309050a05010501080a0b010608 80
    0x10041d8900b060b41c200d04e180d0f90304100701d50010052550008074191315000200401800300e07400540d12000801d1b43c2c510050008a00070704a58070500592002c00c0d030000600180c140c20220035080c90312f5050103080406603a4001c1ca425226910074001e1054083c0000d0070320700d096036109443c03251650540241e0748402e498010b02c03070340060441e0795004c01032171016030000920080011829941d40c0e8050a01240207a01400301d04440035a140c102d01c1e0079010184046c048140c07405914259072054201144016000000781c54900340c82d041180990162040315008000140c4038035240000030050a024041d643c000b41e10490702608240d400101e4500e00340e110b4483c641089202039046039075410500ca030404001e1a030f00c200d0051612480d044000c0c1202d541c0b85a42d9606050512002e0440c0703a0105185151000c0058880980882e1800c0e006400b468041106a01c82c280705241c084c0c0341901030125440c00000188070000060040720729841807107030a20903a43d8900648041100b15 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 208664343 1250 208663093 208663099
    0xf0911040c02072d150f090b0c0d030c180e0a0e160306050c0706020d06050a08030f0414060c0d03050a05070804031b02130c2001060b040303050c0703151a03010b 71
    0x6910080554003c01e44d40d00964086100c01c10f00c26500c8880700d9840700c4c09407007003000c80c00165044005603400520742016009000c0d41c0c2c0e203005130003482655130303200c2002218105607032400541065071080310b00c40d01c483c2d00410178116654a520300032140d1703034084d10344100b020718250100300000c0d03001c10a01c080a59840ca00b12069207075440d0100541401040c11507203080800c00d0074000b0b5802d1000e4900400740120000b0414100000e11013070202d1a045000d442d482444102c081d01440c0c001ca0307080c0c0c0d220701c1062007071400700d0021a520780031b004d80c110300600403200d4a00a43d507040c1c2c4160700c280980c0c0401d02c06501c4006c0e00350703559402910302800040f00300e01c8580c042c00c1940100c2c040544042c1600429a00704a034000480d010125620001400d48504003400e84210004030000c406400c001c200b46468036650501a204a10000b024010007180301e040441c4284a075400860700198001d40446012401c1c00081007010900350015504e290010b601d420144200b1140d1003000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 208665593 1250 208664343 208664369
    0x103290301021204050604170328060807060c120306030b24060a1d1519020102040302091302120d122c0705090f060d0f060f0911040c0207 61
    0x5000910904049400098240d9001c216905072200030090b141e21070307401000034081c141824030f01090940044103080441c2c0d00d081c000e115000c049480f0001f410101003500903000c486a4040710044c0c42d059206038803600419200148507078100c114016224850100300e0074100043c20103a0803210b8502020384520075242c00501817048651402e00000c80c0c8889076840ea400e1400001c4480d4013007161140090718500510900b801030310034441100c10b00702c0700050412040c10302a0202c0c000c00340054070009403141c030144c00c58002c0d811200595000303440a89a880d00b880d252a10b03880000b412406042e0210108184007800305003580403680139501c80c100c007440d81451001900c05221134810700d20741e1440e0150614425152030304440000006070110510700010000940c07002052811415840401c0041650700e01524416041e03006030703030580340e45042c03d1060080180615155203585041c07008000d0100c1c4400491114400311350610184c02c03050070482e00d4045500c06d0703008520403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 208666843 1250 208665593 208665641
    0x50d091203030e190804080d0806090708041a04030306051f0c03080a0209061201060f1e0f0908030a02010506040605030f0a020420031303020705010c1e03050f04140f0103 75
    0x8070740c0007502c3c008030708021030b1000418880c0182842c02c01c1d000407615141c001404200d0144c003803204e000c54008030309146200c1e1400c4c0780480c4011000a082100308200c4000003000c00200c28a20b82500d1159900c0010743d01e01460301030000e04850150a1049409584200782400c8840ca0014000d91594501200000641c0d0588001201500c0080302e260248400300080d101d4002804d4804441400d4103801c1d4034104014010112248807907042121000c5447c4030b1054800c10000c00030075600e4500b41150300c140048a071038006802000850000180108015505410030380c081c0c0012a400c20009075100101642d0b1001c2000d0540e2a400681c0d1440240c906a446141005140410048520307140d0640010540c012103444941207000b072074078070500d079040045601501080c20704c03a1482020361191214022244034480a1400a8405508141c4140203032110307005000718030b07600c9580b240d1004c01059050003101c1e00071031400c18410304c00c0d8440d000b82800c8254240c400001404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 208668093 1250 208666843 208666847
    0x105060702030d0311210a0506120a03080c121e06030f0d0e06090405010b040e060d15090c030c0f09050901021e070507030c170609070b0f0d061502030304050d091203 73
    0x305030440c61018905000d00b6020304803000690b10002011b00c4c16501d07500c0c0c070011b80c200311380c40a440c0134015890300c020082c4031000000c3c1134002030b805017482e0500382c4c2e440e4880302e0540310b0f04442010600507c810b201c008000d034074683c0340c4804216850f00740780e50307807009150b074418501c15803800740e500000ca0b030a6035034007038890b206c08044040d19151070f00180001260640d0301c2079204d454140c0002504009001103418566008241101e0050040c2055104c903101d40081c1074482009a9840000b441040000c0412000459100e11907151040e036505065014103500e103d0425214100400100e03900c0041c0b080703421030003010704203008490780e04000e5046038002c44422540f40c8241c540203c003151800780054001d0001c15442c8511642c00500541414409080c0743c0ca00c1d4840c60b01844600f561006550079210444912134a5180b4400b900e03010303020f41d038009120f61101c5181d130070b91a0703400300040d441980103800711810342441c840101c6110340503103e600c0d4071000d04030517400024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 208669343 1250 208668093 208668101
    0x207090c0504050405163b0402070f0b070e0f0a030f050307080f0301060e030f0a060e011107050a060b09040c0b0a03020c0118030906030b150307051603030e060105060702030d03 78
    0x40203498464241a103d00c04141100c5040d01c0c0c01b03d0b0211181c2c0c9007242c2c41e602c0383c901c2c0780044e1400303601c038240400040303502601c240c1500402c01044c401003105082d038440d40d056807079140d000708034035600c01010704008240c40ca0550b00c140010b200f8407140101400c03c941d11003803428014040503c1d04c0c5c51902c40d4007140b0400003040380c040c0010403049000c42d03001b6010300850200100d00943d00d516022010304403c009141e014080d80141c0c400030351101d004070f003a12045030004008581c003c4c0100340079005010440c100554448041440da0601030b0000740440c00c44d1140504100c03805131202000070700c0d641114001c000c9040c1d074000b0312900c2d800e5405804840b21303d04015040800c802c4d815801e54801c1d0280074442e40c0f940d00109c00b45a84421024000d0180b42400c01004001c000403500e00b005135000031000d00400004590300ca03201d071080b075a0000d101158884d40c5481450b004024002080c409078152040d0000894940751040807220401c0c1d008004000c0f0b000074080542c00786c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 208670593 1250 208669343 208669361
    0x1603171c0207081c0c0e0d150518030a030b120f07031401090b2d01120206090315011701060608070e1917030c0f0102031b1c0617100c020709 62
    0x150308284280c0940c4000e04a0300c04542d2444d520203e840ba40491008044000d00c00215100e0754421075800e0208440400ca058451750b881408241c1c0c1e6900b4071881004145030703100c000035100025a2240c140e50544c05078004000032103070100700c001d0384000e00b1341e2003500d1b02203001142c1040b501040040c0da0100240503015044001280076421070303c400c0c0341d80e0070032904615040580e03044c035850324000070106d5450481c004a4469154142200080514a0420000d0243d0000145050a40e5003000b028140740d460707448060556031651502080200c070711110101540c00c00f000400d2142c01050740c944074481c0c9036a805d205003100b03000c0204410f182405401c600f010440c02081d01d0a460714000058400d12004583c1c42c1c20064140307151084521700602d40f6441481440104804200341c00207101e503282c251a10398003440003207500d0402030f444800310b941c581100004d45001c0994000b5030207141e0001d459a00310000700c188140d41c41d0a409c800140c2104801f0300100403d68094811 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 208671843 1250 208670593 208670603
    0x151006021c021504030e0a060c0302011d071404060b19020708030703050a0503060f121606020c090f0405100f06030c23150403020d0503030405120a08010e13051603171c0207 76
    0x20070361940c01f280c88071600b600a6400036500100c141c0c2850340900a0307060711000701201a4800144440050311102e00e0b02481c0001c48005046000310703516508035601620075030143d40c1d924640000b01c10344401000388510b0250140d15000501100003005481505405d1784581d0714112070580201d600b640024400c3c0d5110701c00c0200365036940c4501c00c070030100b070702044001c1111400c1c40b804072401e02c070290720600455000140410f1b0f10740329451544d42003103201a201440e510b0f1440c0460500f10800402c0889a2802400942800c511307049002144d000d0403401404948628030000d2a800041030403640e10032401700c41c581c40c200442540e80802200c03041908107500c960020301174001903401912070f40d1011091009000d824031a02c0c00c00d0400380162445c2980b01d4030090900d0405100d0b01824084401c0080c0a56490803041b035101640281a80d0412091880410b040e0310700d404107440180d4a4100520691104011544002d0394803000c103555800d9000d01d200070b507002d204100c034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 208673093 1250 208671843 208671857
    0x1030f0e0f1c050d0f0617100e0a03021f06030f05060103030f0815010f030b13060f050a030f1506030b13060606030e1506032103070f021b01030e151006021c02150403 73
    0x505c0d1f0110008551107021510103806580b003290b90400c19246098682d810940002210b40000b90300003e50781d07141c0301280a0850000d00445111000f01580d900152001030507420b49800c1100c04114035040c0c034402e0321802490540d8103800c0340c60440413100d500541c140350507a03035861360041c10031000d00300d0240740210700c0e0100c0070007280c0c40c0761351790303001c02280307a100c800c180a00803542c07400d24085c02c0281d4210500320300c2c46e115181f054204038030103071501c00c000110307211160680d0005005180c000c400d01e01c890904000e9842c2d5982e450000b030312542d180c40c0c0c020900318464003801c0ba0104450000301040050342210720720034080a407a103903043c418004c03800e0304810180006001345550740e112a4980ca090b942c081d1001840540c4401150007001e00e268090505503180c08510b03e082c41c0c00a0003c41001f17005103407020a280030b50b020510344c41000010301031215994150340340365096805140342503420350070b245142015840903030804407a0308407004181035640d500a000f407618071 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 208674343 1250 208673093 208673099
    0x907060801171f0f0b090f0408072f09100503060a0c030f0c030903090906121415090609010c1403011e030c0905061516020f01030f0e0f1c050d0f06 65
    0x200d2804992000310f01468480000c5900c81410303100b0321031a00004d6072045014640001a0241903a00800080050401040301d109000d03000e50010b0481c0303900b0101d03a176040400740b03003064410740e10340515104241080000300500e40542d101400c48401170001c024588a16004201074100c10032583c04041e0b642084002c41c0405000d01076003024180c81c0002c51401034180100807020340c5d000f143d039503810681e081040c1c040101c21510350903000707101d405e100c1400c10102410500c04240703001909007240d06101640b180400e40038007603000f4070000c08c00d0803092401a02c01020604088507400e2092004000c1c0c00010004015060302e41d04801590503240c0d070f12250030a40716000740480350b65070420403602d400e000100345004180b0070002810400720554010f100204404020b0188041d40d000340c10503402074100c07507032886060302c0174010020301980040d55403d40900151140c401c900c42101a80a07819001c2103003d40c0e40e640c9894611500d90003070180a526044845041d501d42c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 208675593 1250 208674343 208674373
    0x20105090315010b0703200a0f020607020910080f0a03021203130203070308040306050112022103090a0b1201050d0209130302100212150a0b09010c06020903010606020d08090706080117 81
    0xb090203020340c6580704ea215551420002d002030000f413090401810f80d46c031035118180b400a44400780a5208045c516522940d2003c51848e001d10074009400a81e98024041c600010000250580b00d080d000c0360208080820344543d0303011314507000340140e0003196a140c4d000134145c00441d03002d443c1c581c111424900c2540400d1030002035500c2039540000c0842d060003005218000e5070300412175001c2d10100c05441da00044c821180400c0c14290bc070158015149034170505005030340ca80341005180180f910f503030b030500010341e5102103030094042c01d0100020800d40b40280100c049039030050003000302540c030411200031060104c4019020343c45120038117503071040ca600007801c52400002200d0b4007401e01c104c03d005c0c3ca028000c0b10a20900c00c80405001c848188030513511500d50901c3c00300c030040500d0503d04000d00c54508110b40550a100c00403443c00e80000f40c2101440b20341ea00d010086d6a6401c806440d1043c3d4040c4c0d500250b07200f0010400003240030140e141c000700741000e48030801ca0b00894 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 208676843 1250 208675593 208675633
    0x4050a0e060d0c08100f0c0503010509041a070203090414040804050d060e01150503061005031b04090f0b070f081603020c031306200610120510050c07060501120c030201050903 77
    0x540e84e6030701000e1131102c2c82100b401940400b0b141c640c001d05c0b060310058400380540c001401b0310b5000740c41500000f070500900b482103940042c40074025031054101080000d4403640300130400b03801f49092050164214650b800c50034482e9030444801806c150900c0c003041810980c404058840b1500c42d8072414600c00c0a200b0000a03450000064003010314150500d03041c507c1c000d1001981c0003002c2c500300031a450120310741c3d24144501090500b41810880050010044e02d440038003400003040c9400100044024000d002e0b00040d10703104210003801300101e401090445640e02c8403040100b04e02c1c0880e0080d0007603e4809a070206690820341000450294034401e6406500016021207550084202c501c0071b10540c2001880039180c03034900aa81d10404a42e00c0c410070540c200ca10081209120b010710200d001d803007071010140418100791410341c281c0d420070902624154941000090311003219088404296417101402284900d10340054995070829840c01d0b4150058284242c2c42d1a5480d103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 208678093 1250 208676843 208676849
    0xa090222090219050c1005060a0e13030305100612020310122004020a08040b0619061107061d01200106030f110405060a120201020321091204050a0e060d0c 68
    0x1a00d03201042c600c000e040c00401080f00500c902080807400d440d0001c00e82031040e04001c640070505454000c0031820300801603002012400d8403000780300407078294079030300c811b000e001c1ea9050141d0748621540c00505505841800041451125040308043c200d4029650100202074000709140d91403c03550141e03030903030350b045030410301c03101d015050b9000b020a440c0c41013900766021418015000e50103405008007500c082d0054003007000260b4156509600f061420051854084100c0d9039a41c02400c80e42440da1403d030035009055001c40d843d8420403c80d8103003414208200b03407626800c0c0c019103e1802c80c0c40d00f280ca1250000e00064030310302c24090b92000354441ca20800c0041442c1c2403551401c10194101d03417066051038140304041d903942001d981500c00500040070210050710050f440e600c02c0030f000d03c25244a510162000300041c0110a1142d811038050341d2049440700342c0c0714241d1080b8001c443d070108030b00d507003444801120925164003039000303006900c104800ba1129020307444183c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 208679343 1250 208678093 208678109
    0x2040b0a030b1203090607020d020d2301110910050c010605030f0f0105061503060108150d0b040311060c0d0e1612030915080f04020315040507051e0a090222 69
    0x1440c0d940e1906105221603c1e804654015500700315002c40010440d04c5403030406441001005c41a034155540c103050f02d42103d43c010b008482c00790714400510f009010700000003d9a510b03105d500400c0b8441c0c0c804880600d60020f2112000f031403108026900d40e009000b142e8420b42d41c8500100707130743e141004000340e00b0035020000d0680020311605a82510720041c02c403802035024002c0c0000495010060340e4010209080c8108030380e980c0e1a0a40300e1004600915511125008002c420301c0b85204901d402940a0783d10005411024024030750344030010740b403001408804008401442c0c403141e000d40c02205125042c0d0740c0c1ca01c1200344025501c940c070b030492109800b20518020416401c80640e0000300075441c0760004040c0242000b51050400520200041c0b140200140440d80c043c07049008041c81031030000080c3c182400d0507a6160100d0080e0707400b516001d550020a0009005003500103500203050803103050030003040a000c1d4002c04000c401940d00b005d61502d00000030300c0181d024104176 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 208680593 1250 208679343 208679351
    0x304050a0209072a0f1101140304110a05060702090412110a050714011706040f060b12060f180c1b0304080303060109090203070f1110110d050a050f0f0a02040b0a03 72
    0x7040d051481c00d00c40c00380003040481c035a00c0e2030000032070170280381d00c80e42e4100c0103030b01c40f400d001e1005940c444240e0f000c020316190004208020001c0750320201c081c5c91811350750308c50521703114400d0000ca8410f07150065480400d0b03a001900045148091070401c0d00c0078505240b034800e01c001d2a91800d034121700704844582003440c042c400615100e5162a0344182460142c148011102da809005000a810f19014580b524030781074514000350011801005000d13007180c0d90b800300c05190500c2000584d01c0c02d100d43c121600301c201901d4040312010803406492310704407558480c4980b0111b550710811010f100044514841094600240085c1000345924000303035070741c2d01e04500010700240c01c641040c580c00344103005011040f54403000355000c1020741d041c00c100006550f280e09280150041358800c070300f0305101c911400c840c2401c0180030402c800d1a01409103848600a2100707482e02200d550100c907448200103106000584a9280c100c204044010b00c1c003902c07440741c081e0381d901030315044c0042515 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 208681843 1250 208680593 208680617
    0xb040c020109050610051008060105130602010c030b27150901030b16050f0a261005040513050a12091208040e1b03060f0a12060912030501050102030f0304050a020907 73
    0x401e20400e0341c496004000d0061700f605000c0001c5400074800c02102c2007118101c0011241c0c1d02550440e88265501900386140c2070396001c009001c2c1500841c1800003d05100b180384032402c200000102c0f65514507228210382c1c581101c03da4001000a00210300082c007004c8040042c3c44c2c48803820302850080c00c2003451441c0420a004a0155034806001081020042020b0307103000301040e505044018a4064139051141e5a200c8040981151f4400e004190307006000341c0741c00c104491411604245c5c1d042c8040d81e05c4007401c0e101e4900c005000380251f000483c0c280b00160130074901601c1500c0d00d0510b00b65258492409400203c051401258102c800290511905040e580400d500214080d070f10106075540d810bd0070558040580268040c0342e03007034059003180d179803039403170321b014100100004804214138180303040940352038582a5150030381d403c101000c00303110f801254161241a00190316261600030001c01c682c3c00200150b03858010a0300c05070050380c0b2041014090511a500c4007541c00c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 208683093 1250 208681843 208681853
    0x40e090303010320060301090513020315060a0902120604020306010513030515150d03110708030c0d0306050102060403050304032010090201090512070b0f040e0c0403121713060b040c020109 83
    0x403402c4d88010041ca0f121030000d43d03a03607541007140e044d250507140104550315032814a41e581e40642500a40c9405500008007260302101c811a1082c80c003114840c1820b50f03611940c90403445a405000c084051440010f0700301e0a03c0c4d001503400c1141807410307a00c1c08071218403002003090355420450b03158100303540c00030b0f0005100122540000c8051502d03080300080200007440e025903d00002c041c003000e10303510128008148001070061150390250703665402e1150030783c0d032a00f4008a0440210340f42500100700c170b5100061542c0301303542c142c4074546552620303103087e5505100803d0b6440d581e1583c0b440040300103c14409104403000c514408284402148000f4199080b10340000e800f500c00d45408440c44400044e650041750148209943d58140e101803414283c030954120500c0d141c1c008045c0320403115103100070011203000d4101c0d09040c2082c0081283c48540c448445e200d1031441402241c40100b694441070801c910a001c00190b5426101c0410260340000401e400940d5440580d0000d0013 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 208684343 1250 208683093 208683113
    0x6010f0501030b1c02130603140601062a1e080a080a0b0a030b04080706060b0d060e070f030c02010e190203060c0c062d2502120d0b06040e0903030103 66
    0xc9001d08090003c18198000b14900c1e0070000d01a4454050500c01401507445000c88107100020001081c880b01e40caa017000c4510108032031010074a4402c1000010341e0754800c882c28543c0e0401c00e5045002100308850540b5640c0a13940305a8028150144080002d0742c400140d0280920510125071201c0c03840602a0051000401c07803035255090191200059990031050740546c2c1c3d010412213010303240c0c1d0030041454040c210004050601d00721020841e007000d07401900c941d450050b014001551a140c005150500a0b1000800b150000c031501d01c003140250411050351030b042c8000141b2903900200a40782113000b22a80e04201d10300031404096080c28403c2940c0100c098180501c0e115515035401c0c5e8641000b4400c0c09448000e142e07280c0d143c110000c0514440d05008120345690801c0114602b01c04400d81c0d08003210300d14954206103150000c6400c90f1040d030142506c40c10042c6c00b034003500c05000b1855495500c02002c100203c3d80c5051100494042e40136200115180c0d03044d0b06d4014411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 208685593 1250 208684343 208684349
    0x90507121b02120a03020708030c03190c0c020f1306060f030b0105040b0412080c01050c12150a1a04050915010f090f0b130306020703020c1e06030a050705040305030c06010f 76
    0x1034001c003060603000640000307920400304001940940c1d5104140c008400a000f8420300801005002003031088045200700510702800701682c5602c0010329000309281150089034980000c05c0881c00743c840580b41102e03000358480c070060300f00840c1070036050442d42100c9141e002203020845505a0000107517240c4505000c5520a0078a036140c5814821030460030700452181c0030340c51503424940300410801000303880c0c0a082d0b64000f40407034144011810b1094001c2d000868080354000c000507000f41d03100c0210100c010002c1c0004040500349086d450940c01d12010304d5a802400300310000c6c5075203c5a0100303100d540e55110907181002c101c1d00040c4981a081007500c10016200400d200340d0141d6412502102c1c031000c1c0e40782e51001800b60b21450750500303610107007189201081c2d81c0140341d000f20b40d9480441c000c0300d0740416000708510001c0310080343c00b03815070080e00a000045001019074001c64000c410303070070720300e0405a03265105132455100d40c070f502e1019044000104140e5440444035006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 208686843 1250 208685593 208685621
    0x90605150102070f14010207030503130e060a050d02010e030325020a0905010e070f0c06180b07110d0305090708070830090402071713051813030c03020709050712 71
    0xf0b01842c0c004401840c150500032003460000381411010710341c0c020000c50004540c40303c181c0b9210071070421900207941c094410310800140b4480054014a001d00c0080151900104001e0804030141c00455554881c11440754240c0300c100312294400100c1c032a0208544060403440400a01d248103001034040654880c06d9120301b071400501c582e244800301c40c0e40c02009890858405213603120700700e90079000c004003d40810b01d000c98103041c14402603c541819405030310110095200d8600490314070510700310044140c0c1020a1078004148aa0880e41d04500e440b021159078649a030940390400002d070344602601c1c0d00002f41281c2c6003114520346400f000d080d003402080c5a40d1000010014800c402d40544656030000f01a410030038002000c1a00d2070300d19000c151989003041d048401c403082406907900c2075081280c6113020310800c1a1141c8a2800301034a51414a903a41d001d0740c480140035001c40a500683c2ca010400e44038900c0b03000c1c45100556900034903086c0b488004011070f4954104035032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 208688093 1250 208686843 208686853
    0x4150e0f010b18100605130e10090c0c080301090b0d051c080f1506070501140c0a1409130b01050d02030903030604110903060f070306030804140a0b070b0c0913090605150102 76
    0x344900c2c0c2100c113801210b4041c1003450b0b6500600302c0c0c10442c5241ca4114401d522042c0080c04968030329100450700303442d0003042c00c0003103402c50030041e102661849402800131078104014858601c49411071481110f000e01151441c2450340d0f120317410800030707060b1018000d0805250106043e400f08401e50000303421108803981d42000002078526040081c0500c0c00766800044c044d0800009610911015907030007108130460401141c41d80c1164801c00720200000d00031240703121074281c8181152500c88004003d40c1d16804100060409131554006190500c0024001072102006600080d445449a41d01a699038580401040100d41204c1e1407903d602105000070321050718001034258102c11721540104041d610818110040c202c19040249a800b0200c1c001881801031031184d80c1c03182040703e00b010007640350241c00751030780280d240140c00401103e0201d5019280340b030050034445005009140351000d00400301054441c04c04046840b613a490042007102817115500504203103092000c2c0c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 208689343 1250 208688093 208688101
    0x1050c030c1902041b0e040506120a0c06022e0e0a05160815010509040b09010b03030408010f1b0c030c0519080705010b01081905060a2706050307050904150e0f010b18 73
    0x1041c1e075251450b507c0c0143e5448021030900d0707403518407550245e0401000c89031550603510b0b0040e600c0d1113038402c200c0548140d8034440100000e103402c15650b00c020b6070100182c80780d100040400b5048495010305140110040380000c500144480440104101c0354100002c1c030341200c1d545049940080030504440c0100140401da60702103440307401c0780d0084083c00d420f48612980c14014802d00440951500c00085e0000f411801034100032254003040804200c2e00c2904142c0c00000701c0c15003401000110002c080300c001901880007000018003803000c94120000302c0644401091003043c0035120120302041d92010040b09028448041c03000386001000360904170020080c19a0114001a00c035032600c0002d201520b940c5802c1c0e00900080c801d0382101a201143c04042d441c0c02d02c110071403e4104900070402d070030002000c80480740701500c0c000c05603455456510200350601c40700112151903001c0d0b0001180c041000c402070246907800004d01152080030014044280b1130b00c052100e541d48100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 208690593 1250 208689343 208689347
    0x1081b1605150606180406050603011d130507032406061e02160510050702030607050a02240a0b030a02040c0306060306170307141c03150509041101050c030c1902041b 73
    0xa102c1e080b180d0802600c0c50310f00c00c1c001030087c1c00300d50480c076000100400002000400707004050f100d03180d9101c0c480076135100d000c0d02c0d9404218000317010340b01d90f003c040d041002605550540c0c01d82d8141c1800d000c0c81c164403810007019140d09900510029194085540302040da071007084400c0b50f060300003460303c2c0d9100c403c1985204514414188910f82c2400e21030350060164044071610382d8004e09031003003454140005415038100341e00300070041c1f0a04500355070000348030035400d100400d041c1ca00141c070313030707410007088050710036507924130380500400301c5640047e1110f008000d40e1200350b440215256003410801001c0301d20341da221103079408040f6049540303d030003c0300711003115801006185610b000d503c5014541a030030780540340788102d20f41740b950f5401d60540c4144072001072021440441e035030b5141003100e078440c1034a018102d01e0102800300803c2d030203040100141c1d882841944c0c1000200e0390b018fc2420b100c20007205041c106920441c04511382032158000c60f800040c8141a1a481c039440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 208691843 1250 208690593 208690597
    0xa1a01020703080a1103030a0203040b09070803030402040906060e0403030608010507030c0914190b0a02120a0e0d03020f1b0901052b1a0103030e040e07050f01081b1605150606 77
    0x2818144000420340c0c202841000703051700507480c20b03041b01c3d602d040c039002d0903000b54001c4a0507603035a404880800d52162300410500e0460314114011403c5460396000c120007030401d1103045030803554501000504040d040e907900e00c254001c3c0c5000580910308611142919802860314003010b02d0114032040c0e040d04030903460240c1d40068844c0c01109814000304820109110281040c044100c00004005070520004c2c911024030740e098900c050302912510074240039480b001d1020030304504e000700c400e081c0f06040388000c500a1049401c1d081020010b2030070100c5690010000d0f1505560071a038138140140748900501003510303003108482510000e184100c180030690392201030003030402c40c24060008515841c42428580307480c40355a403071401802c3e01c1940070032540902d05205c0d05605501011841c1c500702d941c0034022400c130362005001124881401000d01220315008003100b1410b2204c10042c10707002d40c0b4048111300c034401c00d040c56407411201407804200031000104005140d00d903c02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 208693093 1250 208691843 208691849
    0x19030b270a20090c190206010501300c0e03070803090102070b3009012a1101090602070f020102060109020c1903121407121404080906041a030a1a010207 67
    0x8180b003a410030035903103040724402c0c00545540402c400090200145541c0c0c020b00c409143c5080c4810358500c3c940c001d0303842c3c100910426012503501e058001c0500e681505a0540781c000020641140400008500480e030103160010000364600035008401d08042104c000602541d400840c10030381c803000002e5072410345000e001811400412086000064080600c4007a8a607400c00b6904000018903680004d40880b102ca01310741c00d1040d044031110303e103c49040d001c1c940365000710b00640030910641e8401300d040301c044031565030703000e003000410140e2000d040c000f841500700348410b81e0280002403070414180c10160010744104000c61035040002012100c0c90f2607003040e6130701c030b150a007000d40d5a41c1c25034410201d840e060040251500c000c5440c010b10031501a10748100400c40c0307000c1c1c1011241c09140502592188101050124040001401945600030122803600c0c2d00e6804200b000c1001c08018881014044103005040d405405aa046030002d1202210702c15030190000f560740328144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 208694343 1250 208693093 208693103
    0x14060408191a040f11100212130515030601030b060c0606040b150307030c09080d0206040f060b13050108060a1407080403030e030f1308060601050a050919030b270a 72
    0x1088035041001d02c0011941c4004644010100740c641420400b08028143c0400c49080046031180c681c0c82c0b03070206081c0002003140c0c0c001c0c8602040100c6441d01d1358800554010b4100c107281000485660780b103040e00030601d02200d440e85900f030410014095a06400c41540f1804040c8017a000b5100c0c009206640b00204070380100f031a40c840740c0410041d0a40010720008144004100200507406400ca0b00013440c0503a10003941664a82c03440343c490005100c407000581141d004140461416071401020038000c80c00042e003c0c0302d000018400f888484c000a61440d10380c8010040c5900034000740754814529030301800306d00002c00d107210010400404000900c44441c0124050601c29801b403010402820103c80e07880082c07240c00c440540103e84515007040a650021440480111b401801140180c5460f4101099010180d419801c40c1034001d800041801f01024021038504103800114001d511820660802c0c12281c11400321341d280c0e43d40d4400103003804611909d000100081400c0e004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 208695593 1250 208694343 208694383
    0x303140904060510030e0607142208070e0717061003022a150a0207110d2103020306041506140705160605120a0b03120702040902030a0c14060408 64
    0x304001034000c02403900440e800c100e0182c809044980c240d40442145482402284c0c03070b650300d070242201e40034000c0b50380c0009080180840002199540d051514403890095540081600c8022280c03900a084c2d00c41c0c041031640a003032054803608107882c64421048211081039030324240010901342e5003000c213600200742d80024941003a600c0020b00551000c1c030103070138803030b030348010480326569607500c03191a005003044001059480a0900c22030b91310647c030031050300d440c1c002c080c02c10100c1c1e00160026500c02044c02007100d0209100c010003095945d0396280161a402c0c00002c3c001207070b00003c18541c4002c0c07004014024140c108400844448032a941300d5034580d41403501e80e0030a0f1425440001d1829140004541d15400001800030300071030f644420b01c01da0b0750404a0042d100003140c01901500420000031024003e00700900020b0300140c004070b100e03501e130741c042850070b101c03010141c81a581d88101031005213400e4140d00c1450f041160224242414080c0482e03c4803252181400700790b00e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 208696843 1250 208695593 208695607
    0x2191a0f04061b1a010602070902090a062d090f1502212502030607020303040b0103021011030c1b191202040e0307150506040507020303070f0509030106080106080c060301030314 78
    0x7a0341c07100342c00781d00003000c001c02c5121341c07050b0701100d5003809804098003540b000403c81406500c00d072215020000e101454413444e00d50191900d28075010741040f400054004440719002c0b0885d0b89020368115543c42da0407500e0800510f2201c00c86030080c001d010300c0b540c1c10b13007071140d4001241200210640c010041c2c00c6a00f00c02140c0c68400c5500941c0584500410160038000310072078a00301074001c1c0c003500c0c8143c1e55003200301d0302c80c44111002030040f48004010302c05400d0241e607071400d0f1259401d00d02d5011500b02c2480740765400203a00c4801c240d02184c088500d0007000d81c03650209910075511810760000c407083d140c0d07c030141d40c0034444a25408032480c506640e5160031038040030f5900f5060340e81d51031950405801c10344204a404402d20b0038070010404e5400c10703100c0ca034850b0f81c10354051401c64136a640d0454900c660b812990f01002410b000846141c0c0d000e01c5003900404800000294503490003004034100700c3c0e183c1d0414400c3c0000d0004102007904000c3c0d1080a85000b40c02d42e6031349003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 208698093 1250 208696843 208696877
    0x4030b041b08120d0b010e150313061b0f03060b120405011103040c0603050105091302010e01020a1209030512031302120f03030703090203010f060305120d0902191a0f0406 75
    0x89a54005100c91103400805420f41d41d440e4010000364004420522004502c00e0054604144e58402c50b13401a0360064490f45043c40c1902a50700400711009111030010300b52200e070251203904096440180e41c580c003a045d12601709900c142c48041078101400201d14140040590b40282e58046074400c200000150070400c0030360103201c00c546520011900c908060618980c400650f004007000700c2d00d00000443d29203025080390740700d90001ca10508003400940d0045a003144102e1ba0603043d072245100c80000a01103544c2c0000d600400da40d00c1180310700c0d5082007841e003140d0204940a00364100188040301c60f14400403000e40f030b010ba1340c0138040303644201d041c3c2c49d25041104003031890002000b8490160780c10b0308030540c0070340210b000707100385090b204021044600358880280254492550a0304e0794500c3d40c080c01c4022600000010182050707000700b10100300b1410302c0c0c41e0058003e0400e0000720180c038581240d0b01d940c2210f40b4104180c50a900308284201d003e0300040c41880070034001019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 208699343 1250 208698093 208698143
    0x2100c12090501020417030f03040602090402120405010c0e0f1509060d0e010c0e010305070f0e0f09010801050919050c01120b041508100b09010e0a0b060f090109060504030b04 77
    0x166140341000307034030000d04010307000350094081c2c01110300c41180500c11082000064400e0729452404851454a0360713034030040294005006550055001e100a01c20140d014188608c243e024400214910031070b100d008000000500c80325103d8507070070003400c1c540c0d1519440c042200c240da80c030881da20360024000039030314003466414059030703401d11130030b41c07a01d2070190008032100c1c040b9183c0300c070b285074120019020307a04211235081c000b4269401d506e4003903100c3c0184120a103400341004218180d07480c08039503c40001d030488a0300d40c0d102e20071f1110040040080120040814841c407405880d1695541e840700d07604000d6034104260300b0b03441842d0640543c01202e040344c000b0403c01201c1035152680140d0780f141d105800e21400b40b0b11108840544a0040800c0140700414840e807580c07c090003595035480103004000025500d42d042035407034070350038001c00c151010b0f0700040340c07039019080004100c2c8509400071410800140000c000007030308016000d4102e82d00c89018800040484c001032400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 208700593 1250 208699343 208699367
    0x1f0323012102120f06060a061d06040f031b080607090b03090106051807080106020607020a0f05030d0c0c0b06010f0f05090f0913060b090103020a060c030504050607240c02100c 77
    0x2c089440c20800d000c3c0000780d0000140b402c04156240340d40c90b030b01004401d081c1c40c8aa103000c82c0351000c50301540304801070143d2000700e0061181c0d0405446a10b843c81c0700c4c400750004c95440c0000007904058154445800c0002c0107482c009200c240f502c1080140700c0359452141c90700340350011000c500c90700404c1d000070001e45009022042c2901e48600c404082000946600c030129072040004101e40e4804225a4851a440d40043c0b20f444500da49034006032041d980c066502c0c0c0024000070030784003254042c01002d66980e545081071a0100d090461000c000606503030b0501421900c03104c01c40360030a1240009003540c1c208580c071480036401044140c3c03100c0700e035039034044500c01c1000039041803084200c1400340222010071000b1420000e000e0810020b00001e913104041d42ea040069a208209a48620380301e49055401c040c0e5032404920380c0e8101500c00c031200030ba003802c000f000503d04008003004482a0740c0c180645060940082d4642c201c90994145079a12289032301251800b0382d81004070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 208701843 1250 208700593 208700599
    0x20c07290d0b03060f06011706330301060c0c0b070309050918010c18060c0f0222090c180b0a14041d0d0e0303120a1a1f0323012102 58
    0x20711720341241101600b410441d82140828821144003140c8a16100010300c0380c40083e000040c071602c244130002c400d0a881c3d60701d40781c5800b80d656030306600340403001950013410307191100c020202652800300d921201c103400c07072001d0140a02c44140030a0f40b00d64000c0c221402a2481e010581356090006114404c0041000c299030800341503800d0140d01000300a012942454002d60301512001c04640105151201410b41114150400c015190000c000d15030040004d0b140304078064115131500c159008040181d0350051180010880f2403220104600b00c001c000808008104c0c0080004602e220b4030301680c1c5000200e500c4920690f26681d01c01130403031000c01048071800103406c04050350b40089552032800100500118a41810000183c84000811103170006880d07880d00c010174018440c0f264000c0c000010001884072640b038154406007814010000000072960048001d02550310001032054201098585002d0201608590a064501619945d00c600481c0341482c450b003910000c0c00b941c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 208703093 1250 208701843 208701853
    0xc140103180b10120c090e0c100c020103050a02042306040929041e0f09080304030c030f080115030902040f180b060108060a150215070201020c07290d0b03 68
    0x1c180508140320910907859a110030340b020751600c242502001414078024914500c0d06020f100646080d00504028a0318400305c134140c8030300070000340c22600940f0f1042d0105846a40000a65074540605580f1800f1503600398074103485c2010005c4108400784a001080c4001c040210300c41d5520030031107000308075280c824441103541e85c0d034480da16005112018018003040c1189569030415004036100b810310400005d0f006228080414041c008810460036013656400f0050002400039014500490107036490b4200c100315480d000e440041cad10740e5014141301080004000d241c2c2c0c60100b6201044071450007140b89030540c401700c0e001e0031000700742f480150304002c1c2c1310320703c3ea0f103504100051a0140034070680c0b903101c0f01c0040da200d460581d5895000b005105090082c55114810350810703150a10480702003050b40c0451a44e040002d807034010051f5000074080410803c100700c10400b80c50203001d01c0c400c280e03d41400c181e5038100c0c0f810310301440102280c00038400c80b84d0b5210544d03204010b02070754 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 208704343 1250 208703093 208703141
    0x60819110a120e010608150c0702060406050c100b0310091410090c061b060902032d0106140303071b09020403030206041208060f130b0409120207080a0c140103 70
    0x64400760461280702c1841c0e1410000d805a080140a05002c1300c401401074071700304102d491000c400020040816100e16000c00003480185c0390360004000800c400d517106a1100c0309011a01d04186120011442e070a052040c00f03a5940d0300425416040d025118000440442e00d1900c0c0e400c0c2204da0130f107220280540113000011504680151080314070035405040d02c56212103050710483d100800b6030f130024618142d4200058181d0344511b244500060071100301041c071556490400c3e61040325083c3e245108403180d0031301c0718240070b00d5014000d10340401d000e8071070b600c000c00e6480c000c00d0009400c0300301a6045da810000520900c0303020300a0824155680c0d40c40303043c042c0d074482040c0c40881d1600c000007140c0b4119885072042c42e00900d030040000524850b00410400340060f1082e06451466558100d80c05a954501c100e2100354030850040311b090342c0b00d100290405a0907400701150381c01058066000940c0454490140c943c4046074940c42164900124010100782000c072442c1c400e040819 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 208705593 1250 208704343 208704347
    0x20a12061d010b04151b060c030b1005071a07030e030c071a0406120e071214010506030307031b0507090509060610050408030426030a08010303020610060819110a 71
    0x74498601c040490709075a640c0c0c01d01464184950310803125140c2c0c484c2e0703210007800c2c414882407240c9181e80701d0512140050ba282c90303084400d54103c0303d0100b966007504c02d0309410300115020100c0d00a0401a0070040a6101c1400340425844419909561000041e0360380303000380d101d9034201100c0c500b01ca403201056049140c1d944000e020740340c84221700d1405030350040015011a0240c4d900c82d61200d00f00c04c000e1071180c02400c1c0c030913103514580c0a82100403a0000c1e00301c2d000019a40124082524a00d4034230605084400140c102802a0010400200841d03000400140c241001082030190213030705042c1142000c842d900002401405c0c0018840d10000024009020300d0b81200c00d05405089400c0940d40b170320440c820300403950024001001650300c500c140b45061074200c810420360001e50032105003940d01555000020078282d40040c41411350400045501c40598070748112100c3c10304101828419008050000c0d03900c141120050301f03901c80d00181e4046100312001a11000c0038000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 208706843 1250 208705593 208705619
    0x503060619021f0603020607120207080d05040e0606031021020d030909050906190e2b0909090209010b030703020c07090e190b0a09051e030706051e060103020a1206 72
    0x4214940c0c4035035100d110080205201c0d0000705ca9000340000e00e420b81076560741c035508000344100810360152a200043c0d620060007000f90b94005681c8069946081c50210708012401030070740e5006080502c00c03c10300b801c98103401c10079244480c008140403040560341615541e000f0400030b4002d52240013540406070030840b0724090710506101400f003691500465940d41d2022140c1d5502c00d04031502c92001006141e01080b0101e51450079218110301400e007520440034030004008c0301a070a1000e616103558044001009007012000c144552243c54001441707154040c00b0740c3c0c00c0840d0000104240b54000ea04a400c0e1100c00001d540c0d4542d9985440c01c011300312900203005602400005521519040041590465201c0140815522030036200c40c000d14501c0d800306d03020300c202c0c00300012116501610280c8004081c00466480006142031415182d014001d024019082c80800c1c400000c28001554030000078030380185c403030a04038400c403120950240900300c0e02c0c0c60090046038441c40c03100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 208708093 1250 208706843 208706863
    0xf0406090906060c03123605071212031107140c15090105030112020a05061b0c060906090405041e21020c01020d050304032604170c070501050306061902 67
    0x1005210740c3c40c503044c1c03520308400500400041034601d05c00140f2000d03a0025020048680710076512540340c81c2409508490000d00003c0a04902000d9040060070000800079081c265136050151486584a081c040328884448042c1a1940200000c00c108007064030b031400d4111807605420111100095252040d15051900840b011040107030340511180c11204680b8041e541c9606d16864400c0c244061598000100d900c4100d0070400030302d07a61072034043d0041c04595000341050051070700344039281c01c5038910003600503d4140060150b1703941e07071810b03120038440c241c40c0459503607101d00d495002000820516140c480d203005500c1c0c18800008255507400c0c8003c481c501130303180e805005980d039070440b4155500503402001c40440c22403050020310340040c03203400d0008111203103900d6543d55003600c0e81781584140c0250100414440f6162031080e02020543d400ca00e030101c60000c85483d0020703801030780d0500c400000412072a4940300112140d4614042c102042108a43c20003910b90f00c1c510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 208709343 1250 208708093 208708109
    0xf0b03012403110d08030f010914010b070813080706020109030e15030c1c020423040507050a0f1b050d142a0114010305060717010f05150f040609 64
    0x10200110040010001c04140902501401881482c40e82c0d0105090002c0000d103070415188000300300001d0040d0040d600a0403800e044018a6051001190480d5800528420341a4540004201c17511028044440c0b19400040702642c40305111135849001c0410b48c4540034620070f50600080c0e103681035100f002030501c0b96039410b18040070681007045607040024540c0524008002007448841e031b0a000b070501703102150100d24506007040c030382e00890300a5032050100100c0900c2030f64503c49226044810702604650811080c1000b0400400740e0140425410920030003a043d6001c01d40944072008244990380784090010381d00d480d1603030b11240031001590115042e800e00c03820910f04201030360844031220981620701c6100381082080048071140540c0103558442d20880c04084110119020354003500c014041800d0030741c4c1c01000c0e400030110800c204680440144400c0c0b14101d0b480e41203075412034814440791002515015103100f101490030013890b00180015101e41c002100008952a170 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 208710593 1250 208709343 208709351
    0xb0a06020304060f08041203021c18031b11040c0212070819020a05060406050403090806040c05270103020d0c1d0106030b01030605030a03030f1118090702070305030a0f050d0f0b0301 80
    0x515005e440400c001e83c0c0081c442e49800518000c0c451080d03002c0d100c610364030390022082d054540d544c8800c0b00d9103c01002c2000310403260540605801c020070500507914240f240d4040d2200d40c41e0419440d030f03c15101d80c8104d0301c0d00c0907407070124070030800086414455000680c0d2910903140201e119403080c0201c14010000c80d60703490a02c1c0c0046245d0036542d0f04035000d0300107a500c0d961b44d48000c180042044041c0214500301080902040095505c00c501c180d0603000100d04100401c4580407401c0811402070704040c204000c00080702d20214110780d41035403103110343c1009103407a08802d8880c0d0429202c0da19501d04036502f085a24100c0c90407103405e074504101d03a01405d0011019035003603024a07505940720200c540300191081c0e22040c0c1d91011040d00003400550440d20b04042d0b8065001000200020310454401e840d21812168100320180010038106182da5102c035100d004102500080c880c0001001007503a0040c411240005140c000800014845188a00c000c160780c114440c0250302c0c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 208711843 1250 208710593 208710617
    0x203040515090a0e010b0a032c160b040b04030f1103010203040c060824060304060f0e01020403020a0906080712050708070f15140415090302040f020c0d0206190e010b0a0602030406 79
    0xd03603020941a14a03400c1007518200e1003040940190143c4203546589c00e80410141049034600440403c1c8030141101030014200b948e001403506801039008400b210718200001c211038000d4800311000c49501c000c1030200d411050a00340c04016040e40c5290f0554000420481044010519603041c6e940c6900c0310205605c0d00e01d224034110111001c0e03401c0940302e0090340c03038003403601c000a140c2c01031040300b011801c0381007042c1c1c450030340d40c84021400309a90045020300c11464082c2407400034241016080100368540841c903030391400c042c07041c008141d400101c0c00082c41024480c03100501100011039074855a92a40210b01503440d1143c200508114041104403501c501d40000c0c00340407446000d81403170b0501075950311a4100c0d00c0c86a0a00c002c0600000040c0c50f039000d00c400d80f051241d00162240d505940c010f0a012515002d4002c5402000800c08401d0014102008003070048500040220100021900500040c0d6100758020b041c9840000c460394000700401c140d44456440d500103a01c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 208713093 1250 208711843 208711859
    0x30d1a1e01020307240903030515010e06040308070c120b06100215040305031e1906051008041704082a01031e0c0e061b010b060702010806100203040515090a 69
    0x580c0050180180c004103d25004244c0d1040c003800c091002c086414104082e60440504488a6000440100e40c075101080a1500701c0040c22200403c01e09080201c50710207000590300d0f210300d0100404400c0c001c00c00300280312190160202500030610303c541c0e441d602d42400044244201c2e0b5451142381e41d00817010b01c076072001c00c0705a09500400400d03066500c40343e60661713254000600100d5031091180c604e23040b081a94408500840400c07222000d403d882c443c41d4000d803107044d013006001d8500f071000b950031554045546a4002d400c0b040705034100c0a001d40244080c800c0b913005084500c903481c07400040070b5111400700315150303130b00c0c607042600c1c003107139005406542102401720200c0d0001c0c000100d25003180e4111841d05072540c0b81c50702d0b00b2100700f00016200e400200c2d605c068120341940d40071040409100d00b404100c002c882d0300b8140b548543c0001c122070300003801070b03014858501c0c4000e8094003c200752009000000d00d4143d680c522400c54010b15000507000d18803400e200000061054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 208714343 1250 208713093 208713139
    0xb0408011a03100b03010b0406030b04210807030f0213060815040b1302030406020c1c090807210201120c03090b22021905060f07060c020c0120030d1a 66
    0x100c05800f0302990007807120050000d100304002950155210584429241d849119290245114044440441c103044c282010100c0c1c0b0840807554050440c0103400300203070404ca02c594000c1803440c0214002840012070700c0a4001e500c060640c00ea800c50002c41c0380d640001030240b04030911090080320b050703e0001c2205030340182403102e0304494002403400882c0c80c1500216407090040300d01501c2c0c02c22904003c0d10b0141191142d200c601320b03c042c0124800d03807090740c6400800d0b11000030400942064104200c480008560203e040a131440e00021a4004e80b6485803080c03100c04104034001020201401038841d03004122000f40c840300c0041c12312040315000b40034103840c0303884800103451a40e090021040c503000072030310350064458001440780d54034002800003403260b580c03071510748185e031500304140da02d000412810740d001728000c418280d078400159001d10010804180c148070411200c1d500798499880009503041c2001c24810301400490300300c0030754402c06e595020070449070b50847c12101d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 208715593 1250 208714343 208714391
    0x90a030f030b0414090c10081b1b0d0f03110c06010e040218160305090f0c0411040e010909050705060a1b0201050f0c010504030e030307020306012303070b040801 71
    0x803a80384a584010944039500c149095180030304005050442c2c003c1000d0035040c2120b050391164020500c1c03000c107040800340601449001e0600c42c255013400b00c000200300f202240f092107226800720340750115804241c0040141840c01c1c0c203031015032030a4140201004158100700011038141000f22100e00c06003c01c554489500380041d09080c0d00700588072414100141040e82e200b04010324884480e140c3e408000d0041803001903603500c0112489000e03050b00c01c01000b003085600020903001e07200a01251000c0c0100c0101c500080021240b030603090280950303001003108a20800012910411701c4e070051a08a014408072400e075660782040280314400da80a20307000541034960109030500c051003a445407441410050f0a02d00b0381c500741c8682d07800000e04102c0aa440344140400d00d6042030ba4545501c80c00e6028600d0412140c020994602c418032072900c04c01c82c0c01000c060a021400704440401100805890b0b00c2c0e542c48503d00d055401c80c3c001ca0445500e05003031303503418007481100345540c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 208716843 1250 208715593 208715597
    0x2060717010e090312010906241d12010e030324060703030b03071d1006030506150c0f030f0a080108061b030a090b010b0403170309061f0302030106030b01050405090a03 74
    0x105a08180780c0b03044002020b805880c540c8800e1060061014008903581e0281181042c0000c0e928a0483c0381400824201210000365a030100e2508503250710200003010f0a800b040321071b03030050035000450b01240c001d0065041951901c4990049840c010000b0760103801a00e5400a41268520181a2110104025030352003001044081c00081c0690818a207495004013602c110a544000d01800e041d984400003882c40030303400400003c3c0c00d604506901400c42441e0402192804102042401050440098001201041d90440b503501080203000005480c0700352902c42d81a00f210100b1340c1c11400b84880416060b02c008a030202c0c000400610030032010b035495505400c00d8049510300d03800540006882c5445030064804940300a44050082880600003940c2da440c5090001c071802440c10ba881c0204410000d2154420001804542007000d80301c0c00f14034206000c0d0000580b24060380004d425500340340000050020501d80c0e2030481e8002c0e10248000e070754042040713440e0a191440200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 208718093 1250 208716843 208716887
    0xe0103050c2505010603120305010503010c0c0503041a0d0204090510080d0c1502090d0507080123010312020f0a0c0906060503090a03050306010e040f0603050d05030c160206070b04060507020607 85
    0x102e121912034800010a005000000b107150f00c03611030100c048081c0450602007038491004208170308091007020251003076890b2204540e0000d980341307600c0c0e201d10312032407d03100d454000c00d180d40d038400803c5030958a0125402c55966684a403c00041c00d0200c2d51000c008420100000e100c03040803400c0c0d81c03c1c1e25150749001198100d90ba0350001004080710303500c403059082c0f00c10283c648900d14160200c50040008000d11031900c44411700752104140c4281512280001015510709a9102c1a040d40c1d403003909010f0082c40c04c0c03404c03440d14100d000d80194910407031960106101c241c540701c42c10f40e4907081040c000c4a40341d44054a4a20003a50381e00201c0d03206124882c0801e11920182d5088032051400f5035201940100103401d440d2200801100c42d40c0c2d43c01e0800c10010308024802c4010b145080403404d51504140b100c8950117001e000c0741c0e10b01c1c0f00400c524110b50f00d000480d40c04c3c5500c00010141820a410190010704044486001610400012403607046c01032807072408030001500c1d012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 208719343 1250 208718093 208718137
    0x90e0408031609120b31060207030e06040b0301050a050a08060a0c022103100515070b07051614060105150a1b06060b0a1e09030b061207060e0103050c 66
    0x10400442c0e0003006400c1180c0070700003056a011600030052145c2c0101040041c5052440800000341643d500d0b4a08245540102c024500ba10014003600aa0449001a01da40442c1403c3c0c071042540f00030345a20034030000700400c045a4107000355051f10340c19034024040c00c1e121818081080158010180070b0390010000690360020382e084548070003003d1040e40d080449030283e4450004124200352100c80c008400c10404645403452500182070450b410030880b000c0c020504014410104080c040301b0140c000520607074040e0007101c1c0c8400a020701000406124103001c403d40c206022620310f80d0003180000603041c540040402c0d400d019030b00307c161420401000603106945480350f20b910b104c078bc02c03d847d00420aa0300c540702c0100b05c9401c003955208801da030014013480d09141289040810040e280c00d0944c0d0201c01d00080d60362000d494026074559800040e98003440c030b64145024441c03c0c5020642d260302c0003829906900a0301d00b480181c54051000e62a400740d016003a520030200d04900c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 208720593 1250 208719343 208719361
    0x801050909010605060a050703020120030402150f041502060619051905030d08010e1303020d080601020f0d030213170312060d0507060e0f04050f0114121606090e040803 74
    0x2a54000c00c01d900000b450380e50380d0020030780d9900f150103080c02203100400c80e0302c18540c0a005250b803420b001d45414000c82a2103503404424003010380043e000740a01110701c2c3c50781803d40b080750011081e0b090f24a8070b41d41d0340c040744589040c0d0500010018001e46010603460f0803c80d0002c281c18605402242142e4248824840f5040c0e00c001d808016601c0c0c0040000c04d51814813165014049035130b1180c0841d814002c250541c000007410040102d00c0010314503010a40c0418a20f040c1c8c400c52402d20302980362040100d180103c5454601800e01a03d05808030a1f90180e008069507000c918202007401e80c1c03030880d0400c1040c0c0d410130a409810403c003143e401c0c4a521411603010300024403981c05581c5070340b1014a0180c0d15005500400c21220303c0040d82c4c81c0c1820400320480013220280070515164254034601e00f018815080700e12001504a40940c1d604161001c04400080440d240800301081806010013680b0400000c00d44000c07011446501308002e40307108680115855185888000c2a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 208721843 1250 208720593 208720609
    0xf091d0610051813120302072009061e010e0409120f08010618030b09120c03071110020d141c0609051003020901060e010306090204080604030f2f0a140a030e0402040501080105 77
    0x610003011f60810411000a0f6030072411300601001c00703040c41002960005120341c0e51006802d091060b0111100ca01d005004040003043c294420b180c1a01861581c0001c42d01030561702d000141400309000c06400155403100640280d000303507680345030352a682d4000070380e0111030100100d12400d2a500741403011038040e2007042d40001300802115403e0240e840060455040b00e601424690000200701381070020759000182e0200d02240c0700d4070614032284c2c0c003030359818801507988140310340e05c0502c1c1001c1d1454802ea0b181c1c5039009000703405484c1d0b0b21444000400f00b1f8011815074030306d000080380310200c00080350780c00c5d294090400740280e400c00e0410f9501c6055000c1183c1090740b181c002080c2c8203c14001303000101442002464142085d141c0581426036950106d02000001c4842415441c0d0001c496041551003500c03031114030707a840420505007250090040d04114081010702c004010014961400b140640c0d154032003103c0d814208016446030784180d60028008000600c81c81c504010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 208723093 1250 208721843 208721873
    0xe101a0a230a03050304080c18062e020a020301051302060708030a0b060f07120e030601091107050d0903050f030f0d0513050a060507030b030303010f091d0610051813 73
    0x2801d41188450300040e40d40b000541044401e0340000c43d04012a1100300480510702d00103c420f0340e00704c050f09620014100e00100707454131074452120407010450702c40d140154881041c3e184180c91101880000e9925140000224043c3d8038100010b00c0c8004103c007504c02c2503600400b101e00e0325481d034641081a4001401080c149035880c0c0c6141c3c5c00395240b20003441e507004100c400e26200c0d020350070150403d281e000240014045408141501581c02158590549291080c005035410f080300742c021041c064640014224031400800440f41c41d0400100f2003120305c02c2c41103600030042000c205840b40100b040d40042c4000c1030007880c17005100b940180368014400c8a90340207107200341d1269843d180040b80b0658050395990180080581d05d0702a44c08810b10650046145500d000030542c1c43c0c00f018424090b8035071307403030207a048005403020107151021291022103a481c2040360102d00f40050038891180b08045502d0440380003003404200501c12501522104020700d1151a80d01c3c505089032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 208724343 1250 208723093 208723139
    0x30403030c200a060507020a0f0204051f0b090f1c0215071505010e01090605010203160215030c04081903081504020c01020c060a06090e06040f0609060e101a0a 70
    0x36821909840b9104880d03203044101c140101040280350511a003101c40242607101103421441008022650a0000e1001e443c0c2c190340028056070780f02482c114084004105800518190400207006042d200141c0515001286d413006007406a02c100f15544040707092001442d05400d28180161420100c082030f0303045241d07405481d000b501c0da141e5901502c034032500c85009a50300c005102c1504010348442c05000d400000f04140c50030040041c1d580c0c02038841d83d0b412164052021030864a442e2251640002c071015029142e0828044401c1c40f904140103403280d610450005c01c80344c1c40340b04040c0d1603458140e00e0304086619003110b0355900641e01146030340c119808022061001100744010800c2c6c628150180c011424210a90801d440c5280d01c04081c4c00d04012549240c500c2c0820850741080d03000100c01140201880c045024007070b000c0c000b8040514005c2103682110300420b4000210114a80030407410000489079112400746034030080d04000000c1e824002c2400240c10901200046 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 208725593 1250 208724343 208724357
    0xd11010c020d05010c02070b03070c140111042c10030305090409020a090605191d040302070902040609240801090b040e0105040807020312030c03060d0f150e1e03030403030c 76
    0x1d80100302007000d0920212516995501640c10199060000401070072000010600d5070070b0060f0001e0840510381009062600c1e0313642c00741c0051009621449904030140715050f2125500c000014140020201045901900381d920605141d98416001e01c150742100324803205a06544044a032500000700e810b800c10790315840c00015035240c5d0740d000700519a60b8008201181804180324a981c03641807040200b8880200a004040170401040c4038040c0e000ca401141d81c0d95800c081b0301e0b0400550107a000d1610018002c580f5950162120058034140722040c109a0341030031264030300d140108541e200290003480148403124194020344502c000007000480c0b420145d00c522800c44000303076000c548a860005500003181420701000007007a0010449a003140303031444090340c1500c030091919102d80158020a420020818441080282c1040107070320340207a121b2031070000702030485c4440f0541c4282c0d8040c0d0070307110350040c4c01d41c2800701360800f850a5072101d60b41a805059a59110340600c601 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 208726843 1250 208725593 208725617
    0xf0a021c15060b031602060f04060b0a0306060e01050a23090a020705030301081e061501141b0703031b2a0506190801090b060901080c0904020c030c0c0f0d1101 70
    0x4034040c003009007000c0003ca03992030500c3c040d0140320600040350003055401420801040201c0f55441a81c443d8021a002c80d486003840000b4080d0103007900014402480c3c86004205840c903248902e06031041a00e2010541d0b84544500350000341c00c41c03502e080c0c1c0e2884552051142030022410b5005000c0e080c02500f03040c450743e00d10f41035802c01d0300410003070307844180180030f080031000c024900070284102824140c1000d101e51110321a042d88410f0601004121803030340070540808641684003008180503401190f07149003921280e5610007900000d188244850200b150f41c9120480d0b190710002d90395400d140092001c038440800c1c09507401e290906200040c02c0d454080c02420380c1c080c0341c0601c5c201104000005004142d040e0001c001c150301e040541d1500b43c40e14002c8400e1410709007880e10701582c80c488500c41c0c0748211450aa007141c00031545084d8410004060304550740d0101c01c2c0c0c1c14240c141c00174880c581e2400c5000380e070702c0600303410344002040528110361145c43d01890303c003108806d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 208728093 1250 208726843 208726883
    0x91b0c010c020102092107030b130c1418161409190609080a02010e060d060f0b04060908151f0e0c1c09050309060a02150406020301080f0a021c 63
    0x100c007892040141c1d400181021451074621500c10090b036030f4540c01081001a15281e96656040340030082003003045c03601140c0361806241c21108002d5000042411454903440144000d4444403401400349205220301ca1000760341c410300c24404c0501817444e08040705002c40c00c0f6105181c403004101e800108022440a0b0f4032031015148406c031601b4800321601780780600060280006901400c1781e6000b24001200503030f400030034100c1100b42200d06940740d1600340381110042c0a241d10020420b2900100012410710b81c10250084035180e8840100c0d050791090100d49845441894501d0140500e00242c10210a44141c5c0d844140d00380c1030341c0380107841d03105001c0340f200292640041148042550b03400240108208014000c406105102c201a1a41c47c1990781c056980024818203020400b00b0615100304407420f84843c0c00801c5091509007070a03d10005d40c820302460980b80036110030354041d400001020100b0b03940c05001503990038107a1101040300401d041c021610130440700c05a1360040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 208729343 1250 208728093 208728101
    0x2060405060c150702070f050f060d0507020d030b010201020301083c1006230906060f070807030f02070602070e040309050d03030c02060627090a0503070f02041505091b0c01 76
    0x800c0e04801809610b00080f00c03500202030084c07840d000c40d03010080c1032010440f44500e103c11960181c13192206219a18009405400b5070386402074100c0c03a00007041455980090ba04451401c1d5840400600885000480c240d20090142d94250ba011100701c180c84c41c00b10404040400c07208600d00e03014405544041d40011901002c1c0034168805125020394405a1280c080280180f100b40500003590048140c03181400540c0b007031180e00c01030001001c0d41c456201b01c4005045003645240d90304101e28012115070003051045e40003071040740d41040014000101071090700c0c0725800810009103404100c450556000744110100008082d001a080d19440b000480b110321a48004c2002110800c000f0318004000b4403152180c5e1310b01c8031940d800340159403540740500c03614804803125560b5903041468440a41d800811511001400805101040400c000e510f442150240709076035034681e0b9540040c00c00d0040035484500f140104c0c6020002594400d0080b01c1e101d4018140705078010050301716 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 208730593 1250 208729343 208729357
    0x7140f0d0b180601080f01031112010b060a120f020310090506011205010305031902010213091d06010609030b09030702130209011404090218150703050f25050118080a0c0206040506 79
    0x20001d00007840a59030300111000d511403400e06c1080745039803640c0c855584a4001496580c029001002c0e800082402034100d14504035001c0c20481c1d072055402401800280304207820342d4098035100c04407011500758021640555240c5908002ca281800320340070080002610550501c16800500000d025050103071500940c080e0025507228085c044041c2d400e601800910401c5920400c44510302fa81403076281000e4032401040026071030b00841d6800d1028043e00c4500c0c8142c0b286400010345240e1042006080c1c0f40b182480300b1240c0c03200644280d0301d000e2404000e600c41e0005250051010a560181c601c1800c1490401501c0c001043c6a08132903000c2d4000c1c2d81619000070300301ca8002c203c101c1890340201c043da00442c02c1c441e40140280940100340000f810808006580303100800305000746c42140088007842921201401c1e6800c00a0620440440f00c80d42041d084101c0c400c034082043c030026820584d0301e0f00c1c0040b014021184061020000ca81c000c2d001e010100706500e682014241d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 208731843 1250 208730593 208730629
    0x90c09030d0c02090609071d01020a061d0f0109110f030c13051806040c0924080313060309030c061508030f070c0f03030f0807030e010e0a02040507140f0d0b 69
    0x301d01054014800d244d48018140380c0521000e2083c01011688101c0300200c02d518210341e8842e00e00007000407420829005005084030f0b05048842c911084454450745410780c21900700d84203402c210558901342c5541320300260403034448528071441820549120207080304000e003507446ea002403c00040032000b0911103c1c101da50340d4410018446200c0080c0e040f812030410080645140540d01e004019002c0d000c1c1102454480303c120a800c0e4000a81640c20300c00c0d99141090301d5114002c443d0f03a1740245207811612100381e200050a94007a100d0740b0b2407603405a95903415640252500400380a40e4544c1036658600c00c100011901800e00c040d0424804111503250754413410304112240c44003075080301020030b01520040000940048a40131000e03100d0920050541c0e0303d90058005007800c6c00381224035403c01409001184011a0000071648201d5041100e500c1d40d28040790076407080c6502c0c45505408018083d09610b500020b0b1040e10b00084001c11000390788000f04144601c0410000c0c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 208733093 1250 208731843 208731857
    0xb040f05010311030c0d02040c091a0a030501060806100f11010218040c05090603150301110c0a05010501140a0501030b03161205060a0504030e040c0905030102130602010e0304050f090c09030d 84
    0x40050985820b1103d440c1100100045140722000800d0361840c18002032140343c1e5501141600c50040307100c80018036002a1804004014003409042a1700485072440064a024004a00140a000b5040c00380c40041c00080d51442e440320242c400d90085c55045050201a1910400700d1400340010032243e060224541581d022010a11050781c414184400c14480140001a0b4070384800d0241d9502000e2300c40d0100e1801c0c0004080790045c1140c800800c1400300000d940e0000350070014100040380e20410080025a1703036541d0350501d0841c01c511096101600803010001c648c481d402203a02d401c401002d44100011140340700440c440242c1c448207201010781007040c10b00c0700622403d075025005440600091034240e5000303000e5003019a0042c031850b5034000c028003561181c8001006084080d0007195281c4c0050020745507001e1a105420056003407040d01d80d48040040180d404441016001d16202089141000741204d4018454805800c041c408180d050703a003000542d100400c43e1303c03004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 208734343 1250 208733093 208733099
    0xf10091505031002030606120408160308070810210302070506041512090807020405040305070203120d06050315160203070c030804060e010305090a030503150618090601210b01030b040f0501 83
    0x2d401e10580b000042145841030040040395205d2030102c42015120803582a170503601c2d403800811b14051400c003055021040c1c044502056086101070b4060941601e8010030381d542d68600c41c0b180d02150103000c854074012202203600401520407102202e100740107a0307656075100c00c041111504258404039003a200a0300c0074048503000090b01c0c0442c0c003402800d2056050a450b44003991007084802805507640b000024240341c400c5040d81c822560007802e03903481002d4480421241d03000410b0154840b850b15400080310301c0d0019840e291504142c80244155640c84100d00394980c200b02c4000940c0400c11a950002d041c0340700303140145115010741d80e107850600d02d0040c145030701c444106044c180f030078050141814000401b41c4a644d0b040c50300640d40da80f0b2001001c0c015030081d02281d0031420229883d00841c00781400528940d5082c1c1d104503083d942d62004641900c92010810180119405045981d000f25045010100b4060501040313000e00b00d40840c044518094001c0c820641d03550040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 208735593 1250 208734343 208734349
    0x5090a05130605070215151207060e010e04020c03070b040605090102090d0209040606050613060306061412070e041401090f020a0f0e0307030c080f0105070207050a180e010507020304060e180f10091505 88
    0xe1234a511000000300030150810b50042c0c00c0204e07440f1001c0c144400c60132510030940d250f4040382ea620960b581600c0e10340d00b445c946002c000600751402c8404030700703210002e0003101d4144251099000001e05880c108a4145c09019140d234000d08260303002a200c3c640840c2a4480100502081407115004804030f85404402422103817a40c10440c10400081c0b0341c0440c03941204c080e125400c1020180740102c0d03c60300003d80c0d905031a407100c15042414010415242200009858100c031110301080c0098440c00461904070f100f400d0050011030b41c01c82618140d94030900f1090342c080b40240444086540b03035141d660620080f64420f02003175002400d55203c200080c091a50420a140010203405003000001081d800d00707405500c3d8414100c0c89070402c1d120b170980088403902c4442c4000c010901b4041e00013034480c1e0040c040d100101d18030044940090030140c0045443c4542e0040700046071700c8000001b40750401c0a85000400144c411000c1908500c82c07085840e00720b80b241c121341300c645c509014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 208736843 1250 208735593 208735609
    0x70605060121020a030b030609030a090503060c03180f010207060204081e030a0513090c0215010b090303070b04030302091e010207270914011505090a0513060507021515 74
    0x25503030410440301c0003502e0b20841c0302d504003150b8002c8000980c4407002640c0840080c048500100d9062190405210021001000400b42c04410344e030340400e040d468509242d61100b080d20b544465050400000e1241c0600b01500c075120f400600c1900c11042e1304151803420381c0c0182805440d055800102040044410091084000c0b1402c1141550b072680030b03802d03a241d01400e0794030020b100002404090b03004031010a0760141c42d50400c200a06001003800070b540701c01e10003440841c0911803002042c001d00c00d20030f9854150008006600e89a6103650b440f01d03100d0301500440034150203009400aa07a640240907103079070002041c1d00d00c1500078078002803504485070b21004000f8a011aa8040450b4281813500015401d080200d0740b000c252804101000041c03045800f41d5113001c01d4401d42c1c4403a2240d1004550303045520b0000b90700d078020074404603001610180c61022204240b42c0005510340c0000c0da00158600580300000000450003114010888108403901e1800d00c4581d29883e100030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 208738093 1250 208736843 208736851
    0x1b05040504032007030c1d010b03040f0f0f02041a0307120308061207180b01020c151909050315011502030c121c06060c020117090a020918070b070605 66
    0x64240154201500c002d03055000100358014440c01d580c00c42e040801c01085898000c5501c00510003840e41d403000f1012200145148001801c0004400052000303003100035280619009030100031090048c0d42c0c1c031a82c80b41d41000489241070401a49000342e03903184140d8100807040500c1245070050501014140490354010607101c001126080000c6540f102a850f030166040d10500e004081f208425481d0044a0303000481c0302c40c0130100c400c840149a00302104154080c1c0844000c41d240d5800c003c005010001c2c6000c1c501130500411006510200c021540d0801c0f506020002580b2400441c0c1003074628201580d401550310010450003201004581c4076a031244041c40c100303842c1003051521107640400c00a030310760340842c00714011030415106000401420000300100e5940301d901038140841700130141d001c1074080000380300b28a40c01500340d104882d15000340ca00c0b18500d60800c240c003200500b0000c1d100d030502038036000c074038410003459000c2c04d111011710782c44170894a800d00685000070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 208739343 1250 208738093 208738099
    0x8070c090c05040902090604080105090304030b15090a0b01030f0e03040608010906150c03051312150606080a09080c060108210a2a02040504080c010606140307030e0a050304031b05 79
    0x1941250304542c0b01041c0c8007503da8001c005a0f480d00040009952400340d078020b0313a015480e02c018010308100c008001c10459104e1a1108003568412801141c40001c0c045c0054100320f088000a103100e041e54003010b4514014100080c40812051107002242e88102c800205680001401d01ca41d9821548450042030180c3d42400000e01b021380c2d1600c561404016030051001094150f000c060040e001c0c0c1b10000d5840e05048041a680d10010814055907034040ea4900e85990075014020158010350050324002d031070303e6005880c0c41641c4002041c0d803810a43c2c400c0c0050100c0da01c902800c0c0503003070084c21624000c20610324040e91003221480040311100c0d007408200107441000d0740282091022030700101308070342080c2440d4031604548651300030007903115203003004010030022402302402c280380d0004002c102d102e4503900c0a603040b1800c80b0040e66030003014000600c440d07101e034001d6680c00070a8010b8800000007661020300d0340d00f254000320b5415899843c00d59860015400d9039009040407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 208740593 1250 208739343 208739351
    0x60304031112030711190602030910021c0b0d0507140a0306020c0f0105090714040c05040b0c070905090f0a15020c030a050d1406010f030908090d0308040606080109020109180b06040308070c09 84
    0x51b904a0300405521140104501e401000264070000d0921041150665003a802d5648441c0420b0748690401d484e011607a10341e1415080240c141000c43c042119154000010100d243c00c041d20503020705105000160f00c031503400408800a0303902d002508124290308024030700e852864404500f500e900031702600e0143c6c00280100710b0903104401211904c1d100b903e00264581c0410001c5440f0b11890304608200c2400003401c1d860f40c100000d10701e086502c180c0040140f6140e07103000301e0706e400483c1d00441c80b40c0e006001100c00b146521144080c8844c910754010701d070001180110b07046800100340b410120b900401c0700c0e0524180d03401004044480c540400e521307494001700180103c409025020105a500e9841404010717844049401104000b0856594980716260003040810104c03403c41e0001c0c00d00344000343d0710005000c1c44000c44d505840c0c14072200d05100700721000070a9021700c2c80440f0b031074407148075254841000038400386000e50380c035603620f24503400c0080c64219250300c4540b00fa41780c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 208741843 1250 208740593 208740613
    0x30310080a0c0e06040f020a020307150b130f091202070e060a030b1602010b132306150d0b041a01080f010612020703050405030304171207050309060304031112030711 73
    0x5034000c05000e945000700070300c6440c2c984c640410b009012820b290240c092000170150350407038000000c2d003000b5110b0030800c420400320014000549149403d81900114407034402e4400110607048032030503201c8003a0010f941503807138450200c61244861a140903810180003800b2046000c05d2084e40044283d80710f84000c2d21710f5441f01c1600100030700d469801c2d02c0d01011421614402e420032414030400030140594040ea400007100108011035500841314030f0700703103980c440040a0004910554000b00b42c0d0585000400c1495034035400f02c411120036130f40d41c000750f00e41d65881d4822149190502099a1214182031002400b0300002802d2200146119001045080c2c0c1c40580210003036011a000b40c0c692403540340c15a818051900f00c1641404003180109200451003e0040358560090448801c1d0014082e80361940c409c114015107145c1080004844d1f80c10448000d64120744245401c0a448004158040c10082c0c040c50100340c03801c001082c85a160b40c44800c40d601c8840e108041c0c042062 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 208743093 1250 208741843 208741853
    0xe06010816060e0f090a02040503010e010603052d012306060304020a06120f180201140406050405041a03010e0c0103151824060e090c03010605071502040b0705030310080a 75
    0x10551007050b040003200d68001c00b2540f076205442d03054103400b800c2c040190a00010440280d00030b0301480e4003d40ca030004460683c08140200c4049a42190143c180101c03100b002c01c00140c1d0301a5140400c24100801880d241801d00c14400c06c440710107280c1c840754114a6074225824806030040c1c1c802c207824000d21001d80c0d0f8210320b42085841e103003004103c40b0407a605100c040d00b12182420b031410300d00703c00b005440380c2c01048840643c1c0b00342d071070040200a8400c070300d6060055000e0175000031010702090059003029408011131503c0351004d9080800140f00003400d503215a1054a866000144507004950309030140111490762094004180f6041564002121f1341402c00304500c1c50725071040420100d90421070142901c15140d10150316501d995018041090144000b070140440f0070015903170194200c2503030306803002550b80300c0c603100740c94840245100a40403030200155080000040081004c0000e00e0603034400d8014584038035101c60807220321030060740001440e422002c0140000b0b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 208744343 1250 208743093 208743133
    0x30908030601081f17060f2202032b09090501051003020f09041b0f1707030911031e01050105060301080a1b050a0306092003070b0711060301090e060108 67
    0x40070070f1804010301d955040358803100d6540e000f1559450b44c40e001000c03440008070b8002000c0d0350958000c60341d050319080455401264100c03020350a44948400503480a015009078039601d60009084844403c030b40d4007860103400642d1004800f42c80d420030b80418140c0c201e60413000400d0681d60800003036141c20080b40c40f503031440c1881000c05034009591000f5424040c241d442000300540104054107281031213000401006040c280414410089417507028420b038480c0d403401440b481050001d80b2551030a078003a1488903421600d1607400d1840c060a5102000030401d40e0300c013500c400c000309030145e8840d03086a4040c0c11180c00b40504000600080e440040d807000351561140c0b00c03040705602c1c4440e0700507060301c2e50003883d44415901c0b000070501000d600030320030290180c805103000a41480c2c0107a8094100300c03500d03406800c021002c000491002002d00030440c0285c44400200020b00c0000d4141c3d40241c110500e11130740c5c1c014440d8114001c000c107901400c20302000b040c1140540760b031030b040d007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 208745593 1250 208744343 208744351
    0x10603150810110d0c05071401020a0f0f0c06050705031e060312090a0e0103060506100c050a6204030f03090909050a1b0501050403060b041b02030c070603090803 71
    0x181d9250f00c05141848000c008032061a8500341c802c02214500401c002c0450740600015940703030700400048000300c031040c421100b424040e5140c2e200700c001a50f4099071f018803046441d509010b40c1040c600e0101e03a031400350a120314041d42c0d9043d564070f03069030b03d61074015102203210040d000310301c00c20049032800036400d02d41c4020350742c0c403d0319091100c002440c40300c4943c10088080070004000420850f40790003040c003800c012a5040c02c01268108120f8111920020103401c50344032401410210710396201611f09000c1e0080d642e1100c000410b4141d2000b0b0850303604100c50705a0071701c1c4100c5420b6101451004011000240000b00404d070000170481c0076a010282600700d69000c84010103003d403400c20014030182c0420f20841100307042042e1151040e420a40e400b1005c2c222211840e90346013003420079503005848040c1000c0c29a00e03030340c0061004440b11a0000d58500001100e048100002050100c0b035500440d42c40250a809a00303203810f9a201c5001d050518030701c000041d030250240c2c0e0380 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 208746843 1250 208745593 208745623
    0x30906110303150a030f03030c080f04080904050403020c03010c0c051005011206020c01020d0915050106020d020a060f0e0708061b0304020d0201050a0201060b0d0902090105120303041205040810050106031508 91
    0x3184185200040400c4d00c154002800100b13044003580805030540c2100511614039110715505540740301002c2816042110300403e40c0004100411551515070b101c96000380c040d1048451328011080400c2c210340800b41c12001003401100400b00b00702c5d007000841c0d5041c0c007218051100b545454014000e001d10f6090003050345402080c00003290100b54103486048420410034840342089041403000205c10091121400c0d040c6800403404900019490050020720750050005a81a4880c60003d15410301041070321074582142541802c0104000405800c0c8400540041d00340301c403000c03d00240b2201903116541d424020000980e68840400945a80a0800c5075545286c0a0200c0c010b1900da003125046140c04102c55030502c8043d40030007100c9209030780808459880c0c0701007103a00020752607c401e05a008000190008100c80c0d1f01080107551410880d007000c0d103c0940c107041c04200e0a803100c1c0c19543c0c2004019a80e414010a20202401602000741c00d003040321441d00c640c0401c1c00108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 208748093 1250 208746843 208746871
    0x10804120c081206040e0a02130905012319140412020312041113050f04020d03091701090c1d01090c050f0c010b0a060801120303110d0513030906110303 67
    0x424a01900846400507440150581c3c1d03403004071811000e10b0f500f607424500032407800d0404810050300042001110350028071900c0c002c801040c000001d45044a001c80d115500d420310a201914450314600c00c0200d01c00300d08555160143c04220030818100b130141442d42000880803d0b0710f840108a5000b0340c02c80051085035901c800280c2c41c6124030b24403502c00d05000810402404004030601c51054000c0312900d41a030081140300c0c0c02c3d11411b455211828003410041401844c050135026441e0780300341020708056036144401f245a403200200d29045075100d000711010042808100030242450552020804459004c00e11100005000b80d440d400e940301d595500d401d01501c2a141680352046600e5078070802c11032114040e020480348140540d03444240401c2c80e0740980f0045050b954490790008103280d030350b05c02300c020306004600c10501c00c03020000310b11004064058070b4845c140740761041078039040038a03004080c000c1991041c0704001810b60148221031001c4104c980082030b07100d180c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 208749343 1250 208748093 208748123
    0x50919030503070c0f0c0801110901020c0402160b010f050420090909070b040807080f0c03030a030207030507080403050a1205030c090f130c02070905070309030806060703090e090a140a02010804 85
    0x41c4810603030300da020f0808501c8900c14000c0014034030721b40066980d660001e0204000072240c0d000c140c00361000b072070701581180500c90114240350380540a40c1307040300300c880030314031706922103100a5200b0780002403070354801101400a03080502a0a000b400341403142100145208517810700c9002e1410307070501c03402c020004101c0000040016030060210102e55550721a0340d4117030240e80e060b1340c4c8104c103424000c0c408140d0740818042038580020402602445c640034034148118000d42c024107007142400000d001032800b01d1420340191024610890003000115505c2c24540703e200c3c0b4100016041007010001c1100180e40c1c0002e540e2415010799041c0308a840400014816101c9003890f0700304186001c2c400545154005500012242851420011900d071b500044096881100d4003a02103140790703010414074104800284000c0c1c1c000d16102d0b181c41d8440c4090703019603601f59440324540d0301884a0000f4041010005440d0401c200c00601084040341c1c0085c042000007030014105c042409c0c925 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 208750593 1250 208749343 208749347
    0xc060905100e0d05030c010b0f15030c0d15091a030a1e060b13020901080c09010c030f02010b03070f1509050a06080c28110a15020a090f0e060405091903050307 70
    0xa219035503031144c03d0301e81701d150030300c0003900804d10340188520070f040e548515403040c144854601c5410701a00c0d46d003891a540c00850b040c0b154403241207900c0b40ca648118035840440716851a50207800301c88800b04801b016403c04003990840340c240d13944a60414040303a00010b5502220503038082c178540d1050490405404d00500504130800d900c0d800441d942c4000d02d131003403581c0c002d000501003602c0d015983e84440500e0080340c000d049416000c12108861400402e000e01150f400742c1480340300102d02c81040740040780c01c04641e81e00110f2050b1059505014050f0101c0014140384100e1616040c1d0914010004054181c0751140700e080c0182c803c0843c13003c02e5800116140b0b5825440407402c81c8400b50030007294560420258800195119000340d101080071505c070700391a421071f286400020307c001d01d0780004d5000140500501010002c001290682421907200810700281006100d140c00f405210545400810204007070300200455840c100480d022001030942600d4a9901c130303590840f003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 208751843 1250 208750593 208750609
    0x806010f0903021507060501063605120f011109060906070611040e040204061a07020103110c01090c0504060b0a0207180b09010b0c12130608060a150203070c060905100e 74
    0x2a4202c4c0302c0c004a682071021800003070a01510504040100f6a03850030100e41801c0c0722115101400852444d5040e40032502580c0d0142d150950b120010a81e0750754009607003640c0c0250f2000003600118465010700200f84624020711103203082c52480c2c484400001842c0d84034a40a1921901020900c0400c0c000b00d036120281809c1c0300d0291560312a2031320310f907070003180040318228441d9003001750100d1031105491156001d00c07043c810003400c1c107180358015000340004c4c2c0350004102405222200140c00240500e64056006440e20101e03181007000f400142c44040d0050484002c0410a00150650004143d412103880100c04025007440c51402005481124019584000068000300c0c204001c0c41c01480b40e840c0c0d801c00c0781c690051f1600983d00a0042c002d80c920600e41e007400c01c10600c1e00030118143d000100800410060b5110424603044480c501000e40040c3e1000c01c43c8070401594022840c0a000c45050031000c1c11302d4a000185110308540c1c030101002065070840009484440e5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 208753093 1250 208751843 208751849
    0x40b0c070f03031e0c08070204020309151317030c0a0813060920010306050f1201090803130b100f060f121a041508070b07140a1101110c010806010f09 66
    0x452114607a0b941d0a005100c94680d0f403100c400d81d401c040c03030300c00034500559401110b10703030060380141842d4183e02040b000b50001400c01003140160b404424a03a0000d51000d0301c84c0d14400c566000b480302500f450802c9221080500302c902d641007041c003e10840400071b842440415103000d000a07a41c141121860601c80e90004000f50309090112003004000000d102104a40c00c20000144450b400110103444840c42080e401003000c0c2201c40c3c09040c18009050300c002d46400210b030740c062076580d1204540c400c45502024000071540501044840a150740e08141003195080506003007085c2082c84149611510050242d40407031a00014011104581a0071490404100f0f42c01090541c101350420140580d2145151a051155008440702c90780c084d54440c00c000c02c2c3c00c40c1020320303103100c03507100d035000740c0c1c080e04450070844002030100041c418191040f01484503445050300098040803144030000769541201d441c4200c42c0e6403100e0050f500c48400d1a1844d0030804140040d42c01504a0b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 208754343 1250 208753093 208753109
    0x503070f020a0305120703140306130b01030b0d110405012c040f0506040b06010f0c050303010504050403030207020303031005031005160f03022a07120519061401030f0b0615040b0c07 80
    0x302c0703d20ba900390b40382c001d001d0300b6010f6180c41050040100364940c95120881e0702d0bd500014094450a1802095001c4034800506041c000380000d0722800003056040e00100481d840c8c8034075000c04036542802d000707403401001d01642904158404141d90860100040401403400744001e0015040c014424098448290040147c078124103003414403400c6200122600d82c080b0f0f04031440307249201e00c20520944001d80040185085908000400c400703410003820540070181c003841020050703501400154081c0e08041241490302d4039010505003003900710403500c0359092401d020090124940b00c840300e040309440c41c196003c4040315000758001d008802e001c401d12541c0480703c00010501000302c030720701c0382c0d02411501c000e650f0301902c14284250000c010115084403e8100c0700d04081a0952a024440e0314041140070036004000383c5082c0903030040d0b90701c3e8545d0218000344295403410179000802a40e0100c4480004000700340b2501c200d12401c403011100196403900300d4418000f100290000b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 208755593 1250 208754343 208754353
    0x7090506130209062809171e0708010c02150c030411040b0d05100b0a090228050906130e10030206161506150807050306090a0f020918100501030204030503070f020a0305 74
    0x40207140c5c629000404100010a80c803000c081125607030202048424550000144130740404141c0c1003581034024180c4841c548078404001c106210213002d0186803146a0f802800203000340c82d51a40c4404001d400301140010420038400881e01902181001c4039081d10041096a0b441c4003180480030100c04c054142c1c0154002030b04010003540000c4005401151111250f80d10342074031b48124410007261715420740d2111186007032034119000c0003820a000382841414102e4400118009900907a070328111002801d405211a50003800e03401c1d008280d003400350b0510350035136020655034400c003101209000194100300041001580c00c814510140d000240281a554009001000c1000c46040c8c0402c041384005850584518181c070301c24000140303040e0342038a03074031000401010041406480c15408000440d110f440302840e40c00c407502081c410742c04500e03110008001c001d4903a04039a0402d401007000f040464000030685500d85e801441190381400301c0c0c80040c581d55100d030f000a00078050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 208756843 1250 208755593 208755637
    0xe090408041712030105010e0316060e040c0f0f05091c08030103020405180d080628170312150301020c3405031009150911030709050613020906 63
    0x55400a881201e24560108070704140d0740d44460f07242c40d03030040241124501440100001d40c8140d446026800c2d0150a6480c162904001c2000d42c903410742082005c14408a510a86810180300702c8079003100516090807540b40d008401001121800030010402c08085906020795450361505090015005800c1512083d9031400c03180c250824802640306600d40400100d11600782d012481441080c0c0c405004a210f0005050700c00700d6010b8007030390304180160903a0324101c02c4074a01c616400c3d07249034a141e101707161150542c0180885070b0b07a40d80541043c450b42040e41c80c400701c0540c00c001481c541c80242d04448003c06c1c02030264142c00780d081e100f11500c00000c074854001c42c19809180500d107207140c8120301000b0410540c81d21825406501480003030328003c1075035204160040c070940020304074540155008080e540402d00c140d41c2c400d4400e181003010302c0d040001034010045004280301918011000902c1030303100110b0381594503000a0740d4605070b0b0f100c408030780c40700034040285c0e001c002c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 208758093 1250 208756843 208756853
    0x201120b061308100b0111060412050712030b150f09040509010f02030717010911030c0d1506090e0f070806190b040303031a0904120327050d14040303020703030804030e0904 76
    0x60801000c109480c90541e01017980d510038000545108954001401c40762125903600b140b02806000b20b00401c1401d002440014006c039212141c042000e90b0081041c801c0340e0100110700703010102d44050002c00304402500d0380007020544030003036022200003d140d629805071038051311405480d10041d40c40002000300c001e0304856060022010301c00c40c00da5983e00d650720034044a2612101d50560401800007500740c01c0020014040d160001801007200b4a4907885100143c5041d00030001184d000b0409200030740c2030000003640720701c905031000b10605040d034014244603409000103014101140413220340c268001660001040a150300c1562540c1e24103006004148403560b82e00c69803181c00300c81c0004d2600403402d601440e0401540031508000750410307001000c09150703042040d00c5504a6448000d0501c030040e010b1030041002d446da51200050040010140800940135048180b20034008030341e0000b2103005581e071504141c17480f6111740c2002c0da608000035544a03131042c441008c00c82000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 208759343 1250 208758093 208758103
    0x9080f0d0203010e01120f0803060402090301090303020c0d0518010c02120f0105040c05030d0215150a0909020a1a120c25050c030d0c080f040308030903041d01030201120b061308 78
    0xc1c0d01204c4030000d640c0f0782010108141051070090003540620b00090080ba56290080d034006600500051600d0861400f103801d46844500541c0482c5d03011418100600042c000031500034a5441c01034905070f03a0f05103012a107145003441904000d0364096100842d11070050304998884c5210071543c54001da4941c06029000454003290000001840001c09080004500ba400d10041e009864481403005160240c1e240081003000d80040003040002c4071340315480c20102800a911000c00d410fa03190040c000142001c1e48031040306003500c8140032035910840c096481d8400e001510b0207243c0c69100c20110741d40110001c00f6403107151112414042c1c454110440d141c01d106c0c1003a42c03042d10000c000c05072100e01640102d8082200e54610100164440c7c0c0103203c288200d8030107500b8a503e0b62241d0f08190070495040b42142d2002034280103424103080861020010f0f90202c00349581580e00082079108440341808126869510403a2260303280003d5410441d08032206965041e03842e14140d40d60 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 208760593 1250 208759343 208759349
    0x30605010620100c031e23040f0602030a020415080a0c1d0409020a1d011802460306060e060405060f16060204030c0602060f060a050409080f0d020301 66
    0x22079489032221030b6400e000c0000c54140035111014184110364190701c10301a0450703000c00020940e071000103003d0780700c05165600180c08924000a001044c0c03900015648121006108100125804000000707114000c0c0c60b0341a5440030016031a5100c40040f034000e80102c2d041005101541895803108580c00041944550050788090105901c0f081c4281c9120500b1150010051401648140603041c56040351102c00c1c4050401850540c1e207484c01c50700780000106a540040c507100040003111115440c1030f1401c05142811807500304d00561240a00c941109441040c001017040412076582c03030f000048160701d061110448200850310024000c0c48540106c10100c1c01d84004014117003448000c1d1415078401400d460702c0c110501c0308808036038115600c2c5818001503881e200300021b405001410080d885804d8a03034445041ca10040c2c14160000d107401c100c42a001c081000c15500d14aa4808403081074a001a0030012420700c0034152058130402c0004040014a282003803805500450417 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 208761843 1250 208760593 208760597
    0x40f060506040b1507150212040c06020c0102060a180f060b030d0801030506010323030c100e0d0c06020a0201060305060f01060f020d020604080d0e012310031505060f0306010306050106 81
    0x386580e8103040204881c0b1210115402802c0b40f804030308810f2074000205078150142d0301e4841003c40302d0384401c0076607201c0701010030309003500c106020030040b00704480c8001d00010300280c410340101000017581d4100041400d10510b44540111030a403200000c11030400d03130040c011001048072818244060140002801d010340710385250307112000d1045001c02d0681381e2150190516910b10b4480031464005680c029495101d42444410020002c000a00004a000c0b019040719480c09240408581a0306182c41840e0841c00d202d912455112900750300c2c0c01d90007040140c90713008100c0124010842d9070001001e41c440d0b04244841081100c0c180b07030481d021030740e62003c8481445000c070f864010700e8421001582c8032038007190004010a001d07200b01c00d0300500002d285543d200e0b14900791060081442c59090441142001c000e42019032154130090503003010304107501e19629a21075844200c034045000390303240040352640d501c8407001d00d80ba0100070101c50003941c49050403802000c0030721070400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 208763093 1250 208761843 208761851
    0x1305061005090a1802100203131205010507140307030f200d0f090f032a0605040b010503010e0304030f0614090f0706030510060f0c05061915030b04020d060b0306040f06 74
    0x2600c3d070581c0c01894070a1404040813003440d6290340c24010000c2400482134158002803080840f42580a000440180900042e080b031401440c00c0c51821203401809a404100310207a803d9000c40440b030440f178101d031151800103149028041d9880040c55415034a0b18210040010422002200805004240c004076000c1086500c0c498005044400d40f890080c880d0900704080c001090082e80f0b90040c244244456212282c064945210710390401c48084034090343d0b400034082401041040b81e800b610098008204549100800f06d50341d0049120040102110180f4001001219001000d0b40701c000c142114003400c141d1261070f241c0807a0b24240440d03200d005c40000751a8400e004490089594401145440e4100101101d1030040c00800390240550224801d0010b00d04104041c41a40030a5903c40c0100e00348140c00241d8541080b503680015480d0806e10205031100c900740d070410f5049a01c800f182005240c1080900140d02144d540744c0191000c0005000544c100750f030640748241c0c0204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 208764343 1250 208763093 208763101
    0x507030b01031a010f050c0316080a080f010303142a0102091503011d04050109020d0b100503060f010b0a0207090c0203090913150b1306030c050108090a1a130506100509 74
    0x4142c507a43d942d405002800c065101c10b20103014100900c02001d280080c0d0780740149100e040440104603480480fa0954001608041254441145508030301c11080d003100551454034014019900b905210502c00b03000a01419060808169909070300d42c442a403544031b00b1000e20840c002c0d08007c5825010b001e032180c0400062440c01c085134140c640d82601c0ba0300700414411800100c043c00ad20454040d940c48455002595075041070340091442008202210f01c2c4c07041c3c0380000c24125034000c2d40268004820710420f503403000801c41c150358207070301090b03200d01a0310022491300c0b0395684226070280c9480b005c001c00da64040002d05030307854240c030070b00c9039520350b042c0c0010352219402c400b410f41050207000c8025110160009510b0340b0000709130403c0e5009410384079046950a0380308072100325010000b00310658012400039071211500700075103111340302c507100c0c440d040b101e89060b1038854180b6800109141c00480104002d16000740071581503107000ca40030f45907040f003801010301c108816800a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 208765593 1250 208764343 208764371
    0x11070506100b030403050a090e0f06130612020d05070509070c0c0b090105120901020d1a04050601080408030403031509060b0a08160203120408071a01090c17060f0409060507030b0103 80
    0x704048a80e21442145190b8550b28215110f0f04504030072405c01c09084400500143c00300300302d9002708030f00c180110560030700c01c080010901e2299051210b0ba0f05050301081003000004138251060340665421181c000139142c014185a100d0300040c3d0700c2011304052050250340700300741d01040c07486000307100201e984510030f03030300940280001c3d140020002c01806c180411110000354010540b240054141031000610400380d90040340c4610400c42450140c0b10707203140500403948c0110003030170039103e141840d446550b507600c0000c0001d800d040d10b4503140071240601071025001030501d11010003166482e40744880103170348021881000544130201040d05000c0e607410350b1646000c550015440c0100e2040d200d002c03441e0003407068136030703960038088203011aa40410300403180005001c00c005560521202c03400301c4020100031010001c2c1141d0510036031801e8030140b41c200070b04a81441c591000c0070005005041028001090305040005019041c0d4140d00041c0d50a8001d0301d061144402c52416 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 208766843 1250 208765593 208765621
    0x30813020a08030c0106091401092412030e0a030308010e0705042321060106030e03090d03050a080f060906010c020f030a0501051603021305150f121012170f070611070506 75
    0x2382e0010100103100420908280364400d40c412080e070103003c1514601c000c1c3d007080100559010b04086802c0c10900e404060784018014500b00080703a2942a250442c0c600130055101401001d03100020355002ca80709600442c150350061840e2100c0540070440203500100e0001e94203810350060704501c5d5000c00184410103601524807144005040030385c17030980300b1005091100401680780c0020015030b01c2e0f41e120300d10541140340c0aa00c4031507698002c080b0081514000a0203040c071000554103201d6540c6c1c0e02d450a40c1c00a4007480d18180002030b03800050410380021401950600c02c80080104108064203c00d00c2030b441004641500c4103101c0303080d82a40f02d102d081c04021600e41406000070316015020004450002d10840e00b00524070044401c0c0f42d0240c07818502036140a01001146001c2c1012100901000003400901d02c02d1941ca42400050b4a07500c03807c0c2280209489600a0016051300c0d54a600118140301d054440450000d032640580400d880501801000402464444403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 208768093 1250 208766843 208766861
    0x30112061109030a02060a0e0d0627050a0602030403050f070b04140312240a0905060307141f180609051003020310060e0604180e0f0c030307030813020a08030c010609 73
    0x2904440444e40c1c00c0007140e5206002c4401407150b015800c406030b40314030400d814050712412002a1400111151252814a2040c9203465101a2400d030300020030120781c4007482c90303100b0070268498440d481e06440134001c80440f030581c188041540b10611840d0b2008034043c5009003400c814010308200107940700e20965681007000400c000c0840c24074802c1c4180402c034080301c09907103d1810054000540104c85c80e62011954a48403024013510340b4061000d0750040c00e011180c2240150340e1008104603030b1158091980c411800011007102d14003550070780080022212220910b0f648401010f4004015405030a0142c0c40c03864248034031a02034400c5030b0041c040742c0100b44482c0c2c0b9001d02204c2404001038119003000040c4400104032410512200442030440c2c0003050441c00210305516029000d000d110103030b800201025420740380031084403200768052409825030f5881c402e184445442119000303420020384a4002450b9070f0101c06003441d940448002d000c003654420b952825101900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 208769343 1250 208768093 208768099
    0x70c021302131703070501050c0c07050108071220130303080f06061b03070c0905040b0601022b030e0f06060109170304061115040c06090b162303030112061109 70
    0x8020f0001c11500c1014401c640b540c3c0e8100c0303150072200d50320f017400d44000b03403406034202c00b010400e1259001f007072104001070a02841d20300620725080c080208040e81400c100110240c3c0c0c5d510b001028204041c0301110180028405640c480001c0d000004004251100750f00244040c2c0c00300b0006c2c200544110700034030000307102d40e090450280801102041c44000c900f101c0c40302300319000000303100001c041c0041c040d1120002d540c1c5094100241c200d10300410300b5046403c0320310b50320700c0352005441003075602288074032102540c9020f80080d80141140201e0b4000d41c410242000000f12001a01511401080c2c0e6101d8031140c1c0c0c0c14113800d40310704c44025582aa00207000502602c0d216501611035071410a0031142842c00c146c1e400e18140c0425181501c2198040005101054010490400402444403240e1501c00381400d1800b03015010034000b800c81c0c207002c21000d01c43e20140300701282d01d50b07004281c0c0d90300c3d41e403000c0017403490000a508035035040c01c0030700d1300203880e0f03c900c2696640c22001e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 208770593 1250 208769343 208769377
    0x10060b04060302031e010305010902010e0d0302070306150305060103060b030715080103030e010c02090a0b04110a0903020d06020c030a030e011404080a0e0307090c1205010524071a070c021302 84
    0x4140c0c065003008200e642c501154a10303940710151505e10460007180541e00010340c800c550f00006152504280c80107000c0c908031125140020750000c5d40e441166003041c0002041d5100342c00e215940c050560002d8158402e00001005020040d40b000c004500e048007103601143d50382c00c0380016060005c0002c4040380e803400c01000480d00514641180c41014500301d0180d020039400240206001d07035000c0d80d510b903105841005424148524900c0c201300b070120074180a21841c1c0140848200d0000900541004507e8002c0040b1a01541c880022a4080e20748600201000030014a54507071540c40b598280300010340e4035400e0030122401140c116818901d03000b1521400e45a048103000344580500c60000c00040e41d501d184074255038403030959103881c40b1100c042c845c9000c0c1d4106030825441141042103494407941c1d80384110341007020401c5007a8840301c1c9410800d9010401000e02140a40700700c0802649550182c00040174038400c64840141b4180311000c0010bc2c050392083d12124441 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 208771843 1250 208770593 208770599
    0x10e07080603010b0a06120605151e0d0504030c030e0405010b040b18040c02030a0305250c08090312030405100629040b04030c080d110309042307020d0210060b04 71
    0x418690141c0c46040a00003255040b140008204a4861980000005506004040000822400351070000c0500311607010304201c1040244109124126202044482c070009202d030090220054034140581428204034500e040c0c10301410480d01034504a0004004528501080c9040d210b1141a40e83e810b02190500307043c040a200300e0780c00380c20b003006c1f04400f50558407469581c0c2d02401443c035216601464403090f0020000d4291080604400c0c80c9510700241d010311703c040304030784120641441c83c1c800045440d0342081e8100384201d08413643c05009030840407182c850351000842c050740c8140111031420030408201d80803505140070700c034040340c42d03864441080d1803031079044101c1d1589890958a0590b40f40311200c40359120b54801c48010945003020400200184140d202c2072429061002e4944054007100ea00c0b4441c4500c51032086641e000301440510003a80300f004075001c4c0a4400d05c0a0501c0503010350f4030300380699220018071541c0040080c11755540545030844e494040501c0c00c00341 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 208773093 1250 208771843 208771847
    0x120f1209061005042d0c120207051507120903021b0d030e13020f0c01200f070602130503010f0f1a01080f0703140711120306060304021e040c02160806010e07 69
    0x403403c406050441403c0345c6210603ca44901c084602001450000561504201000d0002c4205000702101305205100d81e07800704802180304c050880d079420785e003082a40c50580640c0c086907a9aa001c500c21310780a901010140c000030314040c62941641e91018400c00c42e0100003402e100c8900050010b2841111480341c0d0400d007445140542ca0074002504208076900c440e02d00380c001c0c11003410f10360b446544100100152490000561543c5d00303100745015070100c1c244580344290000242100d0f80060120004011a00e281d0302403e070041c002d00c03804400d11060b002800e03005007100090745c588900501c100c8209903102c1c20740300e410384131515166a51002d000c0440c02c01004207081c15120782c81047c91080c0c0040c0c5038854603203600c43e14a0201c10304401d0381f03852001c2c02d10302c40b410f10820500400c2d56801c1e068039445581220b10042034610b003031484e80040345041889400a0614412305030707041d0081900020300101c140666050b40d5103010055544100f8420010041d40450114140e18 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 208774343 1250 208773093 208773101
    0x51009091a04021201150302090f042303120106020105040212010b010e1912030503190b0a03110307050918010b090103020d0b130b01030803090d1103090f03120f120906100504 77
    0x5030009140348000c1e0304c4000c580782540d07250800a024801c0c0d509046c03003107141040c40a03400c20b8001c9030500451416507145c03071038a404141e180740f404040ea10384030304c1d41c81d0800c103c658810200d4000151560340b941d01901030002075a04034070641c0d04040030340d80d15a052161807103516050392410340d140b407001c05018402035402d113036210311004c2503004203080254171105886a84207540e0990b4130301e010f50080900e40500e00717020246d1342c10880c0c10111a034030003c285040c2c90700040040150100b40c0c0019207805210741c4280d400020704010402031035040225000540800f800a0080494a00403c400c1d007009000c000d50115150041401003004e44030010341c44080c8206030070012206440e04244500268422907003036400104021b0486070a224030001050503051821f030007105101382540740e0040721010381c00342c0d070145c02c0420140d600700030306901d4951483c0a0b0342d68070014414540980d00030036640d0071100f0300e40d022401c0114005103007445007003802005640e45090608001c082c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 208775593 1250 208774343 208774351
    0xf271e010507050a03090302011404081b010302120106111005040804030816211d0a050103110909040606080106050607200d0210030b01090503150f0703020403120201051009091a 78
    0x2007010301400001400400c0002d0f2002e010780c40b821002891031000502c020b003030803076503448410203207c20058140001518281e440d0310501000d441244000120000c0c0a80509507100443c884000102c607904002040000201c0d80c0543d040c81c0c0440580406440303040d540103083c031700c08000800102e04080f020701160701018004126068440d110002c605018080b00010001c07403508101245400410391110305801c5115540141070440010700d44110a20a050605072610300303800c032400d080c2040f68460340d40145400c401f400c0a017040001446580100c104640c606603000c906480d04100380c034982a80008480550185c3d00c0d0304805c1e10181031442030f0000140d803841c10040ea541c20149000d03100c2690000348480ca410001401e03401940d0100d8066048014240750b1103034100380d616444a1318a041c900c0c01e844400c000c400a10465001500d0001c0c0c1380440c1c0191681034001c0c0d4042c080c954507104e4955200d05101c2c0c21565003540041000440c607640314090003982501640c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 208776843 1250 208775593 208775597
    0xc12101e0308030c0d11030c220e39071401051017100c08040b0106110d030209150f03010f050411070f020d15020c07090902030d110a080f271e01 64
    0x4103200e94490440d1608142c8150f43c0810000c14401d92050a604546049e501c0490702d012410313242c0000c2080e800000740c002e140061a07440000540c0081400546540b0050302c040010610881c5003404180c024a5084401080c0780c400394aa1150502a4074021000c80880100c0b0034644100079110380f800d024440c40b00e00401c49003a29a200754403e01c50800040d032070f0340c0c845103071a24051100c002d05130040400e2081c0d4003105403d2100000e0041001c1645040041e65603c03c18001404401e54100100d2004030004100c200e1014400280d0304840002c0900141c0f141c9400400098a000da070b440c010354081444410080f83c02c01000b010581d002400911001002d40c42e00014081030741078103403007217400003080d900c000e4040007004010036240804002640b80c941c0040c0d2200d050182c40010001061460f00b00c0c50745c01d00000e8400d03a441b10b5115501e0314891001079890301b0030280c0c1c400e1010780780e10b601441a802c01c089c4400d62001061051044100e00940325480584805c3c981 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 208778093 1250 208776843 208776851
    0x8040609050118060e010501030c0b070809130b091b0a080c0913020a0207140d02060f0f07050c09061206041b09021606111c050c12101e0308030c0d 65
    0x80410707801c3c450080c0c4031802910800000d50141049400e03145000c220001d00d0307143c00010408680c1703c4103680190741c08443c13844c0d601c02c00c90078000b8150181416296000910f01e510700ea14145030352104140240c162424030803076030340f4405c51500d1000044038010b00710081244504081c803400700e4550150b4004031083c100030804010032404601d00c000c1e2002c0039400218062015010491500240018003030b040080040c1c40124108034030881009003d9140494114031b55400c0380182c40c1034110004c0000d032110f0031800c1c044e94805600900c50300640100c804115503080c03400714980b807600c5880c0188890380700c0b650f42800c03020035400f4070054110803210125006031940000c107900000c00700588103414003800c00344100e5140210624805808000341d020302c840101c404458034102c1e610000c0c4940d0703028150301c078501c43c1e03443d0100e081d201e0320308008006048424040542d0310448421188030070704c01c000e8030310302c074a4003001c0c1c03144200b4000101d88000c50740081000d841c0c0e60ba0b0101d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 208779343 1250 208778093 208778111
    0x50c01030f1407020706020106170c150f0a050712050f030f070207080a0c080601050d020109060311070f06090b09060613050405030c030a020d1404030f0303091109100302030c0303040f06080406 85
    0x9000b54000e0f91060016089542d0070421250309000c1e29000e482d51102e48150010f0b1403a2065690f01400101c0c1d0045510440001d003180715403069910100010f030301d055440e18640c9004015500044085460307544450301c4c40e24a92085050764284a441400a4519100d0703d100400008004221102b1885a403502182009040c016002100e00c20704114108505001e100c03806d1000503048280100070803481d0304050307a84411110f04881081c10000f81c02d038039209404038584540580a0180c0c0320501600d8200101c540c010ba43d03480c01502c1000f650f440d0440303101d407188010b03074042d94007050890064002c0c4070140d100f207800510440440c0d10300802455402e0131900a40010000750708441c024002503508119001c4e042144031120518090540e511102c001a5240c3e01400300f41e982e10020301081120795411503105002045803c007031401181c1c041655105003c02c070700a01811042d40f095003000070030386040d5644000f9030a10142480c07012102e54100600c284c074a0f0303449030700c59 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 208780593 1250 208779343 208779371
    0x6091d07050406112a240901050a030e01020f09011b03140f0417031914040e0c160c09060501050909060d0314030a060311181f030606080303010e1003050c01030f 71
    0xa180302c45517040405c007800c19980304018070044195000200220320b201040c9071411444101d4466403400d0800d20b8907803020241c114020601303d1132030f644542c4001100182021404040c01c20203400340e0341c800d81c080c0c0c8446280c0039031503a40c4001300810b5003d4490440e1240e66406400e44200c0c800c2c0350350803c1d40c0e500b00ec28002e2034503c007a0440d5003001a00e90840000d000d200c4e138a1408508000c11801c0740c04d014526030b0310851040301910142c0e0780208841aa0081c101c42801040c0d074154604141242030548603411346100701c0c420741d03242c02e800044a50080c070a0b1608a40c004108095981d44c0105001407101c0f22442101049440081c503810303804110040c2d40241505080040c0041c01e52030b0030122003460441c460302c1080d01954884030b68000070f034079590041c1400c2054038504c200c0b2a40c81921241d03500003c28440c1462004110500004051b42c100c0303a40c100841d070551162211200e070300400e13002c05007290b003105007918010750103034000f09001c00d079000000405070108286 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 208781843 1250 208780593 208780633
    0x50a0221070f080904050912070f020a03050f0601080705100c2901081506060313140c0a03050114010f080703061e020d0506130513020f0301060306050106091d0705040611 75
    0x4100e0f1001c5001c0344c3d8407002d040c6407046590000c003240040c003002c1c282010701091030103040c800420142040c0c060380c0c115200d845001d801150303c80e08441800441c0c165944c0c03900700034050440d8500c601d010016003032030718070b800a014148a440e00c410701503094458100450040240021041403900c08086090a10b205c041c028101100505450302c40c070585602e101c0030291485100b0300341801405842c0511281c2c800040d984500b100804100540d00d950a0110709481541d208d54a51000003e0040640082c0c0d00c0c0600c07030000009581e211224041c0e403420600070003035942d020b5101400000c0c80b0340e2059200103034100b0641142082180e40201740d80c045800596540d490b6001c0c07000724285a0806440e4088808042c005440e01a0300146200683c1001034802c120111480c04a500c0a40c05100178640040d0148229a12458091722203480e61041c00603684606007010355901c1410481c0d801070500359902407174545400d404a584802030b600014042c000d2811040380f901c01c4860f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 208783093 1250 208781843 208781873
    0xd0906052d04030302011404020f0f04060e0a0e0606061e16020a0303050903060a201e03010e060a06080c03060108041109010f05040e010203040c05210703050705040507050a022107 79
    0xc10781d03034600f10300d4002c1c29980b014000c1c0380590035107014440140c3d00d20440100480060b9205500102c01d4400a405010f40740d06c100b020b409000b06200034400305801541c13800f641c0108a400f203441708018000540300d070783c4050342001d84840d26140456074000082001850540e0014030520250300082d042c0301403640100c0c08030b80005141616800c7c18005640d000054980400c0010000b00c10180705404110221008007000100c62003401e03416005a1400a05001420744a684400c1221564002554001e126060020300002c4d042d202d85d80c49403080086548840c1591200030040d40d581a01800459804007406030100d80c41c0c0381c10727210500800c11803d80300d5200e80f400b02440102c412950094100742d00410800000c1844401010308541056400e00c00114104200590b4848100d071028494080c3c3d00000062000019110040d150110780030072180d12003c7d429102482074601c010f015802c10381c020081c3c00420a9104076502109034250301c1c0c4082d941c1c40c0400943d4680c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 208784343 1250 208783093 208783177
    0x7030c1106070c12030c0c02010f02030409090b01080f1218010909020a08060f19120305070209100303020c040e250b0406021f0e19050709021204020f030d090605 71
    0xb8554400e2144185003813607546001c1c1030410280c40d04140003080411091400b90500150a29402d0450310800864009080080e003c000900e040d182806603090284200b000c1c52082215400c0d085401207500441081d2080e0074a00c0e10090800c0c081f000782400c10580d0500081c0f1000040d880c184c1d000405c1500e100d9541c150440c9001000c015803014075040c0103001e90220503104440440010210b402e80d03103a00c003030202e8041c0c3c5207011540d0340b01d1010000e401c12001c2c0203102d25003a81080c0300003568802d0302520640b1b41c0c410240011941780041244080d40080d24400d0b8402d003424449822078020030100c8a1182c032030307a07100001e9010340e10039401079020110030302c03040e11800c40d01800705040403001c2c4240c09504588a40d0f404070460b81030300c0500c1c4c10002d24204032080010800400304004207545564004904403000c04045405030300402c1c0c0b0b840c0305051858003083c040340441d0b0b144ca55025035818282c2c11941c64002c004224420700c0310114606a160140600c001808000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 208785593 1250 208784343 208784357
    0x506180604091805010c0207081f0b1c0507050603160806130c020f160305030a05160c06080403080a0c0801120804170a2003060c0901020a0c0308040f0602060f07030c110607 76
    0x1444c290342100d80189224045403c100e805010b07600020070344140c0c0500035541c00c4140c4c02407a0f0f4160050401280d41c41d030050f000e00b003e070003005100c0c03503101440f40a002550800340d5a40e050080d2031108894500c2d180404280303071110030307004003201c035004070010340084812000c2c1c0292204480c0c0310b0909070050ba000c00e044043c1032038200140f4000c448104036005a50340b469844e40e640f8084c243c507900a210000c00c5406940d906150f500c00c640340c0100c81c010050780d64000c090104107060b50185d0014402c0000076100400794044c1c50b0840e081c80c1e680403c66845d040074210f9041294808a0f0107001c10840080e202e0000300e40f0740780483d13080001c1d2446c02e0b02440e0003102011010400ea0003803251000303110716a5800f240f1942e01240000845603506620340040b41007580c4070000038901c400e8041c002c01404605c0020308280e501c07681d001c592072611a4004e076502c0004030f60590703c04c140c1c50006180540300750080d070050344503402c1c06168a00b8218810b401e00c201105c5c42d100045c98 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 208786843 1250 208785593 208785641
    0x12090f02150405100c05100e030c06010b2709010315060503030304080c060708011a030c1b0106080c01030605090117030906070605071e0f11120703031d07050618060409 74
    0x40c4d401003040804504111407964216610f003900c071000340039131221643d9503062210400c00180304270358592005005603122507840350881078280c0c0112081080f9032000c10a18082e4004a50000010900091180019078a995105040718050440b410241174403820002030f241c4040001c1d5000b0703480f03032402c3c9481e0044180070518191008118030708120303645004018107160100789101d02001c40449541d01c2c0d50702c4d20f00c8000b07413141e040107080211010702b4896501d0b006601c02801c0d00c0028061b12000019130004505843e920b00601e44e000311a100108101d035524882d05110983c00c0d002e41c1d00f080098400140d8542000c40150f40458540040207486644034204225403c030042307428888030350b50340000300300c6180ca15500303013400401040b00300d01180411400406a4807665056611182c03494000d01030b040100c0000c201c9400410030281c400c80100703040c415920050042c9007440e20f8032900d0030940c0f228840b8035401100230440860708030400e004446000280c0328000302d00b40e038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 208788093 1250 208786843 208786849
    0xe030408061906051c08070c090b03060a1e1d010606080711010c090b1606051515160f080d05070302040311090f06040f0b06070c08070608010612090f02150405 70
    0x14100d084410910f0300106020035a52041c2d0034030020540380c3c2c4401032080034646414280305900780901100000c1c4d800040d668070f15000760702c02d1030065083c0d4002e03448920081081d1806094030309100040131208080024499000c4a480a404d402545a541003154020308466054203d4400215404108440c031500500058a070601420080000d07800c44480245074280354007900d03030800400211102e0b44001c1890310208c00c0c1d00711004200600b0601e1801003c40c09090515000b100000c0c41e2181e0745d441a002c1c0c591072003a90781807031615005640c416504100407030086401c2442400b8180402c076003845030718030921140d200180c1d44c50860178401946c4581800c42803140d482d280811400d00381d03028409411203010f86001c0381024030f6400c1c078000b42c0b070300c404115084013000c1840400c2c030580300202000c0712611300580e03c40302c3c0c4030841200e0042c800d00038880400c0e40f6281607280c0132240d40c003843d6954055902a0034900c05030380020352405c940c841410294901280601c614a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 208789343 1250 208788093 208788121
    0x40e1609150203090f1206010b04090c050403020315130b0703050403030e0d141303020409051b010810050d14010e07031101090e06040f110309060411010f05070b06040e03040806 78
    0x400c039546020500d00c003501000b550b07482007081c4907005d4520511344406980390720900c0c1c01200a4881074517001c1d80c403a002d400c2c1e590428810f088615062030394000005020700c0844080c0e81e009400b0300440748060320301c000007040140c80100c4980c0c0c036160640c04071300c0403c0c003075019000703503900443c1501741410002c09403a401030030464250410002c0340401d6801c407005140040e05428520344908461118502c0c0900a90002c0d400900f8180304004000b07020441984612810708005521500c98004661004040351104429210803c00f800580342518603088c0d03084c45200c08090640482500c1400d450800c0c4906200d54050501441000131540c0c546046060078a0a07081142c9000c50010b01450040c0c02e650085507643d00040c1d0360348641d00300c85060b92407083c559a403410715216141c0c0d501021242641d035102c004110440380d40c81075200c10307030128032551514100f80c0952510480b010f00a030060b07038419980c1003d220150340c240098001004040e010b0b10403486e1024981c0144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 208790593 1250 208789343 208789349
    0x1327140f0606010e1e0409030306080312060a090b0102060c070c090c020d08180309010e06090d08030f0c03040b07080703150b0406122708071e03020f1b0f0105040e1609 74
    0x240049400007110803030388416145e0780034080340c001c2000d085a04041d00240000c0d000049240000240c0c082c5180c040340b26580203803415200c02a010303030f4840c031010807282c50805e000e00503002000032030480c42840002d41840c1d4026068540b401c0d54800d04030048410765084100543c02c04039141e0082c07a000082c0c03641c002d03980340800d411080140c0300c0316180e1151005103414030500c084040c41e1901c4400c1541c007040c10140c468400700b82281450545070300101c03000100c80c010540007505d0707850301c1d6095a009a9100600c242144c40360f42d4190f0380c8913001010541016a10f2013501c42001070414080f0080401c00d12095680d820a50010b100c42000700709402c8450400e250980e202d4841240342159000d41c00403d880d0607080d10740300c402d0b4418a000508010b040002e541021480c20b080e52005034801d8007240c41c0c0b0a102402d0300d44448242e582d81c2c1c9031032810009441d290505107010452400c0501d4028602a182c8d50202052102a0b410b9040c00d101101d980380e402c0c0e0000b80c91005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 208791843 1250 208790593 208790599
    0x506030a0302060c0f041e1503091203020f0c0105010b090f0904020a0501032409020406030e0a022206210302060912030a0213170c1327140f0606010e 66
    0x849120303900d01075030f1410042e00c04034010b80c00042c2c0c0005440410280e50140c41d214408064070080c1004074440b18549001c0c201c00e2a82c610805090107002e0700c9211940355010240118030a8121000d40017034000d81711107141035008200c5804400f10030711840b80600001201581c0324412070050081920110902600034042c2006020140e5508140d40045550910f00403d1914802d140f0f003e10b50700c466002240d800c0c00394000714030031002d43c01400039510390b55000c004002041c1d0b9000e946085a100203074014075940340d0342415242200c0910542d1030095008140c003581e50040445c4503896880c0e1811010a203d032000405030b0500c607442c0c102a122005060864141c54104a5440090400100c140d80000c98400c580c100d418007030018079200d4904050161a22151a02c0d8010040703c203100c4d83c556100c603840360620780301c0c08031a04510f40701102415000c101c0a48035580000b400d440c02d034201c0d00c298060000410000c40621070f400043c0660b410403c0c00540a005085070540c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 208793093 1250 208791843 208791853
    0x14071706040e0a080310030b01120302120a0507060b01140a08040c0605070b0c03040201020c09090a05072715091d060705030f0708070c12050417190b04110a03110301050603 76
    0x220b9400001c08000154100b440942e503912980000c2e007030300c459580010403243c000d400000308500b5042441c1082402902601ea10b1a40310401c044107202d15802d6202081c0b040c0b11000210703c2c81c0d481082500010b04006951b1440b813444804580c000c0b9a0383d1002603180c00410040100d4440c04800800090404905226850740c2c0d00034850b0340200381e10000b00c0301200150642e80300304288000c800001c0c10440b01c904285006a803144118907040d96284912800000c100052280a903842070b14030724000d8010a124600c00c001d8161041404032650300004003058070481882007002416030114107800300c08880d40082d0526000401c03000501c0702c1401080b200c0d9010b100ca0f00d40c8480641351003042070b80c40c41006c1d40d01c0d85880c0c0e40507004400c1910000880345c3c2080007070040e5080600b0070321841c1d01c15441d0568440c00c03201c000c0300354800c100d806000511030900c619041486800b80407a201960302c04212001d40d01e52095440c60001070103900282000e00c10179030820816400f0305 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 208794343 1250 208793093 208793111
    0x21e010e0603150405010303050d140c0d0e030f13030b0a0203060105190507050f010c09050609030717030705010e1006060c050607140f040909110a080607121407170604 74
    0x60030a6010280681c09040000b001034280c2d828100b400c883c01ea8000d01c20410780d41c407424024000d0304003e918900ca40d141100f4605404c1c400c01b049440388500c080b22030300d40103060a0f003801a010300880c8014500c41842601c44188111002c2c00c0b008480850110701c4601e076007400030365004050948080c0301e1040050050700d0360300804481018014101021550041c00c40c21500c44c40f1700f81700034001340210308017045100b5064104820b203921650b20f9450040c7c03150300b008001c2c421621807a07419030207002d0070045211860782074200203038076005482c1460b41c951956800d4413200311040c00503420940f4140b010712098070a15019001a162a400d001c1441d038420351365402c0641100c05000356445580745441e1903201700c5450480f80d82c4841c0c0c94554820041000d05080e02044a6150b90003a07080d041d0300f0225000c0084030790301401003203580c440002c01d5800e0b040e10a00081c00310780321241c8003504070801c0c220900982d050b640300d0106101030400303074074015405030070544914103000d091 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 208795593 1250 208794343 208794347
    0xb03092104060c11091305060604020412021009080304090608060f0c120402060d0f0902090c03090303070f020304030602031512030405030705130902040908030a18021c0204060f090603021e01 84
    0x65815152182400030000d02c4a013400c19101e40528030107a03200030844c04101c64035400760f0010356054486c40480700c040e21590100000e130301882c0500d0050701e000d002c2d208058604844405095123840c2040480607807504289801c5500a401c18103483d078403808100110502000b80940c010010001c0c815182040c146105251083d0343d40080d445500b0008201036558500803500d000d03a000308100a18540480b11901070084980107910642030603000410f26448602101d1140309403402440c959504e10b1000d03240f0103040e418990441c4004d00c00400014080d100a42c000c4d0001112071890102800410141d10305094140e1440c1e0800d21042041d51400aa11070a551044803440c0c0049420000c1c40300601034100c020b907103d41080708840c14013030724000940c042c824042051110000082c1c0e5903903000c80c0d94034000e40043e640b007003c000088001c83c03200e4809100034008200729603612680200c11407960400c014181d40d80c40d0800c11881c055800c0001c51209010145e4458030704400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 208796843 1250 208795593 208795597
    0x10b09010306090c050306190605060f04030b07030b10111b030d03020a1b0b060102060f040c12030c0f0c140405040c05150f120a050603031c0e0a0b010b030921 70
    0x500c483c0d1a1200541000780082e9000d000e440081c040f641d261800c44440300005116903800f01d0071a14244022403e41012411269080c0c4140c500c240342920f56036491a00501c020b1225040503640c85d00404595100003d002140300c0e15074420f08030161149040c1d01300030940030014140c542c402e09105058402203850740c0202c4041c140141c0b6505403074401d130345203031608044021601031922982c1c104161200042c0c010007007a42150b20580d11000f80460195080c1d40107030540e800e0396001c00c5800e5500c800c1c40744e41c502c6840c01c00003011440e580c0780c69200e61240c044a8142e14107105100300c0b5084c40c020050064125024405420103440721a01c101084c040c0d00c3c041c00c02e0720082c5001c210041d003210307203140d0b4030005c40e075036491120422001e0b00c02c00e0300d402011a040002150391444d002003691340710708480780520b12210400c0c071031000038074401000c070b9403a005101040e4041500180e12038000c15550300f039182ea030f00d004415581028030301c0c50107103600f0145001004c104800001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 208798093 1250 208796843 208796849
    0x9010c0204050a09020d0807030905030d02031e04030b0f0603060702011413030212180f040605060306010c110a23010906170402010201090b09100b0102122b0504050f0f010b0901 78
    0x300018143c50711541c2c81e0184c13072071050280d08000c20302914410000b49000404620740250384041415071990704041c0c03901c03503902c2c0c0340b00147d109000844507000300e0407814400b4800e4083c40342c0b800c0da5981e0342090b40030044440c0b1003d8601d0108200007030506200540e4011450302c0200b100311140c0300d159461130700181140000611403600d010400d4020000b1031040644205a546c54000b0320300320300008407810015500a100c160740000d41424540034030b1041c0c03000100628116690700c1d0045a442d01d0a01e82543c0c030031000019100c081d1155001000500103480d00181120b1110030b807054000070a07508a030411030840020000254414003210007911140021501500d803800102d0142030b500c00060401c2c007101c01848640c0030002070a280038546500140a10002c100c0160b03245e016050580707000c50303000c110100703c40b044004031540f4004080c0c240c0e04600742c1001c8030001c994080301e040b116580486c1c861440c200c020421031207070704403c80c001d01180d44900041001004c040c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 208799343 1250 208798093 208798099
    0x111c1514030705120d0f0206060d06050a0902040c050408120403050c1201020c010510080c03010c080703090309090501030501050f0109020708040b090301020c011a011d03030f070212120909010501030209010c02 92
    0xe0040c4155038003400700c8401054020951001001d00b41c280c40d4070f4070743c0c610303100011900b034041c1c1c4050a800412041d203d24401800c0203654141500e403040940002050390010030396a00214006940300d10a610070943c1e90350b07a80f070301c0d503003007010141c07802080c2e0784400d6045109100420000e100018030b0841c1e46415218880e412026050380781c064002c1c20a0300c0215402d000401840003546005101100d4140b012a54500060801d047c2224500022000040c0100c0c0000e000c441c02034008804080c40791401e6001e41e5600d0011000722482030300201d0347c9944460510840703141203c09980944490001145406415902c0c500030f072181e485a0300713200c4030108514012755000e50681d074a03504400c00070300c10050141c21400c0003243c00002c1e0740c04140003100d85a801c501102c44c15080c101c0c080c0046140c142e00c68442e400300e800000c01242d2203441c2c1d80b00c0f641004028032a59200002c1e0380111030f100d58208040091141701600407504241c0f0600c0707921003980e8002d2200440036015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 208800593 1250 208799343 208799369
    0x201171006031d0a060b0a0b040801020d1a03070e10050d05060a0506011106011202151c05070201020a090512011508010507030c0c1203090813060509030105010e1e0c0409111c15 78
    0xa00d000c900251f100c0e5114400425002c100000c40071010340050104810075a400c001e40460380c8402c0d5a0650601252034142c1e01285050102c1d4078581c002980040b4030340c0d800b64401c3c3d5070f07900140003103e5400f8101d4880e003215040c00ba030441c2c24014250018404d00308882101080b0030041d545a1301440382c0c2c40c4100489402d0015500e580204041054900e0203c5950328032001c00e034081c0304049428040114a0303c0c00040c901b0b403044c42500c5211110399100740346c0b03524003800c219006140030800c07103455503640903905070070000c541c80380c008100403070000c99680341c10f0201404a8502c0c1702c1350f5090007203420011000074030360b0700c2100d480c042030708000030b00a001e03080c0b00c41a8042e0080740c400b140c011040114681d03400034042c0c040a0390480c028012030380c0b42c4010b000c82c01ea09403005410108200404004003982440712548020041c07101400e0594800401d000d4542c005001c5503400030000b5050403448120010100028100d6003d001c107001482d00440038802911800d0008010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 208801843 1250 208800593 208800611
    0x41503081207180321050f0702090604020d0c02070f050103050705090607050a1b03020f0301090305030424110306120f1c020a060c090e0709140d0201171006031d0a06 73
    0xb400c80c01424001249a00b500c194032440d210700080484c05104126040c0d50f0700305da5401c3e02c00d9044034603102e0500f00c0b03241042c60540c2800340d82c0b140645a140c1c01602444070020591a41c890000f80003e03540c010007625140000344200c082c0142c106030b0401d420b10040225440e00502103404108041d03070f286541d102c042c1819400c214240ba0001d0000f06824941c001820600c01d03e101501e00886030052440d40c403404040c00c881c10701c00d004021420030320008010a00403400c5c4810300001c980384104000e1001030342802c403122051080030111020043c007901d820300342d8418140c0b0400e1401000f212114081950341c1e04ea904402c01000c5600c08103119030548203002103000594070010601c1442c403001400780002140c0d0141c50001c3e5402800294000d100c0d01303e4104445031310260358005c4a2850902001625092060f4140112900c02403141c00e80401344521546006a004a1460030550001c081c0d48402c0641d201404c5000c123004003581000c58018111035110a000408000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 208803093 1250 208801843 208801847
    0x5010806010e040606030506120f061501200303070e040c020606120a06110307030b0a0e04020f0a0e1303020712171e040801020702040f180209070e1e041503081207 72
    0x401c00105a0404c0c1400710000e0070742d40680025020b20340450b4010855200120300540d56071000c0c0c001c030030550103900420b81402030160701c44103560062522a00881e03008020a1444880007a0391000740c1c000000c008005520000403902c1c500204d60a1002440540f0000d5841c040600220311420a1040900b1031b10800c10080d482c143e0b120304180581100081c0c0c20302e560304108c50520220b428020031610500d0000b803c00142c8542048105e126101c50302800800c01c0ca0190440c2c02030312842000c030f4007194140e11540b00b144101511a00c200462a00038200102640f0a400000010306481d0000d050080ea44491401201803d5160f00c1300c403c0c10740c18a400c00c140b0394014080000d005c1030340f8006400070200c46000340c1e0180141e440343c40e140300c101e414a0124580070003400c1074a00041c64502c4015402c19140c0c0382c00d201e00d4044800081ca900a01a2a441c940d1810f22200403181040d0046101c144840341d020800c06107103443c0c036007591040f01d181500c50484100042c1c8028 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 208804343 1250 208803093 208803107
    0x60a0c0e03012904050108060109020a1403150f10090b0310030c0602070e09060f061201060812070501140103031e1103070f0b0f06010f0f05160614011406040501080601 74
    0x8000500a024101161106141c500c0e0321000b0342d6202c1c41110710500f294105401440d04031510a0000c0c805030303203010308150094128542820822004264101d904000c2e1000303540200c402d5040c0303d44000c2c2c02c80400090f0240d01251034041c0982c40c5181c400303a50082200801c80d4092a041552540d900401c1d0300d030210b094200030900000810003081c09640040c403102554144070900340103440d80407115580b054203d60300107501e00311000044160800f06050f040000c8450000300f40c1710303120700c4d034030b0b0a00d0740e9160758011501d4045404420311009020b0061021000f28582502c2c1d41546c8008014149000300308801143c4c010002c003007240301d42391603a40421114182d9841e0641442c10341d400a1110364280c2d400301d589d00c0030806032004e2000850049905849609040c00300400945036200c5800e1001c1c14803030140580542100f0030b603102d080c420301c40d07140000d6005019045681800d81170b0490b503050804c1d1b5081180d60b4480e9070440d0242c8009007003ca00c99079075074004031659 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 208805593 1250 208804343 208804367
    0xb0a1802060f1b0703050606060918010602010b1005030912090d080a03051008010b0f10030212150111070303050f0d0f090501090c0b09060301031502040b0f0a020705010908060a0c 79
    0x202002540161140070070303010300305000034003074840f1045240200d800d80c0c50701da50001420941113036001c21414508880184414200580105215410f18007883e4001109902080c0541d44549c224041403401c4941c500d03001110b403c10780c0c214140740241d203598220904020580440014401c9040d42d122991038480039800001e10742e5540a280c1c008000c1d01050303619a1070301807044804120001e040c02509101640582824071340541d020400034015070701d030726010a15608001a46440d11940101449440d01184c07100ca68404440010b100c8000b21900000e650050141032000035401012680c020b1100b210090b225405440143c00400d006094100d24900e404052020043d064120310a401c1c01103c0741204160381c1c50302c408051040c40d800f0ba42c459010001400040c91002c0c1140016200c0480142815101d1401085a51110302244004000401d200000c0c0da41081140c028103000e00c1d040b021b00d807a101050f0b0342c036103000e0b04801c8940e88921103200340f207115000760580 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 208806843 1250 208805593 208805599
    0x20a02060705010c09090c0e0d0204060f0326042102030705041d0c03010506060a180510110d030c0c021002010f060b070b06030a1109040f020303030709050f0a030b0a1802 75
    0x1d1a001490464000c100b1003e141c4046681d4090000d40001c00b072085010321102038540e000308900460030418045402e01003280d00035a00d20b80442e4038200d00740030340090343c41a202c081001e038044c00152000707001d5217501403824004000078020420714041d401c01003003030300711108540300c03103840042d042071043c1d009281c0007890008202e03400c0400241405000741c0c1101a10380c100d802906150981d075003201c0094001c01e0401504c034041e07206e032400300c0000c04440070700c3c0d00042d140d01c0041c0c40d40000c00050000641808100d5031114028086a040035405007410002052503140c06043c4034000000a480303645c400c038459013041e0007034001e5078a0411640f400c1213030741e4071074041d503481d40c00541e8155240c0304241c0018040d03081c00200300300440d40003000b0407035243c6030800f040700b09840203104a9081f203440d00100010786081020b18003441141d10389030300390341c1054148901d80a108110500c2140603010820102e411304080c0d5802007028100492601048081d0585e44c007040800250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 208808093 1250 208806843 208806847
    0x60d0201050c0307060c05030115020a02061b010204030611090a06090509040204090602120c04290d0504140d0c02090f040f080a02030c0a060c08010501080907060806040e0d0903030f1815020a0206 86
    0x748560f40031f8011070503076032030351800004054214001c1b83d0328003900d04000d4001104101140c56452005200c85034424408000740c81c1c1900c036a0b6440540b9542e07943e181c0110340c0800c5885203072038000e84200141c2001e14050f10241d00e41030008040300c001420290085c4d45d540040f909101c1ea940494100354481d4007200100c1c2444040d58119900c1840350a4003080100182c0ca0000031900d10300e9040c40c840046a4141070101080c04010500a8011503001c0c250a4640c1240d640c2802200c60f0500e480d1502580b05215006102200f20001c100c810b140c20302c03004110010315410907020300140c000701d080f43c85201d1660240c0ca18401c82c0703200007880c030030340f02000100701903074121a0308030340d05a45103215a6600c20040da0344000030346520718150010041070000034442c80e6542d40c4084018000b05000b13000030301c0c0d1411700c840c2060303040009242d042c0600a16410112100c062413180c0b4003a603c0310b0b01042c820202031018001c0d104040880800b403424244200210340c000c98004018a07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 208809343 1250 208808093 208808111
    0x60e092a13050906011505160813030b1801150b0a18050303070b160302040609090b0d06021b0730080c03030f0703290d020406091a18060d0201050c030706 68
    0x81e548413401d1164200c045201d074044c80b405131203070007903481c0e02108410081c860100c0d69518602500000d103200002581c1010000200d1422803049020306008c3c211000c41c0c603200204c00303007500d09a070541c8a0040490b0800c220340481c02048070300051a070300d440741a83c2d040d01481001140c0cce50f8051a40f40c03101281035800c0c0a4080c1c8454020680c07584505071358800c2c04410b038240d00541c4503050104091107004c0001203d59041544110300091040d0b20303004d82039581c1012608541e5501e0500361104401d80000303101040400c1c05018800000090b000c0000e40781150116000c0111000d060320b00d00c00380401c1400e0056130300500b007950549480307203084001c02c00040003c41d055030019080c01e81e00e08c02d84006070981015040c0451070a09001c03900c0e014030218040c5000200e8203d5030f00d140004a640c081d20402c802c0100ac4c241488412201a040010045c00040000190105001480010f540d65011400c2880d428207005481d8041640030908602074040041d01c0d16041c942c0d11303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 208810593 1250 208809343 208809361
    0xf0806130f02090418030e1012060311030c0f0a0915030818150a020a03030b01120c020c0f0108101a07080315132309030f0d060e092a1305 61
    0x1d03007072100d0700340c604009600f01521407603045061707503402a002c5058040da4613014140f02d503c2c8800307501030341006003000003c03d40c00c0084a001d035209076080a20b03031894114038513052000c54001c440869071400d0698406002640000e03061082c80b108a94810000c114018a030780c1000066030400d501c0e80c4c0380d441042c1200c0e090513a428500b8810b54261090761902d04481003a102c894200d5030003001d00c0c1803070303640944c002c10b03180d40076505000600520b0442d0980c0d40c020001c0000d50740d4007401c68009410284418411328119042c140300c400400c03c41010004c0d05c40204844041800802c2e040703200006040c50311030100090a070351000010000c00d0446032391074050210302940d6142d031040d41016107000300c5011365280c4078602045100710201c1101e420710280c02c201c80320300703591408483d804601c03084c0d4000c0c030141c0401d540301c46040001d404141c030200e47c80a0300c0c201401ca002c0c141c091001c40d0314101c0e00c0c1c040b1960b600301031542454581d00c02400e090401c2910410a40c01c2c02d100c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 208811843 1250 208810593 208810597
    0x40311090106090312051602220e030408031206010912080702010e09040803070c0816141c020a030c03050702060403050109050f0c0a0605070501020c01060f080106060905010f0806130f02 82
    0x6114000c02141000003020791142c07080d0001c40341c201c0b0310460201607140040b0360b150302c20035070719500c21981072010015075590b0b0044202c10144903d04403000c02d60341e01d410240d41c00d409407010103070004d120801c440140882112502080000c030890720740d54200c01a10790500c3d0390000c08c0004180064403040007810001813100034002d81f00c1d24902020b040030409055800c80d00105441d6090012440c05070052117a00f42661103100c40505159554800c0e1907109414502138030005280d08420780030321030a00240580c8021a125050070070354285000c1e503160040d034030040c20428580191410b2500c00c0c403d0f2035071198003c02c0e1a640780d80d641040c0340070300468601a80e2900804c010054940300004940141903005010703000428600344d8281c0b801c1c0c11500040d11295000c1041024501013841040f01400d00c0340300c80308804d4108a010713403c44075182c00c601d0904c0414001480383c0c0c1c1c2c1001c0c2c8074143d0b805a1400b01c0a60783c4000c00f090080110120610002e410701422460b803c000c0d0300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 208812949 1106 208811843 208811873
    0x11404020c0a021201060905130218070309080a08010905182a04060e090d0201020c0c0d0303090b04051011070b01050103090c030b0f060a08030a0819110403 69
    0x2241e00f0100c03090030801c44c0d175540c04c028098810144a016040150000c0301c3c0b8406146601281d041d40e02d0303042c201c000743c40344d000043d0807910036044000c046500522207516040015805800041e00307009210710207060070005140c08c1038070030340000300d5580c4078010444451484100281405102c00302c14007843c048142c4003060f180c601591006002d121101482c61501c0f01c1e820341082010444881164010071144220707450000701c098050710103d4121408814914080d4010b00d583c2c98020f0148c54240e0801c414071a001c1144200070b01d40301070070702c10221501c0401136079226980004104281c96001440380d94881c0e48044480d40c0310b0400100240e03113949942600c00800c4071103000b2400410100300607404c000c005c100c001d00095000750706017146100e000e03080060050424900d03019a0302c12001d108442d401250814043c0c0100b00d54850b00c070305000144100b180 = true := by decide +kernel

theorem cover : BRFrame.Cov 208633093 208812949 := by
  have h0 := BRFrame.cov_init 208633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 208633093 ≤ n) (h2 : n < 208812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
