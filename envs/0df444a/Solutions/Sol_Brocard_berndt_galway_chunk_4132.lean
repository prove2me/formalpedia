-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4132
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:39:51.539729+00:00
-- url     : https://prove2.me/submissions/a28ce686-dc91-4b63-9a86-ca742ae956cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 742985611 ≤ n < 743165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 742986861 1250 742985611 742985623
    0x603100e070b0d0b0306070f0320070b071707120501170604080a18030f0506070c0c09020a030b0607060b0118060f05070f0c03060f150311061c1104091b02 68
    0x811040d8060f1a000070740c010100400110300301c640c040c0248401c2195050b40700c0300b0101c0d403050a4a04204191406541c491703801540419020070b004108800c80101d0074460500e41d0215140c600003011620800d0b4402c0404016202c1d100454000030104019150b6409541d000d010f29a850078018031210011554031540503001401010300064199590303032180c3c4029201c07400c801c40002205650b80342c004100d042c4103030306444500600d000300e0581c03407140742d80d4038031213802140c210b4195091445082c000d6001080e5101490703030700e01e07180010b9110b107000307007070400d00a4000103126030b206000500b10305698001040c0c9841103800c2032011580240040101c2505860580d89411891500001c0f60080317800c00f40107103099050000c200111900320202408220f1014800042180c89485207111140070041c4034400a142100c01410048003030002d401070f0b102e039a14564801e6018a00319403085064005001d0300107418040c640c480c1c040c003034100c60049108080e90048800003074480d6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 742988111 1250 742986861 742986869
    0x1011150c070219030b010e16030b030c0f01031404110301450605091f0204120605060a03020d05010603030e0f031902010201020c2a01020604020d0b0c12040305030603100e07 76
    0x55851901c105101d54010f400040d550080c8808003d584851607865000011282130459658407031201000d03c0c428025160a150007a006104045000d01045103c2880b482c0050400d50364907400c0c4110710000a000c0e020740d00030469900d00005080c00c0c142514076030b641c10b001018030282c216030181810810003a40281c62451000c22590301280d016040740c80030f201070420742c14102486208800480c800401c610103244040c000320240d6a50011780c0100e10803031300e42d0321244014034040b545507084541c1c41a4000c0032803000329107070f038006102c0e200c854006030703281da41d1800107104243e000703848904855001c1f203248100050b0140081e5660013030101502100140308000c0c421a4003d4041d16034104404003640c0300441c0d138814100c800149455140d200005480304080d62354000304001d03000e541c0140040c10301011036211000001000352852004201c10031482c0d1203100300310b80c1c0c84d00840c42a9100d84d42c83c10004200b516021020b0040700301c0a2620a41e0040d42100140550441d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 742989361 1250 742988111 742988119
    0xe01050f0117070504030f050c01090f0b070803090f1e01050a090c06030e1204151803050607180801020a03022205011d0111060c0712110a02011d1011150c0702 70
    0x10340d22950100d8085c051580300405481c000f60700c40781000b0700861000019003080c1d0300c1c03000c200ea5a03652040c80b01070b11302c14001100d03803c0203103e002c120000003c5600500c2d03c0d0032074548040c071422aa182000803021900604000403005481030020301a064001c40803140602007080070b80c449502105aa00c6030300c0505641d070005640c02d9005022500190200c4111329031125910050300d981030b481d240c0000002425030b0018403000b030242c540034054a030048000e090aa950f944155145494521061440441c01200003882c1e242400240421240f40e036026856004048802c040026100d0750f00c1d0b20a00d240006209903640000301c0f049242c3d01800e03030880b00001c5001030315140c4904000126a0107043c0030850b801c10040020303c04070740704040c510720052421100700c2c1c007a00c20b0300c6000102c1d04114692000b5601c00c9070075002c00c400205c00d50b9035640d03182d80000c1da070480c4143d440c4042030f0700c2505007240340300c10300c2048412589100b4208480c43c00f55070000c0c8034801d000d0020702c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 742990611 1250 742989361 742989407
    0x150e030316031224060813031103070f050102280f050f0903060f0402280b0715050f010303021b060d050901020405060301030b04110f030607030c0e040908040e01050f01 74
    0x18507202c0c0d10440c03800003000700200b00b00c030102500380b410707500b00100040c010790213120006041c521440d0075a01c2048503550030000c140803550102d5000100005078261484203024035008078201340085108588030350001661080716a4024400380c28280d0714011480700c0e01e83c51100560414068940c083c6c2da031401c555154415698103c0c24081c0d05c99443c1c051190408000c40c0346034035400240118000c481c880078031525551900150603046848844a807902c1d181003041c1c4104101404030a445170215007000d04590f00c500c0c0440c0ea044508504405802e40100140f5805101d400c1504e684884030408440c134601c0810550700c10750100341c00c01ca0740e52000601c0c002003941a60003070031000740300710364a595a0600070603801068070141c0e000c3c42480041455403900c8001c80100c007101074054601640d55170030a400403c1d8041d0540240881407a940e80d003940c8910880d40c0d641d2055100c26195401c1c070ba00d29401e400c0c141c2006000b07440e995041130b0107a070005141070000b0309d84407040c49 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 742991861 1250 742990611 742990613
    0x90512220b2a010c12060e04080403080319020c0604030f02120906090a090504030c1403030115030c020c121e010e03190c021305040b0601020606100302130b030f01150e030316 77
    0x2051001c020700d14081035103842e000b1013041e40c1c080505201c0001d50101031100684401e41d0a00f802c4d8245c1d001010a481000100000343c0c1d200040e69202240100d8013000c0102d05117032009a9010740c23005611600030074200300c10141c01400d1090b0281451000b8008002c02c444070509520407050464031400c80410402000d55035000241e0282900140910035401c003481c0180c1b00000f00da004940c060759404c0c0080c1d1010700081524100c40c0d5201040c9411521210103400400110a540c0214002e02038140b801d500d5400091100c0d029a400402415139190b944404000300407a0341b000c140d050203500310021100109640c44ad0b1081c17859040300309500c52062301d1501c49950000e40111004100d00f0b070460466005e1403056014000920341130b69840c00490300d6800c00c803040c5900048101400c10454401d5000c4d1058400480d408038a180e00e9001000681d0400c440b501d002c10390303050041c01403c214400030030308203005040030f90304d1301c84001c0042d48174050513020b1484002c607610258 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 742993111 1250 742991861 742991917
    0x52b024017190804051c0224160c17030304170c07030b01060e010e06070c0303030f140a05220302061b0f031501020609120913090512220b 61
    0x10720b00c0e40c00c84010120711821854403c005401a1040e40d1090032010036512000f0003929446201a80c010103001c07210100034080440400040d42d802e18081080c803038090381d51446055011024000d078842030049190400007040a41300f4a01106550024020300001855128000707441041b02c00c01c1c00d49642c3d8039040341d03150044075803003d40031802c09400001d0780d0383c1041e201910701a0a07a5114000c1c031081e0140250b5202e8000c000381038407078910081010034481c0d80322440152440d103000c1120003d215445541c0c2c0425105c0342291035848017400120b82411050040341903845220808414040c1c40207920380c040108407941141c0c00b0060b0103c4c1d48030200488140c1c43d90800c2190303c80c101801c0044840c1041c2e06040d004d40b00d0040818a00355000610700301d00820300d442946131003413036020321103a51503081624881c5500e405424000400070320100c0b91440c0a40002500e99001c135411320000b50900e5081000c10251100500c07000c0710a10886a0598200c40e2462011101c16000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 742994361 1250 742993111 742993123
    0x30210140f090d022d0d030f030509070b0a0201060e0f09030f03130b0115020f0606060a051602030a1407050405190207032d1806052b024017 62
    0x254028281702c90100340e84c0c42da01010790804038a2601d6100d5002810520604101c568001380200340003c001c40c03002072003a0400c03a4840009410b40d880980d9500240c54141c2101c050000980d4481e0024002018100b0000e0b46c400340b07528110308a410039000b09074a074840c4140c4018030790030000020782a01950503021035180c0d4029152041c1d580d503030b0301c400b0b40c1002070340e5100d005004001d040301100d800010203901801001701010301d80040c5070029207640d030100c02c0014000078112890005030340c040c040c90000303902480950a990b030805d005035040c00a5600014800c0f441d0009000489504840d8070079211385001e80140d803080c44e4142580da01034010300112840e0038840064410f960700d2002c039500c68545840701078120b5640c00782c500c900022070180c070000030820701943d503541c80c2d100d800c1d102a81d107802089a20b80c1c0b440c51160141da20401030703100c800201c6800a20701c03807802009103031800d00d00e40700040b50200e494106110500341e4400e20714007070660080c041b4032050911030303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 742995611 1250 742994361 742994363
    0x40b130206031e16020705010c0c03080a0302211003031209050f0d030c260c0c060406060f05010e180a020903011406040b120a120c020d0606030210140f090d 69
    0x70660310707407403d4101104030304028168590001c40f5030340807807400c0991001a4019029503005030a00c1400d00004581401c03852805540000003d080000030500150080002c824199809030b0355000405400319052010000308207011111400c0180c414041410141901d40c180780100c0c2e4200803940710005040013150241c860300518002d4440c0aa0009100000c2d0140d0340b0306106040100f6415184000001d030783c00300f01d40035880800303168107800400d19031005621031424101031001c04001d2908001304d4044507165a13940c01442074448103103200000b407809290107061102c40d50045094103690700c690421842080780030468074601c0742c05580001c40060000c202007a224003100058000544003140a00d1409868a04034100004a007060802407001041901202d541c0d02110302401e058004c100320001802c440140d4a8028041081d80504000308800b819801009200400d10707064106001e01c82000b4264001c031002075440035514052016201c2466402103020700c008444c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 742996861 1250 742995611 742995619
    0x1501030b15180906060702011211070f08043003030e10020a0c12030e0d0e010c020a080607080f1b030c0909040f11010509011e201509010b0603040b1302 67
    0x9001201c008036105100c021410482d0002010b48499060221780d00ca40000031f400030341030342265480410790780c100126a524000c0300c0740c60b042c681c2d100d80700030081c214000c60f2038070400603081081d00c99030000601480c002410301820b03403940d0000c2c00300a5912840060600d41c46080300541403005100258904a45c030b1303000d42d65104804001440c600c1400d108803161094016044c50407446032141803002c00d4200010054030a00c1c06060b500d14402003011410480c01d015041c0040c1c81d0302d0300344001030112a0090040341850340000c0d1030080c00501110b0b040051008020f01c402c0e0445616441600368040c1d65a652981c00d480100391098140c2550030041d01030601080280c815800c5011600800140340c401c030520b00112458801c0113002030029038507120b03204029001c072249048090b5a81801e502400c0080001c0511b83c0002e0000e01d41d981103401c51281c8003000140d00780d48a51088002c2013540c07031040016a035804045c1016000b800d000000401d01403180b03e2000d10680c00030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 742998111 1250 742996861 742996867
    0x100c080301080c151e180604091d150105130612050a02101d060c0f0a032c030703030509030a080403151d0a022407060506010f05031501030b15 63
    0x10782d0b19a41d80b1081c0e240c54000c0381c200c035902c40b40c106101c0568002c840b03001c140c0c01070300003040780820445d0003640442d00010864010864190b40d00300c0200014185c002c00410050b4014130108840d0410707810300e08550f001600f0003000301000e20b00a5054a10844041c14880d003c100b0308001404c094002004000c5880b041005110300042c05000035442210901c3c0c460084040803034010854204c3e0007250301c801c105001441c580032000c2d1004c01c042c2c0381110701c24015840b00614004105009801250149030b04882040311601c2005030080c5e14000090542c40000c0480d6039400648405010000d01142412190760140608645660411003503920f4945a01306407a4141500820811144c03518003012006150b01034101c80310041d240c00f41412918507000e001204c1100c80c1040074084a0903400310300c2c0135440000d00102030007000000303264586403001411032240701021400b03010041c4200039405801c44c1da8016541ca0a280100d03202048501044e208005844da04101078004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 742999361 1250 742998111 742998119
    0x7080a0c0e091203060f01030f14012103390507080610030f0b07030b120c03070e06031c09050904151b050915070501020304030c210e100c080301 64
    0xda15140141d0340c09111031075032500c5042c1115a60025165004802c40c01400000c24514044490241d01032060402241c3c81e40c103031400c0381c01c48424805444000c410140140701014840e18209125244003d45c000900c40300c3d20f01801e11346a0b1300c003c0f1900604400341da5002e00300d10a01c03070a031045017007068005082e58907005032190414040c61030b140c443c92000404003100e4010740b000701c0c0d4105036500c4000b0102d4941d9800c200c030041680084c151200328800c41c81c0c4501400540c0c403049030f00544500c0001400f05402e010040c3c2c01001c1d41d05019043c00381319580840d00721000ca4801004800c0b2540c41c440640309126141d104030341c007540fa50100410701c829030104480040380b10b8002c0140101200d1170624045c3e0300510480020005e2180100d1070418a8023010001d070440c580b24104a0035580b0642179034003c0750100d00140c101715280e401c00c116030f030485074a0f40c1034042500c24011005070040480003d901d03030341c1c481e11030311540d00b2150313003c1d000101d03a090308208078035569070b11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 743000611 1250 742999361 742999373
    0x240315070c03020f0610051e0603192f0a0c0203011d0f0d090603021c0e0309030709020c06131401050f0910021228060305010510080102070b0103031107080a 69
    0xc0007005401500602d102040c07020b030003198182c41070b030713100700b240c158907090030180322411000038440e40240b10007100410881d82c648014501c1040500e05424150340d402603401e041d11820840c1030a20025028941c05a02008841301c030301404081c0040c1e1160701e03040c004c1b100050004c0000e505946801c400c100741801003100b0b1000d50ba245011285001c40341c00d95540d980090409000c00070319243d1080c0720b003c5c881c1d0010029003c0c41004a004003420340c00d91803c075031100400e00305c594400a828809802d0501285005101d04141103040058900c0c02c1e54440d04000c100440b004003200700c5034100b06030342224181d004c011400800240c0f42c04c1c2c1c011818442c090302c00c500103100f09120003023182a0380c000c441031800a42c00d0301e140c40c1c40e54070380018603480840d4040c190034400c0e5803580484506120b00070045005800100b0030781810843ca8488030103030b811030340701039004100c920045001d482c000c078112985450100600780e9807042e030f682004d03495081008035001c0c0c40304100a01c50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 743001861 1250 743000611 743000627
    0x180916080d1404150c300807020106181a0105042d18050f01210f020105040308180a0605070b0f040c080109030e090a18110d08042c24031507 62
    0x8810107002c03035010000d80342c1a0b002103808001c40d40d00001b24051603a5035208107003c0b500510217000124070b035034071182407480018220040501d420360700c000f800b02182d0f46070024070340c02c90282041860715052021007a41d141e403e50004400c4100340020224074600c401c042402018050881d204c041d0661481d9000381c80240c4020740f0b0303500102c002007201c40c440c000085000e06134501e0340017000d01c651785e982d010240a01c4241c0c10300009000000105010100800001002c0d42281003000ca1180810040e035580b1b401c400d00708041484613100040704009030a03045040ca488450981d40e5500d012010031a10f504884a15402e001240c0209601300b8110406040201c46000f466564a04540100d51741d12072070b9540d990100b640180460171140d0210071840002e03001e550780d0082511508116800ba5001c4000d8003000c1d50801c01811000324481c105c84a00f80ca461440d040c1140415148600b404100c243c00440c1c4c800324200765009c000040007600c000b500090145089440501481c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 743003111 1250 743001861 743001863
    0x30a0605091501060f0f050a0905040f091e05071212080901060f08010e0106120b0414030909040b06010f0807020d120b040606051e0304080d1109180916080d1404150c 73
    0x31b00048060038600d0080040d2000c0c61890f0f9590001c1ca441c0104100242026028814400703590ba082440416a000d0f01d14501030b0340d50341d0302e01030b02006e0f10b851403a040312039100d034041150f0505240001350700001314512480a03487e1040e01234841c2081140105215442095041c001c6000000c0d0040103401030200000000020072100342e4814039940c1400d00741c030004001c41d40d1100086c00042035080610788007280c880c103c0f810000408041040c0d02400d940640f80c01046500b08881b80d0380c0990039950b020082d140450281c107103500d000e0340d11031150110905006d074124503036405035099400301030b07030840080060158540c1d40381c3c05051548004948841b13002c14406503c0c0043c4940110303402982e20928140c03a29505844046c004c2684034a035020300502003000100c1c41c0d407400c202680f100102546d409032420000c0e0341519154603417054401d1031f120000308010845020450700181912400d04040314102d04c42c41d90a14825500042c2c09a01c40343d00340011240e0165105c4a02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 743004361 1250 743003111 743003117
    0xd020a1b0308160c0c0905070c0b19060b160314130b0306010206060a030308060607022d0103231b0403051207030e01080103050d0e120d0302071104050105030a0605091501060f 77
    0x40743c1500084540c604c41d4034014100d0a020300c01002030b42d04660005602c1021881d01031a0b0b0085c40d6241c00c81403c0940d01c1030f01d071980080442c1c0000b0400e1007140001e004001145d841d044950b40c2c1800b502c0c040c1440a000c2c41a54100303022107500b0401110080c807400307254020419143d55001c800e540054603a180180302c0c1c0000034410781002c0e11850140c0f03405440d84082d994440c4204052980062822070300204503900071425030030f05d20b9440541c1a2a4061240000c0101f40010304442e81085030703d520880d01100b0b402c084500e26030f21038102c418101c081403080d40201e2a554a0305c20350707000034407a01c80d8410a0300b04401c600c028180c01780c4039a41740c00803040c44000445e04150203000141443c4c0140203888846070241c19407261444001e000c00c0d0100142d01d01c1c0d6405c0207180b6040300c01003600021240c042140c0007841070400782c0c00321400c005a50425000c20f6980f804c0c600300924465440c03000c90038a0000704120340030f544201c88030074981e40c1c403480e00400d00e250400310782004c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 743005611 1250 743004361 743004391
    0x204080d030f1d1203270606030115180207020d0b1f050d0b15010c020604180e010216031b02041806150b0d0c0c050d0903020a08030a050d020a1b0308 66
    0x482c003a06001c0f031070031142580c003c01c0100401c00d20030005520290507500142c80d500c81c2200264101000b42010081d42c0000d012031b4501030050500756114001103d03041c0c500400203016001c52200d0790100308210407401610381d072061011031031504e900e01c00580024020350420044444200c8104461140c045030400d10306da0341d030240a03000c0b041d624010104140c2c0400101920a51503c6400000c814544102d902c0019004503079240d105421202e0710851441440808a400d40100942036101c54000c5261180c1d07181900008020a8002030820001d03039400c40420107841c0054886030b4000f0410000c55000c0020b90880840c512400c4a905040400c40c4040c0c10b01001040c0488000b074803410f02d0044003042c1400241301a042c0c500521080b040c10342e0101c0c400300140c01c820081500c81c013400d03078110300400001e403e0a910230803ca80c8108482803040e075000d0b090700d0701008040005601d82c040018140c0d42d840c01e1540921800044003244001d150384176000310300981100d500e111b8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 743006861 1250 743005611 743005631
    0xc100302030405060105300303010503010b18040602030c120106051207031404080c0703060212010f0b0a020c010503061203072d0c121b0b1216210204080d030f 70
    0x1030340000c840107040707a04520010042814070005905842000c0e01c1681040118103400300408200380300300742c0c2207520101c0180040c7c102441466517046d0102e0b88546846100c090340ca8a90000510080c01c4035008000710b034002d0304440075140b4079480c1d820124000c0da114480240f60784c01408512008051040101c0e0b0401e0091040902c0f5011100300c40196075101d4507104520b50044080078600d201e04e0000001045c1a07201601d400901c40c5680c40b003952500d00121204a0103401c030340300780441000790020313161700001c41d006558801e090160710b80e03981c0303030001d5074028020b5031800c142d003c00550303641000501c03142120500884240c0355405806843c4041350044a1070006240b00d49240040c052884002d510b8000f103803007010740c03402c1e21501d4203070710724103035540d5024040130b04010841c50014074004510550002c41c102c1c203000f141d104114001c15280704055068071b9200c440c0d0400480180d5901210050110a4101e40112034403250040081290050b0110b82c0c614002080d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 743008111 1250 743006861 743006867
    0xc0308011d04030f0e0303220501030c080712060f030f0201170c0a030e0304050a030309061e0f0c060b03120d15050f010f0e0a030f1103010c0f031505120c10 69
    0x10181c810740000754850340e840d0b6906440d44124a40000c05011085c402c1021954040004001d02d00100c2c55507070320030210f8102d6400e1004d664020506060030040002d0100d41d008800950040d00c0c0e00d098125018110444401071400c0e40051645064201d0040b080c0040d544140480754401ea03030382010310018013140550306506031071260b0701110410000500314401d80100f414100301c08192441c2030b948100049680d211035008401045003544100720344c0d601310070403e01240c92400381d4400032410710002000e20704403801d04414040d00b00078540c00d0149d00d9000014104000d0f00716224ac4104005070081e0340c002600c0020564100403000388400c1214003c0c50071030720b001e1302c20803401545200549184a403480e040c4100000c0d15a400c3d03095840e903496000860141c0d2041e0420740711030422215081d00c0c0c1045501aa041c02801c0c1c194580c06031380ca941c103620a02d0001071601200400c40013840c43d43d405a40d01c071074180d03145526118003245110a0040071251702e00d4540f0004016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 743009361 1250 743008111 743008139
    0xf0909070f050f1b0d08041a0411132d0c05042114100b0a0806040c0306020f0409060b0a3b040f05160311070b0c0a030e0304060c030801 60
    0x440000741052200300b07a480c0c02c90b00070748401202404041c0c00d00d07401c007090600c1d00e041035045d080000d001c00c05200610140100124000c10310341e001070041e107050f41714680342140d8903540c00d014541501c40803000c0c00c3c3c00c0d07000030b00086100503641c05078420812608424000711003000c980728946085d84c0d00c090b004038226411140f0b0b6401814210b11030803158010545d2101d81551000c0d0440d00c14101d1030018002c1c0100c2d800c440300005002c040040034000c03110501c1d00300ca80c469000a040c0008100600300010441c0d50260025030b50700c0c146040e24117280907170740c0303c1240203007401d00c04140c1c0d0b5991f030042c1035000c02d0b80d915101c000303031640c0300d0841c003c6001000d500c0044201491142800507004054821240a4004a500c584c1341841804880046503107001a05000540c1c081d0103506014114003401c4421005082901d940c43c0c29842050180918071444800140e242081d406500301c1c000c003000b6a8207894a407541c139400035000d0038042404800082c50500081006090b201030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 743010611 1250 743009361 743009387
    0x92906030a110616021002010507180608040b0603030405042a020c150a2a050c030601081b041b020a0b16120b03010f0614032a22020f090907 62
    0x300c2c0c404070354800b040c020720742e03c41c40204032181c001e45800d82c0503807520002220030101643c00099585800f0030018100d50f8224107010700382d4001041044a80d510511141d0001d4010941c12850349038030300040c0c918071440d0b000b960401d0401c07030703610b031444401000404500c8942c503041500748049002261102000d140750b95100f44220140d010910401300600840c01060030b288000c3c4c041291032443c04160041d0418070421640b104800300a02400040c00240e1f0a030000e142d035504001c1466280c0521030304850688041d801e01501680c0d840e040552800c00d0404203c0519008403402904d4052000c0d00740c420130290b0010500c000c40400d0a40c1c1074152540d00c060320007041170b04c6280a404004070555156403101380c00010100b01d842024001c210500c1c01d0341f60855140d00380b50038103401c000001c0c1ca181010038103030360703c078583d01c403072140b0150450300188018039546030382400c01306261540c2c14052001c140d000c8000d94020060029045c11961441d2694480c901101d203031a01050f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 743011861 1250 743010611 743010623
    0x110a030b130213090515071701120201020c09071d06040f081507020a0203150408120a020c070603020315040b031f051b030424021e12100f05060706092906030a 70
    0x18030100042c0c6c40c1c040d150b0005518a04003030a20b80705106c4030105042a0414aa0303180308082180c115a010004c4240d804000d541d040314500e42404060702440c40201300b0900740040500a002c296a0784084a02400b0300741d10b04520940c403441c84d07598421625401d96101b00e050340102d00030038000101540503036401001004504050740d09000300c0d29000e04200c40031034003407100c0840b00080060302807148107101030058403000d20704000c80c80e013401d1713501480600d4410010b1201d00f25038040a400d1200c0241c502003505844900820310300030900164098131041580031120103851600308a002d050404990880f548800380c1c10324880c40240d42c0201010060494461407290074000b24001580c540001400d00710156002400504d000b4142400d50000003010324090b1440310303005030004040b0445140d024144084940750541d180141449040d0102e00300d401c2140c1500460150341c1c0c890802e80300a040c1d511020200300c00d4402c0c401d00c10440200142140c180000c500c000030750000c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 743013111 1250 743011861 743011873
    0x12120305100b19030e010c0215010f0612150b0a080108010c050306100c05190c030c080d0f0507020420090915030d14070516150516110a030b1302130905 67
    0x14107a00c2c00045018500404c2c1503c1d40141c262040c401e2007108130b409a04e0300030b401e80314613120050325810700507003002100301c105807801d01007503501c40c03103040c114035844000003081c412003000030144192651081180b0300d000518000c0c030319449400e450488000a00078400d00362049401d45070340c00101c82180d084458600034034655031140f140140d555000b041912110714a50b808030201200066042d581640801d00404c1000401c5401c200100b801e0000742400b240c81c4070300284450058404002007120210340306055680d0740e4049142c000303030010401c1c0c0b00c4940e541165002e40102411a00ca400c2020024036611044d81c40d03903407108030090192005201d034001c203907810005072104010154050052200085080107443c6402e5540c0074400b903e1440c216a010308011503000301420400e060040c003482d9091407180408035070744048101c06451200b40407401425480e40040d084080850078440c440c030540150100e16402030350107410003910b2403443d0082d0303018940020000d41c050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 743014361 1250 743013111 743013127
    0xe0a0b070b0604060801020c0102071406040f14070f150206060109180f1b03050103231b030102070c030b060f180c0702010c0615180903020c040b040612120305100b 72
    0x35060a6200300c0040c40020005c1e164070550f403c80c3c0150070001c1c100c2e94002201c070140028145a000d031154410010500c501e415922640621100301f0001c02d0125809401400c014082c803e40b0040c00c1c1c10b1001c0030541c1ea940d80031200040c900084013015000d40404540d45500c03406941007640c1d0720380070100c21042c4405070480145003c494611941e5900c0d4098140030b0b448600c5100b003020682d50202c4c0550550600c41c2c00908e0184d544860241c01d03441c03200c0b8003800410030344d0b501048841080035090008000c41c0c003900c10309800500061414001204000f0000c0e1030754003440c81912940240101042480342600548240707020401e6610b0001c0c070b03618004401841c03500d01c10700d40a114010541e807100144c402040b40e01404610504003802001c034285803203246032139417200c2400100d52644010303455016800e981c40c00780b0f484604200b400c1d22541c004900605640c1aa45a684614240350300503c130100c0004000900b0400428502c12480ca605400c1e1800c03081018500a40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 743015611 1250 743014361 743014373
    0x11030315150906070c03141507120b030a2102030406090905090a0212010b040f020909060904080c03181005091c11100201020a0305070207120b0928030e0a0b07 70
    0xc1c074021004144100015181615040c029128081c842d0003080c08007411454420300240320403210b076040340d1146d151100030050ba1081e01d50020120f00700103006c14101582c03180540518060a901885400c014000700024456031085120018011001c9a403105400700d84a200c0c41c03044c80c1c00280c88110a2226036040c0d401160400b04030b03421200142d60b1540407900c4107c4148288602d65941e49074078841d401e1a0203951100e1114840851030b1a1941d400190813400180500c2d001c1da000c980000d003000070300c500301d80075004051b040301c0c1c891a86044c941c2c405540d0403101c2c1d00440c1c04c0c0c2e802d1b00b505802030301540d01030038006106c08440f4005601c4942012007422060791001c07000c0c2d00d504100e803110504580c03120242d5001581d075403815140501a500058901411544282e20800c0b000340182040c0c3d9556520076140c00c2c0c2503c510b90814a0f02942c207419021026004c4112200c5255501900494510035111824250240c0c410410300c000284201c0400482c10864007002940b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 743016861 1250 743015611 743015629
    0x308090705040c1110020702010c1b0b03090a060b030d02060c0d02040b04030c06020123071d031b0102060703020c030f160b0c0a0315050622030b07050a11030315 71
    0x814001110865695400080c007030394081d1000201099400b0803000c0005020f2000d00013030b03001c50f1420b44c900f03c0c1075400200300c01d0400d0b82c0500390141005049050404d52101e1f1401040c02c0e00c41ca0f84c803410800c0f0700544402c00d1007001c5506520707103c1403081500b40030840440801e0160050049599050504850707039100712100c1620a500300b101240980c001000350010f0360040b10358100042c1048806800c4407800304041c034000e41d599030394a001c0400856100d611509034503201c0c00007646407614221a4000d126405ea01d8003d20000096036064044076182414090303003283c034562544007040d0101e109119031044e480d00204852042d004895000b4442844910010440604a40c54089920320152007022004d5000142d01d000c00c1d6060051034401c214450b1010402450180010100d00c80c0f01c00d030b9014106541541c02c0b12541c620091402141c100707000d20074030301e014040117101c1d6020072652000b240395071072840c8400c0300001c20b0781e12606011740400038030b100b14010800920 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 743018111 1250 743016861 743016871
    0x7050d020906120703030903063e1b031e0c1b06120a0e100605092a0c010204030201202d030c1c141c06050a0e06030d03180308 56
    0x20f0201c40440c0d000401112000b1806907407040601804e510b440f00507200c10004140035200086003190b00800e100540d41c402c840200410510708000c0032244450380610100340310700e00d145180113240c0c110048020980c0724078040c80e5800446204e5140017603400344040492555000c0c4840340c50b0244c13520b94241c3e18010003811141401b600c860a52a103590440749035030216119140784190b100300b00080c400705c0900702c1c070a03c1580e0410002c04c40084000341505000307000c0040611180e2103040e03c01d50122848041c8035070f2034a026100f50b000c1e5205210483c001072642c29801c0385052100c148621582014020304684021554822802d10218040c121562050207020302c44260410003060018500700140c0403800307220788801074211052002a003400580c21403a03038250340798003c4a4070360311051450041382050700e0342c0c4801040240c02641c2c200c80e580c00085901e20a525295104000840807240000c0c50124100c083e00d030000200d140e690a441440c50010380a1030f040350b480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 743019361 1250 743018111 743018119
    0x60207050709021b0114060d030e04090501090317060a030b01090e160f050a0e160507050102040e010906050420030601030c0203070c0b190807051603030b030a0c090e07050d020906 79
    0x4103441d0805042281d1100d052486202202c100e007110210b001e01421003141d40340b895061b1035140a00202e00d0004031a4401401c018601105a0a81c0c2c0c032580150191900a4020002c442c1a1315010701004002000000246023140000c0c17610326009980c5400d0700da003c00c0b0381080303034a0b103444140030304641c0c1c0c6281c00300c2c001d00c80d0010f07414100c107034864020503801501c0c8074814030386411b0145664040d00181048046042008a14400400002c0035051145440c81e526191820218028040c80d001040c040d0120790000982c08500d82201d815180b044500304500500356a144515032a824032100d40d005081c8002402903005c1d504ca990440b02c60f005481c6405501d5603414601c2205821512114038041844048000b400c84207814141682c03c01004034142101e01918500525038000640d1042c1d110100c109442070308901e01c070400107011115038420301d1030005414040c6015038858141f4249090784072240014852007200c0c405480710380c00c88541e030284842100001e00c80d50300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 743020611 1250 743019361 743019373
    0xa060612200a1b08090a09050c0712050d050103080d060b0a0e011209020405270f1506010c08030f0103110f0a09090c080d020a0519151d0f0102130b03100306020705 72
    0x368012200c081e1502500c00c0d070103a40d445c0140010054003121035042010254a44410400c0c001c440604032085e003500b00300c030a5000216664125050301c20400e1510301542080000010090f13400c02820940000325001d1101c40e4442e46400614010210260006587d070109071160b540200640070810071300d01d0f0301061580e0b1a40204066a07420ba030f00f86000102109003a215190100c00c3e0350a10001c0c801a120550502c0758a580c0c0795140d1141010a500100100300c06a02400101100542c441282c07a140d18151100c030003200d9003448107544009090405407004d00d402c400d5105661401040000d0381420101c58400070500e002c0f00302c540d420041000300d403010082000d8090008694010149a0507a24006041c40e1040020070b800d150721402a9000800d66120400086821180015041d00ea08039000380321005007541c1503180a60814807400b4007042d00280303881e040c400d03d040d07800d0340c0c0c44010b26000d10085801c5054814241d4003440000e805400901d80c2c07500030012500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 743021861 1250 743020611 743020637
    0x40608010c09090b060c070b0a052802071a1b0a080f0301060e090c1b070e070203040519050105040b0f09041d0f0d0806041508060a060612200a 63
    0x800c4840005840000c90708a0b0070401418169004800246506442d07050622071001c6421f41e076010140140d010140d00401c40805c4148140c00b0741d007004411204014000307980e04104040032000300c0c016401402003080c0803480840c0404001c4091003215042450411440648001254201c2c4942028062580c0a201045000010700038001c0035400440e683c3d4540f241c080c0030402c1d880310b600d00a110400c02c100b06144c0c00c6003a40d822003001051080e00d42c1003016560705045598001244580d150003e108801d44e0000181040c3d8000352205000c502d0307a041c0c0801181100e120309400135100708000d0140302d031700102030001403018903030b10782c04c06581d0b1000030162047d101d00c0d4460b441c1a0644a840c81030200215901104400083c00c403038200b640000742541001030032103000d1904d811810940100140611004044041c152080d41c1058406280a00690b200b4000004c0d0000d406601d080100d100b0801040b0b950750a01c05e071468446112240c50300954810400c2c40b9401e4503d003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 743023111 1250 743021861 743021863
    0xd0312050a140a090b0106050a03140c19090806010302010f0504030605070c02010f0c150e19060e010c140423031915020f09190810050a0506100507060b040608 70
    0x14041c991500c0e02140c80c21190b4a9034924100040c6011015410100c449010409015441d070556440d40f40042d910940c20400790058016403420280000c0c1d01000c22026000c1c1d10040d18001c0d86600400c8013100f56400100c58510b070501402000d40c10085c0100010f43c002e03c400b045500c090305201c0e042030f5894950004951048425002041d0480e4140301150f0303011004080701c0b0228201183c1014150311440c0841d54080002440b00baa200c141d5a1112810400002c0303000381c1c40340b02c00320320f043c625108014001c041d41c803209560902d000e101c5568059074070b020780084040c4403281864030742000c8404140307030358403110303401d601c0e240c220f401e41c0c1c40c180441c8076180d8561030042040392003441c03c1c0542c1038140c8407082c2914810301c00000e18140c0d0130100c0701200d808580f514466000d09402034240205540809214428446659442c091b41c2e005288140c210180c10491986e0f0601804400e2050002610000b9001c0160100203a030560202d0b800d000c01a03c0054030f16194002a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 743024361 1250 743023111 743023121
    0x3023708010b0108060103110306010305220302070320010c1209381312060b0307170c0901060827030d0204170d0e0d0f0206041d0f060f0d0312 63
    0xe03006a0b51580c0da80800741d600203482c00c4d0054028030302041180c507039100160041c00094030083c1015280c0700813500b0642121601c6803101c1d1840005101c1035001e24001e036540200b84030407100c2a608440c2a1083c141a00c80c414114070103866416a0143c82c0e543e480e0507407103048140060000945000c00e07601c11007015190100007400d68641c0070405100c0842d4005420758220020200401403402440740f07904800044510100d1548140b00b003902d0848040c01070392080075018070950340d002405440020009500c3d000203000d40708210380c0c0e4002c0c8020342e003090085801280703200000c2181c4c144d01005160f4201a1181e0a400a0b0505540d06040d5801541044180d50700031506101400d08180e8040003400c01400409400c3d0b0940c1003d00b00100d600d4410b8443e80421b80e04a090281c0c40032140003866008154503920768441d21030a56040320250040b400800b1f0b58001006000121821401110014419600341c01c100f030401940021098040b0100000829000c89018460040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 743025611 1250 743024361 743024369
    0x30a0608070b0a1106091b040f0c03060f061106011202120d020606010201060e041707241a09042f150301050916171003122106030237 59
    0x81640c0d03011440e800030080c0b03480500c0c040b00c0d90040c5c1d06101c01800c00054803201428454851155404904006001003d4013200c164250317050019050002d5410342c03040059a10300500d03248031a0b2642003c80e060748901e42d12410315440134005001c40100090240641c620013030802c540e1030180c82c070302401c010880441c0405644110180b103125a02802284060480800d4044840c80d041d11025000041c152080301c0c0804000740420a1001e060f500d08407650314600d6076081000c5c502d40311b50040c81038101c018007119222700042c8080ca400c40c8c0072401150060340300c210701c0c1840400000949034901203094082025000700e159030701c03100c03c0c0b0840c110004240384d03101d61400007489910400102240a140c555500940c0c2098214031800d80381003d203c18005281d0b203d40c0d600540b440180c2000e080d2501301c000040340b17554030080000e1140342d0042c44580503002c9150312020b658080c00000d5103d030700303406207800f491002c02d0b00c000d8000514021141c3c408041146c05010b8a00342c01c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 743026861 1250 743025611 743025629
    0x1104150c060501170a020402090103061d0103021318111f090f0806040f112b0c06021b040e0102040905090708060603030a080109231008060606070c0b030a060807 71
    0x1040304240489032281a0050040704000d8240e15001210251104035001c0c1c002d205c1c0360f02190074a04c5074030a911010140c041c01802c103c020580881d40d540c0042c007440203d00c02d5a001c0901c02c41c24416001301d0082c480e0800300070001c907119a5441c446480c1e559032a68004032035406840e194095881080c00c0d624007900d03030f5888242446a207000180980c1c03c1440c242d03002005200018906000d192070031500006000f4001880d440029150004c2600640f04041030840a0000e1030b24040000000c078810522513503d1076a88005a0322041858030100501001000150080c00e154004442c500e5030b5030300041c80d140e141e5243e101203680580300d40015502a8805000700c803401c02c1201d0308440e0480c011030410415035001850384c84140240b0314055104e00c1040c61400f04900072000207c90365800364010f140102e24210464801d208800b1503116080c0410b4a81c18042e0803100d42507000120b041e0b041d410280d01420039400580f00c400416607074080010b014400f07011a60103465428 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 743028111 1250 743026861 743026877
    0xc0f0b1b04152307020108090a06021206030607030c09090e030c07080a290c09061b0102130e090726031903060501031e0c052125020709110415 63
    0x40e500508074802080b104442410b43d8203103042150b594000e54480c0c80e030920340012260b403401621402e2000e064001080c480c0085081c54208484581d81072144a050381110f00030b41ea003982c02c6082e260149030110100303545903c14000241542c04c0fa01c41c030a039030400c80e4039045072003011502c1c20080703510201081e04030f00c455070100403400c49a804d203805082503803004146001511035203140081d00c24081e0f5500040d0079040703510f824023600c01698654910100801c0041751460103944000400c5800c1c6910301030221714800000487ea0264444400030420113041140018510500741100100300aa0f4503402400050400c0141071149411102a6078841c01c0c0101909403905500503505242c00e12600c0490b00c04080c0c1e5849a00c0c1825101042589802c4400d540300e11900e0030407920980d840d02d24100b9450110000d5000364155515103416040015400a031007185412810058210180400400d030041d0007420220030b0384503220746419604c0032451004038180030400701044200e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 743029361 1250 743028111 743028149
    0xf06060103050f16050a090909110a23041d07090609060609081902190b032a030f0c091003050a0e46210c0f0b1b04 51
    0x5000b41a0844028900046030f8100500356008101c40f002c0d50008112010481c0040c0c036200b6940c220041c4240401045032400702d05000807108e145420150191b03001318000900341c00325201a401c000355409000b000540100c2c1000040d1091034118000e18410050202d95002c0601031103000341080320340080c41d6890f102a030b0050301c006a110b4824450407031000c02c00301c0800302e00c0c03035204111a20120803070b802c2d610006140305820315200868244003440410040c20000c02180203283d80702604100340030032006140b1402024400e842914410710126400ea01444440d0b0780010314412402e00f021b1520010900900c0d000c02217100090302c030424881e20110511400c0c68025120005d04121100321003480d41c0f80b2940310b50b17081c0560039070504561364002e04c4035500010070300018104036071a003818454020540b00c0d803004044961555610181400380c000c0e100c9455100602104900503501d034604403403c000e000c0c440c514a021040349110b84680002e1018090111040e100c1c43c1c08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 743030611 1250 743029361 743029367
    0x7050309010608011a0d050129010801050306130b0405030702090f060f101d011404090618021c0c051605010c140403210215040c06030e0c0a030311010e0f060601 71
    0xe900c207015503450b01c0c80070f0f1178554068008400c900410b880d917081e441d03118640140146201c1002c514900f00e81c1c10580c0004040f00c41100c00c0c4c407000d91b40d41040b0703600c50f001c06440b0b49060310f000080d909240881c50004840f05540d41d803180c0070b1000d60742807140380d8000c00e8400d1b408079000c8204500000801c2085d18068201104800b801d480c1d40d000107103011006030000c43c000281c3c161141d19200085010703803050f510301603e64000001c441d19241c1e503402c075201400c4507001d00054410680d0084070b58000503c02c2d6012200c60ba14545e1003022940d030644010051001c0e44802c10408200240000c290880045001445040001004c1c0605c0000410150329000904901c440c108030800202d03404442c1141020081c0010310b4410800c46c0c0d0523450581940001003080d00c1c00790401050061200380030086408a4609200d00d48640c24201e880b0140c1c2990954800e008450074404031780310398904424101001c000103194590030580522381460081203182035404032041011030350b8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 743031861 1250 743030611 743030621
    0x4030c0f173006010e0a051203070303110a09030b0a1103090a02030c0103181704080f03040806010b04030803070c290610110a15140108010504020f31060506030705030901 75
    0x60300e0445242c0c0a91903920381c1407040c2d02a040e40d04220010802c210580d0310b0390070640003013000071f0000b58070100c444150341d103a4024009c268082464074074440e265446901c1110291580c039034a21420300d0a555801c41c07440c0001d004150400c3e9584500c100c45213000000350300079904d0300000c1c518500703075204241c58aa9200301d1641010f0400d044030b000034188040d801d00440d80245050a1644d144d80a0a001d0050b64400c0c522849206141a481d010100040041d182e414064407003685e280c20811103641308511004244500c200300041c50240320704d000481444c4540100e0b82c502650708004004001c80704045c68901080c0c0061103154680022030a44100e0203050010740c5a41403a8007035241d000c48100901034102c903842c444041c943d2940410750111074080d015440796102e0752480d00901c0100c03006c1340a121007a1564109152800018010b00c2d11810017001e11020785001c044240f402c590715101c465200c20700810503944440146208a0003a96030544a140188209096a0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 743033111 1250 743031861 743031907
    0x1080a140c01090b071e030f080106020c0a060516050319030f050606040e153f0705060d0f020703020c01120b0d0b0c09040603030e01090605040e04030c0f17 69
    0x281c4804440c00c25070f604208800c04840b0700c0c0d440591034a00c141800c00612061400030040b14400c074203803a04141c0c200c2d40d003039060600e0b0303900c01049a03207900081e0394035048074520944c4861401010400a4030801c000c0c03071100c0302c0155002041c80030303541d00d07480e503040b0540030500500316100781c5500da60b040c4111407a00341450801d000504040b40821801d110701e01819403810304107800296803030f0103804807000c0000050039610250b4040d1000540b00035180c0080000c0100041003c450392443d5101000c5622000001c5c0c58100c1c038000c10840154000e001c151700030f54442d8000000340c06548040c001181c001e4000c0d2440c031002000050a2a682c50b07581032006140450040140d110302c5c1219030f540c3d910003061036082d100c0e106109001d00410803001d610604007200030040560001a4040014080c0c0320001c41039241e02055540340524000d00100501150008022911400800b02c1c0c8900031030341940c1000742d54940d42142442000c080c010f1034400103442d24100040c908a03c000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 743034361 1250 743033111 743033113
    0x603060f2d0d211413050f0103020a0926011b1e0e06030604060302040203090a1e020102280503040e010614031603050402120a05160f0308040e07021501080a14 70
    0x500502c3e43d68a600d2020814032407400c011142c0c207201031501490300300703801d160303440403090b290364a0300c44054114002e07025081c01640400015007541d4020300946141c0910740d1200c4a805050940810b051100c845000120410f20000c01c00e070064203225621034414141030442110f041104e010302448460260f004005540404120b1140e40c809105da843d0348040311030076500d403501e04c001005410310b9003010798814400000d01441c0140000e691007803070b2290039040d80a403610140d03824907a103921030203409070308502464400d58200000401c0c00d10400f41c440030f174203181a100c1c0c5103160095040210301055040051110a4224909001b07111010348451300d107140c00c0402c041c4ca50705610201d802d041d01c880100c2c0443d035440750103030301e0b265001c402c5440da903250f828215500c003a040300384032010b0014400030130403001d48a2a03000b681e0304919a01d00e002d142c4101d800054100030400002c5018085105107940c040000c020300030140100280100001070400b034036a01e9580c807030740c092 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 743035611 1250 743034361 743034379
    0x41118030d05192c030c0a08070b031906060c0308060a180c1e0507020f0a03020109230913020310060807050d0f060f051006020d0c020603060f2d 64
    0x1240303030311030116982040c0f010031a42d02040c3d00c2d2415540060501a29280c80001050442e0219082c015910b03115100703c003210100140e05d024860401d905000b40d440c140c01c0741e00c0501c020302221740210f070418609002d000c200e03a0810040b40840b40160003030800650001078000074143c1c801c5140c5d8000400725003036290546400d01026a034440c540610764050b80358030b0307072011a90007102d81400301c0b40101044102d290400000800369400000100e22401024001c0c0d00d103818020304440030750390b042e100c0814945c03c2141c28515090341c44001140d41c0404007081c501d07074031155100c41c05100d0384000399500111520405050001c1d0202c0d14000902d0040100b04003400083c0341c4044620a803190358070000b40742041c0c00d041c1c03104040a00300e10b050001041404c865030740890700c02d84201145070300c40e07a101c510403611180d40303001500001d01c0c03100c7d500c0003502c2c00301c000f140c0190004040001e1106080042403020003040c03400340b18030380703d2240010320f80006803441c0803d50040b288030f80c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 743036861 1250 743035611 743035633
    0x40c0507021e0a0b0c0a03030c020f0610060f0e0a090b1c0302010606080901020703020a0201140c1b0f031902210a060506030712051c170c0901020c041e0504080904111803 75
    0xd5181c221b400c0107801c150300d83c1c0c04208900d000b8850f45150504900907038a403032411a28504000300f00744100d80004a0f88215071603990f00c550008000c2a0b002002140901c1c0350590b090050300c0c6142c480740e8071802c6001c0da0307901c29a68501c209401446a00042101c0c2c0c41e05a002d054007000030006d8040d40d00400148000030343c040342034811a982400e1403021204100361030445ea01134030080803071034070406001c4907907180110380b0380300c2c808011682d00c079680903000281034980c850304c005404801d010b400b00e1801881e003800c1d540c4508846288100c0001d0044200c01c0c80c040038103800383d8610b50703a1000d120710b5003002c1c0031130f0015006598610f0310303030007080c2e6502d85d8641d0b18000440403d924011041074080c810801c2074204e038010b00c500d0420b400c142c40300c0c1f82c4c0342d031180080b64050700c28070384044058201806080c0340090918806000000c21820300409080c1c001c000b01e48000d0104420107040e92503101e00002000000940d9442e94032802c029645d01c050791038080c0c466800080300003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 743038111 1250 743036861 743036863
    0x6050108060c160b22051c05071509020d0602070b04210f080405030d0507021c0e0609010e03010b1e15040b0a050a030e03122a09040c0507021e0a0b0c 66
    0x1d80f409500004d50780039555590302d061052480f031400ca40b0703500f2070810711600340040000d400602c0382045c42c80c199140d400d844159000d2141c003400500d0702460036030003110a00030358865041c090001e4001001d588565460000f02d0340008001c0f58951022001c0c003091101c11040c882007007004c10711440c42400d40c010003400c1029210740340f030300300704100c0002020010188240c0359000c0f416a42400141040000a51285560704450741110081004c4089440c0700301c90b003054010b80604840d14001440d00110740316085a4000c0d9050364039502013003c180c1b5945d01c5510500300c176580c10414a004403080025403035614480e412409030502c404d102d4540800d080342c401320081e050140da1000c04080550141c80c6c0d000180456010110b48904c03d40502ca43c01d51184528030b04040d080500c02503025007610101c810411385010a000807800e5003856800340485082604045050404c0c0d9400502c0c80c81d0484000580300b107803440c41c6070860600d10340090160044220306401c00054014035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 743039361 1250 743038111 743038147
    0x60301051311070302030903060a020a0e0f0105190504150206042d1e0b0a0911100908240105010206132405040627030c14030c070306050108060c 64
    0x1641c8035907011403606080790859400003001c103011800c810303155041c0d410041d45070b4000408243c06402000c00280034450940300b102c00001603915140060401c0c1410320a503904441d000a041c800b082004111403000301103040c2410f4010342da01d65a07281490220b104c06801108098159800407040c000002c3c411140307607036035940701ca180000c840c0d1100790080201890400140205c00c2030314003401000e10b200980f00c01035015000c0b0054940710402e0020842d65100c001802900d041c1c0440e0003d4a01842074400107100c40c0340040c07940e526500814107000345000d0145403c201c0d20f00900d040c09030101401d00424090010b44114540342d04c10448009413002d0003807180b8105001c1d02c0c03441900427100c110021f00d0794000c02552401c1d03d0303e10700406100682ca400400c020500c0982140c5407000c00e14113540c5a82c0b140c58148540e41e80c12384150420007030411a000c1400390200840d000c00407c00218000e0202245551500c020181041c60250803548c00650400245428103c100c0c09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 743040611 1250 743039361 743039369
    0xc090e0406091712070e0a3f0b04031d030c0d0203030d0c020f0d0806130c141b120c12030603070e04080a030e01060342020703080916030f1104090c0e1302060301 71
    0x1120218280e40c00b001911203000c070502e2600098034250f10b806c9c0403071955141c1c410b5200703072164038214200340114500080c10800c465031503400241440d0540c00c10107126208544040e04582c10916440502c005030740d0480000740040e4041c954882540c042080080d0402005080c482d8060030401c01184007070000590f00320740f65803510301400405104509003c41101e0b002a11070b1541c6260218074046000ca04005440c0d120f1109400d1200d40010103e07900300c504407004081c2d10300d608c04100c41d6904000c01aa516000e2040e00003240b110700c68486219910851140707654010004002d0119000010014010307803505c0d005000065950300410750f00114160582030384140180c2c2e20b04036207201400a04002036100e030300d0109002036000f400b96180310740ca42c0c07880d0742d8544000942c0e41003101e04181004e20715600400c08528044045403020340200d144510140702600402c0a503074220600f03d964465420302000f0b0084e40c01c88041d0856803002c054a50b003401600080d1250006002d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 743041861 1250 743040611 743040659
    0x1d0607111009051203090a1203020307031a210a050109060510140109050d111302180105130909050a06051303080603061e0720030d0c090e0406091712070e0a 69
    0x400f08100740010411f2111142d446003c1400325050280000c0180d0401c2c0c1c0d1450100742080111601d1161039408102110000b8007040c42d0f00049030100340c0d168444071448007807030141c7c07009000072a1081c012482014024030011415007046030820b209904030350310910000d00103800780c1c661681d01107030348011200201c8600448102c103040c580801a200f03410164010450480e40c071881885801034607880070b040d00d00300448078420740150b8181c45220194640707113441c4031083c00500415402101e8540c042d5048500002c03440d0b558404a9030190380c0749480f080d104000000b055440f42e1010784c0500d040d406051581051580c1511000c003002c03500c4402c87c1c6603000103a40e1442a151041d003d80d2844400b403d648025000c180c49034040241515410700b00900008134601599002080b10050310311114156102d8a80400400ad010011102c0e840d484040d03d80212074800500018042c20782c02034040e04000802400110004c0a076600035a04072008002850349a00a01c4840b4890350f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 743043111 1250 743041861 743041867
    0xe01080a120807050d0c080406110406051909051305090d050705100542010c02060a03150f080c031c020d1b05030406020601210c091d06071110090512 66
    0x302081d1094003031040d40201c12450320103c5002250f1041f00117004501a98080166aa800c0c0d0010603601c15030003480003145040051540180800389044030309001c41c6000001680c03500300041100c85000e0f00c0c0a0440d80354414070105810a100100036080c0e5801d006150100c1661201d4891020388804814107603214009860401d01750486113021500d04c015042c01060101c400c01011854080300760440e000b00075030703011540111546505150010002420310409000071070103003060600711482c04160500001c0c115030204e60020151000b08040c05c03240c1008400d05141c004810030180c210b40321115001c480d117070046201c035081c01580c60200554007800c0524001003403090030092141c400045e0001c0d06680c0466140d040c0ca92441d41120a4480e0b5a0305c1c41c2200700304000a061007007890810000f131001c5a000800c940e0040c4074002061454503c5079082000403650440814200a0100300040f014010014981d4020104000c0d0b170180303890711680e5010350703605d41c00a54000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 743044361 1250 743043111 743043121
    0x30a0e040917041d0f06030604240f0c020d03060b091c02060705011418060a0b0f030a050c01090911070204020307111009030e0301050411010e1503040c0e01080a1208 73
    0x140c030804210b4482030714825a03403541c5095403d865018140b40905009685000c51078001d101c410742409800000c00a28213519203450382d08041801810701c3e415100e055200c038801c5517990141c070007040103c10000440e84180703403010342000d001c0200c3c0740c10075281c5001440901c50007400d44070a0a0300365840c0d80c00f04000000c00302140b07a140d6029512002c0442c3d04002c2080541100f440c10400d0b1014540c5516a0310300142c035170098039800025600900001070300c1c00025440842c04100003045070500f0305021010038140700b40c07024160b4594104401000e030950300500440020100b07040c0400c844c2508001c440d90500078254000c0c461500040071880d92480365528086400188080d40d038945106850b04000f040c0040049000c03a140c072140715198941031003000d208580115800c04000000c0004407030000194031610780c05008c24103c40f80e03000e120b030301a51013180b00c1c0303121415140c188110b02c0041c0c80140e0100d001a482a118480050300405041e0005440340c1011915501c1e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 743045611 1250 743044361 743044373
    0x160804060e070807140f24071a09100c0c08040506130f0e0a11090306060d15090c0503120a120c090e0f041401180816050303012303030a0e0409 63
    0x240e43c0000350a21404d40c02003070304400c010800d2130b409004c540d604002400340080c0413510080411070312000c503516185005103030a079402441914480c205001c034000e40d480311080c14800544030046203901602890203240b04910a00c11950307050b08185040d00c180c3c0c1d9424009200d036000c4c1a008000204096840b030002403c0720f0b0190070182a000c841c5500c40614a80b4100200c900c03600150914012402400c980c4084a04803103001d0064415aa540d1043c08034045060508488204160038071601d6804030388920400c02d48540703054600f4910306410586070228000c003150b1024003c0050041c1340e9040864240407255164007c100712500500c01d07034a05059034010700d4501d08200421113000d0501d0130942c440c501c074001d00c01d100481c0d510f07541d08858103882044c00307600030070f0750820101c1c00c80d401400480c2e48110b403c500d0070380d0f0342d0742c0c460541d0400c0c0d00c01340b1002d80c071251303400c2c40c11014100e00c0360030385050740114100703420203100610745039201d0b00c5140207544d110740100c103000f1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 743046861 1250 743045611 743045623
    0x120a09200a0909170c2503020f040b0114030a2a08160203071703010303181a090d020406030b010e0a0509030904020d0f05070815030106080606060a05120702060f160804060e 76
    0xb03c104c8890b0300c03800b011881c96150540e0b501c5084421782124910b201d6103e10003813420540340c016201801c41129070003403000034414411402d050003110100c40c1c0c1c01c0100704004511800103500c010030b000009004002800d10b0100b403489400054000000745182e002144c141d1158040850f2a00c0c2c6006030426425403165041c003030590403002501507458004040154101c901c13a030340d080d243c2c0116041d40091240e507409203120140050040401180c005409407049640c001e0030300d101030700d9650004048603140c0e40115442c6440c40c2c0100181c05031b50b03440960181c44601d05111a143c50600075490744101c00d1201d100700c1e40420880782d50a403d40c003c2c2c2e00f00c1510745041000381400900a080c1100480303104000d1031500c803500c20181410f005550880e21000014144e50325240100889908403000304002c01a040c032003000e8400b50610f1041c024021900500300a0510110605521030700400048140c0d50803000f08803280d500200142d0322079009600091030210303004600342084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 743048111 1250 743046861 743046893
    0x14090d0e01090b0d06061409030a1101050409181202032d0409050411040b060f0708031e18060708130b090f070602010608071e060e0303120a09200a0909 67
    0xf0300040b842100e002d00b180d0144040e20324549030310641c501c4c8207590350064030038080a071342c06802c07e5208000148507403903011803000d0b0504005051a840700810021902032800c440500d201a81e620024803d43e40c1c0140008003043c80650f1410a5000303c51441c2140c120403200140c511818141003d0112020742d40a800260303401c0c402070520b070034011090204481c2c411f00c40e5281001d140503910b04001100c8221644da096541004400d0f01d8813541d90304010400601101c00c1c000d1041291140307104030748a43c0710b038101400015082c1c1d15992501c107000f44001c081c85070480078040d801000d4440400180c2c1c2c02404e0040c070b0707582d104000303062109031043c82e5110b22840001280954041d00990150b41d0083c049424082d91201c0d0b68075481034a0300c4845100512507402d2084030700c11240c1440d1450090120780c5007a00c0c41e051500100c0c0300702c40c01004180e82e030034000100039000700d0082c0d4400d01d9100e03407003002a13854002903402d00303148180341c10566100b9142d010031a1203003401400c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 743049361 1250 743048111 743048129
    0xb030c15130e0c090906010e01090905131a0a0b01030203040f0807020f03030a03061a030f16231803011509180203120a020708070806011203110601030c0914090d0e0109 74
    0x1410f01e080c4400c0d498014040441c03242803014000380b00355210303482640c802c160503502e082c0c05900d4212080c0c02041e0141c084a03401110a60410204042404205c1840701c4c4a45090b0940b5240399100202e84001e0a00ca042500400500c1301113521400107806113078210162940c1c5040c644006580c1e81c280414064040c0000b01d1600300c1c107901540007108491a40d0351034040704202140000300c51008a52901d04611294040b600a1980200003824442941043d4a004940081d21201c8814000000900200000700d18841d83c10181304003800394070aa00134812040c0d07080481c8001041405100c2c603059075003070310f08928140080708200454000e030940340000d809244d00e100550041c022407000d40708803100058501e40020b40032045450700c902070141c0741d0810442040003042c09009030104500e5540ed481107050500059000b1841100d54000c59446c00c041c030402d0b038485110b0540008910700820486139000f141183c000074041c50301c5069104603800580d102130f50350b0401019 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 743050611 1250 743049361 743049389
    0x30a030b03030d1d07091b0c1a090303101d0f0604020f0d050618040309140d06020d0f0e0109030206011e150f080f0108030d0e100f0603060b030c1513 66
    0xc1811944013011003100002a5803006441300580c005890760a080c031803078062010600c11040348203984a0700424030030200c08001c20381181030810190410b4620484c1e507000001805044d642d00da80e080000d112660421801550045e041818104d005003075102c20030403000002c0c203603940c941c104c8081c00110b60800c1e88890f202d1a0903001403030f00700d910314059001d01241c0362000310250541407040d981a55082ea0040c100002515985080781400e41c000749641a03c40c00160a4005080c2c0c050209a0000711020302812190a45444091810640e4034103401400420f134045002415141e01c4010a6189200c031019010411016442280d920300002e0b42d620081d5400204103001102503501c0c038105442c0c00a05690a0100f0b21a420a42c0c2c0204003540c1588a140c10194007207011105495140d41d900c651402502c090404000400b96941d000307000300700440c41102c1034404242d00504018a2140c0800d40281603000360f006a40f9011803a01c80e40c025100d10f04c0b020380000903200034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 743051861 1250 743050611 743050631
    0x30f0a06180b190b0409120905090c090103090206070209010f0e060907050405120a0501110901030608011b1209050313030605070e032d0f07080d02010b03030a030b03030d 75
    0x1444000020048560034108000280000900c01c80c4008154120b07280303414030388030480004007055034400c0c11401c0c552a400c01c0e5400d40e51314482c036520140101c40c11806600144802005403000b0740005214070500700c14400040071000684000340002c0c01c2c0066641c10300c0c00082d0190140c1d43d00298000300000c0003141000fa0440d2840403500200b54400d104c1d1182c10410140c140704640c8040091010300c8100484d1904c1410b01c005031950f44242c0380e2410035600c0315825145016a60b20100304001070118880d40d042c8503144c000c28566000304890f124015041c003503c1c2058a05030304012802043c81d44154855102c29071850b07000c0203c3e17680302c056180700b0444140b00d02c010f80e006031800c0c00040005000701082001104010040c0c0b100300090b040c1c210000c60f4000810031000340c43c2c0045004e501c001c200d0b04440c5a003080c001c150352850110072614044000500301b04690602507441085e031000029200183c000341000f00c9c0d016140000f00b4650700803c91104016410611940713 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 743053111 1250 743051861 743051863
    0x306010e03031b0f0d020d0c1106070c060207051201050f0403050309121204020a09020705060a05100806040602220e04120e100c030e010507020d15061a13060816120209030f 76
    0x109913150440c05030761604c0081c2038182e0b1184030040f02d05006c40c8100000c100003440001c420044070b50024030140c14907195490b052074600094104001503030060b00240010325140c68402450f0342003000a009914011002400d950b00c007800c014140180840840c0e8285c80c1440582e44054003000001e13181c03c050101e1405d2038100f030f607042c0d000e40b1880c003022034003103964021079400e280c0001c020122515018545c0004040007000c0506015902101141031003040c440603029074041e000c0584c070b41050351004000c00e5014440910020607000c0200311032240c4501d42030380641c002c01036071040100c0d5401503d00041800c6250350040107022546402074024030100301340c1d40269138030181d9806c07400041d140c500c50080c020750f002e4603440d241c4000400c48500d110300030440b94004a000d503a910050704510083c04421202c3d40000f00324501d041c01065a0800100840e20f002461801c0c03e14005412044036104e4100300704003030b80356071040c080c0354044501d5000301408803000600301210705 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 743054361 1250 743053111 743053123
    0x633011b0507030c0b0a0819110a0e0906091015030f0c1e0822050102070803010e0103050c060f071218091d0714060a121d1c050306010e03031b 63
    0x449501c6001310002c40d61030107500a98450301202c2d250820962250301e00d8040c01d00040c11007a20b0580c07a400c4088903403a0490103000300340c0e044c1c0c4640c0404610b000400c001044010300c4240901664400c10031003010105038a401c9600c4004c03d58409001c05200320050540708103890000c034102800303a2202a1b10881c414604200c0707515003211114200000c96075081d0a4600308001d0800c0c807054000711141d1410401d50303030301c07427000189001080d0345c44074210b4009130b100d40544001c06d0300410038030400f0b02018556a0048514526040e10004241000d000e507400260400703440d241e140360700300c0c060004c000c640320782e45102003502507965100078042c002c041940d0040d512200b81c1c2141c0072800054600c10344100030664151480d00d4410310040303410203802e41c02081848451425000b0f498404c410102454100c1e60a0b10030560615615212130141140d51200006400d9500d03542c3c49030541c0d03080301003443d110403042c0956002a10b140039106041003085080480749240c1c890000e12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 743055611 1250 743054361 743054363
    0x30c04082a0d030e0613081615020303040b04151503061b02010612020111150a060905060d0b060909010b03061009140108070e060d051606020633011b050703 69
    0x249030714480d06104510010b018000c0114542c000c183e021391801002800b5101000301000c482c0a176a80d034506e207049180201e6075040c1012000500001c052103c103410290f00e10300040d451070406584800b000d0794001d1014000c0381c1c0c001451189901c03142c009041802e00300d14150038098032030a1080c000c1000c0a000c01031600e40c111400b2136140180210011108650815036046840b5001035401c40c200c1440f40306030380210008650705000e25500140244480e200005810342002d440c00304540001e008035120f40b26007045900092403508031507920000a80f402d80c55a101e0003d0640501010154254580943c13000c02c6084d80c00c840e00e06048503d00b200502c40d0404621084510800a005260aa402c045802c0c0240c021085281c0d4020304060141040444551106400c26000398025100d4140d05c01040141e503904200464002c1e0410100130340f24440c40e021440b0410200d11000343c0000f1103411543c0c07580c0946e02c0400b860700405100302c0500c5d160301d012074881146d404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 743056861 1250 743055611 743055673
    0x30d1802030a0c170a0b060402031e01032103060e041202030c030a03091a06010f0f090e0109090b06011e031109060708040810050f011e0b04151b0512030c0408 70
    0x442003203646000170703d000704903820180c00308494a0300c2d010f000196200a01050785800c003002c2c01400100030303050460085002c0c10030946070b07460320030000d50a020710035011002c15041c0142404006004600c0c0f68006502c241c11080426880c1010380c154040c0c041c0e110141e000105080c40b81a13059001500124402d81da80c81000c81000005021140141d40c0180041d6003200c50150040c00750444032003114060130010403803669100880308444013600070824660b20381d02c2203010070003003510054006509080409400404090182101c492854040b0416850300c040925007890741c07086821014000d40340c2d40d070b512942d0400c41c0e120341c401e00c205075031442400520740704c400c254842d05000e400c000d2500d0b40507901e4280c00355030503440f00400415801c4207041c00031354561240020002000008032044814120035400740c111940005081c0402e8a40618a400030b81d012481c0501d82c0d4030940c0285e02da8865005021036405142c008242610454491004510031103803819020345031a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 743058111 1250 743056861 743056889
    0x320d14190f030609050114181e0c12152d150c0105041a010b090112020306120a0b0108121222050a050c0a09021207120905071e06050408030d1802030a0c 67
    0x180c0e4a003481442120034151518101030803203020190101c840303420454076079980d41003400141220b10400000d0381d08a51604d11030850050906000c010301c0504010041c032582c4100e54000c420105000b0542c090303128001c01030ed100180d20481c401d50b015013007420020061494246002c50040c0c0c19100030b5185220018000260110f101d01240c84949040e036859149070b4221203100040c1d000600003560000b01c0c83c80444160204001c2c4580e120302903284950306501d042c025a00b402c0307401c02d200420b80802c01582120500c0140c2298111204d085440b41c2e43c0c040c0300400c4490419484010607a000326400341060000c000344151640c1d104a03846080700345e40e250341c24100e1099004449000d03a2140010724503902030002d80303502c1800c0e0000800d4200302c035507407103051a000f40c100501c640ba00282c0e000e007520b01d016002d03026040707034200545410b0406015650f079010700d03a00c40d103056481c0d43d4080401034012540032681580074080b140600310501e400e0b803001c6c00d14061050b00c1d054074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 743059361 1250 743058111 743058139
    0x40201201f2318071415160807150f20071a041703010602030403150504031211091c06110909011401140301090531320d14190f030609050114 62
    0x100c070465a2408411084a541fa0940d40e141501c5421400d000d13506640c068525140c8801c00340543e00704681c804100180030310548c62400100c1f08600c80d0f80c2c03000d6000740031440028111004030524101031200b40f03000f0303955602e40818500000104c540c40c82d8400300000460f560000040c4c020f0303c1c800c800019215118903004422508201c5015002940f090b5054403044016071120100380f03011564280341540c89004036406503030b04024011620000c1b101c042c00d110b001d100e2806404c00008003607103001940f5001610030107060007640c08880d801c0007150b0b460703030081940061502c2a4080b46480c1d42c0d46203076010003820100c0b20407134aa00c4190368003403001d5000800c64421000886441c91082e103e41b00c044a1680c224241c803411010480409601d041c80c0c119448074600743c3c0d00401c0e4001504400400d030040b204010702650300c061103c2008038508410310200641340e0714203036046400c0e021084026203c55070200006928000021030402c084003071024203e08141c2d48080b10041d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 743060611 1250 743059361 743059399
    0xf0e1306061d0901110d05100f080a0302010e0a02151312030f111507140f120403091a030604270c08191a040201201f23180714 56
    0x545c403040890b60801020b210441b881d4130490b0810102000e12504988a91100e02c60345038641002445501070124101090b80c24016030003040f07801c01c00b03480d84115650204084100024a85051020200c1ca40d04e81d40555048600180109124841152003905015100204000b164400904003894541034110001181101414500f100000640c2c580208035150f000b160224405410200700d1541e00902d24405040152080307031813980d544c00e0602c0d01a08031419944401c89107071100340c0a0034001e40074003d40782c5c062401d450200c1c3d01002c500d926400d6203e8540452125007c205914043c080c002e080301d400d0380c0f8100100d03404600810b02c401852030384080010701568030340186c04c168511007402c02e80c100f8030606184c007940148501250b040999140701c500154042c5404010303c0c2d65460082503080f951980800c10700c0090b0741554400c2c4c0c103494400760321504817408503010003160399203280d0392502c80701503a43c0b0a88a6844d041d03c10b5007488090b1146103645c0030b605420380 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 743061861 1250 743060611 743060621
    0x101e12300e040b0f1e0f03120a0201200a0804021804050109020a17031b0a020603070302030f06010302190e060409022703030901021b031006080c011103040f0e1306061d0901 76
    0x606002c04c8a041c03085154003000614030f0960000900a1201150380b03041000620b00801a13448a465409c2d44800a0855401c41747c00d00418442d00e00d01605171200104031088103409160a40a070b584034004180519450340d09c04c090480c5850400c400d220b0194070030880725100315560704070143d45400d19030a80d4040132819a9030340007000154078403092004192060003080003640c900400c2500054200e400803942c81d804030750000200b010740c0d180020450f0340b160003400d0440c18404850b441c803d1118040503da024045c012540e21103a07034419090318020003e21800b550380725005100801c3d42c01d40221120103007540720311004d031103180c08415611118010790041000c0d92030341044a1200320640000e030703010301501000b400b60040c540a48000742c1a403400414648030f01c8000101807a289480c4a4a19002480117001c1d0485c40c409a1084a020342d03024a0703203455035411480c1d044400400144010316003880001c1c81d03074014480d8010520801d03041c6000d50303910340016082e64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 743063111 1250 743061861 743061889
    0x106110d180509040521030a050c07151a03030d060801110415050a05070c0f080c0103050c09010e0102031b1516050418090605101e12300e040b 63
    0x101e80c0041c0250700b050704440c1d5001c0e01030f900b12618402c4032070500c0c494402070050742030074000c00410407482400d2030040c0c603081307010f460100e4a00007240d11101c648810510915050980701c0b00d0606588000041ca0506140001d054980c3c6031030b0500f60500038040d501c02d01006508189250603440045400d950485400b4101c0c81da80b0080028100c0c1c407944070a1880007402004c3c4000e1003c900c40360000c5000e0f02250740214001410304016915200310a81c00c03504250400c0304108a0a071001c2c02c0d40c52842c000e003041380e916040c650040c0c1c00c500841d100d500102d0082c040c003e441450018032060143c070b8078184800b6948503080a00c107507260f14003a8074045641000104145452a0000442c800ca09080094074401c140d5894040d1003068903860b020140113007051040d10320307030b2b015900c840406198110322180340000c00400d603694458043e00007401c50580e080c03150a49910115100d46804c954082d1410100b00a046c0c040e150250314040c51403e108940c29007450800d4040388 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 743064361 1250 743063111 743063147
    0x70e1207080c03030313081e04080106090b030609070302010e010c29090d0203220e10030302010e010e0715030e100903091202010c0609110312030919240605090106110d 74
    0x174009a00e070a840c5502010781c23959400c0c205610b4084408401000c0e01c042d103025000400c107030f40340190726015903401c010844e00c80d411907001c1c082e03a81c1000580c0d070112642030900d40c444024a000688110034944c00107000350308400c0c20b5400d4081c800000d4401d0500c1c030b41805a4548851903981c0d82d0b02101004600542d0041041842c0c011403040c085600300b6907403010390800c54640308840740080c02640d003144070051605040c820141c0a010b50f1044e2a64003008002078007201114a5482c2190f10984070701010340801082481e100e0b41042502c601050220703260180c0e842d100724000c00000343e00380d00080e248100401c80b803401000040c09540c0503901c1050f41421612254003d0450380e80807141610005482d807007503142408011002c0d00b034015803546900d0202001d0303040c4075460725000c0c041c1d10401d00b5880006c00e000d00c0840324448600e01000104155040c2100902094002a0384281c03a0800043c0103984501e8401c4003400e50b0b02500c8903610104801da540342d400500940301 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 743065611 1250 743064361 743064391
    0x5060c0304020604090f06030807060209130b0609010c050a0f03020a030905060f03010608070201060f0f0608010803070b0c07050a211d012001060b030f010312020c1305070e1207080c030303 83
    0x50b59254001c00c07840b400e204000502c7d96541c7d60b510b1b00b142e00c03101e01100c0e180d0300890984080c1c41c02e080750214540222030240843d0343c44200140d0740703114049001c0c0c10300c10400407140034000100305401c1000d41c4900d80300301107039003801d001e956480044012000030301d0000c000701d114109001030b43c6d2022080c00441e4107503400e1910580d0b2944004000b402159a5050001909600000e80c07800070880c01441030b20490408000a000440503000f0319944c0d03004015520000f0440412103a01030701150340c440d03d584180c940f403414426100009041846541d401e801c2c0d2010304462545000c0d6145c45081940305612802d40f124417000c158180400e0f00014800d040c02c091100749001c424200307000043c80350f140e0780b4003103040e00207851000c0103c07403500060081003110000c0041c1c2e0b031000e000a0007111041000030b002d21b61402c40704030302181c9480108640d01c1c000d00c844000305200805140034080450714a0f9941d024130700c1040054800d1440da8111410003200300ca006000c22040300c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 743066861 1250 743065611 743065619
    0x15090c05071e02100e0a0b070c0b03130503030108010209091302011d15040e07020d021b22050f0a0f111b030f0c1b0405010630021605060c0304020604 66
    0x10300300c4030440c460003400c20b105540d07500690b0744080780f0003080c100d620741e4020b00d01c030711041c00421035482d0846e40300800d08200207004110984810401c480c0080301c140c1d507039036821450202c030801c41e02008020b0320010001003246a01034010b0100c10744150b5110a1680c1c41920200d15109000c1c000f9011848840c04800614240e034007640922001500658000445c0c02c40c9142940c0260320801b640c01c544001e001c0c23031a5040c0660454050640b0091000a41702c2602d89500099030001520507441541004408840c4040000c10007001c203600f000301c0d03d40880c1c000581c41e412103402c2c001519200780d076030441c0300e00e100e4064840d07400720b451070030143d02c002c458028112880c0c5403c01c0b488284071132007810070244020304a0305000c0003e40048090512543d914140000c0740d5032181e401c10f4014004540c0c09840c015188110000303501200c44041d001802030200f810301151030500001d4201c1c01d4854040d0b40d44119446a0102d61056544240c0d03540c0b6400251402548820304200800c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 743068111 1250 743066861 743066873
    0xc0b060904060b03030c150903030424090212030a12020c070905040c0f06050c010509073b010603060807080a0305030402061b0334050304050d0809060c0115090c0507 73
    0xa9010b48107110001d0507922000002e4655040354484011540c00b01d40441c217039901007007101e500024140c0046046007800c0d82c335010b0200c0718a80c0d0340c0203504140600c65108035103402c26440c46401605900ea00c1540c05074140d03c90f44200e0f03807900442e20a02d0007100460251089034000081c2c1c82c0501ba01d075003408079441c0a00b00103042a9891114901d011804403550300f820070003091262642c03680d03698802c80d0b40e400c0d2030b0020682c2415803c60341c01000a4032814400c640180400408a0020841c4820110080100507002000200d60304008180c5541550009003594026801c6500303450fa540c1e5100d9030741c3e0180d040280081d200340046001402c00c0d8000c0e1034402000142801d8500751702882528603000b4081401d100070754504200c2c4011507001d90740103101e062009600d4000000e486151740c1e4816032103841d01480181e1101d03802d0061200c10303a120000c5c010442540c483c2e00106060180c6000e000c00d1001103984000058241c00760310407020030fa44551280390800398261500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 743069361 1250 743068111 743068129
    0xb121f090501020c0a0b1005010903030c0203011b021f060b0d0e2b090e0f04031409060706060306050105030d1e09050315012409090209040e07030f120c0b06 69
    0x8044059120321a44001800c2800603021601d0928001c05071444c450800c280d160001400c1000e503030a2803d0148a6642d0002d0070740166501400c212409401500c0480d00402c89500c0714003000050381c2c40c0801d01c69021403008607459000610810340900301d160b010843d9000d11075071300140c60400984c041c614154000007050080c007801d50b156581d042c045800410f5420040807040400c41450342005600482d202c8088c003407001c44500c15180000c5041d0301443d0250000d014040c4000c0004405100c4204445694401400d216180e100d60700d00130707002d060075001c115052420f000000c0761a050001c0c1c0ac02028030f540d620181c40c400c1480c0001d809601c000080703001c00c6102c903004542500c040001810b0344c50300c200054015850107003040d800804c040309080385906c1d1501d4450040e54480c0300c03c0b042c1c5e040a2001640ea54910000500800c00602c1107a03040c00f98200c00028009071244642d58940264100c03000180b4890084800c1c0c50343c81802000a071044010032510300b800c58003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 743070611 1250 743069361 743069413
    0x50a020a0518060d020117010603061806060f0c110d082109030304030c030e060307050909071b150b09040c060e060703090902030a2d0e2815060e06040b12 68
    0xc04044a0744044486031f1149007600080b02294440504000507180302680d441880c09141e000c10886d424154018142444150310303800700b0916a0328a010b02020846140c0c6004d002042e0390b02d030506070b2800315400c1d00400441d4a40260803001d45104001d100502d43c495004c2e40082c500d15601c0d50380981f1200a420020741c10044007660030049500e0744402075018a02c184c48564486000c48100055800300802d0003003041041c10036404100304c00016040090b42c41061924100c009025a0009000d0180c1c1c69620880e800d0a10051040010018060710f820b03985045132180d404051100c18030a004000b0006403125200f003007001c83c00d501a54010580c03440c0483c3d032050128610383d0b5102141c2a580702114507072070140d0782034460b102d0344410800c403c01604a907800c9003040b0364003d004171b00c46404068805000420880710161420f0b1421280b1801c200792a182c99580403050400c0390f200317010b0352400840c40203034a01051088010030070b010003002c2d40c07288552406000c102c8100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 743071861 1250 743070611 743070617
    0x302060a14030f16020f061306020d060b0c070e1b07081314240304081b010c03021801020f210708180109170c0405071b050a020a0518060d0201 63
    0x514181c10040c5002903019140c2203543c10154103041c16501e9025480c0a400c00540d8440034002555803004280540d011072070328400d01141045007800e1010384102081d0600603840e05c02701107a1420820080c007014103000c5c0440c1c2050340c039005044899101511008074201d0309030f0810500140c00b6000f070480e40e110350307525800c20803041c500c0003d800140e007110701d0002440d4a9415075003003d80e044960910741c06c0f00480d01880c2c84104002d00c4c48080c101400344000043c1c1101c1d03401e6001041c240881c10f03940200512380324000010029040704441407190b00c02030010924941c0300156a00380c070060403014100c0007214241e038801440f810380f108800340303c0c01c1c00108041004100900701c9003031081d41d1003281d41c1c03101000400140654001c415044010b03440226064000181403620b100244c60006043d00c803080140c0d400e0001440300002054110503060030048049141a00e051003a6401c0c14010740300d8081106c0034140003041e4040304140d0340001c1451070300703602e80e4003040c2c0181 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 743073111 1250 743071861 743071877
    0x7081515090f0a021b011b1d01050405040c11160807470d060314070b04030809030a080d15382a0708150106120b0901060f0201051305070302060a 64
    0xc02480c25103561700c00c0c281503543c00106040d40140c100c00b030081e2012423510aa104654241c0000e44540030b1800703002d00840c0c0c2c4200428a0034003c65070700084005204c00c4500a1013a410b0084030305e030060140361024040c0381d00002c0c0b409028980504003071404860144440b907030a4101000552254007161101c92110303d054010a018000b031030003414030a008142c0701e0645c240030403214188912083c596001d40003c10102051205031010b80380d002042641e11000100040e181843c4440043c0c40408001440c5c580518154030940902045c59240b05016544031180080080720075010340c0c05100200c06c4030312010010a40c840b0b500760340e45007075051490100440e0700304404075203a400002480310848154003070401c56200209044002400000c2c041e00514111010603c0b41201303103c004000b221302c0c02050340106460340340c0030b03214409640e0b603000010195032600d41c0c858055460400860901d20301038000c0344c0c0d0701d60050000d10780d4a185500307001956005013028005c1110719 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 743074361 1250 743073111 743073157
    0x11a0f040f1b0206010f08071503060f060504150e061b010f0e0f1e030a0e0d050d2604110607080705010501080a12050309070b0c07081515090f0a02 65
    0x912401c2c01d156079404a9502880844901a1501c030060f0443c03030018a0728001044424030002d400f00030788800d1205d5400040310400300780c0140100307401228012030446070200b4040c1c1c0c004041d000302c5001c9a0b03a400202250700e1700340c030180e0225407400d800900c00c000010b030156404100030780c2800600000260ba445100108007200c081c85001c42e1550489150404a1a000c106c8100203040503903000341082c840c003840d50707500d100b0790404105210400340da040035075a135194501031848d0810700b51219500d0980b0b0084c8051501000e8046503021240304a92000e401c031092407185510030f00d504c030045000d20802c5543c0e0404001203800e180c0400c1020006082070080c00e00800d841402488903802034604841c0c2c0002c480700c1d040401c641403040020b10036000441d541100d1498214139a00c0980c9408141400c4003904401b0191266010a4803103030700444149200b070b12042c410404900c0c40394108001100c003501c2c880d2000c90010041181080158001e05505c403000004010704600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 743075611 1250 743074361 743074391
    0x120a0204060909020f0109140f010908030705070e011403100905160305030403030909050415052d010e0109092109030210020d1d0a17120f130602011a0f04 68
    0x20342c01c5401c2c1c01e80c0740c0741002c04500b4040c074030701341840c002d01300b20710600d06040701c0308000310743c505c1014440c078000f408000841c0d0146400d440580008010f40c0d69407505420540d40d2903000307114150300d1401c00400000d40701c081203220203401c40d0003030140c82003506409d02d40014211800e01034030a4042c4410071108640d41100910045101c0e10245448a1440c04c0c00381c180340c0c0990003002340380c0c1890208400520303801e581c00c0807521404030015440d02d4140d074160700e94a1510200750f0305010b80a00140701d068024840d8100d03516096070704140c0e03885140d003d003503920140d0020644401d8681700d10301d008004010b080691400c0c0b400341c9605581341c0002d0402c03883c180c04003007d42c201010042000d684007404401131052501086100d54841c030114202c40c149200d280b01c4541c05100c1d800c00391405120200d10250344214864569500316006403c80e400b00007603000078170092400041260060041a4035102c104040b003501c002801c003070040c86038404154513070142e540c1205d400e00e030340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 743076861 1250 743075611 743075621
    0x709091e0603050f01050a020901120c030603150f05090313061b02060a0f1206050604090b01110a03080f0a1103060906040209100201020d0f051603090309121110050a0e120a0204 78
    0x402140244070b414130348810207084a00103081c0307100302030040004e0314041c1d81014000d0540104e607140003034001c54041c4100e00400054000600800b0b104910381c4d40c5080b59000f00c0c034240d4801d04d0801117620303059a40d6540c0c1c49515900e1050022076042004690702811a1403c00c3c00900146800005254000b56459121111100c003094803c10144851036003c1c01004009030100e8041003001d0502c0e001550358000c0c2d10402c2200d9444000c18403c503441500c0045881009034202d50201a031403402600b1204100c480404030409000012181140c500401580d400c0d100003243c95a00d868080c0025090014840c0c2d0b00685c080003143e2081d260088003a110403001d43c00140c80301c0300a94041c080c1c4104060183c200303070401051014002c1400f10000048016080010340045607203400c1d1200c0c079103980489002890705400c08117000e206100c0d0410410f080b1070415001d0442c21099566001d010300c20700005024407424186070814690b01300e5030181e10301c100d410701181640080c050366 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 743078111 1250 743076861 743076863
    0x1b0303020106030605070203070c3005010e210a0c030905130509060c04050105030604050a0902060a020319032912031c140405460c0e0709091e0603 65
    0x10b95600020018480c0703c0c032480d50410201d05c043c516140b0230740c5070004590010301400d02c2d030280001e1403007114100810419070050079007d14150105650500c80d00a054404c0b03c20100c3c02111004030440fa0040400d20601e48182c0c0c0690408101d0710b8120340000c1c4100d422418003ca00c0e030082905d90390018072070a45030703110700c0c0850340d0b1800421690400034007404013000c0744400d0109100076030f003080980364881002d680000b40b41d0b46085111010b00200000a0b40000300040c00a1445601000800440c1c0320f080c43c4440880032194224100c0340740c814044880759101d10301c150801540b9010128010008102c209401900711500e403c0d540582804105402d03403449240d50055580183c1000c08644140c0e41c049150913100c0980742c10340e2038894070315442c0d550000701c603518650300c0c106c43ca0401000b000492904403030201c1240980c405056034420b918590004105040c964040c1c451020369031606462450502d442c2c0203400f0711b8107414240110032a10b02081e0440e4440e482c019 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 743079361 1250 743078111 743078113
    0x912010e0f03030601050a11010b06191403130201030504051608010621030e01052107030b18010b2a12041701060602061b120a1a0901080a08071b030302 67
    0xc0440021501d003140030740010001e03800a0080055507a0410305450048106040402150b000c46c0c800b50300506403002215807207200450030340d0f20454001c5020300e080d0b606845003101c100c04500c03c084240001c4800c007920440d040b40140c0194400c0d08600e421600c80d00c202c40c2214102046404030102642186601e03a5481d0302c00c00041c40c21032041c0c00c260b00d6580f880404d0069907107004100f00c800c596101d05101b4000313114840c2c1d1424051a41c0c3c0c1001c00c0c0400039103410200320040c060700b41d1194480c810541c2025400802c1c0010508a0403a200300f403685e4981199107416146840c8107158520701001c5900c040440702c10b0a028001c0398514110701c440e40c07242031803414898103001c1000c090550389442410b000d80346d00010b00d550428044801030354003001c010b070070504c0e0703118001c0307000554014001400f441c3c07100394021102e0440c0400415a071014034a062000d0003009110742440d9900020440022440b880001c21203240075a0b80310a0070302c14409441c4411001c1e520403001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 743080611 1250 743079361 743079371
    0xf06030602030603150408030f040317100f080d0f0f050408060c090405070c03021b040f0f0e011d1509070b07050f010b0a0e060103110904060b07060f060e010b090303091201 76
    0x104e103801d00140440c1c0e00c0030001640242015154250a400700901030701d900c0c40c07c1c01c08a8181030040000c514404007205600445142c50100840c48400038412072080e220300306808103502d032000c500d0380d469201c190383d5000402160041100d04050100c80c8a040c040100004a0b03401401c2c80220301c034000407010b407036480380ca520a210880324010700042c200901c585c0c1c1c40300000e42c042214001402c05904a0a0240305200082d005000c404182041031346080c0e0b0f4200c21890580001911051600082008038200300004100300d0118041c1d0185410402e140b54040219100994010140c141120b2029071184059015a400988203842c2c591040168400040d82400340200e03855055580940c0540b9000b46101400c030040e01080c18180c4a004c04030206440c1c5050350300c8880000c01c184045551028044213941c86810180d4a041c100000d80280344c140e409198101c813003c02e941252686001d82d03c040d260000c00641e07600d40030800c00100c45540381ca81c85000c2840080c00019 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 743081861 1250 743080611 743080621
    0x18050d05070e073f02030a050f01081605060c01140403020a1515060e0f090705131a030414010e060103030908060a0b0102120a0201090c090212070201020405030c0f040f0603060203 79
    0x602c040003010b040030000c8501d068181c0300419800c60000040000c501154801015101d02e8041c02d60f030b46982c1118808404c10540c404a80c101c5030255a4150f00812141d0f25007102c203481d00300b0f01c00795040b061088032040189082800c010500c0e52201400000c15003040140e160406a0541f01039005a0041c0510401e1010064007211f040394915010462844090352240da541003600c190014041803884900c00340c0c0b80e402000403006e10041c100f03c854a00013001801c6508024068800002170040124082c000d0780d4101641254007200d150850760740340d841058207055461500102d540310601c590350440c08016090196120383c0300c9082d203a091030703850351410300001c011083c00c50420a02d01c07650f0740c0209045046d00c10319500140d0300c02d5107503010b90242905040040c00c1d01c98015000810341c102c0e5025106514421640c006280c4401c0c908a003070b40124051207916400803410031a0781c4c81e00c3d10000007190005070000c02c3c2010f00c1404ca200f00c400542c82601c0c0302d600001042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 743083111 1250 743081861 743081879
    0x31107090b0a090902121c0e040b030703021011100507030c05070c030b09121801030507080708070f0e06131406040b07110607050a0309150504080d18050d0507 70
    0x501104841000201e0060000621550301d030711030010415510282c030002d54650100c001010480300045440c01d000c1030300215099030311072400c0b4000400c02c140f42049407405000300900b2300402002800d0b09401c5808215400c082c0c180e1440a116000444d0120024188500352100b41e0700d0000150328584450b001d8242d441c809440c104002042016400281040400d6420359030890540410780e43d40c841d80601d4045000c0c08400341020110f40c0e1090740c11704c00d46d401002c000a0b81c0038001c50303c2e100010780c0d4030072080c0c1d1540040345040000500d1207104035908107010700c1914214444410100100d40c140e030104881d4031580013000000d010301c1101410055035810140e80c0149400d10b80b81d80d8015074000c800000b00800c2d1071f442603507201d9a6400c00d81e9640c0d80c209003a12032203403081c034002d41b405c1d9040c807881c00010038124004540e1400390707083d94101c0e603500e006098020044d010466003000742c0341c41411000c0100f200030460381c440b0003407814100d100b14010701e03d05003043c1c448 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 743084361 1250 743083111 743083123
    0x2010e06042711041202130b1c080d0903020a020901081f0f0204031b0f1d0a0e0f0601080313050607030c02010804080706050c0301031a040b060f030708010204030311 73
    0x94000e080401c001c104020070350410711088007107401442d0074a80b40b00301a002070f01100e0002c0c8030080f00410040780c500081c00e5180381080c821202156180c58041e140004e5400c0701203402d91102d840c00c10148480d0080384103629040c41454454030700f02090030381c04102da84903007080d40141c0c402100c0348118108909001d025001d02c400800f0101d22804e8280503a143d40c0485940940e16484903898041e0940c056402441d07004011042044500076404852a10740c403901c80c000c1c0e01444c0000d04010341078000d4101d948815021200d41d501d00319054040c0ca0341d00e1b190340aa100781050007000382c90a018030744c040c204020185550b00d040240b164500003954200030b12a02d810000c54000980040c000c40049a0a090003442c0b5500c60606074114020714802500007410a0100003941d01c5060045060340c2c130072991002c5511418011b2000c1b250125001850340b0035500109995240804c1224130401c00103040360900b9489113442401d90708168000c070041040844200e07501003040c041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 743085611 1250 743084361 743084387
    0x90815090138240a0216260a0212010e07090b37030c0617060f1e0d05010212010b0705070623070c0e0a02070b040b06031c0206040201 59
    0x1c14412420320b614031000501e0b040301100c059a034020300d4110103884202050002141203086106003c9181d898000b50750f1001c13916600501580340004003448081c1c040206898461844601c110944682d420031052803102011a901c900c0c2c540c24010380d541c502011000520500100348040f05007821403404800303820204003281400c0d900d0303441c0c0d140c0600d1110a51107150b40c0f40104140b10300c0059803080c11101c5043c0b00f40c02e0800102c240308072424013404a9280b60b41d2054900043c1c2c6060501c48001d83e0745a52003020001d0025141ca4482e00c0e4800c44284204d54100a4020000151200c5a070340300460b96a50085004480000d032584024010590000b0083c0b82038580d030394070b5071600c000d0300620043c04008291984400c041038452030802c8940d504d065603c070807034202110344000c41c0c400d2a110180c080d000803403640a5000f82c91029074400e40f50342c80fa0305c40c4c2d5035990b19007100810b220341503c19140c28540f0000c40306500324000c0c450b50080c000b1400d0600004000c81c29042c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 743086861 1250 743085611 743085641
    0xc060403120b0d020f0d030e0a08030901020d03290316090b120a080f0a1707080f0903041a030903133003090501081302030601080d030b031b01050a0908150901 70
    0xa0f00700050b071262880c6200800d81207428180181c0d0620301621040003081156800103450480459005170000003000f0002c000d808503444240c500718224240c43c0701e03022550345040b114100b410240e240155880306018003c1c240d0b10034401c020f1b00b04848940380d80c421120b0549691043c0d009003808441110514000406048210025121050a48504000800404e00004124200911076010b801c986039440b441d440c65401d0502000342100810394903141c010b0b01071408504c0800c4000110741c1150b0a000b4080c0a5231a40000c00420340c100801410399400100700f42a02c841d1341d01c88031f90281010f0714200501c604a884140360704106460381c3c9803a225100400d1001c25041045030003150b2003480c040d01d40d075642001001c0c0030303580114000d416128000000c1010305010429501003c03856904008008401041507503032852070881f0b02c0300c492208814070995108800500c04c004a07410240c40299590100c40d18000a00c005c4203480038204040c00b200030428020705d501003010358 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 743088111 1250 743086861 743086879
    0x5072a170609060708040c0f030b160c0201090504020715021615090215030703143c07030507141908010e040203101802030304090e150103081e0c060403120b 69
    0xb100707989040150082c41840701c4100018100f210441f00d0b9000741c0f83c1c1018a04e401603480c40c1c901c03802d170419074545004c86411304c55507004503c1341c41300440c00c0d41c05039111003005182c82c09200007907115400c195022016004a2000d1480c0c500040101d1104840a030844030380c0c07800d040c1c5652050068840c0540c0c140403400c2c01617620ba064448032a14240d01e81c0366641c6400ea41074008292040705030b0303a01c079901e208101700a44422400594003074140c074800c500412040c4034004001e0752000b40c0b0440740000700850541842940f01076071010490034128030b4950035552658032500306502450f00000000c0f800c81c94281c1c0704000c0e50040c60304260b06601c50600d903002a80b22001080850005940c0380014004480f160f1030801210b50085d081d00d44d1141c0750702110020300034141a480342031083c4001c2c00341c03100350750112030b048035000f012490030320a400407400742001001c10003800540050044ca6070000b024040e290080e8440d84906d002c038840048100259008050201c0c401c0000c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 743089361 1250 743088111 743088121
    0x306051e100f1e05040218031f0507030c1205041a13230a02130204050a08070509070516060c180e060127030b040c0807081506040501051005072a1706 66
    0x4801c03c000d840c011500580c80340c42038810359607a250780c02d42d002e905102d20305c90311004c4a00000d403019074400d1030030140065602d440d826016200424020341c00102c104d050344442074200c2d1f2005400520920740e1980c0b5005032404450307020f100355811251000720014100801c007202c00b00c59000c0440b088030740e0284030508001a1101c0c1c045074042d0184d041c1c001c0354801e02920703504641c007824006280441c5662203281d095541e641d603004250160340d05201191104e40180c0c1514444030100181e0004d198450391580c000c0c01041151000307001340001011f00280c3d01070205030240481c16400c8150385040c00c0010000240001e001c040c0114010724524080c0700803100506407034111807185450b440d1850109001e5541c9d80c00b0140b130f0f000d00000404c2c138481c003150450158008812104c0d490b02c80b81d00f04001c5800178854650311418100e40365078640e0040020302441c5014401d14180400b42c88803007101600107554481c012002c5017402d005801c814607604407909647c100800c2e841c644 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 743090611 1250 743089361 743089409
    0x15030105190c1202030709180b0607021507150f0c090b180616030e090a02030c27100f020d0201020c032d0409050a110a090306051e100f 60
    0x1c40903950146584403452441d10074041d01e07841c600440c00107001c656034501100300600d0b0707401c6401003401c610b003802d402113188520b5000304002200001c1145151001356420406d5108026454401842c030600c096030118101907080b02c0c212070982008110040d1031020701003207601000c11907080c40340c05003086c040c1100380c00541d0015481d80300d0785008040280000384803402036080c030420300c80650030344030200740d405030012403e500160782c2060240c0303d01850314140d0200b1548a1280307101400707410400385201c2d0001c601c05030318950769140c007030702c10006c10281c645c504000c0e0041030a4840004525504001142030091b03184021400c26202441680d12441010425003d070a0890203a504940c070030046c40750006c6111030010365403a81d52089501800c0c0407034030006494580590307038601c1041d54040383c02429440d681c2c00c40b510b01715620700d401014003804a04001040907094040e602d810403a160164910f042c806161074a01510144080c80c2c0380c010942c4006090b45640032446 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 743091861 1250 743090611 743090641
    0x1505160c060e010b120f16150c020f040e01051602030909010306090311030d0605010f091413021b071403030408150604020706060b03190501080a14030c1515030105 72
    0x241c000008a141c40c0103a24403809030100401c4e4980c44602040f0010121034001510900c20740403106454041255202c25a4186601d210340709107042c010075035903000b80c819880030341c1e214402803002120340d60720710120701240d031001c1c400c80080e95100103100480c40003400f40241c034040c82c8002d51900b01c461010819061040c4001040f054480c0345a20403d03008461900d2800074502c110390302c44014a9202001c2c01d00c5100e841d001ca1f040c60110b628080c89110040256a12243c64031103155542c414420500700d00901400382590910070003000304500481e1140b0894020010300843e402c10072664500e5040b8090f09101c0c0d03004100402000202040b03004004031650713a84801d035907407240417402a00c149000245010702d08480806ca00301d010024601844d0342602c1001c88c2c0c400d9401040484900b0b01031010150b00c1443c40c20000745243c40381c60707600388400c0e058900f488580400d03140303401024055000030300f085008010100703103680004070120f4000ca000f44010f085c4582c00d104058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 743093111 1250 743091861 743091863
    0xc09030106141c1511030106030506060906030f090a050d091406031e13060603060c0f0201060e01170304050406030308010302120c06070221070807060908010b030303070f090308071505160c 83
    0x802e101000030a01411440901c2c1301c8141368014041020040e5100650394424020744000c20301c1c03d0045903417403c1000560b215680c0250016103551104d81550b000020028280940e41c4a0b1803000c030001380050000304d03003910050f12082e45560400c181311803800000c454039030085a0900400c221354001c104007034112541c41c90142a2a21120a4101001c00155004c0d00442c20038100004010304c6500190f803000296444414080f0f00c0502282603444a22491500c1202c800c0184180302c0c14141c071041c100840c504030f03844d1564520128042c0d50a0b58000d50104411030010400d505243c3c104e02451501440038100321100000000c005004108002c0c1c01080080d44440c0c3c0c02a041094442000c000011501c1c0b940d03071200300030340d560490300a0100058010314006401d041c1405011142a07004018609540d510001200e40d418140440400c000480c00b000010542c803034010004035000c2c0d20181c0e510700e52604c030f01040e181c019001e14400800d000102c502c0c581d101d01290040c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 743094361 1250 743093111 743093149
    0x110a0204090c030b1905071106010e090a02090901050a240b090a0521010e030412112b03090b030603030d1d0d0507060f0c0f11150c0903010614 63
    0x14070300c00c0c141082003440d150001030001c1092001d00140300c483c8a00d180c400d035031540d01400140e407082c60486100703c41c0c09501d121a4072800060001c014030f26036441c0d0202400040b00e803503003155000185909000d4032400c010b40d40d680180100c192260184085c1c0d0101121004129003000e806a24041d0080c494560082408071350b40200355100c04c9c2c95070080034010070603205024004100d01264810300a001d0940d80380c41d13181c40000e08040309440440b640304101f07a42105640e203d0002801c40a5406036000520190720216003c802801040700303182134807005000c402030300e000b404c0d5001540203941d003440e050041000710364002048414018101002049a54036514002c910f40e10744120302c02c950140d42c8c0d0b0600036039030240150004a01600045c42400701005004d8200c0340716862013000030708103c400d01d82c07060050444003050843e0108a4282c1c4901300c011802e080380c04d03215042c0c03603040094038100d14074007401000301070103900743e848280c5001140014144010110700441e5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 743095611 1250 743094361 743094371
    0x30f12280519090f060e0a05011b0b090a0c03120f03060b0f091f0c0b10060503011203050d0507080105100201151a070803010e0f1003081812100615110a0204 69
    0x402441203c00b02c00034003120100d010190f45490024041c095001c4a8600840d110040064250302c00c072000302d81d48455004201244401e80c07240d02e4002d00c0101544140e100e100000d000040d00110058000c42c004c82402c0c1e02100301000c001c0070f2184061880d001c06041c40b0080c40700f0b000d0780c0100d901d0098800010f40e500c180341070210345100281c0c036040d0101200004180000d0f500004240d069500c1001da040c00d41d0381e0640c030020010700c0d5015200000e04144014004400f16210550382c41b802424420f040c6251928504180c03002201e1070300010310070000401103400d25404e0a002d41c6190300003440220000c00422070484160300c82daa1114491034280c0b4080f12034101118041c68103c03002c0e80d40c0b0f607120958444128815600b000c2d01c01145000544920001400d10060304da01c07e840301d14082d1120009400c9404101c00c03180d0080220610394080d02040004248811030a2800716031700c0c1c50440c00c410b01c86600b0141d1802d0000c0c0c4112a407400101040900c107c0d5811a40011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 743096861 1250 743095611 743095657
    0x903092d0d0305030603011d0706050306011205040f060b0906151e12061801030c1e0e041202010b04180807060b1e03061005010c0b06030f122805 64
    0x2100211628601c1c0c024041c50300303081c18543c3c4140103505c1044258000e1044400b2101e0345182036010440c00c034840c0d001090700b441004c5c072030001160002c105140014450380300114500c121003040e14110740c0710014901e281e04000e524011083d04200455076410b003444c001c0701103860080a1440d031040030b0000038480c900681581655640c008840c09410b807508101c443d60841e4040540c0d126209141200c0d038000381d03291881c140e6058a0380079040ba4840c034906030100f0480c500144080100700f1880303101041c00e802403d24644607138041c240c110011495103202a00b160301a89040380910f041c180f44142c0e08004402074100c09911030500c80d81c0e10703410304114005044209545030720103481105003401c640b103500c0c4210101d0f4202e0030366640e0340342c40483c0007940b8414850720340420006508580818032000c602030b0302c03c00c0a42034880c0c1d61002d08035282000740c5480356548428000c115100c1643d00760103a01c1c009a40e030b044081ea0002c081401810300c2c0183e42c4281c2c02d4011460081e1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 743098111 1250 743096861 743096929
    0x807020d031206120b0c0304080a030c050906120f181b1f020307030206100f06031806050c1c020301120b070201090b0f0421120c03090c0b12090309 65
    0x800b403040c0ca140c00c000a54444084088610b400c000542d0030a50600c04103007080c4004080ba406250f01060407850880c55000643c06041684410740c00c0c070000b44800080ba80760000109900000002c1140d454500810381020b01d607005081c802141962130081c460090000500510b00550440358501d42d10080b80018510620b5000d441c009002c5007015802454000010b4160301d4865020303584c42c0d62b1501c40c02003a0f1001842031246104030322008200c464040d03032003207418600c04820075420b485140c540070242c58085d00d20416002c0c0000b0b80e002d000c45040070711a401100b4800541c42c551411000588003c01d00310060000c03115100850340c10350007540026015a0320180f42c05052070b0900403001045070032078041e640504c6900000ca000d02e28904c4000007910b194545401c06940312a1641c0140000281941071550340c0303200308003180c0c00102c400c0003085110303411a03a40d0002113100030300d49405022011558424000c0d00c49541d03400d03c000c609095200c0c5200010320700d41c4582 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 743099361 1250 743098111 743098127
    0x50d0905010f021b01090b040b090a0605090705040b0d0203031803030c0708030a09061b0825050a0c0f0b030a090809060c010b0a0503070503030d020a051306050909010504090807020d03 81
    0x14003a40c40e100b00e01c0110b0304160050301040f02c0680072011903441c105540d500303031040500010320644180e00060001082e419009800501800071142461071340e656000854200740e07900100c0343c0c04003000b00b121307180c00e008040003071000303403003c0c0300c4180541c0c00b0030b60782e0041404903041c1c060a6100c02025440401c01d407080d50900504803410542e84886003902da902080e041d800140d4800070114003c1c0c05134600c8003144240303000000c44950b2075110541340d50044424542403841201c0c03010103000f80011344079640340c0284003510002c510780c41e01030220304899010140e59152114204811180ea00580e0390081032031001081114040c905041d0500c0f82100c1650b000c480400c01040c01c03641540080d0b540c1c04140c8442001d00d48075010180c0d14019486020380c136900400507491030542a030003902210300705017000f60074507003000d40043d0400f01580041d4001440850311010303515040081c2070061405550030031084420b5219035109128030540640180600c3c1701c2c007020580704803c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 743100611 1250 743099361 743099363
    0x40e0c1e03070905010501120e340303170f01050a140f06030114041116020402090a030c030f0303050a061521110d0506120d080907030b0115031a01080106050d09 71
    0x7620049502c0c3d000400c000c0c41c080c010703a03001400314152401c40d01034030b100e004aa030b082880100100280c3d00c0a001040402c1300504545a001c99405921510344101e80805180b103604c921f4090300301c0b4032501003010740051005080d4440343c001003006031500c1c42e009041d5503041801d180d9101800340410541190f01d1255a048000040001115400444402481101110184120101200408498050a486040c56988000c00c4100624141d4000c0c908481c028205046041d03a98992400150305a4000d660003e4083c4094080550600c00d0a5103c810080b00704820341c01c1030070f002d1209035460894014803032200301c50300c80c403803072039500314001402c8550611a074600030107500d4003500502095852141030002241540c40c01544403100558000c0081100000488040752502d1002d0609403070390003600e1000c000700e119540c8090291a0320a40380001d0341d0070003002411030700e00907494061070b0407035000d601e4103a80c8030907805e0440303601e480c3c21500c60066800c180010150303118 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 743101861 1250 743100611 743100613
    0x12110307080a150509070309050c0604080a031803030c12020c10030c0908030f0306040527010603030e0f2101290f0118090203070c0807050f0606040e0c1e03 69
    0xc0108055115568a1042030111801d101d00381541a042c0e10000e00e034010507a01003941800224840e01c40c0c2d02c2484058089c2041b6626001c00344049080d55001d42c01c004c030741d600301806610906812149000c1e200708044401010f151658800420076500b10000a180c0c0035040010780c0311074400c001c4624100001403103003040a0b8003400150041c4250500303000418105440014038100100a0381d80c0b03012121142481d5540d030108000003040b0041000c840715811050310100c0129a81800c2c3e441d012030b20000488130b05505004e02411310306060f2503c00c4101076482d200c991641400d400040411480c401501c001041019002d03084a80e00141a242501a180144e840ba5090347c100b000c0207591080080200e940111a110082c0101c981340c0c01102204101405441e80150303880398030341c908015008456500c03a900c1e541710350006ea6060344189008207070031505012064002c0b2044030104140403100305800c0e00c405e5a5040c1d180305414030035030141081001514143c0b19034000f4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 743103111 1250 743101861 743101867
    0xf060507020a060501080c030318040e0a0c0f14010e010f020705030d020106031101030203040203070b09041104090b03060a0b0d021909063f081806040b07060e0604121211 75
    0x60020350b1440b8100003a00c800d814000009201e5902180d280722810300a4065031401a600d2100380203543c03822130094110b552084002801807081c8210034905214003101c1030654500000e1480c2c10722140c01c041d244090b00e40c00490780da82c201c3d800750700c0031b80d080c20b00c4118030700d240ca000d90408907541e00c415010b02a442e20103920643c1940b15109981c4107085c0b025443d50101c0c011401c90100300c40094040d84040b5050001809100180c1448c1100610114020104074115803840d04140c0c0203104454540b18141400c0c03800384034882e4000c241c220100209c02d06480000c102c50010364001e8044d0319412441c541c15403c1c1e40342c0801030001401300b84111541d840f40c0103c100300162940c10780d2414828201d40000554000400340d0703550b000d02d0491350255844014407944807442c0350a22007420700010513142c60300c002504c02007400401a5840d55072501708501a0b0354140841e08254111004120008020103c510000002d03803130400b01c5800b81c14003134002800c41e4a0046401d003004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 743104361 1250 743103111 743103121
    0xe040f0f080a02100516053a0b01080702060411190806040b0405240c030606072a0f0302100806011107032d03090905090307021c1106030c03010b03040f0605 69
    0x40d40a070418128200b04026591090701c240e05004482808000503c10000f50303e8100e240c1b00042c050f02315055107241102503007440096000d482c41d00c035050300d5464041c43c2c42c0540c0c001450551000c10382c0050711644c94150b031004031082c3c440d00424810a802440c180c11591140c068001800c42041122443d0401c0d00b842c90088001b11811525032103083c03003032210649515071800e8407140a0380c00130722940320380380100201e4000500541c3c1000c0c080c0f110304040b807410320050403003c201a0000010560300e0703c0b21304210819411010114019400800040e1160841c03018003000b5842c05030416220f00c00106c0340c00c101058442a50f1195800100c14090200010446001203520750350001c10b04004114042050042c0540800c003040070030000c01c0400d030403055010143c1c0043c2c07440c20315554005040c0381c0f1490a03280011107159403400401180000c000b0a01d101111041c0c04c4d4504900500a07510050080c406920808404034081003000110b201c00d555015400b80b141c0c0c80c1c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 743105611 1250 743104361 743104363
    0x1090905010b010207031518021c0c05042003040c03081309050105090601020c040e0f03220504020403021f030b04110901021005090c061b01110717040e040f0f080a02 73
    0x1000000c0d100c0d9480c00c0300d00340c01580001501012258081010442d04030710800c50780040080c11540e00c1c030700c81001c0c40355005a0710b908816030701c1c020703060620202d86600e09022007401c203141c200301d0240e171034240a08454400080c0642a00a40010b00c2da682e13a0340340352003401464240d00050848001081c08056800300000300c1d81a10305105c01000703030b1303a80e6508001200806a43e01c0340940c200e0602d048190425400540c48640c40c1000c44070500300000701c0f80d2555100c080caa940002c16600550218001210311500402c0111010341c285421a000580c0e00554200d1504400c110011314254142c041d41102407074800007802004601107124005a2a03404020400e0044c0a503064082041d42948140c038000c003403031002407400d4580d580600109070700900d03040c0c0350120302000c2c0c9412070710240607900380c490412140d60380312034082c6084e04049440c0851034698400c148010300080061092441e071044e00280511030458403401d00e400d284148210181a442d4009610782840350 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 743106861 1250 743105611 743105621
    0x41a010f0e0708010e040803040525060306050a0e01170a1709090a05040803160c060507030b030d0c030806060904020d060602010203011a0c07060e0a080613061a0f060f070b0109 78
    0x45200145400e030b98100782241e40007401d014076244014000085000705e0500400745900c42c0c8954115241c0c40c1003080701e20045242001402c80c10480300c2c206002050303240c06508010481651004005400c001c511031810303105000f1945610b0480303a114030304003801c00c121040075804c0343c079a46180e0041c41201c4041d6120719561401031008c031010514106480c8903262240790003050aa065403545000407102d0090900341c1400c10030385030512408a0740318812030740030b40700c6510b000610842d80414141803088800c811414490b540c00040301081c0c0080340507034400c000311121582c8e41210350010b0003d002e58440120410301e414004680c89030158000c50507510000a080c54081401c2e034910306510a01150070308a80201d1030800210340036002610840d000103050441a9071182407592801d2001caa061150300c11400c42402403295a106001d05100d914601c403d040480002203400602c69a041d50b00401000504402420010055030b21165001036100402d50b0b607030140c440540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 743108111 1250 743106861 743106869
    0x30206030403270b19051e0a030b0603162007030f0804090f050609092b170411040c0921150e1f021c050c040906090c0e03060c12041a010f 61
    0x403180595082400e0086d0140c51003860250092500900007094240003500401100c8040c183c4070303c0790075060303603032000994403d00c084c22304880e41b00064280100401c525894401448500c2d1001082260700410075105883e007002000005e84294580a84980b250780d00c5003054514224000380c0880c0b6a0708141e00a64007214a000d0a848040a060729443d0b24050000d810b02c41c8000c0e04035181d03d0f4000b0740140741150401303281415800c40d078001145000c48088a464142c10000c40301ca04e00381c46030428000b01440c0c88034006003400406208a0403400400303140c45c0e10404040704104070110368030a858030400703040c45881c058001066031942981e800c10003290104e00045c00d100903510039240202950340760a01c480b900c2943c000000c1c40064584080c884e4204000b0410380c142e40919001001020400a4003000c5840c0085c01584590b0440e03219801800911540705041029a080303030440b82c07400c00d61a1200e00e000c05024079406151891501c1c458000a00403030803c809404403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 743109361 1250 743108111 743108137
    0xe100206041109060d0b1510090303021605062b020a1812170d11120a140402150a030608060717090115120f1b050406050901030206030403270b 63
    0x9150720108204031480100d8004d600700640800000100700c10200454000000e80a6a0707014020a00410100361650201c500440d042c49400c00805504204000409641e054400754103420f00001555500c03030544210b089110098800900030100d820701880b00389252801c55884802410140038044440c14988801c000c0c00400116651420042280140d000f22612902c01d4008405006034200c810540d458a41e18405d07031581801010081107142e080071703141c1800d40303001c51075030702902c101c00050450301b1822000e03c4010b0300c4040d0314013624140e212000e510fa50400908800422180d070000049100e000140140560050b01075507030b4820380c8424105540e50796070200e080e107050840601c178014101204024181c804091103681c1441617841100300012521901c1568079a00310b02d20650092510800c154035052040c0c100814080da5a00040d42c9150001805400000c2028041c00043d0402072210035801c1e107250f84511416500740c4a80744c96500010b2075410240180c0f0740c0e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 743110611 1250 743109361 743109383
    0x8130806060a08030315120a120305160f080708130f0803090c01090e070e010c06050a151a120a0b09070305090610030b0402041e0e160f030b0f04030e10020604 70
    0x2100d00080100c1b8030a4181c4100f5490802c003070710070b010b41101d104030218100e014420540c0000781802c0c0b0320844060075a50301042c5428222020071301c49085049580500c070b28451071480040e082501c2c02da0184a5091a14050f62801080c01481e210318100503c00c0c905042e03030034200800e000245005012000c11990540b04440c01034504c01824000e070b106d1000d00c80c2c00a044681700b404000364115040c90314822098403a51140151030041d140401c15989681e90411074044d0030071180010320b6400e1852b00e00f2030000c440346115119628410940512210000300640d80641252030031010140804d0701c0e503e44a000100202000d507015442c0b4080c0b00d02140300e03154000b4845043c0d0390081c203080750a84076079003004001c11142c44440c900e0000c40c403000d021201548202d0700d001c0a50000740504841030442c084d441011504241e01040d92180280041984032000f5a400281d0740c0c28112143c89074182552480c103000d05081e8000740401c89540d00750f83c04200c160107684290b03050a5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 743111861 1250 743110611 743110619
    0x1603111605030301090c0504080a0b0a09060e010c0e010f200102120702060708010b0909070c060b0a060903050f01020307050912070504090311162106110304060204030311010203060f0105030408130806060a 90
    0x50508c198400c2d8085540024503850104185042054001d5801200065085410340d941c0040c0c9004180c640001c0e55910196080e00750048411308010509203400c0800c1c2c4030210011b80400b515034413a42101003003250b810481f0200358119150440d0b42c5c0d412041a20701a4030080d038403141140d80f07500003100b080001079509400801d45200f81360040451006030340d2094100d6848a080d0b0040c0c501701d44414080700c203078841e041100085c0c07030035507104414a801c40c00c0c0140741c482c1044020355942e20400c00c005000303900c141a600c00a90454910500b60281056189000256044140d21515203803660080540180c0a060400301410a84107403c1d02809540688910780c03142c40741c400e0080c2c5100c0c052811084400600a1040c0000a41d0401030a65940c42d0707082102c084031101e82c001b40901c18560888000e081602802e8025850f614148001c03030f40001c8452601410301c0700220129040002e00c00584001204180311207803120f0362002c0c0f840c4e4400301961103900800514001003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 743113111 1250 743111861 743111867
    0x3041202010e1531060f1205180f07030c1e0305070b03060109090506151c050123121c0e04051f0504090b010506072103050405010b01081603111605030301090c 70
    0x84c2c400030041c004816040e181c0481601d80c5c0320f1002054040052140090f140c100e103070b1140c1400707440211140c94000b500014414601030120b0010030a6500900c4c0800001c0c00c2041c0c00d034151041034001030503805a80d6082c40c20754045800040060250342c0c13011032001d9800002d144100380c02da9030810001e40c1d51404104540007952819000034200d008009520180030040440d10800c0c164003000700c20040809080f00c000380c11400318007071140e000c01c22582d440c10900b0038940b821991000c00740e10800c80e20380c1e140400c00c0c4500550b54100c0c41da5010714010450500e01080141c070620981ca030464102003d90000c024100d5008060314010406051031710070442c041d82e00001d158802d90a0508008440c1c01c0720700708449400e803804d100c8004134001d80d90001140c040e5100407507541002e1414509440902d1115070400200d841000640c0e83c5502024245c00784a0a0001d80390003a0b60030f40b55a40b040524510840c14982c1c510410804000011030407036041c90702c100050300030100c0403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 743114361 1250 743113111 743113177
    0xc120610020a08032d220c1d0406140709060c03020a1a06040c02010e0d0e0409020627040b010e01080612030a200a02061b0316080712030e03041202010e15 68
    0x30b1b003144414504600e2150031184a070096405014080700180c0c1d1a032001090b12211040068090b0a6006000400016010b5003481c2e8011102e0710300d6600e4900c400900e201d0b010300c01c06080119581e1040207241c002e214001155030400250340c10000f0042840d400b03414152101c50085203010b60b40209284184140c0d2140c031f15003005001d0061000744102c0f007c5059504140d44140d407039641c100149d0340c1274020062110301c0550700c028040c0807100a0185950f8100e4203002d2401c0080d032a18582c3d100fa4000c0d070710768003400d24402603140c000100e07948e000d1040760380d021032200045000712281c210403030110000c4140300300e84121518140c0300d901c0301500d9a000b9006042400110303c1c040c506c0030b4501c540788030402100d040020070500c54180b03c5109900390b91030200001c403102400007645454a0350b030303201d0405210300c40081d80002c0d5a449184a52500030b4030b80e50705041160712072b420350342c90355100419041e0203003580da1076044070b640420150b417407038405c1c98540082da654101031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 743115611 1250 743114361 743114371
    0x206090a02010219230a03260703110d1a13110d110c060411090106021f0c0c060f060603060501090f0b030c040b070303090b0c120610020a08032d 64
    0x5030440c074480404d0034201d081e11581c202c4245d00c40d0b40ca107590301c00f17a2043d00c141e001101c0c401130500049a0901800c1030006658080c110401b0320601047d001107280002c0d04849145000200c00803452415001c85c0034007c00c8040190070702161080424801e10b10f09040d8000b00d807101d904000d0050003070111005aa00010445018840c03000d5180d03141c0d01c49150f0711610368174603185c400a440e019041c07040494040300c4482011800c4540c2d420503440160151070b0703034002050088100c00064480284840b580da1540b0349030f8401c5010b65100b41601040f06d030b88404103000200d400d40c510800351038a030080b07000082c0b800b00c00107a55841403144500b00d554095244071030500348290402a607000910f0f603446440c2c03c10001840c2c80e82c1c3d000034400c0c28040c0e5000640e21842d0300d072074842c1c0d410207002900c0160090041855010245003020340001c000c680d40d26241e482e08005070300b412561030018161040c0401001aa1b80c2d510503c590680c0311551705885060320310703a1010481c1c4098032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 743116861 1250 743115611 743115613
    0x1202071a0402041a1f02072402150919050f070311090f22030e09090a03030b0306011503020c150108031803010903050a2006010b0a1d06070f061103010f060206090a020102 75
    0x12500120041c1d4556017007540d5148160f4030f01d1510f0b003109824004184442824010403054020ba20507410b01c40704660803920352a0300000c1c141160040d03500c2d10308201010411180006034000c0000c104140d00d12482e86205070350803036540707091a0300b040b030560a0781c60081882c100040c01c3d0b040d44000c0248512030b0824950070101c80c03507900c4600a00480c0f41201801010103030000c3d01d540d800001072069214000401210b241490010152000b9843c806d000360b000c0401405403201450342e60a0101c21403600580303c200c0500c0d120300e041d07602c0501c820300c0200c160001c2000c1d0760110040c01308801e4122003084520000d0140b601702c40410300c3c05400281e091124460880c0b240c1c03044a0a44031540c00c11440c8600310140c0b03410031100f0ba01045c45550001409010a608802c400ea421200d2b11920111100d0110204006200d40c2c2401404040040c0b045400c02c121070f1310072441c0040c500009500c039a191181e071060600c090085d04098410f0400140010500040a08900d5811380c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 743118111 1250 743116861 743116879
    0x605090f01270501122a09020c0106091b02250e090c03010e030c0d1b061e0213090f18020f0414040506060109060c080a1202071a0402041a 61
    0x1600b452402124407609110802e00455030b403040301c0c118050075000e01001c461300721070020189054801042c01c1180e0094072440604440c06001000d1008403c46550440260fa10389000340d4440c0103160541280d2941850301c51600d01c00c001c140b4841b4802c04154085600d10101c00e402c08146e81c29100c2d141f09030706404007003440340c82401d41406402c10000c0044400c8000b110000900f03440344a00410195403010400d81360240b82000402d080410908000100340502c8040b01c0c42c8102001001c1c1055449200c42c00e0071100c5004000c44505458004640311025004071300040a01841132030001801c1945114000c1c0051052100750044503840e102d058115a0900804070f83e0b40c1e41e503681c015942c0340d2500f140300ba078202d81d80c841d034400d001601141c40c1440000d059001990026010407818114440002d49140100c90304030086080c0401084c010a00780c101a02c50341c0c0005008501b60020b12505a41c030780070b5207006034821103007071240c400c4015008441c5c56032095490340c01030f002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 743119361 1250 743118111 743118119
    0x100603020d020403080d090539030a05060703020c010c1b0308070302090d0804180209090103030810030c08150106140a05070204060305070f0303020c0f1e03011d010902040605090f01 80
    0x66030080c9010400300780e0140c1800c1d500d850741421504500004120591100310900422505001e01e145414041c00c0c502450190408401403110404101c0507110a00c0c4c49010084e0380e040084a46140d071040446c3c05504c0d085100802079080700041035503646c00c3c000c480800c20b0080d404124500c0c103031442c2c44c4140400b41c404846d0440c1c0036004d03209056081140b00d15540b22001820012801b03070b604156214a880390180b0401c856803030a0a10074418400ca00075607a0701d41c2c40904580c1c06140c42c0415494405c220729860110380d000920300c0303040c0c59002a0110021451034044243d000899040c3c0e03a96040960b038110100d551030441c0e0104111610846020f2030182c046603001400000c0c01644a0b540d0038608059500140001d0000444c01c00406504020080101c00c05071010703444c1041d50b0b00820013040001c00110708105982c0032a1803252002d601c002000024001c1681d43c001d801190300d8020008440c090b4026802d0403c04a958100a42824020078600070f546060f6031030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 743120611 1250 743119361 743119367
    0x2010804060b09180c190e040309050613170d0212130f03380a0207021f08100801090b07050f07050a08030a18020102060a02030604061703090411031006 67
    0x2401291001d5441c98221680e44a003038900d031180e40f4002c07504c85484001025140380c40510b00c003080c41030000103000001902161a0700c41111425a441d05440d2501d24081d1001145034000d00d4200d04085030741c95100c09215403050807910b0440714400c944007503c0409444036009001e81000d80d220a4100380400b16900c02800c4142070000030b034503540d484600c55202c800440e8801da520300d0381e10326800d1002c00403402c05a002005800c400c1d607aa502400d54a01400008020003001e41e40450200c0035074464084d01482407030b958220086180c2d881c01c0c0130f403d0798000d171613004506400c4c2102140c108014411244429040007100100f9aa22070040f100b0364014030039510511418015140058030812403502e00d04e10030702660b5140c1c07a01036800c00403911064440503010f4203040050001d40d80124911350410803150003d81e480e03403610081005030007558000c060300510100c0c10386400401001400340c0e00801c440a000b0710162404440903030000340d903501000380f2418803c2040f640 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 743121861 1250 743120611 743120627
    0xc1f0f0504030c26071208070912110d060e0a0605090a0305221d011814040308060f0d0b0603010f0207051e01062706050a1d1024080109060e040201 65
    0x41c8080c0c404240038501c4c030040712034200480442c0c40320031446920442c0e942090b000340d402442c6d450181d4045281c04c000c55101a03004401404a64240050265940b90f202c041407526400440c01d01c18041650303059a500d01407403074107071409480c0c0004a41c4528010559034840f58140d50303a54105052002e00019400c181e4000b040174018404c400076502c040321403420b0b13054001d841c00054545c51b1420300510f440703400a20f41c4811b454035148503d90100354001075001a014500081d03242e49460103e00a8103c10590076402807444508404220b207520810b440b801d0254001d01c60403440120881c280d01544000130400e8000d41d4000c5034ae0000c8204600081c1e190000120321181d9500c52010300c0c0030480f65440c81a40d4150301c0ca9030800442c000c5e0001040280d5400284601c1c08003100d03001d040a07400e5410b90381096001c201c10b1890b06840c1c1015080d82034001030f052322410859814090354444950100c2d074450000250148075101b008202c506045540d001179550350b00459408e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 743123111 1250 743121861 743121893
    0x51c0c090c12051e09071508070c030f140409091a010806130524040b0601020631081819061b0614040506191503170c1f0f0504030c 58
    0x10007000c022101d1300583e580b00e400384d00c03010b000d070401500340340500030000b04a0020000340404030042c07154055101c0042401d90360145407002c10000c100c1d40803512000070041d41000000c4c041004036020140e0b910a04100d0712895116410a0590482e00c803c24801d100303544440d04071000003810740e50004214602540319409031045e1001c3c40d00c0c01c00d0118032800a142c401c0601b9010041000200014182c10407000d00081c0f40038581000e521030f54810741422014140c0c0c200c0424070784540c000f80d41e001038991240d5166200d0880441219484591044003072007040810768407a1401d4068002c4d03020743d01943e03503100c02c80307201e0340183c2c0f000e1026100c2103c1e15a03442010300c0062407a070542600940c4240003814260805110010003442500d041900c01c0780f401210000040c200d000e01c0c0b0443c0e07848500c12802103161980c580e0b440c0102c1034030045600401e2103040d81c0d042d42000984010000140c10041030559030050f8007150411100140400c090410f548003044103092585642 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 743124361 1250 743123111 743123131
    0x20f010e0304210605010e0f0f0609010501211d0105010b07030c021c0623070e1f021f020306131e09240b0f10080f0a06051c0c090c1205 60
    0x2030505681c4501c201d1710241d1000307a054440c1c0c4148000303400880003d130307042504604941c03154104040022407841040c49002e050168122160003144000c0c46400442555107004010700203052000c600e140f0700d10780080582c0e5103040004030301c0e01e1004054412194169a0b804184200d070b609001d5501c01c0f450039a0500c60021801c0000103125005440792290420a404400c07461a4400c1010a030044e00c9502030007040b11a1002c591640f200034521aa41054403004002000c4026810009070503584015060309140002100b00160011750165005031084c08580340d008021600b1500f45c1e8640510b401d01c02041c21030042c0382e070b03046540103d018440140e42c502c46d040b081100103240c4440c0201c0070740c85210b0f080d103a02d403100481d90781034010707100c048082411140c0204102d034003c0c041c040c0c80018102003880c1904950014000c6d08000d04004503200001c0c0841442d4000d018045560381503e40001c1044411400790800c2041e0503204e01240e500080d130094050500100980c0030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 743125611 1250 743124361 743124419
    0x5180406110c0a171c0e01050105010e031207060b030a030c03110610050904020117090106050a090b010c02092a0910091a16171b070513090f0b040303020307020f010e0304 75
    0x5c003441503009001c1d02401c3c1e013000070650050140755003074610584c48941030225071818540300b5180420f030f400921121402683c0d076451285000c0b00209001c06405402d48a800303983c400305500000f5442e0b6090007610b130891400d0f6410071069641204541195071401c0c150020006820700300201a00144141000300740103a0600703500401c0081141d01c9c4030300e60f46401d4204021300b4040c50318009040b40c4101408074402c180e00103000140c54890003401100300b04001002514100000000b400c1800b0158004001403203d840d000d81011742c03058410000501c1c400c16090103405400300302c5022078009008a10311240115403600201c501c0450076040d03030301035800203600100b40110207042d685015141c8080b20361201540388c01ca40d402c003081d403054609019503968940b030100c002e003000f400815000040d03d48611030b560b000300000d2840003410306110400d50150081d40c8035040b41d0b401c0b140d403101260511400da5841a0800f5950b410800041c0a0030312022050b0711429031100007608 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 743126861 1250 743125611 743125627
    0x31409031c0e1806040605030a0503070803100b1c050606070b0601120e010203010e0a060e0408030f13080307030c08070c0b010b0c030c10140a0b011e020705180406110c0a17 76
    0x10348074400c01002e1140010f20030000c2034940ba114102c0a864190010462500c0355910325540b40b140070006480b000001c40000c5a100e142e41c1540007506807070707007130070344608400341200c0c41030800e0030072190120704010006015007045019100c0707071504010304528075200e000041d03d00800c10010b40c00e8880e1036404003825440240021030080c041c030519400a4600101c0000880d00c0c0307a007020081d101e00c2c000344800b098044003540d4120b804c0c000546d02c903465160b681d410004510000801840c404820041c845826038403440181c030705500d43d418980c2e40c00804854203110071000a080707001d00001030180d0380c0e0781303000303005d88007410f100b12851302410b90400703031501e807124060500042c0c6950742ca401d00d0350b100d0800380c2c000741490024086c0c0c41111b0000307818401a01e41491003440c1c4e10304040425882003100400801d806404500307008040c8000d042c8000c4103e40556031a400d00844c0c40c20ba2034040101c44100318441c0c050003001c1e080d036030b50880507810303001030400d560400d000000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 743128111 1250 743126861 743126869
    0x30411130221040c05010507030815040915140f070c0f02040b04060b0c0d050a0801060507020a03241b05071b05031e0d0306271409030403031409031c0e 67
    0x1c1d00d041a10030300542c83c0601c0c000d07a00c08100e411850400109002440001c2d4000030b080e6084440c2c0069024458a00c002080041a0b0380384050808101241c002e0310b0b948560780034a83c3c1101c01c4d0b01184c0c03d0b98601c414100c412074195003680c00035200342c079464041254080300610080c0b00070404103d51044d0000542038440c2604229044180003e0302e2251403400c203d0b2809a500c14249135040c0a140382d00580f14100500c24142070120002c1c00b441150b482e140c4120240d54460741e106107404400030720310022220040c8100180d460b01101f100c10100750318540842e8041d560700c070303031802105070340e201249910b1f900701c985548140c04010031103980c2400641405103004d214003d48102c40d03d440ca20b08107408440c8003d041c601801401700c560641c4400c0e0110015a0110b914032400d100c0c03c0004008050350024115066800c1c0141d6031804130040040303c0c00b9a8541240701c3c07800c0d0100b000c7c1d102d00b0600d294143d0110b00322848009910070312006c82c4a043c180005007070060800300d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 743129361 1250 743128111 743128147
    0xc030a050c3f19091d1311030a24061a04060c021503011211010804050a12020c03010603080901020f1f0902010c020d030806030105010803040f0e131202010207060f020304111302 78
    0xf14022540d507000074049010041d145034a20441d22a0746030307141c10b20400f46000003c850101801120320300b0401c1020791410041001c00c5039002103e280104220078090308142c034070000c0b0420355030908000240c90240040f00007050245602802d140c141b8094040c0c030030b59060b0004903004020900500c202080c081e01444c0240a0038881062a0466290219414035191412410b01501e402400041080002c1002d0101d07400380302c90f0b000d01400d00d000d82c58542c1a03030b001c070fa15600f00400442004040b40103000b640700207800721101340001028032902d8000741e41050420124801c4482c2503020180c020002c2c0300d0040c101040040c0d0300340c02095400c00e0001081d030100784600240031141c1024803a81e801000303800007550a050524144001b44582c61048042d24261100400c0850740900d1401d04156805003103461004c6036848040c0c040d42040c402035507120301d81400f15001104a00071248165449445144503c03030314002c003c00c82d00040c0a50159036420300c5001003022410071a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 743130611 1250 743129361 743129407
    0x102070c05060d293109151104030b07030c020a032105010b0712031107020607020a1d090106050a03230a0209090106080f010b03030a11030c030a050c3f 67
    0x30f0314004003070b213006000d08284e070700e500c0440741c0000100381400d0300940060480040e000da0004a070088850a22480603200c54104041180c0f4000c07035030b4541800c00005100710313840781e0564000da41d90020180c00b1100259454400742c0c0104402c2c0c0c000910501ea071941540084280740d054401c08022a000c5610136002040c842c000003031000301b0321041d00e00343c03550003405240c240138480c4a48d140220302d005000c2c0003030203800302158600c11581c407522000040d12880301440c01c1c82c8034803c9001c0300b5080c140c0f0000c6d0254070b082d60200c0d15050181ca0807040e2508000440e540c280014051005609440500440c0e80900b416580c0181d82d50b611850081e9a41000840c03a00e050510300b50508044050180303e6a02d443c50f02c19280d01c2c04001c3c0c48610030075080c03090000e070b03425028506520640031550254000003030301008498100b0b010307001c04041e500032035000500210610464000c80404020400740c01c102c0c1208220207002d85000c82c00307074071079094180020005440c0f054021050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 743131861 1250 743130611 743130671
    0x171504033b1305060604052b050303071d150a1e050a020f07141002030d0c081518040b0c0f180103050f040804030f1a04050a020a080102070c05060d 65
    0x1400e010580b80c600020152441011020099803d2000008241d4840d62085a0050300603070483c000318610150324203802c560350440e6100c1001c0e1031514580340d40c4111401000300d0a5035101090b4440c484d0707070780b42600d14090000c00074100d80c1c0709940d22642002502c80308104060807002d00e0024040110b000300da58070380b140c5c1c0c1c03118582c200290030170f01c15400300e02e040c0d4040c03141003080340001e240c00c8103081c006841c5884c6500403032100701d041d446030060050040e4181043c0b0030b4800c0e88180a039100d00c4901c00c0c1204281946001c1084025044000320900744510307022130049100303601d14541140e0501c904a242c21860030004000b030704028180c400c0d400c00b1032131080303179560540034543d0b200d410030100c4d070114a0150341e0b0300024001c900000c1c05c0750040710070801c1003007102480f071401c0744030b401007407102491310f460301c0d9507900e5500404a0103581d00000008103401c05000340c1c0c000503849814a840036040030180f10040d004070715044d03a0161114084488000700007000107039124208 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 743133111 1250 743131861 743131967
    0xe0f192a18020f16020315130606170c0f1c0813120510020c070e01140301270b150d081b0a0b07030207030e06040f17150403 55
    0x10781076054004111080411003401000711104040a03c0d00b00c5080d850501c010000c03003286030011910300078000450880020004c800d001c8042c5580c044100e415200322024003446444145607010903024181c0b0302825800f02030310a20501d4005560080300340041c0201d1003a10144400c1400052903a074180c6651400281c09a51081d45c502200050605042414400449581c500740d94003210b11f0034403a12075001c111b8035142ca0040c0a480001c14101ca058421945c4035081409108103c0c10402d100e586841044002e0ba8240006041302c0805100781c800f1b40f24440c0c403035240c407480062102100c200d04010462090391050f24000e5a140030b44509074036100c8094182080c00c5d88000410710f03d51181d09540c000446860b01c0e00d6103d0214a40940c41e00303140e1a041e0b07001ca03041c0a42903840b090101e408100c0100c01da509000311a0a513859014000612600303e490300c0c40444040e0020b0100700c0018040390040c200c05190300d030742c1c0400465150f00440c107131039a4950700424180300d100c81 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 743134361 1250 743133111 743133119
    0x15070f02060423030604080304080f04090f020d0e06071e020a06020c070e0108070510050a0509031f0c09052b080a0f30050a02040b1801030e0f192a 65
    0x34032080310200c1000d0f1300800960074a52580581800002c0c80108800000100c0c3c1424800b504c0548000700900f03c418041c0e0046008208040c1d086410040c10b02440e004115242000000c0c0b143d0140c5103e03140e213071722910710500c6180c0f1001441c6101c0d0070b51152000c0c80780010080d100510001c1d80c00005802d2035420006c5502e200c10040e401201d030741c0c1c00000140290b41c1c030344010040c3c0d1501420520b5441c0300c0b0000c00c0d5110302480845941c9401000b02e06131040034a46c070000505206a401008440c41032001561000c4190151580042c56800c1c1c184402d4800800c511545041c000e50351b10700d140c0b90f42c2c0d40e0720036442850b50000180e00c0e10061247c0070b40050801910402c00194107140b40c400b40f641d04640c0e20885018924141c8860101d0145442e640c1200c010f000540c1710540d0b120880704285003070012803d4914006854040406070102c0c0100c2c070b40e00f008402c1406004141c912140040e51024030003c261032604824a0b11031480802e0a40c2c050340300848034541650500e8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 743135611 1250 743134361 743134409
    0x20c07030f0512040605031501110d0206150409110409020d0f05011b1d040b1f11070f080303240604030b0f0c0301080a080309070f0f150c0215070f020604 68
    0x41c0301403040743c0030b105100c24041503412005070790344009098030503a180d007003040041301c0c0c00d201c4003e008564014121103040e041d40c081a45c62083c00400c101c514400c070014180001c0703034492031000d0a510141c02460600e480c1642103206000d0009021203211400c5031110b000c42d600c02c44048543c4d81d5180c60186001c90007d100308e503010098205034001c0d02168038540c03010040344c0308180c07107140d81d42206103141d5600240e0040004d0399a4281018808803413010340516171803003041e81c0b10f00c2600c000142c0f128424400000b40c42036030000d1030840d00d07004800144004501030746249401094103001c0c054443c42d0103032005601864000e40f09062003481c000e44007901400404050400b0801444600c40000e041001c0342c4c2d10400d010390fa569031484403810815150010b514000301c2d03c10010b2040c50341424030050f00d1005103881503503144d00000791403160345148025001904610000b9440c0d240780050722586008080008281c0e4407030307000600030b41c07103504440080ca4980c84d0000103048 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 743136861 1250 743135611 743135623
    0xe0d09050102010603020906040b121f0b03030307020a140705061903180b0106050703110303070c0c120c051002161503140f1b0c01060e07140a1d04020c07030f05 71
    0x82c0000c00107142160041183c0500041009010720746480c0a030b013040d21070328050384148002400791000300c6030348c7c400c910301e40902850054405041407456001480c010048900842054009000140c45503407022008601d10316428480d01940070f000070305495141c000c02402e00c0c01d080c0c2c81400d04507045c014080b500e41030700220021819510200c0014190302c1410b0540b00e00c0d040c01515194030345000c941e440e1000c0000300342800f000c41401030060b00034051044883c41240300c803140b9903c0700e044444001c0700d004080c040603002c00301040350307051051040c8141076592043d940002088155a550644a988070f2042e10500ca0b071882c45450341482510030401c8020032181c0541030800c41740700140c0c7d0280c14103030b880501c402406075440d4404104c8424051800090000c03503990200c4614043c400c5600e8000715406c1800313288558812000c45011020075107440c6020703081e00041d0300c0341e980000f9400b50440d600308220320700d10004002d890010b500c00c9101c2030080940349010b90420f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 743138111 1250 743136861 743136869
    0x302040905090616230706021308030c0a0204050601140711040c030618050a021207020303010305150402030d0809070b12160e132f0304062d09050708010e0d09 70
    0x3420902c24000c02103c1d60f00701300d034007800d14a44590240d003480c01100b04510154413201000900081c4802080110b8000c1d0031003000d0814011341246e41c03644269184d201381c0020b49100e40065240c4401848e196010036080f81f018507000d40c0707140c1000d41842c0c2d00d40c40b214055400303e0781851701014525180c002c85200c44601d18040c80b00601e041c5544e444607891850418010b81ca4030005100c070038495058501844540310245d00a09000c14065201d030703c2130009031050701a040242e40040f001c3e90360140501c0d03001c0c0c0280f141d8000c40c4022110808050a00b003c1030140580005080e0300300c0000e0f002c0c6070714035030342c12415040c14052180020701d2015903900780014800f1018003a034a02c042009822740101c00440e42d07004143c800780d824103580501d002c042e02c1000c1d01a036502d048001651003544510001c028541590700502d00100c03003805002c8003001c6030800310280503840d4000b45181c0344240103d58110f51644d08850070350b81c9001c1b1880c5035500444c2e07104440b560020b204d600074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 743139361 1250 743138111 743138113
    0xc0e040e21090604030305160215040812030c0a050702030c040e07051f090e1513020306120a02130f09120809060a0513060b010c020405010905150a140405130f03030204090509 77
    0x400b207080460f07058022440050700748040843d4aa47d01030340f601d05e0180169000b03005e641c0d10942607408405a4201e80a011600c0c800c8010300c0c4115601142180d0140700394101c21b03814501c0c100c40c01c81d110b0b413200d04203e030036024190052074107031038034003442808400d000c0c00742900318100401d2001c02c0841d21400c42d03a0551201c040e15440390041d6001064810035032007224243ea5a0300d030040c00c0542c100740c0303503040f050f28840a04120304984c0034501070740701103801710421901d01c129190380310220900603501485d00356104880b071055500c43c0500b85070101011031721100c2501d40980d0003440d543c5041c00703d56503800b00540b07204203103c0e0b07940c005184401000607040c24614244c91004100d401049169250301da40d5641e8002d01c0e80300c02640c1c0c010418400c42da10740600c00058202500c900c001e003c005121000146406e030b6140007510102074140000051103420031000d000090111002c14511704110000b04649142660005010792030150fa42c2d0b20b003090b50001c030362005288241c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 743140611 1250 743139361 743139367
    0x21006080304090b18012c1e130506010623030108030408060906100303390c0902181306211209080309090709080a2a180c0e040e21 58
    0x34100d415807415100381428545a9540c841001100c03000c0c45038101494600d24001c0242208c0d140c9005004402d0348030168045440c0d15210440d01c202c3d0150052890304810b0042c00181c0c421003155042404500400e11a0346880e00081902d601c283c00c455043d8000180901c40e001e4200040c3d41c004061600801035440c00410924016545000080c20098500d9852f403604000500320726014001d4010486011440d40b41441d0b0001040030485010442480001c2d8030b41d45403003036500b0700300c06840300d4a5140d0b51004202d078001000c0350421410b0f958800114841d1462842800c50100740d02002040780003a00307043c81c000c03841d0300c00d003405c00040300001e100381000401641c7c4840801c0d41c0d040307200c1d04c2d80d100c00e507040a40e9820580700c6d40b0900b030049003405201840d00b81820944c45041c142c0b2540e4000d1070032404094000e284840d00e074407404143c0d0740ea075a800580303580d01c146407010141c3c1382080042c0603161a0b1440e00e8460f44141e140c8008101049140d80e140801007025074030b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 743141861 1250 743140611 743140639
    0xf0403080c01111c11071a0718150e0d06180309120f08030a09050609030a0311030709120303110f190905010e0402370f081005040c021006080304090b 66
    0x111003a038134189890085c5c0c54480c07044444801a00762840c450340038a04415a050a01c00840002003c4852900080e05610302011811650210a043e6a10201c03031011600382d9903402d890803c4101c10380c2d80c0041410b1004000325685204070550701c914031020003901c940d00d05000b0b2100b005600406943c070007a840c26400140509841480240e1140360182c507030341e0781b111b86002005088405003460050310301f00401120040024940055182c50400040000110100c0140001c450768004141c2d000001e0240002210120030007611925000c15041004e04d094880b0360451900d01745000d0001c1039003d140e07001020104000405803074010052441e0600080000c4440302c0b07154003480d40080c5405400e044001510808540c00c081c4425a031142403801d80100789440d1524001038240d404100024440d000550041c81000e5102c2c01c8141003170104401000403080d0041035210341090384406c1d100b5030154100420070800650b48a03850b1000000a50720103030344107441020400d045071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 743143111 1250 743141861 743141887
    0x8010f15020c040f0e16060318021e030f0d020a031214040201110a020a030807030206130b0103030302030a060e0712060909080d0f18080c1627020f0403080c0111 71
    0x444100c02203c000c030300354248120b10740080021850208160003255086d580c40040003410404484103641d040040c2c05075a0507841d604403000b03400941c030130070300682040701c84a940407840d01c0e0200201039401c0f040c58088028035003011a10f502c00580c00070f4050200781500b0a02c801c1803203045100a001e404030303690b0900c005580042c002418410865119000600b0411011a005034060008a0709035142d0038210301c203402c5071034224010b11681c00090720810034121064542c1d40e2000080e602c59083d69010ba010b508020110400590342c0e5400280b0003425090340c074060021902c6610030030090105d40030646001c0e400041c1e615007060304d810000b4441400300c0c3c104440da00707000902d00c1004941c4602414980e03400ea840c403d100c1c014002406410740041030340305491001c4904c120102e4a80742070042480c8940c0f42c50b00480310210506014540d2019014018038000501d070140d4006460f4060b04560001c0e81c0c21500490340800c218007d01c036a0440007010b550103814409243d02c1d103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 743144361 1250 743143111 743143123
    0x304261c0903110f1e0f03160809040c080a06140a03110d230607081329100306051503030f1303210314040309140105040f030308010f1502 61
    0x161401940e100000740615104100d100316040002e0280c0710022400c2401c15903428040103007140c1084100c003100000034002801580d014001800f5509040c0f00086c2d031001642c4004080d80c061204204210b4281e86503c03420200c0303c41500c4000080c140441c081c01103402c6a04089036055001a41411550341c054030305c41143e620000c1c0c1000c11030311b0400305a2000d006000102131007481e01c8010245a1101c501d942000c220500700c454a541d40c03403040f6140c902c182d402c1003c074082e091001002c101c0343c1b10254510140320b00994004043c1d03209a2220b20301c2102c21280c4920f0504c0107204004a6001e1706402070401841c2c0d880c0c0b41c51450000e034070b80c42298807100c400500043c80301c480c126240c0204000b03641180d68000102412054080030789080d141042c0000e1800d148421b01c40001c10156004603055618018600d0400a0003510224616071070782c1481000c0c0b02c0090986440098079010310b03c05e542d8120719514295135a10007078002d0b0806908a06030880d0424596800030305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 743145611 1250 743144361 743144407
    0x906030b090c011d12010f061505090d11030a0b090c010f03060b04060807022a011e0903080a0504090203090d03060b0f0f0f04080a11131e110f030426 66
    0x20300307095950100041030400c1c4d4085c4071040d5400c00084407171030703c415440401102e2940e504001d101100e0803003180c041c481d800c6201c2d4041f681044c101d0101d502c0c0203440c0f1142e413010b02102c86403201c030b0b20fa903e00c01c002200c00f03008685c07103540c01c5003440d6440344415503039010600301030101c0c41c1004260455806640108010801000300060320603100300400e034040b00c40b02c0416171124608209041058a00e546100c0c00305020b0510710700381c41a881306000d0420800d03a5103126582c210303070303400420764440c1c02690104142440041004002440298040c2111100901c8007484084025065a600794000c00d81480180540403100a422048a55100303480c010555642c42d145041c2d04580aa9008111984a103410a0b07040101a8010001082c8100e8010f0006a8151041000d448031004600851401d040c00707846941d51581103d1020489804070314207107200000b40241c0fa42045609031000b082e6011144001c105601368000000c5980f04007500e00318280b09411010307104425 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 743146861 1250 743145611 743145647
    0x51513030209150901150f0905010c1205190503040b0f130605072307060506041a062104200618011b02040c12180f1203090503040906030b090c01 64
    0x45042c0c440b100c0ea4001e5100040003142c4c0c03941c485840c0112500300504c4807000c01c2003503c81d980e0b02030003504220212081652010320034029070f500c001c007483c00c80010700e040c807200b4801c003546180c9003125a40300802558900d84c6a1506090284540d0b0010b06817122400105043c4100072800406000d42039070003070008101e5403100d020454481005110703162000e00170440b00b100d403046d03100081a5540c00341009120540f501410002203503009542e1803110340e40103d2841941c1445030281000403840e4071034041c03410344501100349042e01180c003101d000220004900e4190b45181d0a429403540a42d0200d0400100c49898100002000e41c05414802c001907400781c0b4000e0b090b0001040d03903018200784015418071101900e180b4044c0c140a01c1e0608003a12148043d941903000300405030030100e0403000080648510002c0360414915000b010380300c0c0c02d00c0010480400c028402011b0312031000401c1843c50134003141031003019000d008990070980e41c1c1d00640e80e10820140d05481600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 743148111 1250 743146861 743146879
    0x10602100b0d260c10050712050c09131e06030510020301030305030a0f0b0310021305032407020304090e0d0311090a060e040b0a0e0106110a03050f250c0515130302 72
    0x14140307501d40101540e02d4411701c501e45800b803181030030350007081c011501900d840381c01c1c0004080110990707030101c0c0d2a20640d1310030b06c0192190310f001c0000ca4610303170701d5100000d801103041d006030480c40d0340c000e20020601d032222410410841c04012011030191a00b004504550450354010130520010300045512030711150684c012103d41d038050968a60002d085413003203007001540b04042e400501c040d0070003455400d40003505007404164001813400d0030302c0080780000d500001c0f07a080301c0040d0031002148018080403410120600c114520ba80b071440003001c04004900e40181514805c0c001d10030300c07a0052008038025143d41d2841802e40c1c602e8105000303105212408134004100083c10990701050480c40000c91240d9882d40c10305070f400c25918819481101900203503242041c0724010300154081003c1010640d1441c043c0075201d03040950800703d445007007a401d0344000b0302c1d10180e4400e00881400c000070f1030160703400c005007003640c0c0007d4180f50340d0102c03a24441860b840041d004181710 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 743149361 1250 743148111 743148173
    0x10609080718020c060f0612011a0d0c1a0c0d0c08120601030f06030803010e07020312040f0f080406020f0708010606020705060904090b0106090812030402091815010602100b0d 77
    0xd83c05a8011904080845400d4500300b00b5074041e403101030350818015504c1c02c40c0c841686d50180141002480d00305141d0342061100d00600100500c4071009446218108102280a2400c21402da0150b6030041113a51110341c41004641071041c0b800c0c817241481075070f61710680064103642c25501c0341192000b20502d2a541c440050740a0102c0440d061031143c030300318000c0204404800a14181da0340b00c1d034008220750b905602640e992281140e40e001c0f44450130005070000d40c10404051155204504003c0941d40c40c1e601c0b03598680041e0028070150f0058164003a0300101003000200900000317009000403854a0740113915103413a8002c590044030002007014075910340d5042880075551000700c4410035a901c207402042c1d404107000358101070155070048410180070790107482c092900105001030546450144619100040311000083e015401c8000c01a02c000b4180a0080070700350064000b414410040a044604030403680c0e215250000e4418081011a403007041c85015484da180320340120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 743150611 1250 743149361 743149409
    0x6100b0304140d030c110a0f020d08190305010302010e0d150c210c08011e05130e010c021c0305091e0f01180614071403060d0204061d0106090807 64
    0x508081d40c501e07201e0f20010f094010340c1075106908900040d940c0c15204403201250319261251040050100342c42c1c0603031039025140024444041c203100d6412a460640100e4125a02030491078044010071b079554010019543c100c5001c9000d903104588403012006103036204003054141400800700155511041040c2ca130240300b608460340204c03c1d101d2100d11640c1c0340c12024141182e01c40001030b069000016410310266000d008000c0d040e240e111545081c041880000208002e035074480c10f031030b40482c0e45a480d080c85001a6450240d0142c20140007452030303401d881074048001c00c101481d20080003919803001c11200261216181c540f0840c10500e030545141480807071041074294640155851780450312280740782c4881c0700e0b035024800c0d4502c4504100c03480c40b00320744d0000860303010112020070440d60300065034031000080580c01e86042c150045412504190000314040d5604039800c10005c20000b0740c18014080e0b071500f400c0203420300e00300d151904141d209000c2da21110703000c58918904 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 743151861 1250 743150611 743150633
    0x601140a0e030616020f120712050706050a060501030b0f1e030304030b0c190c080304020108060a0b0c01090b06030703023d0e040e010203090a17070503031609050306100b0304 77
    0x21009044541c01c2c1804c1c20a0710a00001c040381c50007520440e040b801d500741020074107228981c40c0c52050350a001598950b88202d0301c1030b032a07100406c04104070843c0001c0451086a0250000b031400045250402002500712003040c8419803140d00e00d91560b00071542c9141c10309800080c3c184403142041c0f180e602180c0f035800703170703800041140e03010320204000100c03036801800c0e49a9402c000c1302c820700d0404805a40c0174815030b00c09030100000700000340c0554000c0141680040000d00300514069890034031ba0300c42c1c8c01860254405075120b21000301840b21031205240c100dc400c0b006090110b180d41c0c0085c00c9a407408410000441945c5440303020351900a0301501c8000d00c440d240244840d10440090046058011031071040e4a450dda0f05454801482507910400b2001e00510706030380740351100204960201c12114900d0300420501e000a40248007a50040710300d13200090100154213401740c42040c407500600e0213075000c04104610003503220441d008032a51034000565945a906160200320 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 743153111 1250 743151861 743151887
    0x9130524150a080f01060e090c090307080f07030b1f0e0a1b09080d0903030f050c0309041517060c040b0307020a0209070e15040f0b090a0e0109050402100302030601140a 74
    0x4020500403250b5400001e42d9110b0842042044c405a07201c41041d40c0156040742526000300300100003804032000d1000410b58110000e007140c016981d6940281e14110203403001d0481a000060b0130003c1007003400d04a0b4004801c4a440f1132141070100c4070304140c046501c81c1900c128041401b1410960b01036001d50b00511100d10140091450b0a00241550403988600c050310b111709502e0611741440b0301c103a041034a07415502c02c04028400c038802c640342e03045000ea004a50100300700b900340315035440c42215010000303005c040c40d006181c4414203124910242d0556001c0e004003082041110504084800341d40038100140c1c4c80380c42e001c8040780f5290708804003c0d00112180244a0426005062885c03120350486141000e88140001c410035401548a0103002411201c0240100c82044001c0d000940c03020340300360811a610741d025000f025003039201d600740c15580c03020701081d400d1900c2148041492400c0070751850920900007400b1300c1d0b403803480c0b20f040b42e400702d004601c0d2803007a940c0300aa2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 743154361 1250 743153111 743153149
    0x3030703030c211d0c0102060f10090906060e070f0509061b060702010f1b1d04090c06080603120403081617070b2505070b07210209130524 61
    0x11556610700d600003003410400781d00b03140228921045611500013081c0c0044031061f030107050340383c03a0303410242d80c0f00102405d06142490200e03c082404221440340c0c0301264002e2501094207440e00241c51600c03500a0040320403c41800c90301d0300180d8002080b91181c0300c05031561503650150101c40c82c000003104081e68030382d00486082c0103209034150480307402001014820805c20040145404000041d6150400840d12004e107402c1000c2c1140440b410b200c00142000c910548159900b10340e40310301f50482d1000c20700460910041c0c1c01c04014407407000030011540c52616080d61a28a854028002ca2400c02003001d6283c00400402e448a11350300c207440ca081c291912103503d881400100111800300820b40b5a1203001d5000c0c400743c080c4680d0340320750f4448a143c0a0b580d01c910b1200b40c00105000180300c05551441c0349a0302203410140041303154800141c881c008401000558801c40030030b10703a1242010280301551050b089031030111802c0a111540c2c1e1030000c8040303101d0750313030606000e045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 743155611 1250 743154361 743154407
    0x12080306040c020a0305390109120e0307060311250c080615190806090a0b100302060901050d0e0706050c06090f031b21040e0901050415020304030201152403050603030703030c 77
    0x40c7d00c105401100c01e55103d0300082d54052002c2a0071101c0d09140c000843e450342c065041084400c4c02503205402c480b00101d80540390140c1d030800c02c1080c404000041c60a00750640c1d00f075003840b42d00f60b191310107040c6500140c01e19081100b240304581480300c102c584aa00310702c1409429428496007040105007050540d41e4614121945a4681d001c0400540b0200e50440c00603551300b01d881ca07803c1c25242d008007140d0411240e10011129038000100b43c0c1c0949039121026814100100805d50003094030b580c1d26a651012114441c0c206980a0841903039070340080742101d00f855002c4281c03503c481c00704840c40f280b1810010510701e44119500108003000016001840842c0200000c6c0103444540f0f040441c0354440c00120f5088900032240074148062000302100c0141d0076400560f0418000e00c00801c910590682d9000f070b00c5050b0f400050780400031031000d03400c11014140123203019514101000b0310324001d000f09840c0d00ca103030002020180d80e142c02ca0400340c060102006c0c00d0701d400b000400c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 743156861 1250 743155611 743155717
    0xc03030f18030c1503090816020a0f0801021b0c01080103030e130212061002060f0c030c0c030a17010f0e0103060e070e0108030901030f1a090a0612080306040c020a0305 74
    0x340e0f0320741d14001c01240d0501c500040700d01d940207000c0e2582c4150300c055501e142a4030341801c90708003070041c6022030384113460390b00019403c404901030101405801c000107030744a210b0710764041c04003100704021150f0b40000da245000341c0e03041480c441c1100d03054104452264801c0740000d403400c1d82603180940c003074404558403078074442d40442a48a4241030b0ba0054080c409200b0581c1d50b0034040300c00d400900340c0340300054400324807500a10382040400e03d41d103041551084401d4151b4005603001b03000a8100c40354014000118603540d0300400c4040c5644c2c1d103180c14102d0b1a403051405010103018ac07901c42044454064007002048000c100715940030341e0950f1288022902d03544600c0505000909065a102d8075101c5449035007010200880c0400e802c840f000180604010020100a0010780d80d000000d011000b04203541d06952003151035a48c1d82c54550700f000304503111851603108640c0b0046c40200026003080864103441d40301d422310301a5240d22210704014000312003104a080b41d02c0e440b03840c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 743158111 1250 743156861 743156873
    0x40f0b04020118081b01080108060112020a030b0f040606090b0a0911160309090c030b060d090302010b0402030a02210114011b0210030504060b090709060e0409062f03040c03030f1803 80
    0x29441c00c45c2c985031105880f5281004444050080c0141840b5030031407070040110f00c3d840c4800b182c840e440034103424150f60f41ea86030326001c032034122000e0b051035444208000404c01c880c450a00a00141c0004100c440381c042c0128040a2081c054500807503aa826a11030940041d001e139801032388143d5a0380c51680d49860001c0c803032042d86c86056511414992400c0d2030b01d020340114001008083d21041c00c06c40c2e03407091a40030301100c4800b0303005d42d583e4009940c0303561540e0000b144101d960b560301580c0e840d422019803041d21880c01d02d00841d4500540140182c50321250b0b00c0c101140240b0f0181030b00d900412403481c80940300c800007903100312140c03407016401f600b44c0c000c03d00c00c9004600800200c0d81040600205e19422180300740003030100b04c014004140184400801c415028000003032401140e03840c0001c07161f803103005034402c0d42010b8000741110385c101c0000e187e50105605c443d056050964951504001700d0100070705201d402e040c5600c0703444c8199094846403e02c4148264425a07a0407c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 743159361 1250 743158111 743158123
    0x1512020a05130c021b01081902070c060206070f08191d01020703020d0815090412120204090f060b0403030905060d02070b100311010509030a150207021314010509040f0b0402011808 79
    0x143c016000f07107910895070184114910500e00c0042e151150306698554840e212141c805021044041d42031040e10b0110b2250964080a411150001c2080b0701b803101c80541080c507403002d400300300300c00941000884030310804c40c005c40d0251341b01d000c142c061441a20000421403088840255803021500a06041c0d000807070000980003520742d00a140c6642190503410445000300903080400d0f4000300e400206400326442068180d0f16015407070300c4003004418141d9006500101d0607544462821b0800c07142031240c80d005011102c2564038091845d038028064407003500c6000e11030003001ca5008107480554045a040c2e41d0300c0041030180b8606412040101c000d80e00050b100300354132000811455000c2c408944038000000c000780f145481d80e03540e0b114110b241000340201540c00380408001130311801b4070038000794644880401c010251040283c0d0b21401640103a11501044040c0b00124621004041031950000754440050b503941c00141d82c01560140c81012502e42070400242d05c00c5c010401c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 743160611 1250 743159361 743159381
    0x30705060a050f130311030c011d060a051b16082a0102090f131104030821040809010f03091b0e1b2d03010e01181512020a0513 56
    0x1080241c1c0e00c0303810f406280b44000700c4942c10040840020701011900441041540f4030341b00c002c5070724100d6010001c0b0b007074860503000c41c800780080305210004541c0c240715065118608007820451890020a01c00a209403003000d5912450001030800b24105160940030079240c00443c09580c4407114221820f50002010b4484007903201d40c20b00400704103041c000c95406030380003461519164411002c0117107500d4034600348804550390310460100012100c01902c015800340903165142e1076004000641c06030b00301d110204141503c020400040c10400130b03a4401d42c42860200441441c090041d4001c05020002a002425002021602c02082d8070071909031100088181415140c245454080d6000c000c1170038105c5405214000740e040a5030201c1001e40d0f20742903ea1100d10000911a0543d402a00301110b603040d0000144031501d03003043c0300c0703460580711082000340f00c0e00c40915094440f902c5c0a415100c42c6029002d90955461104410240c100106070007140e002c0500f982c1d00402d08070003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 743161861 1250 743160611 743160631
    0x81207020f0a030804091d101e0506010f050f120412030e2a180705040f0503030c1b010e0312182409060c0d020a020102060a150e06010c0503070506 65
    0x260740155041c61000303181200da2100000b070905060101c00c002401a01d65010000242600b40c003400280c100b0031031700c40064200f00010860345041030803108143d444610590303507003444140603007640c2c4422045032034500e0b454a00d44034901c0b01e200c01a240f0500940401c014602d200784414007070039805a542a49003a03c0400140c011020516203804c00303040e402d802014000801c00d0955104482c0a40030003004100030300580e100c04800e05181e80a441e03650000740c0108040c080300c12011750720b10140c07000710001c0d81441040081e2980c0c900a0701c9032069280d40100301816a0f9004003210104c00800a0964100e070394840c24404c1142c0040c2000304680040d0400f08001c0c0c1420690810320340d4502e10820130030b8170040000216a1702c031554098004500700b02000302d00d0b806101104040919901800c1400f40c5400020314103403000d800744845528004451f02d204580f0316180c2e0840e0a0000e10280b03540c0c030301c00141d450508029025015000005407070341004008100343d441015844 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 743163111 1250 743161861 743161879
    0x60621150102100e12130503030d0209090106030e0316110a08010f060b0c030a05031005090f060922170708040e0703051506071e1403040603050604020a08010302150408120702 77
    0x410041c0c1070f104c6510b403082d4150400c44403900482240c200400c1499807921180108660b90700100740385601020412403010381c0810711a0782450050742c5c0d2801442140303010300a61802507032580d140e210303100d100104030103141c8010703081254800c2655101000108086c140e01d5852940c2c0d07000c0d1155401c4c86c0c00c401c4c0362a03401701d1080e05c60420741d094404200e000303600f80b180c940002d4805038000f500b151908100080005802da48004209103e520400039000042c00c1c003a0900c412904044c180a99207a241c101003803c130072202c1c144c01552034220040c0c202694101c070240c241c0e4400d81e0303005000b62100040200e050b00694001b280604125a0200101d81d101d1000c070803910103c940e81640060b0130031440011a84c00107030710004a010640070140881c0940c0ea040070708181004260581d00007280400001f81c0510440340c2c811400d4800f035251030381280300103010210501000f84124021900307d014442e1342400c1d107020703002031400c66410310800c0074542100c2d04150000c9128401d14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 743164361 1250 743163111 743163133
    0x2221e0c120c0f080c0408100204060219080f0906160302030703140306090a110d1b0207091406061b0303092d060106080a0b04091b1d060621150102 65
    0x42d21a2400600c65a81c549150b2001204202d83c4901d015040c4503200b40c0602010600c02000c1c460308151503d801c80c0140d07201d26040020303044c50020310034035402c1541c500302000400c070040119000600080d41c0140d03298450320004155000f403a020441c008001d0200b0b0b8201034000006009041c003e454400c6d159800765a02581792004892440d0080c090002154110301d86401c49003550010351811070425850844c5007040318959000e000303200210b0313051551181d8050005d8809000d4800b411301520440c2c12245e1441d402c090300046c06003600103050700c1601811128500d145c0001810b07280d587c00c0c0110104c4c0d07030341a140b40c1c2c5078a0036a4091107004080d0a4188035200880000207010180e01c1d1000c252a201030003000d03054425140d0150b00a43d0340c0703c0c800c52003170610400c59050044000d148070180c88239540c000c00144540c2c000c44040e204001c00701d4640c800c6003140c400341d842c08114881143c3d0f44051250194944865050180a4040440d02d4407105400e80c21560a10780e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 743165467 1106 743164361 743164397
    0xb0f011a280e190303090519120203010b21011b0c11030c22061703040902030a0204030c030305182d030106080f06070e06040302221e0c 60
    0xf600201380105508021900c015040039100c0f200c52150048065240c40100d0181404041d4114032031030840d0303003d411a000d00740e00508000c0f84000000c5081640c0610030032100301650811f40d076890b050a0313100842c112540f0380d550f409555182611380003072402181c10599018014908540041c1d100c9050801c00004035a191001c5002d6078030283c1e0454a0b0354001440c0f22071002c3e00142140350000980d0269800031100507665151a8100d070002e1085a10040c0801e20001c8000b00f4581c00070040c0103107490a4280b42c00c0c0b410b1141c10405c0c040e40050b15881030070101c10160301c07410a030944c00302032f0000c0900006041d9031035400c941e01d04031620307102d503d003980004100000d1542c030560000e01c40c80181c420906203400d55001407201100d02d030600c01501c081c6941940c0600c51138000c1d0705c011140c002c501d2282400400242d01401d1a618680041007810b0981080394507 = true := by decide +kernel

theorem cover : BRFrame.Cov 742985611 743165467 := by
  have h0 := BRFrame.cov_init 742985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 742985611 ≤ n) (h2 : n < 743165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
