-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1567
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:39:34.478658+00:00
-- url     : https://prove2.me/submissions/571e607a-bfad-4fe5-b73b-5ded89f0b39f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 281654676 ≤ n < 281834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 281655926 1250 281654676 281654683
    0xf061a0a0b0a091401020f060a020912030c06060d020d0807060207110f0f09060315090303070f021203010b161e0b1f090e070f08010204050123091002011107030e041409 74
    0xc2600c944c42d0428000d404183d0090010925108040342562454034010703442c040070b54403810066005800310360340b401c0301e540048103503020804508098070068960600300320004107010426a440303d520340c1c00d40005042e010060441038860040580c071038070748d4140180064070390304132035019012110280e20141d4030030315040d60b502001c403807002641d00c42e1800309140c5004400140c1b4800c6070f0780d09101c0240700c00009584100c03102d5a416000e40c4010508030b882c6c2c1301845a8102d00081030005210700464038004e030450011071206281000c031540c40d100312503404550341911900520b00c0d0402840400c0760240e0340000444c500707881b045518107014011081c18440c48c40b22035601d50030400701480600c100401014115640240c050b15494000c2c001e610520841e0f0100d260705c40403090801850004410f0085108051414070000310140f09202c5918003440c01155600d0780c000138045d07000c0e00070b033061500903642e8000c0e4101030018401100c40080401c5001403505042218004000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 281657176 1250 281655926 281655929
    0x281206241d07050c07090e0706050a021b0303120a050a050105062505010209190e0a05100302010c03170a0e1b09130302160b03090105060a050a05010c0f061a0a0b0a09 73
    0x159001d540e0b05202195140244544080a401010300014040d5690380100301070348000c00c25a0304c940e6403182c003a580d9210b0450002c0141e04019016a0214580c4a10b9182080094140c07886d102d000d0703811307000040084071000400e5645100380100c4103418810207000d0300042d80d0345403519820000c0d00300d07032285003c08030a4096603421100e0412200f90196050018060484515242c4010042c03502c90a280640408017811000044a131240c900a05001d84841e1910704102800c0d60011034098480c40016800d00007000d0000320041549418503100360300058001442543d1b0382116420031150344034402c1c20209800458841d0b940740418242c00071100518480302180600e4142c0c10544182c0b094007001807020400218401074000452144402da402081141c0d85c1004101280c3c820b0b00a440c1c101c40c6401c0240a41e501400400b078000d0f0058400085010088d82d94100707407104282e60301c0c0003c088017400082130400840503000341c07911a10b01c0f410481242001004012103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 281658426 1250 281657176 281657219
    0xe0d0c110609040e06130308070203040e15041b0306080c0102030c060a1e0614181302060d0e100207020901151e03110c16060e28120624 60
    0x3070342407000d07580c0ba4441341c222042c490540310a80b50820000e01c5a00700c1090580201d02090000f581c0b442c4040100c0301a2880c4120144c0309403121140900b0301c440c044803103500241d84007400e80301d00c02d4038008551074900c01d5801050944c1450342007400c00184e070056a041d90310902941382d20700008900c01780e0003543c805000689842d00b0030f4803c000021035036036104d12450144046080303070a24025000c5035038186c6402c44440600455021510012501100380d0320307850b6021801450034400421008071400c0d0040b0300c0e00e28000c1c04c3c03070801803440040c541c8260b001904500b1800e190101c00d00401e00c070519414040504000588400382c1d002e265218440e040358043d0f1518001e42c40010009820503a007503c0e100b501c040641d84000c1c1d16aa286080c00354100090140e00c210b1106501c880c014241845016001044032400c04441703800ca0b1011070390142c00b2408070703050980001c03a14001c000110340342042d55605c42442c11660104040901c03000002d00001080ea048800443c0300c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 281659676 1250 281658426 281658439
    0x603081b0a0f03021b0904032337080601020a03050d0618050901050603010218011101061706151f050310050603150f0907020d08040302150103060e0d0c11 68
    0x300c0310540d080010400005080c104415070b02c2c0c1c149540040e503500740802680c814600b000040d0f041090689089030014006044000c0c4c46844d04040c409080d81025203550007810045030401c004001c41103009000c4000c90000b82c101c0c540d00b0b13645c03464000820395040929642c1030110000352900c5c65054081c081c0031001410820f002e078140e100e80020b10b01003004009400c0424070030405050156054081c85d803c24002c200d0301c1c541031003214481480381c0c111844402c9018010740f200100c1d03101c0f0030074a5503241d0300020741001e180301a543e02c7e0007000140680345800115070104458404142e40290802940e80c020403207a25000140c090075804c007580c4030307600d0304840f942d80101354114035003003a00402404084482d408495072111340c200c844940c4007002c0c1061104182d0100c42e4040113a000050726014180100350326a00940244182c0c5d00002c04a0181c01081c0421b0780125038441e911041c0040c01c0a0903c80003001804070b25140c40807403820384070300c1620343c0342c03a4406101d01b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 281660926 1250 281659676 281659717
    0x801120312150623041412010f151508040303050a15080f1203130f020a0b0f130605130603020c161202030601050d1205090f04090b0613060308 63
    0x5028211002104189035020b20401c244904101080000c52003810003040d0003d40019a841d0141403c1083c0c0890b002c1041c201807402d448404110558940c881c0c0082543c180e4604c440b20a0081d07a03801d2031103c00100381c544244480e2203c400311580403224146041180340800c9511002898000e80c0503d000700c0c040c1c5498a8190041c000c00206203403540035140c0c001214000414220940d4405205071a16412560a901c0942c4011140b20f0310f814440e000520015402c50030600c81e0600290804a1154590301504056842200e54130803104011500c41e0052501c561680e001e4520740c030b081801c0103035503002d4446d00b13151405204145034010400c4840c10504125401c40d0301b86a00e50201401d82e6141c000d9820511920140d00a003d440300115840c100b9190a000300c4e03903c10002c01c3d00c00d00040003115140c12000000e94000e1001804d0070b401d95460082d0384480740108034000305030401e8420805c1c0040032100404441e424400700700041111101607030110868003858041d0103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 281662176 1250 281660926 281660933
    0x60703050301050f0f0301140a06060509092703032404060503301303051c02070b070602070b010305030a090806090c1c050708030d0c0c020a0306090c030206030106050c1002040303080112 82
    0x21750b00c040b054141d031030440074540b1004c0e00d940782801000202c02c2000500d4840100320b92900c40c52003201c1d0004801f03400301d9041c18004196548400c01c50000050542c60300d210b41c0d046910030f5070b141c01c5201d50000340c3c1d004003c0d0482da002d01040111000c0013110318040200c0d0301c5070034802c04002005c00949039100c0f27065031a800304141404a0510039626020704030304845641c0c4c2c41c0001e03190761040140080403507007050700e17003400048140c0040ca00d040c03503c451480264044901102c0042d02404604001604e40c165180614464005140c591800c0b0200800071800c0f90300c6003440b90302510910054403004503680e500b208003a0359441403110124029071010b04074075002071143c4203803a4005400000800500b19107a40b602040c0800c0c0722900d070440e04d03010a200302075485802c00504200044103070340680303916031241038140e01d929900e400203045038000740d20170004070b0400905e0021801e800c0c0b094540c102c04040086040c54103540b002800407205000f441d540c5400c9170101c1090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 281663426 1250 281662176 281662189
    0xa12110a06020d0c0e03010606080f07140d0b090f010b2512030204050108130b0c030901150b0a03060504060308030429280c140d180c030b06060703050301050f 70
    0x1642001c0c0541d61001c00c07840301401024564840400103040111000062506010708811181c403a5102401c1c0e4945541407d60414041d00c1d0005002e062604c2e8031203195210080e103020800b42e00c00050803282e401c180303c80080010208216039001c0b100501c2a1810541580c2c44251030755495a074134500c004a00d403402801a0005d00010f41003000c03110140d0741a0000c0c8141d44c002e903900380c02522620829a244031850000401c40c0c5c04010000e400600044081c5600084800012a48007500180c0954404040c0c001c0c000ca0707100080c0e40b50312980c060050700d0003454150340030031178140385071181c1106020242c0002c0c00c6615003043d20001c00d040118800c152150303a14042414140200804550f29400c006081c158001e1121429071850601ca40181c1d032000781c407004442c6d02c2c005040004d0f40d2214014081040d81c0d0400d070040a00c41840005059104800e10841613046090520b82c07143d00800301441200b08125280000e54410300b50b0381150800d581030350300340c901407000621 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 281664676 1250 281663426 281663443
    0x30a140304090f0213050d030e0d020d0209090105040b15060403060207081e0405030c0103020c0339010e010516090e1902030703020a080603010b18100b03010b0a030b030a1211 77
    0x11203d0400040155201c1c0960050480107030900e40905000d50b514280700700312041100281c0843d401810b00340340c6042010843d900d0754030090100090701c4035540002c00400b000d48404205a6541c1d08010821580701942900980142050f07a46030400c2c100140840c4128000200000d8010580b4401c01c5581420b035207441e02225103034180748081f4446016103030020303c50a44280b0911116021a5000303200f1034510b1000003001d98644140d500509805a01c82c00601495401c0e801016007085054450121203070700000000c100c00048490352400d507500038103441035951103a40064205600041a802210b400703400d030601d07a82d135000101c0600d00c0f04840842000f40004204030b40203a243d401048004a84d4032124420b44400e001c1c107080700c075410b5030389421180380400341c041c1c808292146503000c0e02e030f401c07100c1c1d589440300003602164000f03030303c20100c0f05030200d0341140d100d0f00343c01040e00c000d03c10340c001d003185000c68842001141d4800c1034101400317103a070704011179540d040c4104070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 281665926 1250 281664676 281664689
    0x280312020405030102030c0c100605090f09070806070f0810060c1b0f150219050606041a03010c0207061b03021216060c0504060e0405090a0308070c0b01030c0608010b09030a140304 79
    0x41d207d16000b000c0c154642e00c48145808a0300a00401c490101744910a05056510243c03a00c4040d50707400540031500e001c0a0000750b010310600a001900da10100217540c80b0f80320740e0317466185000c0b94030805800e81c803010b040340180389240b07030080c0400c80e40250845041a01301d5400882c41c05c1c0c1020704860302c038075908600c00c0c0e00114100812054580d003000d80c40584c040d400c90f100f00004013545850271403036010060082d00f012000c61071070b2401c1c1d00034117440039024165079030f0540c0d1100001e0840d5a510300e403c0150300008410011241c1100d01041c0d203407121070080c0d1103100640c1d4025110341250507944c001d036402040c6140f0007941001d20719580d551040041041c1303a0f41d4813015211b81c1144c401d2200050009034100c1d114103190040c01d00402100d001802c1014480d6000d4a00e003100600c0d00081102580b404808039130b0904e02d043c000d501685c00401640e05040e00200000e00c142c00214400c841004260a46d17100041c40011540d0005010564020071814880c10362003194002c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 281667176 1250 281665926 281665931
    0x9091e01080703030905010e0a06030506010e0405091e0a030e1005070f03030b040c11070e060612010611011406010f080604022a0d020c030a030302090d060903112803120204050301 79
    0x400e00c18000030b51001500c0c082e444075508160b0303034401180d040c2c031840b00c0e540d00302486000804c101390082e0000c641140c2c05043c925900200d841c04501103960803a04451180d122070060824000b0340c0f041c4044622008010300b1004000c1e840141200d44503080c000e000340e41d8211140100741c41207041c0c1e55440e500a01c107014400e0035041c001c019040f40e1499501c0385c2c5c0740070541d04d00c0500854455072080c071a0805000140d2070040ca1050000004201540003007080206441d2541040a1a40071306680d440b9000c22040700030f101401c417400e10620341c050704c890000340076460780c2022504001c40c0075880c20810035a102e1740444d0186c09200d00b071155002821040c0e01c03d810b000054007418042800417229481070314141207944003012607269402d074011a0034200030034800d030020540d403500a80300079014050f66403500e04030b0720304000c154001500003002d801c41c02818004c902900100010014080c5036417503a140310181414801020701c8203104c0682448140f58064a00811004008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 281668426 1250 281667176 281667179
    0xc1101030f050f04060c0221090f031c030f11030f06030a051b03100614060307020307170909060301060b0a030213030b150108010621090503120406021e03040809091e01 74
    0x840490244d804884d5035060144100f110303440007034105106500304004556a02c040c48040049500c45092140c011003405400401920200684000941020b0001d1418492140010116000381442404641c10040300c1307020b8020f507206494000304e6000582c0d920361180d0000910b020700c41d110046c802c3c064450011003442c0c1c01200500c81c090147c046da4501d810b002503050480b0860b0080b804001c0b208690046941043e10240d5071000441c01168078000355034031080000c2e81c044000c084407840002d8038812900301040da0a8104a05400a00940d030510b01066000d0086c0c00f0218100765005c00c801e842d06100080000013541c00217904000342c10301130652a00d41100303070b8200d4041400c001c00018020300c255524800c468010b6950b20301903901402d04406000207880c281d40034403041c040c6a000720f2001d0181c5000c0c0b4802d810040e654403a10402d10303140362150b0341c00d032070311034040c010480820207507012144452002c0b1981483c0c0d989041030140c45c0c80c00b40f0610803205165000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 281669676 1250 281668426 281668441
    0xf3b0405030901170c07060b03030f130f0611060105040507030b060c060106020f061b0901090b1c0c020a0b0406020714070306050402010905090c1b010209040e0c09070e010c1101030f05 81
    0x2010310002c207030380d10192403030070300e0000e8203900050701c078070321108404c01c405030205001c3d9101c004011802420799280c102e01d0f240940c03c03904a901d004002180105c010008bd00401140c140200310a00300b10003400c880319840703038885605220b01d5009030b8880d0b00103078441e8401d41c050302e24460002d14040d110003104580a5a80200340a4200580300c1c0f0400540c5680703002401c14420010a101c9a007444003040d2a01c81c140c00019080b81401701c3e00b8000b095400e2550060403580b6a0443c02d1503681000d85038030b0040c1d4103000c0301d0006540161000c1d0000c12403924402e54415000000566184620700d030240101c1284800300380640a40b0001004200306900440d000358002d270703156070a068459007001072058060310325170f10f549800c00200c003486840c07009405403180030000050500914002040640e401960500307500d8200c0196800245010b201d5560810741030b00d0302007845154800040c01c510f030501400b83c011030302c04404801d0340c2e1003a0001c80380042e0400051000b81400031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 281670926 1250 281669676 281669683
    0x20f03040b1b07030e0310020a03091b1a03130203030a0c06050c04120204050910150e0a06080a020607140106090225150237090f3b0405 60
    0x980444206200402042044410040708a00b42d264104214a0412140d900380c1d2400303d10081c082d014064180048020580c91028181c1c8103840d40740411191a540340c41107070008089030340c908200038a07100f8041c0c10b12048074000007141c2491350710360341c0e200d00400c0b00303e0b001c41c004001c3d40362100240c82c500c00c1d6071200c1e615044903c40e1400b40004c0d00c2c1da0b003440c14140158040c0e04150f1407990448005480c0c1600025049410402501c0076030104041000c1075440741d103002022002d1090082246803501c100722507003d040c008041128a0600c00a662684a00b00e00070b0300c40c40021485100788400c2d803081c3e0645000e064020003c544d030ba040d6600280d00706800b20f82c03042c0c016166250030300103030080702140d50364003d40c4400c1e000508040100290094084141c4881e50300711100d01c820081c40f01401c507400e54409040c044141141d00810082607a0000d01d884865124104010707000381d220034030004c01c02303111421641c1c8019000c0700d000f081a81078180c12004241884240540070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 281672176 1250 281670926 281670931
    0x60f090503071d0a0c0e0907050d050405011a030c0a15050d0212220c06120b150d05010f0807030f030311031005040507050f04090203070c050a0c06080f06030307031d04020f03 77
    0x60150100c55a14100200f041345e40820184012a40d4074041150a2a080d05105d40c000c0e901d040c19410a050b80510f0b104440e021103040b26160755602003000700e00c0807803141102c5080124000d00c03c14400c2e02c0862100241441420340c0d8440e00e003003080300203003c0c60036034290210310002152a105c000380d0001700c522040d6901c004600ea00d40c000c04624001c41030b1720100303070f03080403498000c140b601100f150a00d51b10b0b0400302920b5075422000c100c07a0307260310780c90310080701041125481e00c030900101d004561041e44140c142c0641420100a1660041052002c9940200d5072461400030303424103401601a000b003420806d40000304006100c540424010f080c3c600c269820480b50355409800d607114071444202c0c0000c4602400104074401d10381d0011070b400049440c00c04502aa1542d6180c1b80030b800841c21a00100d8483c4280111a88042c2d119444125502c09c1d0185040010119440f442452400380070013004903000040902d130a120031001140c0640f04641e9070380d240490400c00d8109 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 281673426 1250 281672176 281672219
    0xe03070803090c1011030319060b040801020319050712020306030106120308041203110714070302030d050301080105130b06010c02040605030d180b0702030c09150613150c0b01060f09050307 83
    0x410400314007131849a05420608071600008619646071040071005c0003185000004034940c461501086202601015200811210002680728201a8041803200c04c4010107810550714002c00c00c5a015408003a0111301d9080090050f80c039102d85010031301414007504014070510044034034408056001814034031075030080000e100304403009070084007500c0c00344a4041001405018030004600c41c52a62001c5022541c01c40d1282035032035012034101201c61354104041000440101b10000f030030300405500280b44084003056204070b42e20442a40c1014000078108400c0c41803000440d290340d0700c1034015040040c115840e500c0003590080c0349804022010308400041140000c149a200f4155400540d0041c0075040780d514440c12300c015510f004041c0031012840e4050702085480e48801018803135400c440300f1500701e042220a0282c0c0c1c0c3e451050104000040c2d081070041920001400d06641c1070f45003485c20300900f91400ca5480c41203400044d4980a02ca0000400003155a411341c0c1c950708 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 281674676 1250 281673426 281673439
    0x40303020423120a1101050d0204080105270703081b030d050a05090c01210c050f040f03030e0f130f0906020d1d070612020a0c0501090501061e0302130e03070803090c 73
    0x20a8040c02d0722041d2132600100b245a4000681e0602e601940c0649511100031a0041c28070342c1e44c00b2028207484094072210101c414181200794a0313240700700c1914082542c40300030210b4030701d1640e40d0030045c030402810242c1c032450a00000c00000e414402c40e10001681c880502ca58100391811900426054448007001e110b00d16141220f540a401c5082000b0740c00c40b42c1300d402c0c403048111840500650009c58040003020403160030311a0702680540060301006100500740b070300f9458003030f0000300907400071841095010800c1c20995941005141c035204460004900f00e076075003071401c003d002d000c500203100340c1c004500c948070720340b49a001c0e880c40680649482c001c8818a1451926243c0300d001e171000003450810213207000c041540043c40100700a2806000d41046e649401c2c0c210380101200f01e556035140c400410540e14103198034501080c08a5280d10620b1a680c002201007030f035130b160001c00c00d4503000581c011000c10b205484a03da0004007035517807440c100d4a22901d4030500f01b01e4600c1800d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 281675926 1250 281674676 281674699
    0x912031d0106030305040915051e0306071e120621020a09020423210a060c05030115080903040e04051f090f1e080c010204060801080f15040303020423 66
    0x3014050581120340580f202454141401b06500c080c00c0006104503141c49440310004564480c10a207180c600c0740421380c024900520307020541041c0029160900f0000303102904503503034800f4814442c200c205801c21014900f203c5030010064a0140d01c0a0b0107881840d000800c115980c401d0b109800d4800c03a20351000d20f0b1900036900c100c0c080c5000d506400302d0804c0301da0702030301e081103010649402c0040c8083c03c80030020402514020460ba1210f074079402c40c1c070084041001c940a6510300595604009080d50b040420500584403814440400c02c0003035404601000c0c01803007285c0c098000582c81e410649001e00308256600d85102e400506a0041c4540c2204032143d40300d008645540040710480c821407503224a00d482d0f88072001c0c100c1d41002c0071601d1000908900c010248900d00c1c000258a07240750030005400c1d1b0380b050313100c1d00007504142c042c02d2076050301264060f0140d44955121a8580f0380d130408030001c0c021034200324004500400219002e203445282a154428104c85548540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 281677176 1250 281675926 281675981
    0x2010f020408060f1b030117010e07060f05130e011202030f0106060905040e0c12010608120f0307050318030c010b0411090a0302060306030a020d0b0f010b04030503180103091203 78
    0xd1255200708111500314002140103284d00346642a04100c04072852400c2c44900c4c044513256920aa00420f0114071045081464402c04e00601a4580480020380700041c500b45020700008030403a801e508004001a11007545450303002000080c00c0c0c05013108040d9038640184d03905800341c00209074420b1046002c8140220b10500031503040c0e400560318046002d1810050001420014082022034000d12080302a2600e5500045405400f401d001003266850310946070700301a000e128803841214100200201d2052120440e900b00c5864134104d0340c0c81d5102284c2000c070303a03d2010140c03240c1c000010764a200d502e054114498040741181c0c204031120304424004498403174810041e80200380c0e007030300b00050316101c0c5c061a40944090203039100c1070b0b01503001034403d4564010480b04080e4490a0001024084160b5409000e141c00090301d01400c0d81c4881d0758034082c01200b020300405800c1d09403101c0c0d209130041d040da164400c1d02c9509072507150b8005805410a1100203551401440076800d02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 281678426 1250 281677176 281677181
    0x50111040e0c0c1b0423010315200705010b0a1503050601050319050c041a030405071d0a0b03190503091905010507020105341e031d010c1b0602010f 65
    0x3d03014110b00900c40b07001c2c00c00302070326030300c02c140040c540c41540c480104040c03020401c10881d964206681d006025070551810300c85034070b00152807801892415031104d0650008000301d0343c101546406050300c5507114030b401c60240045c0b0125a40144d8240000a04000d581c91700c15000c100c19107050000f666044011100d41c001261a01002243c0c42048c40c980021548041e80184000e61910300e000d40750007449403c892508691036005600204000070f0220902183d00a402c40c00002c000c5c3c80e1b40440c0200340c115024000c103030410360351840318115035010402d2044050724059074a1107110242402502c03074004c0c62410707008510302c00d8055107051200d84a076040d01d00503141c4904201c2d0075001110707140c02c12044101c05210321401c0303051044940144500f43d44103602c00618058803071408641403200049a08020b0400030b10240010350407507045004124107403284003004026000484400106174030141c000324000c3e040900d101c000f40c1c0400d0503919150000e0058040c40340380c5004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 281679676 1250 281678426 281678437
    0x102060708010b07060b0a0f140301052a0903010c050d05060d0506071d0a0806161b080705010b1206100e150906150307091a03040b061507050111040e0c 67
    0x24007010050020102c0e50016016003405400d00007106103c550101c0e10700d51440e0000a881003240408011f409081c2624101c43c100603002840582000856049800e100511070010301c03071001c090340f10107003452060f10300c40713131005000b402820b901d400054025405460000c0005040c0f4000486600b002c07904486003079030010081c15940d0f41c01d0390466807415241001c10200d4194120803a0326903c040100d0040c0210030080c08040c20110b00b070103801d0070700002c40c01c180552080c040381c90700500f140d0015515004200665183d01230716007280101812155158006140d2401c1c45058000082840c03140203070340c103443c030b030207441c0c103000310006000703c4180c10340c4d03079828000003414100381a107035410040180c5041000c10400b00b00c2d20f900e41084641c000000d8502804108441c078400040c2301c8030a0100f4403078a541031a444525913044000c08080c02184022410201d01c9054012160703c150400c00820031400070054409030340c0d001f4030404180b00b25940210b100c0e401e041c81200e1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 281680926 1250 281679676 281679691
    0x1806030405100507020a0c0803030a050907030809010507060212040b0601030b01020f030429040b090924040c0513090b03010b100215070504030c080d0210050606070b06150703080411010206 83
    0x141c1018545a42c00c05440010440c10460040341d182e0300010f80b1040d407440c090540b80000d03546a103000c002c520112500102010030590106000f04041140700040300c1601c1400c2c60415035a4a050802101074071801d4a9409001224410070084c0500c00b0003503130050400743c2c0c00f808402c031250300480e0303a40c40780035480443d0b800400080100c071100c1d40c28000c0c100d0783e0006502d0130241c8514100341c16081580400111040040d0503012480c080d160240d20070680302e49201c2440241e44151252a900034840780100d60f1003e040151500a205554140d102212041c0380b95898213400c0015000721000c0c0f500030342c00c10032801041e16001c448171152485990040103221089100114009c7d805414002070220400c40440421105102d2001400c494001405403e400e10340c02446e01c00310700154031659103400700744801a65114100d884481e00000011029140e0b40f0000d00c45007510408241c0d0080001000400c264121680c180303da8041d040c100b82c0c1c03c0000005a0715810100d6220 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 281682176 1250 281680926 281680933
    0x6040506071a070504030501061a040b0c0c130b0a230105030a140708010305150103080a050a110607020a0b09070e0c030a18080c011a09040210050c01111806030405 72
    0x52125080a102070306420b4098010400b100d0505084180c03014015100103000902c009403c0c001d00c1003d000e03903401400009100d202594505624025502036400340151160002800081040041000e050309200082c5034080301d60000307802600405020340c80d04d01926008400089070009450440440d0b452400c03420046200300c030045509520040c003545020395034a84c5440b00380200300c1c05c1d51158400d034880d25500c0d41141003003482c046a2800c3c2e2401072150070010710015450000b566050703161405d042d621981c06103426034621081d40100d038298820841000b52080e40001c0e1418031500800ca64000c503151804400c5e2940b2490141c8a200344110740031800c2a1410301c01103504c000d01240010b00e41b035201d407501d03190300d10303113041524003000200d041e04224500f0312448036a00b2220b0501503c3d50705200114030703004001440a84154140740300822118020002c0b2028000940c0007006200e20300e90103446a5084181e81d044100300e6901c000c5130b0340c02e03d00112406540c000f80207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 281683426 1250 281682176 281682179
    0x4020a031115120a0e1b040c1b080912070308030f070504080610080d022d12030a090c0906080604021216080a1401110403030825020a170301050604 65
    0x151141c007284034a00d80e400004002a030460000544080c001405050a4005450808401550503191403180440c031940100020103041064850401d007154400e98000c14284440c81d0292000e04e944440d1401980418803110104038881c03006140214085030b100744021034184546d581c0e0319090000a00e0940108085504102001c081c1c0d94002c4c030900d8014901500e4030992410100d0994440d0250201d000e0705110742074007803040395207100586c40140350054003001d4007000500300d408043d0018000d140746101c034007000c0c00454140c020089000350b072400d003010101300428907040c090b20100c07c810070105843c1c50b18029901200e9000d40101145c1d1290340070070540d08036140b00900603104402c11030448182c0c00004c1e1004045040c003074000002d45042501c00f25070102ca103003405034500b5500001d04068001900d0640344c15160100050381e4501a0416002c251140d2406407428041c2070442e080d4000358100c0194400d80f00251000110b450b09142e0340802c0c090580c1c04130b0b05000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 281684676 1250 281683426 281683433
    0x20a0e18161404050604060f03050f0c1e0702030601030317090a080a030216150209040f0b0a1a04080109120f142b050c0702100503090d0c060b0901151704020a03 71
    0x10000c0c0e4502c4034100140340a80d40c0c2c002803103e5005a12a50105280802c2004440c0d0503200307907503205500c917412038400d00c0d08200c2100540318005290b4010110341600e40c00e10702065055802c0c450340a0126000c5584908010b000c0f200d89440d100703000540400054032040c40410014655680240c80500b028058041600650080b21164424950001c0d11602040000d0728003a081c0c9002c0800590300c00020b0148021703103170380b054400d16090510001c0030042d2540350340801155100b008080440c9800861001d070b034429a40110460b6080450010034085052002e21001350a44c40b13100f10702d101c030041035580310211045c2800c0c070a024030019002c000301304108201c21085030907019000d00c00300046030071500c040d10b0706010014042061011403c00341c41c034010751034a9081403400e615050840c155100180d1081e14100411170480b081003110581144100301001800c400392981c403000642c0c46500e001011100080042e0f03240f03255944141c100c4e90080d500039240590003411a00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 281685926 1250 281684676 281684687
    0x2030a02030d05060102031c060503010e070f06050a11060901020415030e150901091a0105152b11180102010605010c03020a02040903051204030e010801060f1d01020c0301020a0e1816 80
    0xb1304d0503055001c01c00c9008008680d00e214400c0100600400240f01d6013084149800c554840180718080e601c030302010301043c0e00300c282c2c1d00201d41d06454440d6031901306000440380122151070310351491040784280b0910710410340152080d00d0700c901c45402e2403408440103e007503441c80c0c03120740200d41000e0200b001118010904941c0071000d40000700c0e440c0090b41e1816070724444c008401710820810301c0103102503e030003030190340c0700d0a2890085040c020002c5602c9584203910b00c00300c1a05045210a02142040c0c0c1c000740450514895510b0712190000700300040c0d40700b020b003c0740c010751074600c0106007580200c1c16244460b40581c000d00c0484084d609001c01006500020381c00e000051000d0040d40c41c0c0c00c0651441544a6560340b4412006c03400050f0519406811000c20b200c1208412080540d1101d00d10602a40d142003422130842c0600050b820a100c1c09030f00d40e01540009001d503002c0d41c20601180250000341d0703808c03100ea112910b8000009800b42d4164000b81c1c0c010210043c9a8800d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 281687176 1250 281685926 281685931
    0x11116110f060304060f0b06040305060105100201060b031302030a06020a030c090f0605070b04020f0405040f03021515060a090905181902010519090807030f110907021e0c12061602030a02030d05 85
    0xa1b000000c440201c0c1e0001411034105030700c1103e0320b031300100050006051102c1c2c080241e0007540001e020341c500340030300740019020040c002000e0100c141c030507000303560b81000b800c0162900214119035801c0302643c000c0150500e4103104001c1500c1040c00182d03d80060031040482e2000c0c3c0e241c600304802a5900ea40b008005001039034850516025a500c0e030703542d0b1188a009510a002d008603290440c50081d0030041c2214010341e0303881031802006030308880c11010380074a4404888950f0b4454541da015140c0b00001c1c0c0084c0c003024681820005a02044001403064540e03103030480d4440c80180c6140e4108060b681002400501c040c89501e0241e000301c0d16011076400d65040501c2080c5e00d900c8414a07150003644240e503c1e01800038194203001b041d408a455003a015030300c1d95001e14001e0400307962910016140045250003003000703403118400b84002c89074144020b0482801f458a0000941e4481d03040c3c0e84e0140e140d05140580078214000012250140280d8000e5414610b00103801401130000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 281688426 1250 281687176 281687201
    0x30c0d03020c0d020402120a02040302012c06030402040e10050a060f0f0608180105070e0909010507090302091b030a090c150909051902130e01081203011403011116110f06030406 78
    0x30b1001f041a50341e19042e4a00c24201c0d00340050b103e620b103000040140d80b680c0b0740d18a41f60502260710070080350241c00385660807000e840c0700340e0304d46880c404540103041c50030018000d80601c40c1a105d0b0881644c06ca5030040710465804c0c05242c2d10741c2840b2080d4040c501c10034000203022041003103a40c1c05100c1a95106d00e016030b00302e400716802283d450a48000f280c0100006500041c900071034a0690211900214134500803c0603180441e4050041c2d01140406889000c003040000c601000303100d40150024020386020b500da00380618600b010340301c0c90744100c0c3c41d54522580410085880c642e619582003065650602c034920b440d10603001004051304c401c0c0541d00360480035291000758002040c00210740c6031103004d0780d4035017429500e015006070000c000319000a08804041c00070782065906403484e061a1041400c0c56000003401030040110644607910040781c0074004a83d000c42c20611107008900b2081c0000d140c008110032485500a800da0200d03061012134049a156882444030060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 281689676 1250 281688426 281688431
    0x112141603060b0307030207150203010509040f020a080a0c09050705031003110f060a0512060f21010b0d0c0e07020105040f0803070212030a0209040b09061f0e0402030a0b030c0d03020c0d0204 84
    0x44881d0f00382c205604c1182d400780860b40002d0b510040280f4140c000c40d12603000c550031030455040c403002035941c14010b4000743c02d00716000b61450035543c54035841e038002c02042085945c86e11991401c4400703411a88202e0707050914000005d9120340c020360489104443da070f4800c0700f145082d5541c4a05503110403d15030b070440e43d6082541c106440d204003e01841b241070304c03190f032155445042d008560400416035030065444150300042920b803031444007803102c0748889000c480040d213600e0720300402e4200c807229841440700e50b80314103010300c041910b401d0714521a01d00926a071160416801e8a1050310011f2050b200100c034003000c54a00b802568000c5058410355000301f080205035a990f40055515485066001640c01007074505807181c103020035420751302c603020740c0780c448001925510034542001e40028502808011240f04075499210150000c0c01192681080c0501c3c900400100c60800d0003485204d2588d0482d20f840d20040080c40d0340b40d07004144426240d014844440703186001203030882d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 281690926 1250 281689676 281689679
    0x4020d08031308030c2208190206071703100e0702030a080910050c0c0f0601120204020306010c050607020c01110a051e03071a0702060f010b0706090809061602011214160306 76
    0x940701002140240b80121a55843e44000e038a43c1c81b00410b40c0380c0c41003408114103030800600c000420140350035111038040012414590002c50100d00c030300000100300d0044c4110003030300c8042c40c2010b54041c5000c4a041310030182c0320020055604802d03254400564024800a14030034491042140e0241144040c1d40c4120a214082c9040d43c074160b83d0312070400b10204113600d444404002c25800c1c420220024000355240c400c800811003140080603018540000000e01c040e4080c2409c1d88620303501504850740d600c0d10800003910b404e0440b000500242043c0d825000d66040020751070380c3e082c7c2041c080c0c40901903070704610300e07660850f0300801034500043c040100401d1807100b03107661100c12100da80740b95182010000741071840040028408030902e900511146000e8000d0b100c0350b5600200008224140d402c140d4124080c00303010ba03502440c00113885503800345032108008200d2003a2510008105401145016122080b40c040000003905c00081c202c036010f0509580740100130b040004866 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 281692176 1250 281690926 281690933
    0x3071e0905090c09461a0c0a060f060911090d1b0608160c230a06091103010507020d05120618010815010801140a020d06170d080f04020d080313 63
    0x904001803090b030f40360803448002c00c091001810008582250003001803244806002c0d03a03095034041c5c007603046c21626003c03081c200f0014003000c440c003907a414800c5074041d0b035945c61700e10050503405402c42c14950804c41c2c00601420a0b00400c8016260404035a0811117040d09002c8031100114050300c1418250314074450341c03060321140c14094500703965444200d2030180c0d03644920200c001c04400821804101410216040e890711251081942142002c8490080021480c1c8081202e0181c03080b46021244020404e482c0006044050190028446603840718020ba8841c5104000c0d1b501180007040ba12800403e106001984440000c14207249420042621074603000240c0000480c1c0d0b229800c4160f11040740005180100414402803003000c1055420042c0d902c00600071200c1980c0103d220701e90403c580c1c20801c09031004c01d2102c903240f070080c1d20140c2d0f14108680307000e011032481c6022801486810014034440c91300074180130060f101c19500d103801544010000d0307007803102200801c0c001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 281693426 1250 281692176 281692189
    0x20a0902030c18030a0c120501021e1206100e21010908032403120903190501020409060e0f1302060f07030804030e041401050402130807090203071e0905090c09 70
    0x300444610301d92100001c90380044041c1640d540a4845c1d07100005d01c3c0001540760b0301c401d00790382c944180504841d501d450010b000e1b00640c820000541c0320602843c2221400c040501490b134403400070128141c030340c442841006400d2407082c41c009840b40c0c1021440b400c0510320f4160111030019910610b4107000095400c5130550305080310640f00c0001400302030186030001c149031000c0788244030482240c09000a644030101d0351402c61208010480895a90302031041210340f0084c1880c0c1c0c001e990882ca4241e000354010300030812814075100011841c4440130391481d10030f8503641c0384c0e620240c480013117640841c1c1d120b100403a03005404114000a000e40c0002800c451031007900c900425007000d1401400300f4800020b424048d0745412000c01580c40c040201504442c0143c400603600d5242d8111100c150f4004e0308500018401c5500028188a46a00540c2b08003000e544009104010180e0008602041540003000078241c2d1000e1103d880c0210060f5080b1614044d22840c000c0d101c0082000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 281694676 1250 281693426 281693431
    0x227040c1409160c03110d0314100305210906070c05010201050c07120c0302070f0e100b040501050301210605040f05100209100c060e150103030201111213020a090203 73
    0x40310031110310200000c0c500c060740040300d810100c1d5801098600000c1c8148481d451035442e80400c10030046840c107250050303001c10080c0146034240c0e01040d40c4100058060100303494501031880002000807d00024240c800c030030340f0b0b032103000340c00b07411401a00c00f00c0c214021350200103507035000c000b21141d640e030b100001d001840c4101c4007140d007103180000183c00c540c4d00502000f6211030800080c00014a0784415001c07441543c00c080d90500c2c2c960074201d14149960f00241020101c41d08049070412040c88003d215107102061555180d03113691480103240110b22805022800c140018400c209024500007901c48102d0ba20380d401d038006860b0f1006480f010b581c260381e0101c0404440040c0b0209000c482004092500d041d850081c12502203004004900e109804010380212a2810820540c001d0000e00c92600201d801d0080c8015000c0c061034004c1c4021000b540c80e115440400b10305142c29942c02d02440e01032851a0360301d1442c12920840c42d608100d80c052040315001c60036410b644081d50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 281695926 1250 281694676 281694683
    0xe0105010312020609030306010909020a030e03160b13032120121f091e0e06010e010e010305060610050c0a05010f0b03030f0306010c05070e01080d09150c022704 71
    0x100030902d448019082c1840a4281e191a41041003041110303600210075404685040ba80107135103001c121821001444180c11004030b03030000190021401c140285248492401410000c200c0c0d04c8030810545410444440200802c00403559464000f000e005036881c10b50049401103004520950b008040c0c035020000e100310342c030000c02d14003414442c50344120b5014002ca04050b0344a03030310102e0441060060301c1400d0f001616403480454160f070040940c2070411015030144035404c8100a500d444d04000d0040e000369412480000449400c80c41c190b6041b01c2d0804050021520340c06c0a219411222030180802e00c40200700000f0440010800681a103028070000540c41915580b80e0081d0b03050340003a01d03c00d9000340701d81100c095221044a4101609081a41a00045280040c00d0140a9014480d520000b6000242a00703011800c1101e2458941d00e02e00c0c3c0c55243da100454119821083c0400692410440001800c042611580d8095646e0840c5d50401030b0034060f0580080468045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 281697176 1250 281695926 281695943
    0xa0e0f0706051201050409020d020909010908030f061005030f0112111801060801080a0b011415030906010302030c01081302220606050904060602070b031308040b0304050105060f030d050d0f0e01050103 88
    0x10000c0f0302e145445107001d020110341c00d0002003071580006920042c0c2e04c0c006403107030b510440400c800c55401d5104c022010f910140c03060700ca00d05010b01d2a0b0f569011a08540211206803c0f480d41a105070300726481854144c02504240c1d0030078118140c59500c1c188100c0b1100803000000d0741699881e04c195001c001c510440c5202c0b981010307001020000181c0c0401d0855000d0002c1d0800500f420b140103040d5186012136180b4109041c0020304041c541c2c14040741c0346400007003481080c440c0822054140c034020b0b0222100400440c0045824080c1218000e07152003604641c00c0051820101d2107004500e445204102c0d21600160903046480301da102d400850800030301c44101d41000e0260b14014140c2d8000f4040003407038005600c40d940b0005210380c0c48842521004410401140c0c10b4501500041e030600781c0324070300351405a000b00016511035104a84595051545107400143d8002c01d45069a80c00d0811180100a00c0605410804514800c2d00d41d040c02071048424072540703000754000c9011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 281698426 1250 281697176 281697187
    0x40c09020c0307050c01050901020a08030901021303030207150801030c03020d0501090c0f0311100212031003151d060108120c070905071823060a180f0503120705060a0e0f070605 78
    0x4e00d00d06046228564180202401100c00301c0c0e03000315003480b0360f0b90048142e554950751002594024407130b0701c1d803c0141c0501c2c068044141344d8000340120658162217040241240c240100740c400b41d0092000505452010318144010b06200750b40035412440303030001040ea4041555036a00f81c10040d04030400c02c0d5040c0b8020001e1107015084410340c29804d4550b0200f460f6019402510b54100c0d8004050154000000c149002c1c401e411601c015900000c0c4921440d46048155000c0c16285007032111480c1a020308100044000c1070f924100c7e2601c400070941c134000c600341d00c02c107500b20840008180c06420030010700d0886e1405054803402c01c07555040010250032042c2a4070710303030340c0d00a0080a002ca90030f243c10b0500110243c2d440610032203040f03131160720034030341150501e03040340301400d500e01003203400561801d11400e41d0003555821400c0d240004041c1850907400c0c05040009061a48500c01081c025800f9500411386500d50f28180c03030680340d910f4009032808040d5400f040004000245 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 281699676 1250 281698426 281698433
    0x103090b0123010305040c03111507080406030507050c0a06110c03181903050a03080a09050d080907052409040204080d02030c060a0501060e2209030e091b070803040c09020c0307 78
    0x484600b201c1c42401c04000078200394070380141c000018000100b003d4181c0300c4245160340c81c103c60654004128508644d5082c20340340c000d03c41e401c14800c0002081c14680880e01041c0680242c640c1864400c00521f03003002c41e40c03252009402e0801240000080130450f1040d546800d10042a08944441c8401c00481120050008034600c1280b00000560f1089003400064008600e40580503098a0080b500791118000d0a0040450038070090640c45240c1190380b010340c000e00c1c080d115002c000140c903400c5641e0b00038031051354001c84a0004081280d00b042081e0310f4030704081e2240000c082c00040c10941c07a00000c81c649419500d035007016a01c00f09040c605d048040101c030307034030142c0d40005014a51401001a1040724080380c014812010440342d03402e00300041000e000105001d41060241c003180d070401400f90315120719024000e40d4147d000920704bc0c0048140c0354040078403c1e900d46040c80b0341d1160011604060070440d015801d444002840d55417900240041241c2d1002840d031b1461a40f5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 281700926 1250 281699676 281699729
    0x2210903101514060a0507031404141201110d111308100501120c0902160611040905100503061906050303070b090115050603060d02011b06090312021c02090103090b01 73
    0x1803180c804083e40c020a40b04544620080ea2040342550070200c0e260102880c0c00e03070781c600c08020442004000481d00054910b00751844101c084000d9446000404981c56418281d900604800500003810806000c0c845c0560f48503148c595440503007103040c005000104418400c45501482c020780c40804482c840384224410305004181c00d00c0707c0800300c00c2a5403182d0501009104800700154049401c105414521040c0404d4940c009010802da1120010381445070300540030f14103100b45403900207010700c126101490103441c0003c0080a407903407600c07250b0b00c0864041a003520380c9a221840011a520f0810207480804d114140045d06483c05808040c00c40b01e0081a007021813074012402c01c81c0c3d4551808803500010155644130303ca14503400180c58040c0c2038507607545884403241044092102d00d900c0405268402c1d07079000007410031201603209034007640580c00e1141e4081e00c1c0398001998698010105030f0302c18100400d02d04c007143c482d250480002d0b84501548601028103500910400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 281702176 1250 281700926 281700929
    0x7050616020f0c0117040602090406030803011a132d1211030d0f050c07080f0a06051e0106030903030f02030411091e06060c1e03090a05060703022109031015 69
    0x142d00811000c200c40000038480200305070380c0f2028154400125043c009107804070790118a024205004540c0d9a02d44896940d20921602c4070040c4083c0312154002e00803411201c0c0f10040c3e00031807500702d043c1510340c481c2490041145020503600c4502840703c4003548501c5000701080f101006106c2d08c0750500290500084ca04140709812103a890000315800c0360300041d07079114070300c0c01e070383c981071403010b228980009504003a0700c074420050050005000042c040e840c4a1180905100c01d844072030102c141c03510b40c6480170951191810060007031030311980c001c9040c00c1c0285404a40d041014080004980c002d40301514481c2c5042456801401c3c250034881c0c000c01500d44040b8403008890301c1c0440a04003400d103911a20001070101c1680b1010000740c40c0c500e10a801d50980002d10314412607aa500c101c3c0c04c030307000710300360040040c6c02c1c0b801c00292145d81c0d4144d0060220440c2c401031501a501c040900d40c070541e1014803e1044544040200c50b10341e0141800006415a03400d5411400b0300d0b4a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 281703426 1250 281702176 281702203
    0xf030601030f02090a11030a09060e1603021806030601090e03070b070c0c0609050d080906090603010b0403050f0a0f080c150106120f1109060a0c061a040b041b0e03030705061602 78
    0x5020341c00b0041b460b100704581d8800300c5c501000a100031b8901e400c6d00a0160b10098803000c1c803841c11440c5503030721507100d50001c40e40b085030742d20441c04003100040b00f0048103c1e00b00e130381030f00702d40010410443c07242c02500d522400007059a1030920203948801e2401750035a252000103900e9552242042421141d0102814040c14021099442d040015504911341c08000306241c03004920251a40c54a03026210140d500804983e144d40c0c4407003220300070390030034441940c41d4803454681003034180300811415442d542007003d0300c143d05501d0b00c2d40c0405600c4248107441e03e200e0f545156812051640b25907020f01181e90b50240c01c80202c00ca42000d42d0450848540319502c0c00d048a2103030242802120140b69050f2a0551500101c91040e900003a004001030241401c1110704250140c1d0501440514001140e003081800824001e00045070001079409015030480280300e5140c034007c11a8a4000c100101100c0ca030102c940d641314201003064503245549113154840001340c54043c030400218010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 281704676 1250 281703426 281703431
    0x3071404090b19031e02011e0f021c1704080c0a03020303160905031903021603050d0909140606130305150a0506010c080d050604060815060118050a05040b0f030601030f02090a 77
    0x9544444180c1c11001d102c8014220405c4403200459008810360600c0c0c2c1c50317148100b814444000d00c0a0041c104091820005000e552140000304038840f61a14002d4055621070040103450b04c5406c84001c0050015501e5000600c0042c518803010030a401e1010300c240d0240d512410702d645044142c0c00c1d1403a110f010310222440074001e50320300041015030704040050f1184e46081e81c2c00d0a90505c220400740c0140205502808824050005410440b0009641da00502a965540460308036500c01603521010403189002c50003918201019080b420701c00c245186001c0e90303941e100d81c5000464944a03c0c0e042650041000b9600944030385a400341080c02c1c645001d28903a42e40014a06c01c034801d440b1915510000b1906a89a90b071000c00a09041070489040280d054a05062a801121803500040c540c0c0b241404030500301148034100c0d42e0140c0300385480c1e401c00013040050301b8030400d1160001c0781c405483e0302f5a6030410050780203600800380d4003c05412401408480d0100a100052490 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 281705926 1250 281704676 281704679
    0xa080109030306030c121703131b0302180702060402010e04180b01030506101d0702070308072f06040302090903130308271008091213060201050a0b01021203071404090b19 75
    0xd40221078440d09000b422401623680d0f58114a81001802112028102c2100c0d0145618004000c5085500750382c001c07903110b40d400b1a00040d004000208413902801038001c0d402180040d40a400e90024010380108003055106640c9560080405401c109031541401c0000420030300c1424081d15820850744001808003034100440108580d200242800c10380c1c0d28440002c51711032013030160002441c3d1084020303683d13000030300349039400c4030855039400f00c604016141d081a01000c1c54815100740e101900d4a82042d14580820600d80300040122030a0302040100006c50744e40e03001d0110243d4800e40c900b82d2920300d188500d801d80302081d10092440307442e1100800c9141c0c2c409010850380720003803505007010b60f41d50040c41d060102c1e411a4035240071002c169210100c400c10010000e0380c05544c020010307030380c0d17034007400064a901b2001640903800803102e4004c0207010100456008119003043c5131b035459074441c041c540d94040c1c3e000c0010280d9520040500e0304c1d0605800007960101c1240d00b0115 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 281707176 1250 281705926 281705933
    0x915122f03092109030303070e0306100e13080c0d0315210816021005091801030c260a030302131e26032a060403090902090a080109030306030c12 64
    0x421026107224001154030f101c03101c20481440c200d0f0407a0601605036500c074280b0540240258581d111554440d00038100041c1c00e440b00b401e48072084400d9400c01e800d00e0b0701d0381024101c407921040c8041d9104e95080014010b42da00404c00e1501d80f42c2107a400244103281c4800c0c81c80d211a4079045103101c0100421881e030249003c02341141076a80011201d0f5035002c400110b00502408000000c2d003107440c1004018119030804041c041c1d40001340c1e21103010b10143c0200308010002400001c5c40c0c034006050600404c250785c2c0b00304a2611421203001d02041d51907800034a00a601181100001d800244500078285c02c102d040000b45540051040210600d90604507001503600a8510b41e0f103610002c0000980520240301004d8201d9003a80d5a841d49030b0340e56600b0507a8503040300c00c01d015180c2500301800001500e03502c9950180e8804590600308220380019511454500c2e40c055002c0c0345c0440c8810b820701c0f51441c00c3e07100b9100010110b2031031034072407003001043d88140d80c110f03807018020020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 281708426 1250 281707176 281707183
    0x30717070225030213050f010b040509041e0807080a090f05060d05070201020d090b04060501050d08071b0302041a090601030b0a03020f04110310090506030703030915122f0309 77
    0x4610207102c1c580b00400d14030050703002c0c40895001941c4103040b000e002040b11030940c810780c0514030011018201f130382c80b4481c0f5a158442c3e40305d8103030040b26a00000b4003098204c3c0381180c0111200c0c0507400042e80a480c2c090080d0031103503054406000000e480e00394141c0080d05500140605004d50f01114034103c0050100c0c02110301c00342c41d00d0303200c4001410140c400c1d03044036000c00c2e00035030030840784c3c403c0d041050004404481c00c0320403515020010401c0d280c901000b000c1c0c0e56118240626046556a540300c000d0014150000d614106030350100c01030f0342c0c600071410042e07036920180f05800d42c0102000015800503288506044c60403041c1606034869005400c01d41780c0603580400c04c1000c001c0850024103200c50302d414001c0c000b0007070000c2c06821b00680382c11241040028003268464004054494610340310040200308603210130802c41845952020740c529140c00c00c1d4007a889210381800030741c1d1008100d03103000c0e0848004510340d00800882c4442505d80c0b6043c0508515000b50039a81d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 281709676 1250 281708426 281708443
    0x6021903141017071e09110f0f0f1207080403180e01090b0f060a090816050d110d05010c030e10050903040e10120803010f0504021602010e041404080307170702 70
    0x71503546107449120800c41000024003c00c00d1140b42094410391382d031000c00b40c1040c1d02501e815507003406107080c16411001c00b503074001d428071118140b42806003e2101140d502004200c2c03450281400000369454101d2f401c0c0c4d11950098846624a103454600200000d40b40c488545003a034083d01c051107043d40d6401c0d078074190fa59002c4001183d00030280001c00324110326903400d1340490005051401c540d403115078902211802c00450b051200303c01c6105444403880d00402d60048050300341317000440c110100c001c040c03800280c51030781e01f26642e86a0a007502c890003e6200801c0e1200000d10740381808000200e040b40381c1076800c01943c00d00b06101912407080c2d01c10002e525442801080d16040e08515010003005800b01545852940c2d02c0d180e1125042442490202110180002500e0520b4004c403010b0180f2801e00701c0507001d580d8015608564201841c0d908650358041c10081418400d00c0342c4d0085003d20501038991500b180e00400d208250040c00c1d580c0f110300801d10070b80a800248654 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 281710926 1250 281709676 281709689
    0x603060506064902040905090a110609041d160902160f050f07090e06070f021f0b04060e060f030d020d0f2307030f05030106140306030a060219031410 66
    0x9014200308020a2030400000040c0740c080c0f40500360046011842e4000c00448090300428040b5a41d81c1c16581d8a0310140d800242075245882c0104550f464004d00505046200420009040b220581480c030002e007244601d83d1158018040000011081e10b4010300a0809440640c5000c024074071340a840c160311640104420017050b91407040100a2100840502801040f1001646d54020070300241042c182c2c00c0d101d0307000700004141c490340726801010040c40241c00900c1d80120010100d96a44400f0711003112403666840c46840703581c1c031030180310014401c1405004903410b024080054440f49506002e210b6840358121403070306500400c0444160a9904103625540804202a1071260180d00d40300b0070844400710903144641034102824009000e640c0388000079410301c4060f22188800c1c06000c001c50b0200b031010812070781840056510180180c1501c40741205503407074030140e030130021480d003031418404642c20015505100781103074036180501a011034188280c040384c0e00d599900554 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 281712176 1250 281710926 281710987
    0xf300717040c030602071b120b0705030702010e071205120403022d0d06061403011a06070606050306100e09010605010c0303050402060c15061005130504020a020a0c09060306050606 79
    0xc1d0a00191484800003950044020742d40e4107043d2400da441c04001e00516241c40d000c0610115040304c4100c88036900e180c0c44075080c0c2450312020000d48403900010030701c204540d03c448126134201400e02201c1c00401624095100428603854403034244851400c020050910a100030400f40c0d8600e074120074131100d40c13409901d05680001c1c910449000c0d4503e12900702e101c202c01142046001c4e400031007140d460f8100c2002c8c0040c203a00301400d0700c50020280798068a0300c41c1811807441c0450041131124030580c3e0001d50305235560042800d041d0115800814072100d82002c101d44c419608c24540d1283c0010002c00180d82000006008064441c0002e02010b680d00d00090454407600211504549210100c40c40500210305a1068420840b03515000d42580110080118022010307100400051000d1250880c00c00c030038003009401c011340d0441103201c2d410009001c10184855074002d0804801d002c6a4a03003035003007103070607643c0150480d8043c0f103040180f00c0141d054040b25412544c0c40c1d0b01d05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 281713426 1250 281712176 281712181
    0x13050f030a2a0b120606071a07050c071508010618030308150d060902040c0201060f0b07020d0b0a05011e0b0a0e060f04090e060a090c0909080f300717 66
    0xd07140e4119001d0211465609902c00441c64080c4400600003442c1280003a410703e649050910801d030280000090911301140c5450101c0d0b05182161036014101d45000c5050050b50b10b03880345090590380c02417040d00c0f101011200744584c008403150160041d0700f81042500005480c82a072172400f440080c00300030241010031181c0c62810303804114608000c0982244c550541000c000074078100c0381c101d10807482c101c440c01d095801801a00d003222086440310906a00d4940702000c1e070782c00300e601240e100030b03134115000008440b100c180c4c2c02501c0c0200001810b40c1000718913207211841440140e90400102d100304070301c0b41107504a59020010389404200c894107030303021500900030801c000090100c08200451510080c1e0301c481000d00c42e131400c41f8031540350500903074211810350b41c000c0d25521000360b0601141c489134018100e014840d802c000e01e0400107440b1124260032003411a9a0400c4680030070001a1207198801c1130604890b003000042d04045401a006224a12052031603840703a500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 281714676 1250 281713426 281713463
    0x509010305031803070b0a0305071205130f1502120103050c060310140a0321032f0a05041203080f070e1011030706020703052d0901050d0b10030213050f030a 69
    0xd1700c0080c00380100d0151101d0b0700d88406406000c04641d5440014401d8010f2180b203009070103024007030b083c82482001c1103159901d0b420100721036803009a1706900e00c044030a5014090788010f0850041c0002c004640d075040d441c3c2075092054442c909403080c8014070a00c072507038040c902d8501c01c4401038501d081d075044020001c40ca1031000c44d480548201440002c40a090410003180c44160032213540400504810002002c181c0118902c0310741900282240030f122103122000510080c00903081c413030b05095603624a0908650b0050048000519800900c40903030071000d0003d03003000c21420038100410701880403880030f12204101da02080303400e5500070341a620a2003202c0341550082000c2d03595400302d007400b510b1544004240e81c01d41d0546465101d56943c00000707440c1040c101010b0314903101d8000c0046440c3e401c000f80d005c12180c0d03142d01122071581d90042d05074100c0c0c41c54801580b50107116880c1ea04010003940a24007813010100302200551b0007080d04012541c1c041c41a00c10038040300ca = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 281715926 1250 281714676 281714683
    0x20108130f060f270c0911040f03050d11030306010e061b06010b07030e0613030f14030c06040204060906081213170a0b1320040e0312010509010509010305031803 71
    0xd018007207034580b0042805054098105101d4400a03900c010075100c1c2000720025849180c4d6005007124241c09001c0c045078456401071016449030f03480c4142007948428682c4100078003640122000d610030150001c046411414000c005451200590305624000c1e0001c1c205510300340310b030340c85080d0019862800c010451000345203940d01c1401c0755031070368540200000c10b9000120540100320358440001c46442c0550407140145102004e050780d0600d180c0c1e440301c0812a491040350300fa0b101c031004a40c0403100f0030107130030f00238a0440186040c4c1410b0061004075074217a04020313003407410180d0a00c42a0000100384400c40b07054440580d8031882003070200445641504038024102c0da50003841c51140300080c3e84040980203140c8110b10344c58841241900e9001604001d1001078803110003942c1c15001c1c80342080c81180a040800e4520565841504652100710100c0c2d03d07104510043c440341c10302c81401c901405042d80c2c03ca01550540d2070f100e903240904cd881d448800c050001c01c03805500c060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 281717176 1250 281715926 281715953
    0x30605060c150415060915050a0f0b030712020711040b060406050f0306120109121103120109020a0905090a020d05060402090d1e1502071e020a090c03060e010b0307080a0902010813 79
    0xd03134003000740940b42c44083c1c0241046941c80c410102004401095600d4040030280480d4200a00c4109003845d080c0001d00703642008010030300388040069542407101407800207140c01840f48e02e0f20400e501203401081708072542c000103135010f0380080c401440740f19004800c035090040414a101c0d107950b03400340065905141e8035505016542851644000c0041c1d22030014460540394403100d40e08042e0300001a82c1c0e0040284007010040303004010016404c0c03a030b00801c2c0102080c54121030f44c6403035501103518010240c91011038241d00240c221140ca180f0b01c580c23500080121815403500900e54005240014841c5003c1c154406205181103911302d0f080c1e07074820550b07001100030010300c0d801c12510000d4110034400d0301c0c00400c19507040742c10b903403072401000b801d54000c104d005040d090141103c02081038032145400d0694411000c01d150301d505041e14024242c21108550320315040e60014070595010703003079025182c244800480141e0b00580030542c4007044030300141484a407800c0103202008403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 281718426 1250 281717176 281717213
    0x705090f04020d201e1b01050f1608040507091d060f0f0121080307050405060d060302010e010534020d0c3b09030f0a080601030605060c1504 62
    0x103002280380506410021000308884d0f101c035141001c3c01c02101c401c1c460310101c0c80b404003204080d603200c0c030b1103440600700d00207141200000006c8100e1000c0d0858a09455415690440c1d1041198091041d0000c4107500e800341341c44c90031402d155895a42e070311414011800043e8451090154140340d40a05507008800c0c20210b4140e800c1c16554010b0804059a0850704c5514190000c1a00d00c0140046a500c1408009643c0f035040b054444a0050f00b000d402032042000030400080d40d651488040d0540c8034541c074001415614500c005440c41c0310a68180381485018415503201107000940c10074020b0f0700c0c4060300080d0164a582c070310b41c0074070001d00a502603d294440410300c01d010040301c0c00e445d803a900342401030b0081c050710300740712441308541145c07038143d0819680c400008440791600102d41d41c08980c01c024101e20401012382019070b00038000360440040100d2582e160047c10014001030783c02c5403500340c1e0041007646803648080c2540d030202d228404101080b40358680308056540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 281719676 1250 281718426 281718431
    0x1060302210a241e0503030702040f02090a0308040503010f0501060c0f060b0907080f101a0d0b090c0706060b0301051302030601090f080102040f050f0906010f0c06090b07081006080705090f04 84
    0x30703e00c000780c03544050280011510384585070140a114550080d0207a0308020000c600f0010a0380c2080040d050401d14004925001d201c00311158881c0503060700910310400c802e81d1580d0812040c5400c550701c11a06031700c0c00341070a004000c62500414011005500068948200ca040d030800501600c507a1544603044080541040407455010110b0350042c4040b41c052012603c900215100903141030040c040c81c00c1004040c4100c000e84000140888129820040740c030b80720640001da50040300b2a01003400c000000344000400140f03104910141901d080c14608550400d008217219000034201c80d41600d9000011400340c1c0e008420707500092001201100d6503a4807600c50740c1c003171341161056105100c42c00da03011031185404030030400310f20b001504a03061a80c0b0203004482030201400341c241841208400384d00031841d00c0c041c00b45003c0c001c5660207107600b0328540c003c3c0b00381c80060801545040c20340d0240800755100f10003d03000800b41c41d04580300c8040800003001c0e41c02c4001c0e015401072 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 281720926 1250 281719676 281719721
    0x301060c0201020c040e100902210f070e0f070f1205040302010e070e0f0a051801020d02120c0a080c03071107030b04060c0c050309010507150c08040b01060302210a 72
    0xd40c058081038106200382d003912455540c0c1c109010507070740d0200c9a450590001940b80f40100d82c107030300ca40440c0380000c060810021140d02d4040c591900c0c1c42a004040d0442c03502d500586030304001580080c490540c00703c01d035140a803810281d42c18007a1511041201010310440f003507203d80c1041008107013401007003000b42001d250183c000c050481204140e0b00070200b00089101f01142e500d481070744c4044460b0856901c000e1000e0061000520000700007462800c1085c8403c000d2010703100904107044c0050351680782c0602c0b00d401c440c00500c02c100030f210030401d4481c0715910580048d049450055080c5d2aa121154152042194610707010007621840000000740070148006a002d180624030402c05050f000310115000004e442c1c2c0509954401c002c0119694480d0000703089803070090118a00095085070108161420b0161b1400020036660600c414000102000b50041440c1e040451822640c090307010500401c0714101081d111040d40010180b21498211140b01c18070750302140d0004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 281722176 1250 281720926 281720939
    0x509100e01030c020c0102030d0209041509051017031909050303161103031612030f02030c03090607050306030d0c020307030b100f150c0f0215190201320702010608030301 75
    0x1000094030600190500c00400c40007030020980b5042c080040e4040c51900e0503031001c0801a6100d00c0309660082d9a600c0e01c4990b0880201c0d03488050081004042180d0400502c5180c03000001e0308919007041440e1000e2068010020072503404c10780d0000648a4507007c0003054071080c0e41070f80000c0d014040082c0300300c080505645040c000d1842004280d030210315580078035a49004144080302c122905649910101d101e4010144481480d890701055000d20359240070181e80040c0c0d2141140c080c04414096009000d00099510030103621f0b1041c154646000040d981d0310b00b01d6020010f0012001441c000e5490500c0440d01554114446030316600b0700410020411082e4498042407140700d15010400c1c844211030311a8401042c0d481c2501860991203001d403040121400700d80c450400b021034601c95030340340003404428002c4240f60410340ea08100107800c0da894542102c1000c10550540858a03000041c106d03100031010402c40050760314894142e0043c4610381001420780300110002405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 281723426 1250 281722176 281722187
    0x12041502010e070305030703200d0504050f0f090604021e030f0906011e03080d09170c1005061e0d061a011710050f0112020c0304030c0e09030409020a050910 69
    0x10650a5000b00140311070410016207440e43c600004103150402c104c40f4000ca445440d184100d0192500d03403001c0c814900e0441840c102c8925156004180c01190401007460702140741003c00d5001d9607a6450b403040400012410300006104e24412036010441e9800844543c0c081c90340d8801c0c41c40301544e00e00786444100e00c031441c1102c51103001c0c855140003254000e000301c034691044080840c4140f0f0780d8215560081141c000074403255056540780c1d00c6d200411100c19001000600e03a0794241d90702c00101e1001e6080520400034119001d003008103100303041e1960f2240f000711400e45020352400b08100c0d030005510403012100903109900b46500d0b01a20324820030f2421200009881d810105110640030034070020b004c640c00350000d4883e040400040c00c004d10b56502021052501d140303411904011070003240c010806d4040507074400b06042c4204614150004007034a80c0398407440c5540b81203410705544e88100c0c02548011500410b05525450282041d00c1440d40d006100c860220903050000b440d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 281724676 1250 281723426 281723459
    0x1030c0206063a0c0e06030d02030f07330c030e03040909170d0623100e030f0a05070503010b0d02090c090103061d0610030501140909031e07030f090b030a05091204 72
    0x100c0d120345d0000c100b4500e80060880a202819006141080322114120681e5006040251100140c00030f411640350082d800b00c40c003090241e00110458980c850b48402100c0c000c2450070203062034124400c80805000040d1006c8031402e0300042520f60083c41c10706440740b44905002e2001c903020462502080c02a044682510840221002c4000e40c4145503020440d0017081c0f241c0086051f0450303d40c0522681000c510202c010701102d950a1803036001611742009040191015048064240304c2c0345000c0c00f42142041048131070580100b103540005002c900d0150650280d00000a20380c056a4000e070024001881c0018003540341d80403c10803845082c90496900f84101d44e034140020200b4000d20545040e100400719500500501c08240042c00c64060000c015034030050080c1e0001c0b03410310801c2c03100008960f41c410703200c0c0d82d030b450040c1c80c0703131098003450051003901d842c140600041c60007035980c030020030b4401043c10f07245c00346481d09241d0514610241c40703000150100300c1c21000244c0c041b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 281725926 1250 281724676 281724689
    0xc0a1202010e061e0702010b031204060306050a0515030702010605040f06210519051e07060f0309080d0c03090f03020705210604020111070f060e01030c0206063a0c 72
    0x2c0714045103203080c1d031201d4048038081440550781c1610200803400d000019400025400009448858400000d280c03400902480090002c005802e10455901d401064010441500c007500e105042c58000f03402003014915144401e0301c08030005a0051007500504001c18001d0f004000010214101c10041d007084d0040310004001c170708544c0c402c42c0200d0b1424003ea80c00c83e001e4101e1145d08405101c1101080c1000c3d2158480c444002221200201080c9040d071010710090007074919180004e4600f6009440800c1410310f88207401c40851000e800b00c03100c0c458251400240031030a82030540040c24403050291280003543c501c0030425800103582003d9a10840f6041e4469030f54941d1100400f00124100146030407a0340400c0055010340300403c00101000f0070394038601d44039120241c80104960101c0001000d6000040131945c02d0b101d40e55009040744040c119034038020010910003400ca144551801000c0c00a07052901e01746072844129a540d0710500003003e4007400c0c1201c0d000168000c08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 281727176 1250 281725926 281725931
    0x503040e0f040507170309060d050115022a0a0806090f06130503070209070905060f03010302101e0c06020f12100e01060c03050d0605040615020d08010b0409050a020c0a120201 77
    0x101ca581c1c510044a104a5029000340009401c00080c18008190100760701900e02c8144682240e550350030000d00914010404001030662520071403010781d40101e034280c81550000b440000f41c420329011a40000c6078902c181e5008070180001060880381c8580c41180039003d040244010200003082103028002c40344126046611602c0f00965401c2150b90b00505690040022600606100f00c03900c0d80402d04d4200002800e6462022030b140e68040361042082d40b03070003c01402140342c03003c03000c409c2c5a030b0792401038500c4204023150002d004c020314a00062101c050003034010402140c04a0314100402c0c0551616541034800c00e00c410b000c10794100b8000c1011200100c0d0064448400504803105590382d071001980c1c58909031469417140001c01c02e0b082c2c8800000c81d454480703009413801040100a60500030f031080200070300384007003017410f441044091401045902074501c19a403d4610713802e00001c450b211408510024031650404507618007403820390200f4008080b5860700184082d070001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 281728426 1250 281727176 281727181
    0xc1e0f010206060a030b0a02070206300f0105060d151d091b090a0b030703080d0e0610140f0d050d08010b0310090b03010213180b040e0307020d0219030503040e 70
    0x5a80341c8400f100d10b10f1300620040000c0005c03540e41c00d60345800c08140c032401864510950040307a01c41e40000c5070580c5038a038070440c01c2c034004d1180c0896440c042801e50381d14034a0620440340780c1c05880c184034091059002040080d0407500b48e90000034600741254074921000d81d503074044000380704000400128068041c000070003510002c260610b00e0204002c0b40d000c4a40c00900b000711860000c3c0459004566035900303000c458031700b0031a02002d14010500f00f6215401120703540140c0e00300180c03034260ba0b00000b0a11080c5040c20303517210241d503180f40014a004244a012812005180e601c103035103c0e1420200ca401d110011408040103001c0da5504ca2042e82c07120b50250b0144410703211100d050417110401c01030601140c0c00001e0350b400042c00949800c81d842e00b038082d1005141c03c807201103081c10720034011800140c803d04003282d0081e41c043c0840c0312150451a16400344680c080d004a101049c008110342c0d4090009003019080384404030f403e5100d040140c3d0740d4009021784d040c8400444003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 281729676 1250 281728426 281728429
    0xf0603060509151905100e090319030b09010e0a02130b0403030807050703140304020a03051005100f12111f03020304060b01080f0718050301110705010f1e0c020c1e0f 73
    0x20300e445040d010713550403043c001c40048440144030082c8513403110300b00c00401042c88509042203d0051494074011500d4105640c0c8104008010681d0f000c00c0c180b5011070f030b84540c2c5600401d141140e40201000c2d40555900010340068420300c00d40309614145950045030382100c8030080d00c103032802035031808415918544180c800740300d02040500441d0307a65110712000382c0b00500540d4030902c060300501219541e5500c0c1c0d0f18143d00c030900d1881154862003080000500340f0040c600811503040a030107030300e290449280200c1d04049000d0040d50b4038581105484c1c903154203061045803000d268004541000c003000b07009420641f01100c56a040405000b072544c81000c11074000e4030f05a40c0c410968684842c03e492402c3c1a850f0f02070040c42c10640026542c5c0c0c284900700079118486000c0790703201e0403131825600b1901c2c00072801c482c561601c0404800c0c08a11070700e080310a581003d00113402022880c007a8902850711518540c00222003844551880c540c0121041020003030743c422000e40707041130 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 281730926 1250 281729676 281729713
    0x31207110d080f090612090607020c040606120f02070813090f14070e0409060e1e0726030c01020d230408090f0a03080703050c15060607020d060f0603060509 69
    0x1c015000030070030300c0030950400a01c4010000480700400300343c80c00030030000102001c0001c40340035140741c1001c0208101030381c040c001c082141904941c208002424120080c00ca5070203400b030b20401540c0c40200d080141c83d0342d412a04080d40084185031158240c10003a4010140b50048030070301c3d81802503810703000c41940030306a40c00410800360307401d690fa00442101c001040701c4400e948542c0b07a540c0e01011501512071507400c1d0f200003002c3c08058a407402c00f88042036610f07024114541c400300042003490380d5403881c2d8840107004500200c3c01042541c01c985140500110401e241d4800690056805a070354054104801d00c0d02000c0810300d00c860b141c044c03000f004c45001d04021802c115030403181ca044110171081000c0140040005034403920780010703507040f200d4110082000028201420641007001d400c1700021181e00c049149002e0012400038040c281c0c000740035003101300b000e1307040000c00c1d00012008140e039403040005039a60b050100c05000d0179240c8207000d00840c85560031001d501c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 281732176 1250 281730926 281730949
    0x702071d0105040c1b060c0f09051509120609010b0a080313091e23010f0f03060207080c161e031a06010e0306070e150405090a05090c03120711 63
    0x440500241e03840c00b810300c005007148480c41000c1003100b0301e4500e40d900394071001c215401d02035000000e10307544c030751000340040110700c0f25142403044c402000c000650b5030b402685040f549030a0350942303401410f40403c60001e00700f000665540140400c22070004015030240c02c40d0602203440b0b25040390744604140d1607101c5c60302140c040d402800d6080c0030307140083e000310442c003426500241250450444003c1110701c104000d076152804d60003080c0500170310100e02809041c0c803480c44200d03140380650f40820041035200c028240c44c2c02050318070503c500d0a09644043e65000140c481c44103c8001036902c0b40e00600443c050041050080e40610b81c2c001d04503400d0b603a10000d090203580343c44510182c1104002c00e814108039640c64019260340b0103000142c010b0105407980410202604100000710182900801e48030400340010041542c1d031148a0340c1105801000007040d448485000f0f003030850340003103160180310f14444005041124002840c1c604e004c0e807061240c46001e0b008000054454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 281733426 1250 281732176 281732219
    0x3170f0f060111070801020406021605031501150c060e0f1203011503090c1a130506030403050a080711160303081f170c0901181409030406031109090f070207 69
    0x4010001c1d61550141904840d5880791030100c8240310395030340809007642d005400070001070304075000329260164034901c24409400110b01400740c00e2145180c90a4001052280c160110b10414444140c1c5000b10051010160424400d2008800303044101ea0b17118240c400f014014814917142c030f281c400c07840007960306071140d02c1d030003c03040c0c02c4044040b03016015030a0207690b601c460660000c0c40354400f00c8c1c00f40200307107030240b0306490303d40d4010f0085200000d50301950242204204100000e6403080840e212000305e404c1c00d0782103441e06030040f6241109454500b078603204010280075402d0303400c5105030440e8460764814015076524250303000050100749400341c000711441014003c016031b00141c8080910039104079000c80c0035a4000070801142a4804000000352440f030700d081c60b11074040e01c580c9070392041d400250b50034008010360781c80c45284900420142e544e00f030210306031121001c07502e07100300040898055091417216264030f0380e4180c030ba03900503114900740000c408103401c0d44500500c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 281734676 1250 281733426 281733451
    0x71b180501031e020301021c0902100f09060c050c030a030509131a041e05160e010203070224160b101205030304030513081009060606110615150703170f 67
    0x1a42070003c038202d00b4610081380c0c155000d000040808030505c00d010101c880e41c440100c1d00070030b10300501c00d260300400780d4207007003000340c0840c030880c55004043c17602105d402e46002a018072080c01c041b4240800c480040b60305010304017100c41031580c00006000c3c10f90301162403c50344d0354290b840d4411502d0002d4214028001078032805650314155122402138090407200604c1c45041030480811104119105070050685c0380c80364003415880801081c00d00c0d000e00042d4500310860300041d06120f91f0501b142d81d255840405807407a03c1d800b01c01e95440c07403041000e904032a40c03a850080340c4400c0c12102c1607403083e402e00780096900b00403040300c001d0311b400102843c6540c41c1d0340c90468066100803421180400883e0700010a0a41003169184402d24401c0005149207685450419118030307034071007010030015501c0041030101c0420710a812000010300860070026800c04200318110500d085800200040303000c00c14142c11080c0070702d1605000124040c50b070341c2c4100c80421000240c6449002c00c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 281735926 1250 281734676 281734703
    0x1d18030c0c04150312051c020913090302030c03040311030c030c01080c03041e140616020309040e15010b03100923090708030406020c030c060414090a02071b18050103 73
    0x5140e0700500b2030302622030790b0302d003480e81382c0d11580d030600390400c2c2c40c3e000100001540340322419080701202980c0c0024038158607090100c4001020740300084503004155030750741a02c604041c0204111028000004266612a5906c1c00c0c003890b008100a0a180280624a80034105260100f800e500401c416100c48085888401c0d261146805c010801c544400c0141c9a60300a40300348503010703845920a10048404000c40480981041000fa017008804c0300b0080306650300300d4005c8191503410300b068a00040c46a03c0044a074500314101208010a006040021905294183c0110302c1074542c180d129032210754680340e510480d1002c00300311041c1d148051540484c080c4080307210360080031500403655195150444107040d94440d50090001d83c0c400740c00360b5580d007014850303545800c1040301e030542881d10b041c0ca40d01c00c4032904a4807510a88843c00001c0d0303010780c1070f41580c06150300001200c141444000c1c40095012060088103121612003000a035510385502403181a030342d10641404015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 281737176 1250 281735926 281735929
    0x4030c051c140106030f111009030b0c0a09050d08210f0c07022709010605060903070611070b0a08040303110c0c060d09020405040c1a07050304060e0105041d18030c0c 73
    0x20b4900300390400a554807603000201080180340783ca80400c2c0901c568024100241042040700480244540c0502a04c1242000441d003c2415668804100d240081d650924013000b00d40c415140c1d003100340c3c0641030170301000a01400001a0003000c0e00001c8105030480e61400600c2100c5003112050307a001d4003140041d4440b41080c0c050b00440b40f01500c0284410760a5480550400580000d0319051f5118030070000485000d00034100142000d0b00c4862a10010030b010035183c0e030107406900d0a00582c90010810300e00c04015400c024108103821540340c0038903046c02403400b0415038050300068140400903a142d6000000c0b144c90181d020014034101b0800ca00f40071040e0048292441c01590b9030284e107000d41c64a000f510b200b144681d0a40c1c80301c0b800c014904510010a0001038609102442804000fa400004482c252005824001014007401004881d81d10442e003100b400d040030102c1c100403840f10390038002c1c0100901d1100c140c84911410007241d0b64007980b40c912038164040052503a07035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 281738426 1250 281737176 281737193
    0xc0a020f130203040b060a051c12020f030406020708010c031109010e01090512071a0a0504030f020a05040e160602120f1605120a02060a06030c0302131b020304030c051c 74
    0x500300981408400d003000d90030342003242c0048400396002801107041045e54030f441090a000342070205e8400d5105034201c000194461840c08005228840400c0c1210304c080c002c03c00c0c204140c2141c4200c9503500d440303000003501e44225200b81403c645c20291010802c5000707000f621005445400d1040c01c1c16a801d00444080e282c580c0d5803070501030390980201d502d440394011074843c0d0b043c110007400c000d45466400304021000c020b80144100c414082a002594480115400c5a800ca043d154400b94a400040d41c0c005555003ca0382c41803030b0081106102c0c4010802c4025141c10640d00760f5241d540b060300380d880d010400b00400183c4410021200101c1341d500180000c55825207116005075801c0e619a490820204c0070000100004129281c285a041240343d51000c19081c0900065180d80c0d903410b44824240030003442020000f03c42c000341c44256201e4007801460307803d050a07010185401035142d0307200380403d0350b400880b01c42c0071031b050400c9103400416525001d45403800c15000d8560024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 281739676 1250 281738426 281738449
    0x6012301020a021507061506022a0f1203040e0a0603050d020705060a1407050a2121050a0228090806100603090302120409051008011a01050d1808070b07050c0a02 71
    0x20303c0e030b030303200020b1200d947c1e904c0072540a001e541d0000c06422940c0307007a0306100d141050114002c1540400201c4540d1900801da411001b420b80d134505511500300415420360089800c0303400e442607080d003000701941580d000001124010000d0384e161483c0e56400f240c9403612800760301e800c2407007002a8200c4910510982c0c400c0c03d11010b049040c540c107992100d08299204105aa00c841140000b46251001c10740d4088072400c1c1d03050800c108140300205030000c100031200c02d6215540d490006603800c102d50101c5008070000c0c8880035900e540309601100b40048660950001a03000c0303004120241c00246440c0076900030190710a0952030000b04602904426508804500428152620341c0800304041d201400031290041141d150075071035000c11140d02e0380030030a50380c1890b98512256014001c00303036280d0404e18115a49000b803500d25409003284000e0303074100040d140081000e000d05400684221442140110b84944070b60204903010b0040e018203039402e03000041c0c0100185040918003c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 281740926 1250 281739676 281739683
    0xf060d1410061e0f0c0206030c0c060609071409060912010f0e0a0c031b050d0302150a091a040c0b0d0e1204060906052109030a0905100e0d020a050306012301020a021507 74
    0x48500019031b0228519030019a2072210320031020841000d541d40a0207050ba000d0340c01d5402c50290710b4660b00003421050414a18000c0700000106a4825102c41040312900d44001d08180703801d080c07003000c05000700316107504528110f2410044030048040441c0304c1c1c1c0304682142e80300d0041821b40d220382c01e800d000f074010b60302d64a1554500240c41c3c0c5442d0250b01c0e215000780c0262075a81803240000c801480010140071107075107010030000c0041e6000d511000360362158550680f4907511807410350b0760301d161500414151030001c510121001510342001c0c580c0f541c000251120842100e01020a030b008500400000c00c0d1225018089944503401414030300b194401015014241c000800e01554403d131841007980d0030014103c0c200307070b421010000081c0800d07120380307200900e0788100411591002d00711500c200c401d8442d4500307642d280c1091070090103004094607560359552143c3e4085108101c0382c01c1406915460840b01980080307141000560007601220358038001946038003a0382d11180086 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 281742176 1250 281740926 281740937
    0x6090b0d0612120e06040e041410020d02040303090e010b0702063007110f1e150a020304020112020a050304080c16030308090111090a050f060d1410061e0f 68
    0x60060407042c0c0c980c1e0241e01420040510000f103a000410451503141083e00605040208200c80d080090000798026040305801c100002c1961403581003000004010000c1400070070240303403901b0154018030440e446178448050450b660600d4590410091299000000007030054802504002008100c1041071071200c01507291000c0c2090502003409825401c0014040101300d40150000d08444659000b24020070202d0b03040030a0320387d034041c510500702d0710703902000f01590030fa001000550810b225108030700007103103030220703004000350401c48080c0d00288000c0c2c000941c5010501c2158101c2242360f4940d032031543c0b25180d62841d80c0c0b000070541c0c5180304085001c80c010340013000200c0a10b110b6600c02220382400844c1500f580c0d0742070007102859004002c001466501d011a040c11a1408e071005a5108820307400a42030380070f40041c164400b420980010031003c0000c08103485040302d4400c1e1a0f02c2030300d50034200c8030820003203205503200e1154080100d205000c1c111140c50345010b807900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 281743426 1250 281742176 281742179
    0x117011b030e25090b1206010510020a140d090f12061d0303040b01030201031a0918010204080d05130609081b030c060a020a0c0501030507020604170d0204120203010b0a06090b0d06 79
    0x9003a4184004511100c481c0e50038009101c0b00d0420b000304030150400300c1c1c0202d4050f00030071035242c03514018031a49e4403c4212016150000c7d00030700c5914465500410140307241d454800580345c4803214100d01d0700028070a01400304400035040340380429039a2480140c50034050565403000141030700c1500c08a44004c02c40c3e610440ca10810007548038621a204032a11545144000f6040e520040761200c001421521000002d0300c0301c410047e8800580310324199000003280c142030080c481d54005c001c060084220001d80c06802500400d10f075241030f0305029600f0b94641046030303002c0c8140039030007040c0c0200810310b00d5007840440d0b003c008070004003a0346003039482ca400103010358040011240540c01c00310180b81808406944030300104000c0c03e0500c031031300d0300010003916818010401004180740042c0043e40209c883d0548580144410045659031744844400040b443c00c40d808078800d608003c2042d4003401c002d058042164030903103454100c54100007400b03031281c12001002074441c1e42c0d01030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 281744676 1250 281743426 281743453
    0x120b0417040f080c030601140f01050d150305071a0f0a032d06050111011104030803040c03061805160e0a0c0302070f0f120807080f0703150b030117011b030e 69
    0x4002d030003040d107200108400243d0100b41420914164845281a0000c00e03458101c1e031501050907200440910740142d60b9028245150000d081040368940348440802000c81004400126542514800081e45948110203050040341c2e02c540c00c80c000d0281401d01012039000d0007034100f006603003030b01d8008900003001d0081c2240c11a4166070f20917aa9070b1100000c121a50f0003071548030203070507124001d100c14001d0b0b541c6401140700301d2200034074083e0300100080500060300c8904019503402030b000d01c134240031003180c960306411260042d102e500966004442d68170034102210708866101c1c0081c0782580d00e00385d1240040c100d5200740014903408200d0034000440c00800000c1c00c5114207403a44c1c408210341040c601c1d880c0c09121b90018010b03c142400b41e1641c00100559001c0b0011000081540e1444011006010020102190421868000f286c0f00441901541c141c81a04406041d035541ea2072059081c1d500c010024200c000715800d00079081c0303200e83c201440c180c003e00c08880743c0990f082ca = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 281745926 1250 281744676 281744699
    0x1009140610150c020325080708060106030b010503060901061139060412020f0d0f051b010c03050f03070e33070b060904050123060a120b041704 63
    0x8071100c4555296081c1440b00c1240c2492816038160146880fa001480c1a13000c41d03076038080b01d42c0400b10340d01c04107170088003034507102c040d48003030304d10724056480580e40c0c0e01003a66560300030f014100102e42002034245465101d6015280300304c100901084081c2d00e007590544010780d19000312111801641c50442041881c01043d150001c2d0803840c014140d0000a041c02124071003001c0907105038420070080062034140c21714500281c0d01100c44084203041c1c10300103164950301d0349009001203201081c0354244400403522641e00801c5140d0181151312a13001110400d10324180180400c1051000d03c241e52004800366a100906040403080e240d101c0d800111406c040082519101c40341c511030818031b20711004100c1c0c0588140c5041400c0c401c660f928250950740040116000d281c0d0784c0001001d00c00250031410030744020015040d14140c88001c045400c80c3c04907411402902449400555030102d401850340b0b0503000011040c068807155100c01800d07001c1c80781c1e400c000b901440040381010384034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 281747176 1250 281745926 281745931
    0x804030807050c06091f14070308040b0106030e0d0807090f03050615150703030209060408070e040302010c0305010605031317030a090204050906130b090c0a060504030b06220c02070b03010305070509130510091406 93
    0xb80ca6084ac28039143c9030080742480141c000e103007018202082400340315000100c00e101040c10303051804050750786000071602a0969401580e00c80410380c4004144000402c0680c040c01d0140f401c00350554156080c88082030300300760351141017881001307443e010071321960203007584680046c1000c0c545540e94012900e07261198220041d941030312014031040603024455050f501e8030905060049601d000c10203005400003c045201c81d41101c840a401c10186202030404106400042502c80c100044054010101040224015450031020552105c4c002400e075100e0700c500d0021200d548504d07501c00480c110080e000070468814401c50f5145583c07000d8010b006800541e0f2215101d6155040203181154060921401141004804500d880d0b41085d0b07003009007085440812420f503000c1080340b920046901910490750044004400c10030b010420004803541150050340644030b0750004400d056200000400551240e064522075016a030000c04049001d01221014250411810f50408204 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 281748426 1250 281747176 281747183
    0x609060424021902032817040611060402030a020111030d02040909120f17091e011d030f04030209060a0902070605040b130209220804030807050c06091f1407 69
    0x1001e49403a410001112002c502d452090f10346490380d000300e0340b100b6803100e089907668469002505850390360644440c820391300140415400c03000200c059515003040c041d020014000140800d0101c20002d000c07030140d030f0000c001d060450134a41c0190780703100c800501c91070340c3d00041c441c6000c3c07000548007070002003564120201e0002c8852400300070080c1c00308261828002e4002190041c01d0303200c5030b18410f604a51013a4601c645031b01d10180d14010442416654699a00312200e249000641059040c1d546032951803900d07403040402a0746a00400c80d01d4100007000b0b1100700b0161410706c03482500078001502000806882c0e4030844c050b0f0b40015010f80c2c0329901e54003480108507210380c24580c04120210100b200141603070000e0700154020300380c454815510401803802603490016810303803562040f6426038842d52450300b081c00d034004030000d031142d00403210a400b803130034050100c403107640c001041c0750080c003c0740c4c02da0b041e0360500d600d4001c20030082035080c00b114042800100801800f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 281749676 1250 281748426 281748479
    0x18010902030f060a061d04060902011b080408071406160303060e010611062208090f0d0515060d0f0303050702122106030a0c030308040503190302030105130b010e06090604 75
    0x1040320740791050305d0240d0301840e02c003d01112003030380c448041c100542d0440c1c2d0041010482c101079000482c5e00703000c840c03441100c00403050030040410001c20f0045c000c072a0307244103440500703560f00e8060305218044031340740e030f0442400c00c20444c1720b161040040c0303030700f40c4a8140061450740701c00083c190004245c0240b004210448040c20030644200300003680007d00a9103074a0341142ca036203078680305480c0320000300707000000b00b01c6072180e50b91020001c6c41441e014244c4042c0c0c0480c1d003000b90391101c0c01503407407450700301007000718032181005031b030300103130755800818140843d181c43d038040f40203140061100046000300d0454008111a2000034880004038a012801c2200b440040c440440c202918003442580400359100010b064140319404880e0141046150307966a03013070260852192922010040016818540403550542c3c0510f043c2c130300c1a1003042465074280c010504680403500310901050403d041641c0c203203003c90081c85d4500b400790005003882d94413066041d13a0760030020200040c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 281750926 1250 281749676 281749681
    0x13030903050304091e05270708120a080702010b01080415020904060902041e03260c030c1b033904091101021213030209060d05031b07061718010902030f06 68
    0x240f4071480c5d000c3d28454900100801d08100b040c40803092000046820040f001903240c4002d008284859002808400244c0e43d0003484882e40300d510b03500625080c0041490000400c0006105124841441906071100f400c01e484a8682c6281103a041c4071a141d9941c003002802415200d900500e03005000c00b074405601d07903050500c4008981301950749001500b164030410008540901040da54209250545550013082a0172210861160a035401c2c4103100009100c880c0304e10000d50304d40c40c841580d50380205d1007101800c060321007100e0031543c0c0404650140781d22a036078040d010320709151503c03c0f20340c10a84180d00441c081d1150304030243c60318040f01d0300030260380d60144000494148810b40c0c3d5460074181c0d410010406155000c042e020b07100070710001e6800c3d20b4190100c0803440d0088210ba44a11501032a641020640700c4180c0c4140030b401c2000078140c0c0a240062600500306e841cbd007180e981c824200190035401150040300a41d00d400900b07015842c1485080c05c450800409060f161 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 281752176 1250 281750926 281750951
    0x4080c0a03170916120602210108010b010f120b0301151d06040b060406030b010309080c030c0d0e0a030209060604050a1d01080304060e0139110901050102061303090305030409 77
    0xc10010207510300f0307400060103c2d090715101e200320780c19640700c68001d26504e849070514400900034080000c408a0200454842c0c0c1081044054100c0702c0b107c000303020030101c039801142d030511040380350004241022429004060950070110248d20040e0001840201d50600700c0e9111405901c00310011b80d1800344c0c0c00c10007200c024201e6110406560902c00807403044041801849980f14001c1096641c1c041c40380b00fa0310030740041d21804d03000003034691031f0240e40c01526180d0b030105a03403045c2071040040801082e4007442071b01c81040703401886150b07058036580030700441940c002e181903404241004041125504d403c1620094032002001021072040e99100c20700a40040c0c00540c250340c0288801c01140b54003003d81c0d1440e58082c60324001c119000c1c010582040d584580e0703210100f8010031400b0390030f00f108100a1696000e1215503859050100911210110030700a560041e0400c40018500b9215161248100ba00c00e00d400c0028580c0c944580341075400980010824688544c182d5040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 281753426 1250 281752176 281752217
    0x330c0806041401170106080d0e010f08060a151e080610020a020a06051c0f020d1a03190f050303010305070303080a1407141b060a0e0d0801090504080c0a03 68
    0x890580e410070581c0c0500400d80b0407503505125980344030380c02841d41d4004460a4000500502072441180d450340c030491800342c884044c03090300c0b40c001641d2340c042e02c508520541281c0d015650240500c68090b0500c0c440000c00c441b100110001d01003886c0004da20b4040f0a80104e1a40b81590340d8103201d424980100144800b408074410708550056030844056560940e40e10210381a60a0499a4500400303020600c500310540800015140903500006200300f900200345540e99071808201940c0780c90b40300851000d100744210b425520101c51240030550144400a44500441c4c81c2003584035155203446c40d5501c01d030021625500028070810405801c48005500f000c080c200c00e01c100746404241c00b86814006000c20300300003a50007007a86510700342c01100d2054038210011036146003c42ca070981d40d58010b603910700e9440c2c50407012038403950300030446500c0244a907564040d079910307050120000d001c1c040c0003a00c0c0030314104104081d011080184552151090b02c0d032000a040c0040090360 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 281754676 1250 281753426 281753431
    0x60a0e041a070306180f0e030406140310031b0509060616030f0516061407050c03040603090201120204060201050412022d0a0503030c190912330c08 65
    0x1950085041800005024069000101510540e41110642d01c600044010f05140d40c80000351a640c0484504141c4054000c2d05161400c440705202c04484000c1c00750340c1e40f08900c00c0740c0001e99050420105451b49900440d004948103682e0b00e4201c2d00c90315122981d00d5203108042130304075142b101300410300304820703081d6200200321040d5042040f0300421250128029000504100c01d42d0751060300079008405641c1408a00e48098007200c51a00c0c2480007484808601080c03003803204005142d0a110350101c0384141c00280265007414036021b026000741506c42c800700d051000340c5200c44203c091a1001d8001410301c0d07400070071a03051030300b084680c09962245200c01c54219900e0b903451106000e0314007450180301d001e10b180d00100d0629450501c03504590082c001d010000521400e40c2c9248040c101400c2130300425044880111000c1c0c8e0103030018890101c10601d100042c0001c14000700c0340140020f800780c50f440c0a10310404140340350500d81007003500740300d54480c07441c4802540001e000381d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 281755926 1250 281754676 281754689
    0xb07060b011d090907230f150406140f07110f041b0e0414010f05011e0f030504080909010305060a0609020403081603051e0405120c0a062015060a 64
    0xe02d804920035078006400300c9111128010015000818504a070801910000341303184582141426600340d450b548090503042c08901c6104000807407513643c94410340221038001d420300d250f4034044c507151060760313070313000361808405542424031006000c3e1102d44010504ac80c481e0703040590340f4803071008110743d5000141400d401a4640340c140010103482142821914800c0c0c1001b8520000100002d00600150308114070400c04240000600000d440922010740d24240c0352800300120321a000c0b00303089409e140d68400150754500e11480c1c10b009174021a042402098a98900403a0b540400c80447c400c0c1c0c0102e845520803010022102e0700c510410b000303001c0704402541b400d0b107141c4502a11f40940c0500042400d1105101020580110229030b5450119400b0411300ca001e041240c8a9801c18130400e40203110301020010030150106041041e0b40c4014100301000f0f0400c10121025041181c2078007001e10146404505040e04005041080b200c80b60841c0c85481d1030700130b000c0d0702c488a41c000c9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 281757176 1250 281755926 281755937
    0x5060906010e01120507030204050903090409060b01090803031003110d0f0b070f05090901030b0c0405150306031b0d12021e01020304060e0607021513080403120207080c0a060503040602090402040b07060b01 90
    0x1303000181e000c1403c00840350122004103440d1520a0724500b584554080d03181d00030700d00301204040280a41200c0311800003601e60781031050791514065268402150380c001071501e040000e000103100e15012070320f5914041d2185030710160a9403850b21600548400f03582200c41102000409270b4400818414501e807450001d0034103400e00c2c04641d0015060100603c290100c80010306030414080c2a40d004000082c14503c10f81d510a035081004c5d4802e8940d0381c0240140d00907103540d00781032884c0c0030216001a0486504e051651600e01f104016403400700d00f18041c6000c07901101a840d100c055080d060030b80016078a003454540300c412600441c48031076141d00700c41c00708022140c0100f90000c9183e454030100165544211000390070295641d801010007802140c04401d010580c40c0c02e1406908076000c030b440030340d00c451500d0740d80c85106076001c2d4040040c2e0070502c902c03807040025580240c42440702508040803100080c0503600140c0180450260109160060200c24000c49106030390a01b880c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 281758426 1250 281757176 281757209
    0x1051006020d120908070308040b010918120311030907060215010e060d03170c04090b090402030c040b01030b0a03050a03120608030702120c03011e15050609040e070305060906010e01 80
    0x107920742c034041509405100c2e49a0140900181c42d420507003581d40d01545080d900c42d40d070310740a400d042c815103054600c2c000803070011640b520607100c0c00c034280c02008001c1802d0929a42e40315517210002e4a00e008060301c071080007016070003a802035030282c21004094410f040c10039100902e002402e000c5240b101e40ca00c40100039040b0200800c07a000542034a006021346460304003650040c0801058440003400700040180c00281400548162125004140b182421340d008011502c5000d0701e002e91301d5003100e03c0e596514030b8a50f01880040c01c0c18100401d2140c1c0000000304003800e141d1040d500c03500319104400415500c4489035200e00c080150400c200d5003132803000340d941c1c064180001d024801d030712150701d4902c004102c4059024030080003407192a1080c8050308442c191078000110007401c080754100b421b44281c61680036178030054101d5003042c04000400c80a00704c080ca0b090780901a4a01c0440850014482244030b50100c03001068954980361401583e180168480d003e810304a800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 281759676 1250 281758426 281758439
    0x20a020c091003030f0c050d05181225030506040807030e0613030b0402040f0c09060e0102070303051e07080c15060f060702091807081005010501090b030f0c1c020309010510 76
    0x2d00005483e00743c41c0c88111176040c038806541915280b40098054401c5045003182c1c181d2040083c08240542c00c24010907051290a000d0b8012110b074a81005811840185110a902205401110003030386140c0030810340c1c0352181c508141c1c040c0e809407580040003c400d01415004054000c4024040d1922407600c01c00c202d03000c100308814040104925601e40102e030542d034a907008100044c626010030455022035030009080f40d4018400c041c041101866000940e41c00820480100d0342c040e1560780c54412900181d00481605516100c2106410300690001c6010343d070141540000440c0103201c09201c9116480003104011301071403040c2090442c0b00d200e0b0329014255425281e05607100741240d1a1400c0c0080095140041b40c01039101c1d2802c0060803040c0021442c60074948420100002d0341c894004496144030350080fa0368a44080021552031a0300c070440942c4411010011410021900d04036034081c0b090a04d04291150080306004024034207104440c0c00c40300440a20055515101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 281760926 1250 281759676 281759701
    0xd0806031513060f0c0207080102130b091503042405060d110325050a0b0315010f1b06020417070303020c06090a080a060c0801080a150b180109020a020c09 68
    0x441c806039400c001010800444a440014900e2644440c003071110b074081a41e20001050250005001485015000901c0301c80600c01c5501e00307159a1148121203040041c1210940d00006002e0b400415081c0ca0b103900c60400c0d0050350103148109400710360660aa607811804244000402019915103024800380e84e0f152100b0b000301035806039052803920f2040e00083d0501d981e01d500200c0200036560300260a060381c085400550744200e030481e8000b07865201c007400300d020444120102580d6101c2115066010300079480c07a000c00ea10b400100700c44201a03c8420762000401140c000d50081f80c1032100704280040e0b0304944000c50000c0c03803d01d243d034074004d581d088992403041c00345400148450090700d07000240c1c8041c04207407040300c01031040c0b468500014540740708001e0010308010008583d40c0d01c0840e01169054003e03079100c0d240c150369030204e0000d002c1511030b640d12600c61100055500300111040e4024065003100584400b8840300290900001000b181d200310440400c010304414100e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 281762176 1250 281760926 281760943
    0x140607090b09010e0118030302010519090f0308090a060c030504061802010c110d0f080c0d140f0a111615030b01051e07240605060c060417190503090d080603 69
    0x920b0040300030040302c0c005917441b640301051003c02035004079010041c141c05410440c000c440d015141c0300901c0b82ea880d441c044540d01800186811102410800801c1c420405035422468202c29901c60601039942e490031a20074003400780110b52100d04005c14800d4612482c0036641c0140ba07c00b416036107560000700180000d03400100014902d0715010b0150315480106800700394030030080c1024500f40e0800b4480d40d04500c04406040c490644070400f440d2092000452810368690705600303101482c4c0ca10003054204c2407610003003284071010003c10f004200701c000780700d00740141c0d5040700a0521140c02428000100d240d800d1504024103c51141d920800700da2018100b403451020350303881c08491003070601c2401c0f005050200203102440d00c010001e41849801540700104020103595841808003d0280e88207032003060300308030005030103d0446441c0307880310070000fa00b19180001c2d040c07640d501040c0015400d400102c011007048000701c02040303081010701c1981840d043c0f914110f000223a8030b002c2c0d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 281763426 1250 281762176 281762179
    0x70f080a0905030f1303020406050604030308070e04020904090f1203021815041208041502070b0306040e0c0a0618080703230a17031e070806011b0b04140607090b09 72
    0x1111040703824480107100740d484000980b1603540e6078000d017070303100b003074012140c002644514a80500041c05142080450301181e82c5074070350f07404035a90000241c41211820f180d00e031b0411f0702081007030100e58a5124049016200781c50030b040070303c080d06003040c800300d5038040700c028544100803c80071001107400f4a076002c5422100700761280031654040420340a198020320714200501ca0640422036a80c003d4400c4e140c40c4031f070f55415480340c0c140481e81c07070a8610568000c2c10303080011844a0605402c0030006280480448001c2d8059101180c9a0380c066440f0800149001d0552403a07a56204c1303541000b0580d54004098103421178559556112040300ae0240702e0910b41c01c0215040010700c507080760300307403c414a08056403a00760078075040d40c01200c01240904650000b003000c0e01c803001999001d24000d648440107582d41000544904184802c5100c1680e04c03850460001030005030042e00c6248a43c0c072400c015401c00940e1403600201810000070300008401c18003110a4030390540c0c46a460 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 281764676 1250 281763426 281763431
    0xc08060306180a0501052809020105031302031903050913090215130f03030c06050708070c080c0309031621260705100c02070603060b1207021f14070f080a 68
    0xb0318450545002003064004205500304070811848600403c0344200d0003484c103101c5010318001d410760004940c05040000c0c0412024400702e1150360210f078402d200703248003034100c0790a41c204400c00511b482608000324001200010138a00c582000c1030a01a0480000028021603c90f81d001916400280c0c10a4100080104c0d01000c441c50900740301004100c0b0a00380c68800f520781c10b00034045d00a40c030003074800a0800010600301840366048520642c0c941e962074100031940e0340c40f07105607800340c0400e5203107200a00c4000040d070780600c114108142003e4510340303a50310b0b2081c9161172407411f00282401b100524025408200c2142e9034002280a81034650300c20119440026128040e00002401a22600000d40300c514113680c0030b40c66400c007a400302c3d08041c1e91060100e003640d0303a5002e8920102024020b403046200060710440c1c001d2640c1c010b84107241c15100c03408488070402c2a03014649a196081803500c1c0d00130149c0160400c0142c42c10344a90b561015020f07200c0382c0040c02040102d075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 281765926 1250 281764676 281764711
    0x3120e1506040212010602100c050306090a0b0a0902040b040801060602010501050105160314070302010e060105060c0a0b06061209071503020a052203021504082815150b04090c08060306 81
    0xb611541180c800c4107140d0080e02e50795031504002580e0701c82d1502c41900c42c51a00001e000624020b2054230b11603540104400302a980b2050700c0c0005c0c11407907004d207820464140c1c010403544510300240003e40070280440d51234a140100d07a50949190f40d2010056900d81001480241d9108007121103030051082c940784101c00702d00d030480c1c0c5410341302020001d42102081040400d94190820b886060681d81201c055907203c0042040a10501c2080c24265100380c000310300040c90b04034000c0e031000002b4a418100000b01d140c600a1a5086440035a6a00800c80911943c040005142c03640030f800d2404600b000340c90800a0000c0c810b4030920f101103e800c2a4450b9014426100d88001c2c4d5070140c180040074204485854050308a8046ca60315801150030359802d116059001b00488503030300402451500302d0fa202e4840006d0f484008514841e02e508038022103a0b240c030f400c14010608050b11603030340c07441c05101004a860b0090081e04100b010410300c0b03901ea0300003c407290440841c290103019007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 281767176 1250 281765926 281765929
    0x30b04050c0405270607021c1403090321150f060d0c0e0f010c0f0b2e140415181d06040c0b0c0d050d0f09060903120e1506 54
    0x207038042086540c09802c0c0020040c0072410008540070240441200d903801d8220104025103a400403101800103038003003020540e41a003601a540350b001100d007001850a40031424528041d07104989031400d80d800002c01154001e100c200d840348412038100360f982d45040040449000e001e50030841d0348503000c900d80b034a100f5079844080b141480c00740d610070003121303441c900b0151a204002582c58403610f000c0421500395400340c4c02c0f80720810360140c180900e020441c0d94a040c3d111008d4042120101c0003400790a020209003503243c0c0400c3c1200125250a2915054008190422100c40e0040742000360b02000c0301c10b0030750400285c0740712a03150001c900d11485d000e001002d04ac0e981c14a081c106140d106440031012a071280030780d00800c08629902d4a4041c28010780c400d0410841d507651102c40d075582041c1c2b080015200d107412080c4c002c6100b804070031032507060710080582513404650b2565100105904070311030491221092006010811020990903155140c85082c103103904400c40c00241d0071b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 281768426 1250 281767176 281767183
    0x160b0d020a14031905010501020d080a0c0c08040801060e07050715091104140a0b010309121407021003150510140708040e010e01030510050f070c1a13031215030b0405 73
    0x100e40090750307454584c580410b41400748108001a105003514101c0007051551001c125900d02058a840c0c5107042c2d10303010210801032416038040d90410001c0c1034900005403d0f0b0008000401c0c00c40000300d511030604140900c0000058950414403104005640020700180000f104074100301800103011840c90030050410316030100c409074803910341124442034980200c10280620100c2000704042c0000500650813251481005880140e004071900784280c803669003404002c0e544001c2d90b0030140141c2c089040050780720801404030b0707201c807441035601ea0706440c2d90f00101401c80306910b5100e0706490291501c45200140b9162030000916031040c800804100c9006100a5010941c0c542e51115522030418003800101c51034064a1524000c0107202d003d40740c09035000d06d064003425200c0040c151580010401c1c11503501e104d40760384030700560300c000200e4841c2c0850405a1401d43c0c080c074006041000d4500760b00f01c03880c6041d00c645c0804c03a0441038407003902c1c0e020300c014541d07071501e0509a14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 281769676 1250 281768426 281768447
    0x108091c030207030915050f0d14040326040309092a020303010e070e30101b0206010e0105090718030804050a0e07170c04050a0803030405160b0d020a 66
    0x9030602116180065603900d50700401400d4025543e4090711a1603400840058201004140c0085c0c4107111589034003090200600a442e0212400202003c0060b101107070311008403825004500b00c1c0c06440c45261000c100c06002c0441e41c42088001d03d40b507074001c4d140842c0e0703008103552207945154107058100a00700c43c00000711002c04044465074032940080d0b4951003401008600000d05001c14513182c050b04140c044c1e40c82c01401e01442c0b08000d400c9483d80d01c0c981d000420290b404110030192420b0902113089045181a004504002e01c20410300103503801b110710b40210341c4000010040090101c1103141511710803201c2d40c1032034888140071038800308030281c5440e510088a000108009108006108884041c0c0300041003e966040881d254141100c44101040c0202e6202c070710143c10000540d40440c40d000749038101034841d4082550807400c1e4100c840a68400010312050000c100708199400380d00f1030716561810302f132401e440514086c2d010681a034a40104000b08014041c4030100c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 281770926 1250 281769676 281769703
    0x804230303010b0d0c1d0d0c090f06170a11040b06091807030f090b0402010c02010908030406020601090513052e140a0b04020301080304030f0f0c06120608070f0302010809 75
    0xd48a50b10b0b404280d11680c003003c10b03090107603d80320501d403540f405200440740c451070071b4518090883e0100c0900ca803040100208139100a00b41d8030208a0f40e0f040d2241a02400741c009000412038101401646c1c000040c80c010701030f40d8401c00840300080c0040409a41c14541958045a640c0a640104105005191600d68404d0403003d0036645255100c881511501c80c17035905000503421008050203c5030007400240900d8003e01c00100554002c80035400400e00c1803402464540d681c42c61641189c00a030000e0005030071950040200607658000d90b50440e1081d0088410b05d02581d0350300b50303074103449485180441920058800400211b22204089403010b0300d0a2103d001d401c1d44286c3d05101c21200041054986412641d05082500c00e40c1c2c1650240342c0117515060660300c406a0140d00c5003021580070000945100c00603500044400c0144803a0f19081d146868803540c4000359601038100d444c4583c0312080400111061400050490b902030802c0e20131a1120740e03200e0b040ca240d140840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 281772176 1250 281770926 281770933
    0xb0a091128091208030703020306012703150e0c010c1401060e04050f01050411040e0f0a0303060614031306050c090301151a040f173a080601080423 65
    0x8840c000c1100e051070101504aa071160050b98032074018030300c00d0b0708541000d0190041440000c1a86001e94010b6030019014140300040000301151121481d5586011500728804e00f8410400c010010108401c0c3c405c08040900100c03484548460b44c4580c0000740c2d0341044100d660120900102c03003c49450f4083d100020b02c812603d40804003005c550070f8408072800c2c42001c2240546070018401c4a00850b480441c2c899274005040421019001101050905009054580c0c8400208101265100c0d1080d00e010620034030305440905100742c018103265080b0000c06c02c000b107800202414041c5680d01200000c0c690f140c644140340b4500070110003d0300f5601e807042c1d40c000c41520140d41411921240402c1181040c03c003c107100c0d41c080c511501e00c0b036094040e0140310649000100e4200320b0f181d030741103a001c0c155506549020281071189060300142e220b819043c803a00b0214029070f05400d9041c0f105079420031030f00082060038024005040300d00000744540d4100c09014201c11001c502900f00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 281773426 1250 281772176 281772217
    0x9250b0c010207030813030c030f0224090705010906080606071110080901180309170a05070e0603070b0702010c14120c010e010b0306010315020a030f0f020a0306090b0a0911 76
    0xc00d4001d600c282c40c15004a01c00303600007914200748108445003154190b440c01d250002e2958203a89180e1168424030a60080380456200b42440050700c0450450711010328560f424070000d210b051a40030b802c528100100181c003800703220341101d80c0300d800c174509a41c02d070742d04c111506140001068a00000741e100c901d1004103041698040360b5a40200700c2c420081028084440d0191010310061710010f010412a1000b048007501514456035204680000e03211502c1040da5294100410340e00008100424203090255600b001c004a101a041014040f03140c152140c001809100c0c032040005c01d079141110b5003601c8840240000704191110300e0300141c440e12a588050702810101507000c01540c40d0200d8124689800908a8120ba070005080c1c40c90000c8608000c01a503c8121108241600d9180302400b1588510039881c000030800801620746045120003800e90359a07078400d80a50b801c001c0045a141c1d1404400c20803100c900c0c90000b03050030390120100700e83c0914a00719155007071003a030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 281774676 1250 281773426 281773447
    0x30902060409090b01060806150306031617060f0c160606050913020418111c051903180b03060d05010b030d05120108030712050a1e02030c0f010509250b 67
    0x21203d0340707100e00c25400c4160388511048840100c21107100c1d80c8544c0d500b8905864602c4000155040789000e001d850003540c10002c0340042d0300d803075072040d00d00c070f044490300c403013014018446541c00004a49144105003002410f80d065070003810b03c2a00600e0890202c0000c0202541c8a8401400e0107840d0031018640b1801c88601c1107403c2500ba8004c0b41040c00f0041002280f440c1c640d0200d0740b002d88614880aa0424851400b1013400d1036804a40d8034806940403c1c0c3c10070640c60100c001c2040001c40c000c1074500140101c1c40010003e039406a0201c0034081e109000080d00e03400101660103a00018171801c1c00d9014199803804541c140c00380300e650480030342d40840100740b002612600040d00b640c0c3d07000b00079602e02c80c560300a020070042000b021aa80e00c210014a1005c1d222301c2c28070349220b00303c803c507043c0642c40d00395480540c1c400643c1081a1009108550001065000130415480c0456100740c0700d880e0080c04800380c40c020030303440c211450504140b9000d4203411209503102c2601c142c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 281775926 1250 281774676 281774681
    0xf090711160f05040209031510170a15180809012d0905060406050403150603150e070602010b180912071505360705101805030c03030a0f030902060409 66
    0xc0c45072240b0900310003091508107402129078654025000300b4404d81411500750054001038200401600c0300c99001944403012030650020814550191040710150310306010f42c071034840e0b48a16458200b205a582d0a41c3e0310000400640d0400602d603581c441180c0102d6551000c03040200000600700d0746912070113045284041e80c0c010a403100500c040c0c4810030003016002e540301b04400103d00300800d01c0019203111500b010740c90040d40129001e500c0341e039103044100d0800d42480c074007560f429852020a4040200100070282d60000704aa014950302240f400e03010013940002588450f00800c000100420020380907a150500c81a00e0301104d2805034403407042901885541800c0c8801300300045600d2a1042ea0300c0410300080d0f0348001c0c0d1400c001418160008200d40741d0185070f02c0010662241c4541d83d040e424180d9900700161200c1c240c0c0580303c005504141d000b44d20614007040380d61800004c882681c0b01c00d003810086129403e00c210040c01c04a54002e42054000ca070004000d4031a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 281777176 1250 281775926 281775929
    0x22020613032a030b130c030f0b0a0f0209010c020114040305070e071d0a120c0b1b070905070807051b120a0831030903060203011202090705090f09071116 67
    0x16880920040394404141041072200c0c04040c02c4c502520300400c081e1842402ca000e01d4a2145801c0b1144030b940e5200e500703101090000603103400c502c00c2c081200840e045d2082913089004802e0450a01e8552800201030b0064400001c0c140280035051700304d19000242178400640c0d100d8220b03400d00d603e90710351404085090303a42d070b004906001403c0304401c0c0d00301c0722030381800d00c09810135036050701e4086901301400814805690000f4000e0012500c2d5031690000e00c0060822500840c00c6107820a00503e03000480d0f0003989118601403d00c01d51503400307a43c40d5044845031500544451420502e0700310074036440c003a03c81030704c01d07504900000b00d1000c003d0100f070040c0d40c0342c0034256611051211500f28002103280111b840c00000000f0036104c03101c4101d002c1e4028500181d400d62030750748a8040380d2003038020904001025911108600d440950540d101c00309207031090406108002040c90030442d440c60b98864481d840c00501e0341c5108a01000e221030902080320b0404014003018a103030300c01d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 281778426 1250 281777176 281777213
    0x906170f0304120b0604140906090f0a0c0501030b1201020301151b02010f0f110109140f030a0806040b06070506150307080c010c060209120a030210050f2202061303 72
    0x14109200300d88000030040c0c03401c40b030144641c10301450b1282d8400d003085100801142d8007550f02c101c0006141d038010f661b1481039995a0041c00541003100449160242101c21a40640c0c4005444c0001035110300d000002c4034000e0a011440700c00e10070000f00072200c0c130305072804d0542c40403000080f007440080c16940090002d455625103486410203d015801c68810040d021a01d500414000e25101d00c07809190045c083c5400d1000c01c10484030b150071b540d00400281c1d4814a9041c850408003002d01140002400c1e0400540c5012400030019100d00b4000b44070a1003103035a0b00a02006480d00300c00c40e094075920000369001031920000c1454000705002c00c0714024440c0d00804951420006158040010143c540c8281c030225a655203019500880e0707000e800c003425005d00b40e00c80e90200700c8000018441d40160410800c33502100049520040c448a401262181031060b03882c0b026000b10540c000340a03000410b18014004030b541440348001c10041e0300102c04c4000140b0450021401800c0c42 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 281779676 1250 281778426 281778433
    0x1e15020307030e060901080609040201030e0717120307080106140409051e010b091e0d05030c07060e0103051b1305130e06010801050f060d030c0218011404090b070315090617 76
    0xb41009005090088914840c080780300c50010032385a181c04007966074481d00c1403501103070300341e22070000c035042c4a840d038000030b11303085543e0701d00400340d1091000020000c1e1440c003950031031920641c0181594018407802040c032649429514850400c001241c004c0d180c400010300c16810600e0300b07003a42c0c5410006802c0d9640e000303000400c09122100c21201c00c082c004015410202c1c1d0140c54840805440050581c000c203600c09400000d1014070240c1865094080508045407030144081e007100c0011007428101440d0104103c450f00c104960610300c882284021902c0354203c40080003c41d03d280c1015602200d219115101082c00b60840e40c91851944d05403240e07030f6641c41700c44e82a110289c8180048071a6100000c50a080c8840080e031024003034901480050469000702d861411039520103d801c00725400144036000c94000c0501c03030410207807402c004060040d211a5080341026010004064440020b032541c190f07071114200c0030307101c484d6080010558800c034000310f000c0900040c8003070f0701 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 281780926 1250 281779676 281779697
    0x7020c03010c02060703020c07030f2102070501020613050c120706111207080a05041502011a100c030e040b0a08070518011202010302031e040c05010908010e03041e1502030703 77
    0x381800350802510301a0010706094840720410781c041e40044482002030711030322034000045015100c0c0b800b09113000304002d40c00c91098100c03402c0c503000170350b140d8002e643c0720080411081c0d0740005c0055000340d0580d401c560b044400d21f822814261000541c9500044203031801c542c440000c44d4803012520b580c3c40c0c00540f52840011262200c00310481d50082d4013090190201003058500203150144151403c3d500c0c1940740c10305000b84030f10042550005030340d51030103a0001e402c40384803142098021118041140381080c001041c84054600050421824080c04a01910745400c45100500020502102c040d110380c11b8555444491103003521404010300640480d06001c00c00314181c4d01454001511400c1d943c0045d4003a51010740380080c801c2c9214500d41c480301a0a103134070b000710b100da00c80c1d0103598906000100315003156000320110ba4985003c440110f13800108036001c0b00c3d8282100c0c03845518020682c8203000d10f80c0e21400204000d807004d4a0826400f1005020343d40c880d484034000c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 281782176 1250 281780926 281780929
    0x120601091505030c130b0d140d0806060d0e07080d02010905010506120a06050903070204020f0304020102070603020a05070623070801080d090501080a0b1201110a032702091b040e07020c 81
    0x90000c0c490540c1641010841143e1030034003042c408a00201000041b85940c4200c021422981040d0b80540d0304183c0200e44200c6d103c1c06201100c0251200d14040101b400c00c040001d42070300c034a0092441a581d190381800d03d054091140c0c10041a01c04d0544900015844000e406002d0000c42200c96504c1e141c000399081c07810b20700403507511000c2002050549141e03500d10008180240000e507641c4018000c0d800160348600003006038920440c1813a440b03061034400689408650b03009142898010b0000340000c55000c400e40b80550382201011070050451003204520304990880c556054501c1c0007040303005504101b27254104e1721204202c40002c164900116610b1201b400f0b081d001408050214031640051742059070102c8008106ca002001714140540c01c44580c8000300140160128610360710340d8061103603001c035090310000313181c40c1c60400b40440642400c2c6130009102d0f0a000c000305619641070311003102c1507001c22655541d103a4440f40464050300d81150200014443c0380c2985106 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 281783426 1250 281782176 281782211
    0x60c030c23090d150507030b010e0a052b0f0b16051c02030a150f050411071205070503130f0e012405090102030904050a090b060d030801120602070212060109 69
    0x11000810045401e0608031000c00a120805030410b0310440d1005890841131149485854020180c948000504c0603071000054514040d12007500d1054015030005c01694480d0340898081c490080c0042c0d508944000a21800040c0050040c00f19506503942c0310030091000e840f03900442d40c00d80f0703004290001c81e204440030311820041421560b2490040b031103010054001d560450100d4402041030b00d6200d0017104042095400a000c81c0c00c003050030000c504185c441c2c40c91403032540307d0031442d00d00b0740d0304c401340c082020f2600b40c8100940020840c05002003401030f90000c001c183c241030022a40c0b40b2011803100f80c02d001d00154141c7c03010000400742c00540d00c210820f145140240480b0490950541b4030b07401070040581903001c00c0210100984e618800c06200c1c5075004030000c0d120030541040084110014082e83c02064954848000b007608120303000c0c1110781504828524406078508200640034144009400000c0103041c480702880202c2c0c0d160581e6030080003040002c1c007040c6040c94 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 281784676 1250 281783426 281783477
    0x3010e03040b190c05030a0309030e04020a02340305030304051c0c031d0a081501060e01050421081216020d0e06030a06080d021c0f12090c03060c030c 66
    0x400204001c0b50f034000c02d48043d90120840e2a003800c150001e59500d45d24119840004004002603a908103007041581100449082c104141ca085041242c588006507640c400c014680407a91044000200d02081a40c0c000803001700f40d50303481c00110398906c1d12556a820694007102c035405050070340e1008401031980c452581040703540b00341c8100c2c060b44007602c500a6020708180d20f03001d00c3e904102d290321743c00341480c005e01100c00209074021105d141d080508006801c40300400c2131190700d02d82d4030380c0c2c00401d4030700355803204840311111644c86403000ca03800c0c85000018000d140c00b0640702e1000700107030701e00362203100c0060211829040141080ba02d903c121480310020840708018140e01e4104503001e10b41c040004540000c5547d02e6a890350300e070103161a01000164400052003e101c0ca407420b1440d802ea0150800e40c1d203540340d048014194004005640d00b607655034107881000c2c002d100b800b0400564102078200104500f050005000c0d00207150b00c81e020821005601c040c10148480808 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 281785926 1250 281784676 281784689
    0x204060c1505150f0f040c050a081308040e070c0204060609090b0f1e01020a02030303100609120c0b0a020a20010306120c03140709150e090607020706050f0d090c030203010e0304 78
    0x2c184190a0f001c020142401c41080c540049100e03000c40c1190b1114030809024408507100c41d41ca41890351001052a00c008008002001c40c88452200207205901901c06850000e10b1103d980c0d541d005048400041180c3c0280d405814110000f40207504043c00300251100d64000380550075004090001d041584902c0d544c02030034066060003442e41180d2142c40c0500c051040d12407481172600001e02d140c02c1942d000890a207014400c0103001d03004010507004061580c050b600d0b042c060744880300c40119034890501010400207007a55514400e200805804d98055000048503020030410080ba12000c0001800301c0e1078413001080d0990842ca00d401c0d001c1c1d10441c140942800c55545a00104504004403042e01c200c9001107840400350262400c8441c0101185082d2440d003414850359140180103002039030010014090403e60100d020002d461490074005d94589043c01a01c000e44503242d01c941d403081c03402820380100004070182104680c0202c1c02400408100d00c1556100d00c560700c01c20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 281787176 1250 281785926 281785951
    0x10060f14010c02091b04080d0801060219021c020d0303050901060801110d02130e0f0601021b090609100906061e02010c0804031404030b0c09040f05130213020c010204060c1505 77
    0x1000140f401c2c03654103922001751310351401e500300070040e03101c816013054000c1c1045400c03400c882080076511046041c014141031004142c1c0382405241e2030380d80d042443d0080c1c000e49503442c0d00e140002440f070701240000d074043c10100314481c0030306008008000940340d90009500340300700025810014025002c845114880c11450003841c070040f40000d602c101d00400340c2c0c407010b1707200140e000326158100b4403074410503940c2c1c4400d203001c400082c14088440e00d084109462088852002e490f101e80b05948110b064802c140c10b92145d502458140b8250f80c8040345050400d8000704186522280d0f100d071081c00e8420261902055020603401c0e11248940800011100300c0080d01091080c9410445071100b070703200500c0e0640b25216100994000c5803402051032001580b07201c0d13800c0511031503100c3c3c00252070400003820882c101100f420118180a03205102d04120480c0b200710580c100c9440011400007150b9a0350b0300d81d40a840008824800c0d1525503480540750502e08a0303020f400d00c01c03000440b61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 281788426 1250 281787176 281787197
    0x14030c090108090601350a0c080105010905041707030c080a021609020f03061009091506080a09030210150e04050c030607031b031e051005031009080a110f10060f1401 73
    0x5400c400c98a000c0003404c410744e00307060046c840c001840700a032998082c0e28170082803801d00180609644040c0c0c0301c3e01c000d40c548002c00022602103880804800b0740755411654070900ea0504907030a000c442809001d1400014040c4802500002e44954003106a6000c0829560344c00c402d4040380204503205840300f0080000540307600e440711141c00c1d980c0b91804c001c480c4989a42d00201210403031040601000c0716504c043c00140c0c0c22500580d8400403252003440f1140450b0390003521101c50081c000d020f2a21041d48580708114142d40601902d0450703401900d0340740c2403c4c00385c3d0b10540b80a40074002d000c1c40c8041003500307100380034070380c900449282d09260850740d0880841c0140311849038587c02c819602c1d40c010440724030780141030107104180340721180c19007450101424028001011106640341281e2040007803101c0c1c00351040400d00f0f090000c0d080c050040c10724100205560344500380c2c0215040800081300b11303070100080d81c100c031003106022034031150501003140f1003001090204032100754 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 281789676 1250 281788426 281788469
    0x921090906010f0203040308030901020a0e040e0703020918030c0102030f0708040b130f120914030304060219020f03030703030f051305100906060f09020d05070e06040308090114030c090108090601 86
    0x550300e143e0300d401d20450340350903a81d85602e00310790400d59845810742d4000036259600c0fa44001c580d850890119420001c01400021007655105d4500c4002c0c015440800002d42d049407150a82d03110014038401e070b0342e4a200d074414880c001c1d80300302d400318210b0065201040c00b5920030340c0051700c82c0e9403000c01000d9036101c104c1d4001010b10840d4048512603810000301c0005000c2c414885000407181c0c44403040d2070f04107024030103d08031642085029500c21b03c410442c0c6640019610098a1440018481004503002003207041085a01490f01484000748200405034103500200e4280e105840c01c12107900c034a207980d0a000384d0088064000c1e4800501c0e10014440365100039205445207100017a074550f0707035403c4a4200715070390240540780e60200707144000b140e941c0142a4860110328005021001050004107580150302002c0c1c0100b4020446038403031f0b4000d010050645192030901506d91400903443d502070381c004075480740083d64220108140007400500c00d8141c40e0b4131040c0da01b80100050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 281790926 1250 281789676 281789687
    0x10b1018170c0a0303030506030d03150e0a020c0d0f081b030f15091f09110418020d090605010914090d050c19030c03080907030f08030a0212092109090601 68
    0x100200d1180c000d905800c000c603510410080000d600c00d40300480c42349410001c050a100000305448207060030110040c000c08190b02100c2d00345c40c100c1d004808640c45c0c0c0c00c0d01030005d00903280e00010501c034035002e82411541103a070f42c480300d09880d6214100c0c2d6942e00780000000150720b8041a60741020b001188131050850001a4001a8050318070f03244544000082c0c2125400c2d54150110310345411a14a859600310078800a010104000e000c2c40c00c07003507203205151080c0d02c1444900603900c400c9030407081c6a40c0460b5512a90000140038007910380c106107008280c01c0c40345010341e51502e40c1013500007184d0708040b4801ea103141e001e000d80001f004c5050302c45500026101e007560040d00d800d4852070a030a60f00c24000c50007a2f80340ca044021034900545960006000c81105a0100f0f80400c009103d841c885040c55a00501c10380c0c50f070b10780500840c0603004440c0040d80360a00d00c000c1009202c00041c00c804030542191030341008000b08605d8215500c5a000c0e0303260030804102c0020150350080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 281792176 1250 281790926 281790959
    0xa09050d02060c0d09050111070e0606030c1e180f09010b1c0f050a0e060c0708070c26060a0b01080103020607022803031409011d12010e010b1018 64
    0xb404003440d0024440b041411325a02c41146404507480c0d080601165034444056108002140000c0050b94100048400c0c560b00003000184211400000580402c0590003601c0c03401901040950001e44d10045006882d00711242c4010305166524203c441440d288240e511503406c090042d0245900b0482c2c0400e1035400f1300e100e50700e072604120f9031000f24507d500c901003011070619400903d03400d041d200c450645110014401c0d0340d0703010905103c08507031070400b1560416031100c0705a580300d603c1e1403c805914a550b0014800262000203c201d038624100c02040007181c440c2640c1c002d550702c6034610100c0d00c21040f65800642c0300030044c001420120b0081c185640003c1030303010350800c030620b0b40030f14a01e0b4041e1181b03281142c010400805411071001c1004180d48082c007400e15407403200003048141c3c803800590b03410001c003c1000f21507c03060040104011008024408000c030045034a000c0e1820780c1009014018501d000d80825104040000c00c40c0c4440c500444260300d4400f24809007200c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 281793426 1250 281792176 281792179
    0x12050f06010f140c16090e0706032c0a0302070b03220609020312120f0103020f010e0a1a04031106030705040b07030203091801211e0c08010c05040f0b0a09050d02 71
    0x84440300e162410840c0150800071505001072040090440101c00d0f4507100342d0207441b0140c1401074520b0040300129030003060301c0043c85c00158004841602610311449180308003005501c00d400520304080124156176403901903000c0b02c03030340da586951f00380c0345110840341c3e040d0000a580a508452000305041441c05005000100b15100c2d15000242058000b05819048841c0042e03034030352411220410a40c01100010081255803440e00490306403404003d009040180188a4004541e15000381c44041c002140b0090116283d42d030017108158014001500e585004115610b140d180c580d040300e00c0343c1c1e22580c0f8035041c0351800032064041e0308141e10403810340c002400032100545032580340c4560307401c1500e140d004951504a0a1400302000c00d10854107034260710f00d0301c020480401032420b100c84418640600620107040c030008000c810341103481d040d420403814800741580000588281d44d684500c0780f000664683e00c041151003490348980c0442d40b00541080549007070014500313000d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 281794676 1250 281793426 281793437
    0x1020c10050d020c010612030f02010b090612031902030319061d0c0d0f060e010b07030e12070305010e01090515010305060c0a030603061404030315031e050c0307030f0312050f06010f 80
    0x100d01382c503401e503859034000f201c481240321050301c1859804040b140005810f130008024000d0300e0000700701458002404140200d08640c10302c0006c400400843c0c03800c00110005011400a03410000d49a51007038503c00100407039401c90019030b0306148103040459440000310400070728001494248404000c01a002401003440362036541d0486024861803c030724547c0c000780081c1080d03540c00d010308068024540040c024401e55000a07085420b450384c0000c12140c5000c1c030800c10030030700c3c6014501d4000030019420800700080c40407054001d5800b081c854000c2d14240da183c144940d43c40d0509220250a45d884040400c803a401c003800101200c6801d490007107100342d183e8590406941100701074800d4003ea2404001c24940e251140364020054084881703040c514580381e9610302800e10900c0c803051100340368a00100708040052010000e0090103072040c950b80c80c01c0c200b2481c0d10b82c900603008901c04031036400381c0220360300c207441c401c40d01c00507000e20580ba0600111713610346000c06041c05005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 281795926 1250 281794676 281794687
    0x309080114010e2d06031615030b0a0503100e0118021302030912040803070506090705060405040f06120f060e0102030c0304060902030c0406180b0f060a0c08190504031101020c10050d02 81
    0x11369140100c800103010302c008500780c2018000c0c14035003682501000c515084c001002d1081c00074020612241c0c05492501140c0b0403039100c005844620700798030a0368107100740d00c208404109140c100101c0b01c0400c0e0300030071034102c03440e410004905245034000e40c030100540c0e9030f41858486a01544d080b107d11000c488042d44407102507901e5920940021915905c00702e1404c08101c01008015401201040035205603803030403000c10f5403401140100381c07044e0349450340c0714031100440d80050004c0c210070035401022005410300c05000e081803001628403d0800c81644c08800c81402124014201040d0440c035541e81d54a03404010510120101d9040c00345118084071956203004030405044030b150780c49030920140d100c580440d02e003060721038040d40c41c031000d600c0c040d6a41005c0d2001070140d420301110510700c42c85d000b50b00d881810301780042c0d0025020841c1c046d43c0e01401500940c2e11903c2454800004100166591826a0b801d01d9110b03480c021007082d0584900050103641c4c036894005030414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 281797176 1250 281795926 281795971
    0x8120a0213030f02030613081c020d090c15180504020a02030904051f06080907091107050d020c0112020c060105211015060809070b0717070f0309080114010e 69
    0x2400710b80d0054030081403c0c3c103840194070301804090780008403c100345d04042d00e140d0310304086000e280f050700c600c03041000711804000465012580641400b4000b00001209403428032900c400300e0103800221405028082c0034180101500300440f00710701001c80306a460320301000080d41c00f45a41c030003140010721095441d601c6602856021b20104c101c82e6030368202103684890b2001155102104105070b181c14040c4c0040c02107041e000b40d80e20036601056850114200e02d01511030100c0060031882a911451505580418528850102680e4813184001c0f0150034000342d0040c0000382400e50480001000a454140b40f010600d01780c000001002805800c0c109051950741e42c1010503058a483c0c08819411a2240030809400d1508009026007401e88010b40d4800d040c1c080d00c0d60400000424005200500d80000030121202408940e1000c4c00c1c80c203c105034265410440110726000e42c0811602010b00400001d41c030580b461050700e070700c0c01d0681020a9005404110b0b0880b080600c0303284e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 281798426 1250 281797176 281797207
    0x20f1015090f06140402071a0601020a1e0c060f1e0207120b04170307120b01050d06081e0708030a0c020f030a0b07020c0a05011707031419110708120a02 67
    0xa0210b0b003000a03c1900e081050001e00200c900c2051240f032040040d000090590040a40790342c1c070000050007555107400050f480c044200601918036015010710712808500086084011803050404110071507403080c007038600688000c00305010502d075514001081c1e010036006c011404480c8102e41c01c40c2d84d50320846054030110a0b085d900300c8140d07010841032000c2010b00c0b11000c02c0d41030740f007072551804000003005071000d01c0c040b40426854160140d10303a0711400c15129010003101041210300c0d55901c020740d41d55406050750034480c002030300500300303800041816411504490043d52808815840849110388090000c0341c1c84000890750700e01d141c0301080035030f61141c800c080c3d01c0340d1410b11001c0a858034011350710aa00c5400400c000380003d0f43d000340044602c0326900e10f001c81c5500e41140c1600a04400c0202c04d503002400d00401076185034090b06804020f810715020801c1d103155210700f03d4144038400d0b002d8203111080000080e041c0399078000716030203400080014180058000010319 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 281799676 1250 281798426 281798441
    0xe0c1c0c050a1712090603130c05060310080d0c030f03020903011b05040602190c061101020c0f06060111070f0e091207030903030801050d050a0809180f04050607020f101509 76
    0xd031280361407452108034420404d100d44041c100c03d071a4245186030300007415901c0300900741914020b40c0c404a5081141d103001d950090b000c01046030741c40c0e250601d101d4525124610402c0301c41e1064000044d0707140c0c0220440d0b641c1540540d030f446900e04040e11700360065448045803a40540da11119607045403a400c81005030000070350340329941c991a010000f4500444003540000200c0a02a80b60005400c40001c2040719210b00700500d107580f0710310985009004021b910a0b0501a11040c1c0d000240c000c20410300c1698244c0b5214040030315003e035250780f04207a01500d501074046180c140700c0b05441a029075800b0f010101101d008500140401601d82c01070380085000c20b0130303110f0600c205504980410302500701600e80e40c20300d040030b8442a035510000742d0041d002c031200003079501c0c80c0d4070b075515205562480000880001c0c1494600706e140b00030f0441702540c07640540000700c0c421f05d20101d400a1f403401d140000b0401c44801411540007450710f20285c940c030802c01040014040d00300e010342c19 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 281800926 1250 281799676 281799689
    0x20307140f0409060501050a1b08070803040c0306270611070215040e01091b0c140102040608041101030516120219050310060915050306060c010914010e0c1c0c050a 72
    0x2e446501d003107a05800c3d2800358200d541408000e05c040344180f6030207010514502e0a854103a00100428180000c85102e0f505025100c140000200b1007400404c007010401c0b644200000c0062880303105841d801c480c102507601501d11810003240011640d250040588920320000d285d250403080d03130000d43c46500080c8003140d0b0250108003000000c03ca40b0f00b282c014254074805002c0f47c0050080c100d00750444220702c005201450301008240030a070380280380601a000d00856545468010150101e00c08450440700c00198242c1c0c4081d5521900600d0301441e070558050911a00a040545c1c83d82c2816100d9111b03030b9406c0c42401302d903ca0201c000c40038003045d9110303181d5038100344107641415105500b104040c00542c401c100140703258216021411040c0b841c1a5890b611000c0000d8100d1140c02015034482d8200759501051200004d8200e05d4660103100030003d00d42c4140700304e5100c901c0c3d0040594881c80031210740100c40341e00c00d0b440c2c038910f10844a6001040e19580010005c001541100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 281802176 1250 281800926 281800957
    0xc0c1103030c0a2010050d0e1e010b150903030307080a1103040303090515011a0c010b030604060501051e0603010501050a031b0e011805090105120f1f05161202030714 73
    0x444a2012044141c3c03c08003614500410810f80c24050018414405144441c1e235450211440c074000038030103c02c020b0740c101079952214400e80142e501814110040d60311940844085c10300300f401d0702c002c40b080c1c150040c01075819a51040c4090b19100d41c000c2070660382d41d880b490786820601c1c04a000b1b42c82144a620001140809410114908417151100503d40c4101074014040d1641c50315681400e6441898400e50307440c100c0e0301540c05044109030060701840390506000c00c01c41a60491070688070240c0b88206104290301010582003800305e0034030740200c000c000600c00d07544560b0090290744c0071400c2c04512601e525980100d1804079003444000510078ad8000000f540c0c2c85455042158030000c000e442c010b0030407001030441d9106204075072203441059040a11080e042c044204902103000030780307c2d820400031400714544a203c2050000c10b140000103010741d01a0320402034044055590b060070003540500d5100250302c05008002401200c8050b4544151382e0030080441d000510010f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 281803426 1250 281802176 281802203
    0x712080a0909020a0206150a030b0a0e06130f11010c0f0c06030509072103020f030423060c0c090a1104080109290703020d0204050d03020c0102100c0c1103030c0a 71
    0x9140d620700e5000400140c0c010000c0100003640018029002942029180a881852400200038100581c4020b06e8880480200f0205207000da001d00c44000a030000e64800340d0740c804440b000000c409000403d5a603500b200e00c404a0580b1140300d441c5c00042c1401462600340b5100c00e40000f0010b0021180c000d1900c1043c4540360f4180681d0340c021941c14010000329040483d41d81c0a1813506032481c04400283c81200e0501d40f003044081c1c007201d85031040d241c0e542e407a1000d0501120318402000d122007601c0c40007409604214007118402038114000d05446600c90b4104407000e00040d20b41c0c0c4050751070304528103c2500342c000410040000c01e0000501c40c881780b420030074440c1000d0705001c2ea07180c60031504c0d15020240048952040d01454016621003c03520500000d00441e04403940240f00a42d81c8820560001111502028241c0845249803a645040b4082d203c000c800400000d01d02c0c980304000031117071170190341e04001c01429603007428038055886142007100c11040d180030500841 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 281804676 1250 281803426 281803447
    0x402040b031e091504080d060618150e0103020d0b1207030b0109140609040c21021f09060e01050903061f08070e0f070e030d03050910090c050d0302071208 68
    0x12464408115000c00c42d01070310741491a1510340d01e2545281c111010303548001800c004985080303e10743d4882e0102000542c1e11900d0003804c001d20850001d41c08181d05c1700222710801507043c81040c00c0071659070800c4402c0c0480044020790013407180304180d1501c441030140203a07200c9034600c806840d40c0c1c0040c01c6045c95414480c20704034041e841825001e00d0200e01c1c1b480c101c2d12590f09540402e0581e001c24081c0c58600d05120340c0c14a40e4004541010004010261040c4c917101d8600254021240e50340c1649200c1c46c6148107035507024100b004960b4420082160f030340155000140b0000504010f400c00185502003414401d0842c0d607401545c3c035a00043c400d190701400d501c03000c2c01207000105450780c01c1060302c05841c50050703c145d501c20900303400142d0180c40b525480303100c400c010301940c818180b00c00c8058041c1105036110b9441340240c200d4800d0030100f52050501154001c2e1002000601c4c000c18005645c090500640441c02100e8022613000e2400102c10080b81c4224401c0b56030b000c110745c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 281805926 1250 281804676 281804701
    0x30d030c030b04090c05150d0c050720011d0307090204080304060917060106120f0903110d0c030c0210021903110706050f09040b0301061e2c010b09030c0402040b03 72
    0x2a50540300d18900401007002c03840c1c2c05d0468003541c100f9269604114101020580d61703000d04d00d00c0340302050500303100c0c200b000d43c00030182c5605881598030f50707008070036440078085800859803840e000401c0e4035851540950030300d0241030341c1007010b010381d07a98a445104174801d030303031007900040c80603440000c041041c50360040782c1100401c03581082d2507140040c48043c0e6216101803041c2000c001040000f01400840e96200021503880d0020030407544055150181030f040f0001c20469007401544a00d1030054050010864213030346c9a92102c4034030740d1960800000c0c50010741d01d2821071003607081100700d0b4141c2d41c11403c5007502a4881007110400c4090311482c0c01c010b50000d0080000500a10a1001001c41034400f643c1e81194041491211500800d00501d05580681b002600030040318034800e01c1800940300b55225041903070a01d50414641011010746038614433120b00d0020010000100d5170b4000e4410781d40000e0954500ca40f1150004090780c001360070070b54124200209200d00a142003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 281807176 1250 281805926 281805941
    0xc11060903070803070e011e0c02010905030118060e01331d040201030b0f06031302091602150703060b040b0406022505130f0e010204231f0e030d030c03 67
    0x40c0000c6281c803440782e0350240381d07000290541060100340c681c4090b8903070248500c89582c0f4020702c0f5001002c02510402840c52079801c1f4140d000c03030140e000108803804c06004110780190042514601c1840981d0340000401c50400c035400555a00e07180858108000b02c4021440c2200000d690707401e150000510010541c542c0c00504a1002c08030300c030810100c204480c075030268090a0015990410202082c0c8445c04803480541c803400000412607001b02c40184941058000d86010150b80c1c0d500c0d241e03140c544198030300203000d82e11080303082c08451141640e907644079200349404034086960f1200b402c40c5410035003008220f0780b0082000e001790380c3e04111f0b8008108030b0010784000f100d44c0c042d00003100d17525401558010210f0000d00100385070b094105226140c1102c00420002155a252038003d41190260420703610b015000c4458000007500a6010f002c80200215001112040c0b0400005480d400b50307000d1102c40b6142124913901401142c20125050f1404202d5910030a4010129141c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 281808426 1250 281807176 281807191
    0xf0f010302010912030224070908010b060313020a1206091a070f030c030e07140306240415080a051c09030f080d020906041509050405090a0b18010c1106 67
    0x1100010405070380c1c040c1104080364084100307458564260308040741014100468115045c071003500c18a00101c650349101c0c420800d030750302c800c1036070303240e40c00c0500761080c201d016a4410018808110181d01c3c42c00c1031003000740b00030100c22410741d17039011181410405003000d0310041d80da2080c40d0103004115441d0f9401d0b10455400c2100f900d040000501402c0c218801002050b560740030401d00c1c24060307449800e0780750701e440864000030381d0b40f8060381d888038403080024000d01035a008180801041440078206880150780a40d44070010340900c0000d00c6182010440c404040300005401c010620244070036601401c090f10300c5074000701501c00ca101810401030304004000c5d60800226121365200719002d0391086040b543ca080b0041003d001e030052990441d4404030024001851220807595103620401e25100d02c040300b5a21010802140c008480301c8400d90085030f888000500070103000340d1700002c1140e1001e0ba8909801c9000d0864101c230f036200000c41c480140115080d4800c00c08a41d00420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 281809676 1250 281808426 281808451
    0x709050d0f110103021e0306120f07030809010903060f0f1a01020a021201090b010e0405070906030c090513080408070503060609040317040c03150b040506180c0a0507021005030f 78
    0x1525916900c0d0804a20320181000c0080a1008010b138807039011a100b007408001c0c1e0b50b941d50b941d1841c003c1554020b80d180c3c0c0c454040756480ba521901d01280114410303051002800301c0344d03d5512140d6095002010580c1080071000d0080b00295040c480c070381c0c1c2400402d04c00038203d400007241d403084032035550541e0100c0c00d4510038501c4582e80010b40661195064400c82000c0084070052409400c103100000c3c110301014002188140d010500548903038040d6049401440d5201400800c480701d5000141c500c440b650400c0c442e50b44507030807664200308910747c082107072226034890300c020360000d4000091503080050200000d15007003044c5900668100e4000d02d030ba040940e00a81914808804d50000e14440c0001030b003480301d000d0390721005503080810000134031090135600c001004284522171050303140402246541c10295001d01181c032401020002580720031203000d050b07800500c0030201b040003c01015005899240586000c0b80045e21030a490342400e4195000c0c2d03080003409005800c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 281810926 1250 281809676 281809699
    0x9110306010f0603090614070806030d03090b0a1a10030b0102010b041817270405010602060702060c090a09090b01090c111b0111030a090501081608190209090f070905 73
    0x81c192a0b80104031809400c0c00202c034520303031030a240503095440c50414000a030f9401c22404a411005013072103180100c0030b90340602c5140109030700f110742c4040701a08031020310000400c501480c2c0c0c00594940a9035040d0b086071880b11000805450f666054440003a4640340e00100039602405860000b49003102e06106040d04101c004401043c0441e02a02244c200d41c100a183c40c1807400b1036140741c600e43c0d1400401c0f8522034250f0081100c03070074082c0c0900c0c6410000a2040e10204415005000c80c0d8042c105680710141d0741c412a400060b811036200e04070000c00190f2000ba80b0170b40f40040c2c0701d02181c80c0d02d585403000040071030b030245a50070f060000184080c24400c1c40401d110102d8440c194135440042c4100e00122680b07612039400c2c2c3c2c524170000403501c6403c2d400c83ca1f4402158400d03aa1a01d8955591194000e4200340c0303418200441e0180f40400c00d0210702d044c50115950900c6801400e11045400040400d40159408040b0546041c280318000743d0010541d8003602003519600d4490 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 281812176 1250 281810926 281810939
    0x11011e0f020901051606140a020c060a1103060904020f030a140c0415231806030129010c05030d020403031e140909060f040e030d0b0f01021c1701090911030601 70
    0x1c0c0f145c8100202e41388141402c104c100002075011a20142031203841e000140f501403880d0000754062290503180c1d06c100380008212410342c0c001c0203241c020200049046403621411b00c8400600134008a80c080e03014254140540c0341005030502c901d0040c141c9180d58070062513a1070404400301c1300f0ba401035040c20044103011014010060460700c2444000322125601c210544948070382000c0c041d80492211601d1500d00c0c1007060f894011401100200055100350044003000c140c51065004080c4003d11000c00c0c542c00707039440d03000650003242034a20b130246071034646040382c0c0150400ca0101d0b000348115024030310b01240c0c000c144070260a0170010308401c007800c888039009182071284030314402030000380e058843c001c45c0c10342d402c00a03106103e540a1954101e84a401006040c190b052a00f00a10300c0da180200b03100f03018a0060b005000e440d030300780400c3e024005640c3c54141c140810780e1241180039550000190081040700d000140350f5507030f458202d040c01c00034450f05120346e00c10030052026 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 281813426 1250 281812176 281812187
    0x302090a0510080f1806041202010f0b010e1002030403060c11152a090d03020102030105040b1c0b1e130c1d010605130f120b0112030c060c11011e0f020901 68
    0x61003412542c211703911904009402c29182c010f50a85015140034001089040300b41c03000055401d400030b003e49041c01c00407004482d60302641600050024400c40050b0400c40720b003c45070380051041d40e280603120b44411090b030303000c1c0307003546d000070a02c44d03180701008014041c124100301c8044502903241002d002c1442140c2040c6100802221000110451003940380c1c200c0e60500e03070190000400c10b0b91810040d000750000d115042c00b41d801d005000a452600e08810014404a20030301140c03500d05440355404c401c0c0080100c0c109105c1316104030038916010040d9071240324036441300c1c007100c3d04a242c05080d0055a60281c24881c0c98600046091680d401001c1c0c1505c0652038a40d440e203d17500480c04860101c0d901108100d12501700115105008000410340140034854000381660307103031031511011080a8014002417040700c20000001c600d07400c100781c030321158907111400107034000f000b0b4211081200c030708070304040007070207040c01c04814040ca9218181d80b02e4118202506a80043e10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 281814676 1250 281813426 281813431
    0x80d0606090b180a030506070306030b07090815090a1709010e060f070b041502040308130b09060a0f09050a290c120309070e101d0c0403030c020f03030a0302090a051008 74
    0x200c02c1e1203d802000035846030b9070040015504441103e25070304112401400605541c081500c54224150015402a01607048034046800000003454221503180a800c400b1001400c50040d500415140e00c0105150000c004141d80740c016000c5c1d5a940c00b0400540f09100400303080d8000c40d01848202c0c40320700c03050141c5400e40e401c40d10149183e84c4030301e003074600781c0315250420445070b1001c00c1c040305001d4010302910011802100c0d07003840315201d4440107828000c5086a40c3d01c28003c00010005901c20081c42c644901d4504060090a460700c0000c0c8061905800c0007150704d03c0f0001508800305048074010f890308001c0c00c0c5a03d064041034280340c43d00050309038040b030403600102281c0c00c0d0000308049402000381c4003001c0c2d0107040c88051050100e840d44526400501d041400380034849880d00c48a000b24400e0090501e00f600e10340d015202c80344495400c0c2d030302119078925075400741c0303080c802410320844913900182e9610050713041000055031908014080e00703a42e00f00030b84607030b08080000d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 281815926 1250 281814676 281814697
    0x627060e010b1303081b010635010221160305060901060c0201020a0209130b010f14090a0f050403180803040e130f0f0804030606090c270e04080d0606090b 68
    0x340e031014800c168008600c22607100800008001900c1c6c98941c441c0c02c021981402e1034002400130540c0c0c3c285443c125000b1201041780f0b80062444489a030036040030750341491210a00160500482200405040b5500c9800c1c4c1c3d0001c54110400240309108500702c140d18034281010440750800c1400300302661414020b45c07040c400d100038107400f568020004200c401da40142001c0700343c0b44c0100d50031454032108804071811000900081100071414801e101501d50b000340492035540d480080110011003d4001100c2540e034903030108202031940511403003140252910748158100d0107907041c641c0300691161b00319800078042442516000f80076207800881c008081c0c0c0888865040012001600d00002070504260034840020060746502520441e80200000c000c01982e41ea203420540c1d80010f40200041c119061a03c107a090800b81070103142c4003400c4281003181c6030040c05841720400c3c0ca003580d0603070780840d80c80b04100d194003070b600241681e0319151100a1821181030030500030540d604 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 281817176 1250 281815926 281815949
    0xa08060a1518170a151104080d02010507050304030e100c02060a0305060906180a05101d061f02061825050f0d03050403030c05011b0809010b040e03090405190627060e01 74
    0x245c10034100354201c4085480300040c1d2544c0c46549054042c2d903044108001e0000d035083c0000924132a0044003505d200e603405440744500b0034024420403825a050801ea4014801406004009a02d903207026181d04021624000780074107001c03040103000c20000384a14403a9144121800400180e10841c0b5002030f50300c40b012541c1c0d10794202c0c113501c0d041c0b243c024583c240c0302c5004400048500c511268041d020a852020b5804081c254034582c0000f03500ca81c00141e88804089242001c0c1040200c000500b0f403000c0d2952801040b03549140d04250b855001c00018100c60184881e103007070f9107181c821040845c0d26140b804d00c1542c000d02540142d1102400b440402c40803441882000c0d00b240b085c20820b03403070303a90181c0c50700324001e40100c1003035800d98144c2d86000300140460400c0c2c401d40266084132801541407203c064200700c05070200800104d080302c40f0040c42000a01d0500541c2c018003074810460010b1110038100032140c2100429260505050607800c01859403551040d42c192860107201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 281818426 1250 281817176 281817203
    0x131103030d02070506010e060a1a07020d0203010f060e0906072304050907030903080f0c040b0f070605011203080c03010b3708010f08030f0a08060a1518170a 69
    0x6400c601407558000000c070b00026a030ba0412001140a81c140c0e8004070b0001103030b0700ca44041c400a03540c2802054180c0a02c40715141e0400c2c02030014145c03591000740742a000031250740c042402d545056035100c2d00181c030b484080c40810701d820206580009120000d280501d840c0100800c910401c907806400c1c544120a0312454419100480f800f5141c00b0301508014200340310010b0042a0146055001400401c082102a0070f0184a10f0180d5912044103091908200e8401c0d096030120485185c00001005040f00144242c05101d00900b03c1d08440ba643c04114100a0702c5103d009005000090003000103010302d1080c00f040d00d1326a440014101c00c1c12100903009421260840c041100f0001840b01c2c011189510000480c145c6811401d468a01603540000d11b5803401042020101070f0000e00102c0d4016110313801082e4408802050f076050745964000c0e804038031401d50307400400116108101c442403c410900301e4024455018908a265110f80e00c0a4944150150040c088000000c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 281819676 1250 281818426 281818429
    0xc020703050604080901110c10120207020a090b1f0801060c0f060e0d09060311031317030702100c08070e190503030c0705030c09190f06090c02060f0f1311 68
    0x588005158003008031121810305040c0b02d0b109800001c021400034a210804034008400403540744d8070110054020300b64683e0b101c105440c0380606c1d0301400c216590a10950026036a0503c2220081c0512034001607002004070612841c10400e160a4400c2840e50751074a660f507900c204480e0440b40c042c0350001790700c0c07840d1078072040701d024020000d070481d82480f0040c1441c00d00415240f00c6540030f07403561a0055944c0106070103990082c0ea85c003c02c1502840091485103446140002003441120812480200d4a56a5006400507180400181c2c011341c070702da0700c0c240d4030710a00d021610182050f90b902d1510060081042da100e401c0d23075010f80880200c030002a9240200c140141200400b41c1c4d407281c40f44180c8603074031710f4540716040c860b200741260883c040c1481d40355a0702803400078040b0300140b03406a11500261518154981549503540800140c4824501c607250f03090113954060241070a001c4102a185030f070103000e41280c82412024005100b020601403941c080d030101d90070031483d41000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 281820926 1250 281819676 281819683
    0xc010207200102061f17010b030304060c0309050f0d0609020d02040c050a08010e010e011707091107060c021b1009080708071706010308121314100f0905030a030c02 72
    0x25001840386148664440072154042844589000c1c00e03403c884040c3d50394180b00c11900b0200d540c102603100000c0d0284418401c007114032198259460000c030309003e000c004645581c2c41507005800107041900d2060070175600500c1c2c5002040101e51400c1c9042103800003070100300035a00b000b0304481e62140100110348038040b42d0300280e600200100f03c21500000060051341c002048000040c1d0000004a01c1a9400c45400c0c143c401440030081a40e08010343d5481c00880b400304060381d4030603060300140015603070054040100c0c50143c25078a49a203840c000042d209128003000641d004030b40405c0b0450200c01c80c0d1100743d04200c82040140002c03840c19a4040303075642020000d030284002c08182d4840014041c000c0ba140f030451401c440165040301340d2602d40a0100a180d4041000101110000314480c1a040303000509103a01500709a6107811014040d1320118546401c03441c03280700140712511070704c400c9481c14201400745803103580d6066128403a2000440500d80d5030140119914800c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 281822176 1250 281820926 281820937
    0xe06060313020901030b1b0304051c0c0b0a0605040c0206040312020d020c100c020706020a05070501140909190e07050a0506030417030705040806151f0302220801050105060f030c0c0102 81
    0x6009140607503142d00b0207a00da60310444100c01f2140486105619100c0c120045070b2140f83c1081c09480e4152000e82c800203076003085c0c0000b10402406a410750041004004120b004840304840060102d1810081c801030f6000f0900e0b82c0255041442048040798103c40455440d0401100040cae0314030004100d0310080c051000d2081c1c0c944600e4070849038902e0a0752282d019084960200c4030321503550b8204a0b0344825203000105503030094101000194007508140d0308800b507000c0804c0c200904d03200030410650085600d550710a0121201c490508a548500c2d140e986002d0003405540d070801022a0070307401584501d50040800000043c144440d580c4444104402c00100c0c03942c900780100c0040503608240107900d044c0c0601004642115044110b501810001820540c80c51004010f800c00ca07003034541002c0140b5808000401c03105910141c122805110009203500700f50070555820300712a0160015401032904000380407000c4c0340d50302030380e61204410315803541d41d070000c02100c0d01a0084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 281823426 1250 281822176 281822179
    0x415080c0f0a02060105090105030705010507060209031c0509010f0207080c13090204050408071b140d05010e0313170c0d0b0406200c010b0306070806101707081605040e0606031302 79
    0x115000380c10a6020a13400c3c125001240c0010301644c9030000c1648411552065070301040042144a0018090382c0180c40004001403d48204078845125852102402181c400004030b0000b101140b668214481e001c1e481103038801094103a0a10101d203540b400d002001d02e106101101911750103c0a50b00b007442d00c07a81c0640144203606062070f242da15908032a02c11941410840201080400e00b140e0710300884d013030380440340c06a0390f80030107000480449060682d019526180319111041040004200c4503502103004040c0501d041c410610034440100f6a03407558200307500c8401d10b03a41e4402400390f00c642020045525490303618064008103038650310021840b941ca0242c0200304501c0c0050802c2150185c000c0c05240081010107846820403200d0344042014200410002e003030600c000d50244c5541e0a150705403c0c0079501c407240030f880c01c030303010400281510301b080b0450361074256600540c040790800c10301f058104860700e440804000c00c40d44c081d280c08400a0084075020901d41d1080f81c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 281824676 1250 281823426 281823457
    0x7080c0f07150e0706170703050c0c071502070509060d0219090c020c0f031f0c0c08030903070c08070b07030536030d0c051011191e050415080c 63
    0x160040442d000c0c02008405015900401c60006040e5010f68035a0b0501301c080141412180da4244065000308005802152540800c2c8030381c4414090400c04c0e03a01502c41c500300481549420714000b4644601c42d00058000e44a00092101681390062400c0510342d0440c1c0c1c4071951410081c1d00d04ca404803030391000f0038107422b100100030004d4002c10b07503607901c3d40161f8084010007844405e0646d1903d2086149544005180078841c4680c2a50312000000c45c551070051220640764030360082036041940d0001c2940c1001844400300b207070003039042c0002d110700406400c100307242a000c10224007605802070140900000c1c0d0304031101d148201c10180c1095032070b0040c0c5d50103d800c0da204600040030070840c000c1c072810300702e40001070042040102c90b5074414014000c0c00c641540c842c01928070900400f00c00030f810310008070009054050341090031100e039200e84640c00c7d014190b100c0c02074502900c4040c000c00b00414886c504031030380b00c229680500d0400c40c141d0b855442c030301800d40c810044107510300d10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 281825926 1250 281824676 281824703
    0x8030910031b08040302101a010f1b0b012c0f0907030b0a0f0c03022b060504020f030a05070302070206030a2c03040f1707180207020a060e031507080c0f07 68
    0x1600f0040079070045010341e080302c5454100c02e50f10f400f203501682e40b43e01300b10040401e20b042580300d010003000958803803601341900c0e603c901c1d44541c1e16070810030448d8802143d00c0144039400c0303100c0580c1540001d2a00c55802c1e104940303810380d0340c1007002c0d006030900016100028007501e0704022150045501a65103d010300d0300180d0000200651f110301500b190030b00c001c2005d40743c071074000c0e83d60030301310301c8000c044dc40550a03101e100c07104040d09965000751502800039561342c452010700b07030020303000035826540c0c54034203000340c00c0b00c400801d2403080c1441808010003607144d100a980d031001030401d0010f101554007e004600840882007503440e5041c1c0d81e1403c0816002101500c02c132409140740340949034640080ba5842e9140c250414080d501514042241c5091005e8050018201d03100043c80c140c0103030041444d41040e07030001004103100c00a2504036003030800180b004600030650024603070400f640001d0409002800364a0300241c0422002c01150221088801c0c242d800400c00140c0d6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 281827176 1250 281825926 281825981
    0x12030c0c0503061512010501050a170c10050912190605091e0c010e01020601050607062406081509060904060f1514030d0815060304060905030d0b0f03070803091003 72
    0x5843c03101d0344c54020101c0151031150701d130050084074142c6000030310b40081503090581004404085e50840380c3c40c1c0c0b295824103801601c40c401c611900f9501c035a2643d64500b004014000140321214415807164031141d120016814000002903409610140118054503180d1016141026070840a8034003a0180c0b0f41c104074480011b13402080801c01c1e21303040201056a001a81c0b50142446100e80101e01000907400140b12a4825500380c03000c4407070501c0c0c24100c031800b200b81c0c42c6540c000c0000701c0e03403490070f04c48801c0706041e10044c14901254105e89601d068404625201f401030801400c4944078000207411801c550064408a0910781e940603100780d0703c580000b0f28202c146c2942d406400341658034407907513215400242c07007096039401a43c90740c8030140500c1003a81c001081902e26070384d1000c5a00014a044c801442003074001600401d11820030800c01244040c0d0b440c14900c40d501241c1e04000500011003a1007021034101e4580b840800f1001054015107001400c8902e01034080d40401140d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 281828426 1250 281827176 281827201
    0x70c0203010b0406120f02150307020105040312020c0a0308061521090303061f02030d090506090d020708070504020f210a0b0a230a03061b110712030c0c050306 70
    0x459008500a0101040d20020300c01100e00354082c403465800300f0304e0004042400700b40c17aa4065807001d0b20300d055a80c50414042c1c5660001c1c1d611340010f0351128240024954816006407012004034401c600e00a01e0742c1c002c41d030f1407012a0b001000c1c0101c0800040b00c903624498210b580c1182140100e946203c10010880d80803c0302141011540c51080840e90000000003568801c900c05419001451091100050041c00700710600c82140b00801501c8070b180414020703492018410002003030542494010740e030605030404001c80071940101c0b0b080107c04000103c00080707540964006940301c440980141e10740c450340c141c92040180c0e24141403c1e130940c1410307140c86031010400070060121038100304240c55115104810f00d0342c03603050b91800e06e888d51000741000c1007401000041f05a0381c81d50390001344c8484c680d203201403858401914080d1034024004420524114000d40389203030600c0000c0c00c0c0c00c98100740c09010004882941c0c02006648a080c1000d07000c01000c4440f01d15041d01140700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 281829676 1250 281828426 281828447
    0x506190e0402191128060b0409080403261c09020303070b040b07050c100519090c140301060315020a050f0c010f1b02070e07050717040f061701060e0d050607 69
    0x20308910704d03510960101040c20504040c4032421181145015032080c4000c2d00c440304166002ea5407a110002c590381c4610800c40011710414420f078682d803660401c245013040b811a0300f41c0400d0410354009a0800903011101c03500c80d00a03400421410a44a0030014050190025014400003a4031002d01c8107503aa4944a2440b0716600256035407107050440e2103000740303400300b031059100348811417a6103180c1c1c0142d40d00c000d00d03c101000d080d5940c00b1301c07400c1c2e0701e00044c141c0e40d40c00d5580c030901011030303800c02d0305030700742c03403e80084c8005440c640d158001d03840c080c030580604640c00303e0484001c5104808540305486029030081c1c035103114500050080c801440d184040300d20f003041010b0036554495020f05c08005035005000700720f00c0d102c121850200020031703440c20003034104330b00000584482005070b1030030360201842c1c3e269820252403010401054000c0d0060005072040c845401c5c84484038141035403c1c0303290085e0f2217866880400c40d0111f4050008140e070080c0d4040100c0103078000c10004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 281830926 1250 281829676 281829727
    0xf0306070e1c051f0506060f040b07030c0b0a0e010506040908030f2d0603010b0d02100305270703110d050a030c0614010902070510020a090302060f070803010806070201050f010506190e0402 83
    0x30740c1b034030300c10098030b407240703c4c0701c8200e2100a000c01c00c40c00080d003010b002c03c10300905001020f002103503101400c01408850712000380780d48840d040e90b0b5103024468158040720030b9804020565840d128900300e800300500500c91a00c2d0440064000c1d684601664501e0f125491032050807040c40d4481c451050044864501130742c40c2103003030007103440e04080b2911070540240038054007104440b01200901001800c4041c0350651070781003403070b50040c1c02c0c20782110750403000648035650451800c908000224a1184d01c41c1a421005001141000c00d012403103070780c1420036142003869440c050004d03001c110b16040701a80350400015028840350021300070a4031482c19900031741c2042c6608401c03801807260347c40000321307490801c1c401030421310002c2c40401403800c0d003142040d0301540e62040d1540260090302060308440d060010b03180d02401860703001502c07000340c0c21042d030611010a11034080c1d01042d0a2040313108000e041c07141c6c00f6084021112a0142080d980c4400812074070940340e014000c402c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 281832176 1250 281830926 281830931
    0x70b01060806011809020912030409140124110c090f070e010c030e060c07050a030f031403010303050a03050408090a031415130f05120a0e0f0306070e1c051f 69
    0x10181d40c411146900c130801c450041d0b20610b0700782a0288000d40000107484d821400428001104d22420806071000703241404010400741060007400e011000103030f20411400c288405241c104500310344d50107116840a240141299403e420300c1454810f41d556000e401c43c004500340a800c017008000c8511414082e1640c070042200840111591840214003500203040500c042d1001d240ca01d00030841682c1d8442194691600e400000e011080c031540215078800e82c66150800705a00316010740c90140030400010700355172458802420f6803160f51440003c042d5200002004c02c0300c5442035803000070024140d0b6501304c2d10b034070b0b090028480d030717016101071031060460004a524004415074829000010902e01e030342000d540740c10190148540880c0d0078020764400c3c1003072020030341c080c02800e040d41e83c03240c085032071a905100c0c0750303403034480003a0003600310404004105820150240d80c1e00000d032800c130020300500c0041c109064130801e00034800c1c0245420510030301300740c030f410180c00c0400341001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 281833426 1250 281832176 281832181
    0xc07050114032e03140303090705060f2a0a03020c01110106050f060304170a050a0905010c02090f04050309060f120106091a0a092105060a0b22060902070b010608 71
    0x200d960703808120b0702510002d003c500d07048010802c000c070783e078510040741e40c40448490701c035174401060300490807640c481c2c0c0d4000f10400c15110010021b80004040644d40c00303207046010401d146403407113111110000c0c0000f41c6480c002100c1040c5507034043c1001081a00c4455220b403074029150850340a005001854103514480d50302c006124050440340020a8404411f030380e0800d200c0b0300d8000070002c0e02c00007001c40b524044415018000d140f40401640c030a90780720501480070f01340d0500e5030802810800181c0c4400010b8a60241c199041512219081807540c0c55140407807551048804494110201090941c0900c406802404840400711400103044c0e80b91075080341c02c17030b000b4801c40f24110b0070700744086941c1c00340394000d2000307114070700c2c10301c54054540d4408101144400002c120103090f0240c8202845000e000d0ba80e006921043c0c140022910a00050f199090340c1a86a000c40711002410408089940c0030300c0041c500c83c10159150740c402d081c1100c400400f4480c080208080500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 281834532 1106 281833426 281833457
    0x50a0902041b0207060c080a03020304020f0418110306040b070507050109120509041d100c0203071e021c03022d061924030f0302070b0c070501 63
    0x2414110b02c1c461020003071030000e4a81c070200030440350048a0300040c4080003100c4c0704001e0b40c500075032242c541d800044d0103c050a1917050703006180000d24010340c0c245122580b85180240c4000790b0702d030354800605031030344000c8400400d02d1621100080409020b040a020954000c1000295104060b036900319004000c60f040404a0300100310401d1601e081d010b000c0d0f08000301ca0380010310240d00700d502c556039030002060750300c0c00d5145c86094548910030420303500150381106060058106074848052641d1100344241c0c0181810405482400d0901c2c2804419551590060241240c8114681000c1d030601d448000c2c214403004480516501c204807040c0103820710b40b00d201c1940c2d9400c1c0c100b400c444c403030705404002c00000c104074490034025508103001c403900000c140b04d07485420b24040307051031032a40041c140020081000411404d0004800e030948100382c07945000213001c0c40303 = true := by decide +kernel

theorem cover : BRFrame.Cov 281654676 281834532 := by
  have h0 := BRFrame.cov_init 281654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 281654676 ≤ n) (h2 : n < 281834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
