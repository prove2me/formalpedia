-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4234
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:57:48.65398+00:00
-- url     : https://prove2.me/submissions/d000d2a7-0a08-4dc4-961b-e270d106de39

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 761330935 ≤ n < 761510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 761332185 1250 761330935 761330951
    0x1a0105150a030f05041118040312020306061c051b0717250507140915012303090307062702090a09120207050306011e14030f0d050d0c05090d0b0406 65
    0x2000c244c039030513903003501e00e100311044024840c20000d46001507441c95150111642c100380e98000c216220030780398001c00b1640803002c500359540b10412607055690010644d03040070310204440d0020502910b202013180f262010b1007604170800e50541e1405500440c0c0c0301580324102d03840082561048410310950054040350080007800e00c0c150310340c07441c0590014039001e81415144200740e031000028070b00c2000290200100d00143c0305401c5121103003880d00c1c101c144914800a035060440c07440c9600640d4001c403c1003406800000600f8103940988806d01812146144130900703c6da11960100b036000f20a04c6074009400c00d410310b150842c0440500181540a03519905041d16042c1511700050f00f043c2c00c10089490100052409031001d14240d8036220701d9030312159482030140c1710340500344400c000400c14540e000c2c09000d80e1044401c007510780140510900820f1030f440514034a900c00d20740261080a640305405884c1da41402405040c00d00740640c8a06000c074034004c1044414075203500d60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 761333435 1250 761332185 761332211
    0x12030f0408030d0605010309020d02010f1124060105040b030106030c0509091905060a0528031e1406160509030109080a030f0f09050304031403251a0105150a03 70
    0x400041c5529005507031514120000441901d0641c1c0c0300e03074101424a100b403400760340c410922103a07165090819034002004206c090302d500e22410b0040300700f4050741c1100c40300d1440c0940002c4c206c4480c1354082059546542c01074a042c0501d0244003001841400144401e500940c400441c4109a090135414408488002010740400701c403000c40e4899500081e100b5141503000341134100e42c0894180402605090200f00010313040c4a95408005640201c0b41d0003038511200403014542085000003480400c4800c402c20244000d000c503200562140250707020b46002c90600d004618007c6030f000c0b95140008101d805410041c0c002d82d2655a43c1004e50000f85250014141da02d40c684001c1490750742900c1820031550f000d0307840d0081c0303030034506180005000802124141d076070008240310f00900310301c02645140203105540c0000603044081180703811034005100c0345a84a443c00c80d11a664200c00011007000078418540c01020003940b4078038280c000c0e40541240c112514000900f600b94041c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 761334685 1250 761333435 761333437
    0x30501090f02190b0307030f020c15250203040b0306130e0d120504020d0609081e0702040c020c0a0b0c10060e09010e060f0c07020f0603090717010902010e12030f 71
    0x8212034410104a00d2021401e0951089010b1890743c0e1072048024039280c1c3c41107003840014550400c16941e40304813401102c00e07a05590103441d1503000ca61055849101f512422081030701c202d50b0030a4400e400c4070304175143d070002c84404100e55000e1401e2030f20380481d00320315800260217160306c0588031609000008407445000c02520600c0d0040080c8003005001901d0410411600c0c24001c1c1800e01b0400980ca5102500d41d545500810008440d0f400f400c0401403801158000c1d061503464602070002c0b50803150103005040d0084500700604d48050100b641d031110007038602a0410408030301080b010155001610344498500107640843e5803115280007212070075082210500090384c00e0140b8401c0c24030401c02140d0014000b0005420506241c6003522001440c2180c01d0380001510402c54480c414030711403404000d00155203c5c200049400d440341020f00035503415002c0c2c4400704950000502407240f8103034040e150900c624041106111450344901c019030194402045485200101c8070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 761335935 1250 761334685 761334701
    0xa1209030509061c0501142209020a0305060402040b0a050f09091c0804060c050c061503190807020112060506160c05060a120b0316090209010c06020a030c180b1210030501 75
    0x649113a1a04164880d850486030306811a070520310340c200018045032120801c280d064052442414480e114817083c0c1d001401540d10002e4015140c66000001c015000405e18090b138400c46003400022540310a004250501e80301d45035000c0b50170078906400342040715215400c214014142e9161544030301002c840f1901d10b50203800000c105000304001d0000a201e505148038192808a2501018031407499841c40098503420345040385040003010382d502041840e090003c11005031810700c09178240a40f15030041d80042c0d002c42e000c00054214a0264495542a200d0041000382018400f407543c4991600354601154560b2030064089041c4d0f0318000500701da013003195124141801802248010703200703810301690190b440501d419944000702e0b00c050060701c1d2031400041c0c0300c20788070340106c3d0041081d460160981c0c0c4005150352100b945600135441c02d45a40e07c4000c0c61a848020300c08201c01c035842100707401c07401401203000d45900201d0150b0010012101d0b60f86581d2a501d5103401c5503101c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 761337185 1250 761335935 761335957
    0x1a0111010b270105030a03050405130212010f06030f0501030209180a02120706020f0105090a02060a0c060c090f171203070903240507020105060d06020d021c0c0e03030a120903050906 80
    0x414042d031485512a001405041c0980c081c12964031a690050035a018a0007440e01c6455241c0c0324408098003a4103489681000c0c0406002030b50b911075064a803480300740156400281011042061400382c7d009250407a0340c003901240d03856a0380c0709030805c800b81c1050300c0f001034010307410458050781c0e6000c280d0340c01400c6000907040407841d000c00039141c04040101d6a036164180800c11040030400301d02c0100c81501074400903603802480780c04172003810765414010040c500c0c2440303a060080e4015945c000340e03110740d070030b89140790344864107003284651042e03001e000780c0e0000e4664941e41185030080c5401115504110344040e4482e90388142c40300ba4218203c0c40036001d0325200b4107803c2d207406001e0f044000f82c0001c201ca41050004075041c5d640001700030300210b400094644091005a040702e41021041038040b1034820b086001202600b10750018000007139000010303665070320780030040b5000710040f500c9040c0c0e44550b0a0480000e00b50450058081c0003003441400c29640701c04004088038030503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 761338435 1250 761337185 761337229
    0x80406020c0117070503040f0b0a050405011d060c07050c0d08090a060c12080405100c1101050615040e2223060105060406080a0b03030721031a0111010b 67
    0x20014020701d07011021907182d041140d031801c034400303206566a0444d0085070a02d4a1030b070ba40d949007800780c4400301240d4000c020a1410f020001c803800070398000b9001d50321500091143c0001d40c803001c0450042c101200003680c1010300801e00404403100204101032258055401010143c1e00150799400024810f030340040300002c144c40d50745440c41c1008041c02890a043d20403010741d4030381c03400b000c90400c04041401108c00c08942482000c014204155042610600c6401340c0000c0080001894074aa120150b007003002140580c5007401d0b14109840404803054105858883c0a1180c002e015120400503289035034100680c0402014896569025012400c9d442411101500d00405c07814082445c1d50014401030203141c0da134202f00c400f100e9080c41c05541a440d012401c00c01011034500b00341e414440001c040081002c0082c071400044c51409e0a158500a002000d4080da125100034007540c0c010311000c6e401d19801803065030b0184032440c1c000144903041d540804d0546268a0b040101488 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 761339685 1250 761338435 761338439
    0x60a080a150e16140307080105090a03090f0510120906110315092203031b0201050106090611071512110301170307020319150f0606090902180f19030804 67
    0x103040c0c010024400c0c0090300901c402c0030081a9100d26003184c0c0100441c128241304d49003510fa0342082008007030308002c0000c20043c1005c0140310313514407000400b200030900c5000000b9808946c08105401c4800c041c0c565018061407220440f040460030005103561961001d0032400701c1e01c5031045000781a45a000250343e81081e10182c6c1c1c80013041d1340b0741c6110b640d03d0801c00c41c2d02c0011603c80c0c0000601c504030644072100700d29041d07010780407811658420f42e54080c401480c0d540e054003c40d04a5a007074030b610040c1d40c3c8664084540880c0d03026510000d41c06201d04010780c02840407000c501917090f103054076410b040241c99a0071358041c1c0024104901c0040010f1084003581150040c2d2194407100843c6008072541c0800d80342c8000c90112403020129440410901602035042c0e1591900d0000421820341c908100c0e0b03004006a01450001030f100c0d050118803580a80308940144594041e5115840c040e10108007106480082c1203801c00030901c1c2c1948800034444c9603001442c440c1402030b440354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 761340935 1250 761339685 761339723
    0x14040e0c09120604050c0f12010e150108070b0708070602042606090a35030702032212060b011806030b09150d061a0a06020a050c01050a1403060a080a 66
    0x1070140c5001c82c1140c00040a01001a80000d14a451010203aa01da17400d1040702000034141c14445040c0c0c640c6500f80b1600300d60664010500240030804084100b04603600d8000c05a5107280d079002c0e02c2c120403804c100d5240415031000c041c2c401688034000240c40e107a1501c154800621107d42a0721603569070501c10303100d03484280072481d030000441008200c0540d45481310580c0034281c0c4840c120350ba201e513094520040c03402c0d003842d46500d2000382c140d589080040000f50343c1e62092a421903c6840480d160350060300f042e040100700c9a020140540b0702e0650f4403007900500300d14183c541800000f46090540c03517003036051030f130007002c2c40e4400040c1e00c0e041d1414042d05c940010903038100364160000c000d06c17a640e880401d4810682044001501003072050440c0015034100d541594040803004000400300c0d4002242d46c0118807440036102d480a46000646039401410301d09004141581e040082d84031842d000303540d10900040000c140195142800d074201042c14005803110740c40907070315044407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 761342185 1250 761340935 761340949
    0x6360302070602030f0702040b0a081603050f21030a1b0512250f05040902030103140f15130203100608030a02060c120f1801050f06100206090d14040e0c09 68
    0x10302c03490000e1480d2032103000d4856414801d108009200300c3c0c5d54040e20481ba00c60828290203000810200ea540e182c5801581d401108188000ca0351842041c24044224501090740302130082060f08100d000030700001e2034412900300400405070140e545c0b001c500000515001454041d850351a507543d01c2c070b000501d007040c0150080081a106494840e5041206444211003400f0a49460040c281c951001001c84a9220720b83c08000700d00d00100010050080141d186502c3c00c035084100c503000820b5080c4151100c2018580802000c07a03080080c4607016114898403009100a083d90510301200c0301d00381c121075280d00444d12507480032450451072501000200c4e00010084441410000e044900411100d0f004000d0000703895458046203094490041080125081034000e0045252820410b411004103d030000d102d414181041c001c201c4c00450b01c203001d051204050b00b041c08140d10f0588964040311081c01c4000002c20000071204454003c482c060400440c06a903210701d400100014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 761343435 1250 761342185 761342189
    0x4050a240c1a043207090c17011d0901150306020a0210020c070603110313060b01032c1b09010b0a0e0303070c0330030e0f07060e1c030206040636030207 67
    0x200d04402c0141026680015458111600586c001c0f40e0344200d4007080305c1c840c8000c83c004040d840c06030008600d442240e001c0b10407059a42500f441c295407030005107801d03030308c2c070f90f8110350840300600f81880450b0164006103031802a900480300b425861400345422a800703401172080c941c001080620103240e25020350350a103020f441d00c02e4154284000f14071030910001c0f6000b400280c0d039440d40e09a90f4042e40110780e6541c5c10186011043c00d0401103000005010350802c0d1070344c0528503030444015000b0040c5002c854018014102980c02c11219982c16809014802e00380f0004a96030009075508100400110f40706640da11480c0745141782504a10580d60198020120307902d003010010600d2408903030300c100b054900494820250119181004000030118105000d0120041001c50f0000184c81380f00c4010340d44881b1400e407141949461841019000340144c0096000c10040b9006400c54800707001c2d13034810600240000441c958201d0b00d00042d540808410082c040c01b499014410040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 761344685 1250 761343435 761343503
    0x509190b0315060a1a161b1e051c0b0c070602030c120a0216031809051e0a020903030301060815030a0f1b030c1e090e010204050a240c1a04 61
    0x246806640c210707082d90013a216141c6984010450200500007c06494050300030802c24079060319854000c858656107005000c1c980d08003c420300001c09040c02040f0b8800c44501d00c1d0003030740040081e518004071200c0542107141405c4148102d1003c83c103144000c5014515000d411075680ca5035800c0344010740001080f1141e01c502c1441303507601615417144120031f007a52514001c8103609060104900c6140590000c8460302c0c0b03094100310500443c3e00b00a100c0351030481c03024a40e50b03903031a02d04040e440340300c030610303050780090004101c0702d0300525801c1e801000c22001e078a068032002e0f010a140a0500409450300c1d48600b444406201c80281c980a400003981c1210300d2a03421a1505a14503010340710300c4d00e0f0013001c901640d02e880c001e81e50400161902c4602071000d082e08a903003a010b500300f4000d8078800c1b401c900e40010044890115544940b03400700e04d1001c4401d00f600180c0300d50122401c10386486d10200b0100746562070025100784201c0c482d800d1000049038862105040d134055034542071b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 761345935 1250 761344685 761344709
    0xc01050115022a0603091c180b090a03062a03050f060f1516020d0f05060c03090d030903050f030403170109060803040302060c0703050601120201020105070305010509190b0315060a 79
    0xd0810401c0b00c0100703425800c2503461903603917100c910031a4900402e26035108580e80701c0b181e5591f21541d110349004c00072000c013003100301d60940780e0600030018401c018040342e0180c550381042001440c0c0e40c000c600c1024140700020b0400f44121036407209520795120042c0043d0790303402001541412101300c41d4108505940720411440c440021454505801001c2801d5036401300d428407c13901582c2e0880340842c3d0241509200040390320780461001080c1404070307400d001741c0f80066519418030b003d4034405c0c07080c42e00400c11201400800d5004012448081e03040003020403010800054003001140207912958900d52840b28082c030441c0341d083c06030811054682044010410300d6800019901941d03011100c85580d4400c4071002e51030004682c3c002800c50150300c2c0005000121562109a801d000fa0002d0042ea42d42500032411280d09020343c03940845200c1c0880c0394000c0409040c074104158041c001400c9421500203841c1900000c555151114030008000043c14190400802865160014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 761347185 1250 761345935 761345983
    0xa02060703111215060d060f06030c021e0a06140601080a0b0112050c13060909150302011d19172107020d0c030c0902071b0602060109110c0105011502 66
    0x15010603c00e00c426007035802060360204408210540181d100011300405c0300c0ea80e0051009031401512142c41442440740b030026001400d980a406030348015190381d4043c014400c17202400c0b040304042c1c451003610912490081000240781c0b807007a4030504807100c04000300742c40c1c2480010040340b001058419030a0030407800c441e259802c20808610090600004229541c80303590380e80d000e0007099108200c03403005c1c0c800015615000440b600a6840c1100f0500c03032200000c0e1190340c1d124045c03000030b0000314806034048c44035200c41189541010700505001004182403d44518004141c128100103044014462402201002000541159609092040342da020210715082c003c046010b4090703103041948030108012070300703110007640d0700c1425840f8054450000c400250840d060480f9180d03880c007040c0b00b4210015800a080316555401401d85a0034007000c18041d1481e0100c849080c8424401c05178050710a0082a0103060441108480c6150041c0000e00d041e914000c2961103034004500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 761348435 1250 761347185 761347211
    0x9030f060203060f181b1606060302100903211107060206191103070c02030703140604060e030c0c041109090c0a0215070f031508010c030e0c01030b1305041b0b0a02060703 75
    0x201c1750380014064110744140c404ca0710071408512507150304511040034001104200306c030703075400102070b00d001742c6251242d0480c5417429a0920b04a01001c0d20034661504040060070420504041c00081e030b1802103550300300c400d40507190082903006140940c0140301000303000003e2100001101c80c0070101400031f134511100850640c031016010720100b294811040c01552000c0080900031070740b1449000600040c00c86098136003406640c11241e50342001d6800c3c80c40c120001c10303146000b0440c03018080c162540c0c01004020202d484507402138002c180640340c030303c1e601e0700e80300c0348120140c3c034441d50365000d00f100080c2482c80090303a0404503030300b400600c00d0f86d95209010354414096800c00195045401913260300001e1254480740300c643c24400407501c030381c5d4140c000f461481811411907517007901d400c0045d801d462142c12144e0f04105085000004a46642c11141d04540540c2240510240c4141030700c01d00480d90300000c000d0100081c01484459042103003581c0072a440c5010410010300480c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 761349685 1250 761348435 761348479
    0x6070507030507020f01050c0f0c190303050901120605131b03180b070c140a1104110d050a02120f15010c080706020315041a01030509010b1f09030f060203060f 70
    0x60f000c3c0c061540200b004809901034011540015a20360490356800400d40030580d80305418880c1e24040e201d941c0c0208071500b07441d401c2605403645a100e00c0e040105031401107504a030055000185544c880c2c0c0c2c0007406407a400945986842c0000e4003240500d2881c5814903050b0307050004408041c6060034069140b1071040441c2000c5510003960011030701c5200040301d603c0c2c01120007a1200704084041d00b00c1e4a000030f0031650a0340300b1250103641030707241c004100c1107820807111540208010440300d01820760325404254004003180005080081019102c03201143c00c441d886a0401e95400788400180c07100c2c9403100f40c600910340007001050300e641e0741299020340680102225004000300b41c007000071180c80e0300c035580060b008004600c0130070440080c0c0487c030403803940401d1034003022464080040c09040b0042401030300d0801d155400a048094406900718414100030101e800031000a5a580040c4c211a015802c0075849040c00001c1000b82c1206034109071041860501044418451103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 761350935 1250 761349685 761349697
    0x4060207240c0305090307060314061807200f06043f051e0a0306230d080c06040b01030209160e040f1107150e1b0f1c050d02060705070305 61
    0x442c0c000301121070307840c05440c94044c2c4a079044c0e25000d4001e01080701341c0d02d94050804030345400120040c50b00d9260600036246c188018504607030017408000760800740a0491504010900d940c841c8441303480704030f40344c14805080c84820080c1c1003803007480107015151100e0001ca0b4460740d4140710400141d0442e98500030503040100081e14186610a1103502808c00e83d52200c00703403552050300020742c2400d200247d01c10342d142d10109240c0040816984100010b1110400701c00c4a1003450b200f000081059186419100b21741d501010800d1000c090001e008550040348200315200301941944108240f9680040c002c2c003000d000c1e071413210f2201d94007460040ca110000d440001c0c41030390000c4000e002d8181d03542c4d2500d00040000c1c0b0701e000c10051806510324452500810844103c8255295843e035015440c007442888030360b21000c0d11880d01410340c50501d50001c18241e40c9103008621203501d11415401600d094204021450340d245d018040300b94040146c1c81c0491600d070142d41c0240882c0641 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 761352185 1250 761350935 761350937
    0x20f0a02091503060a05060907020c0a1e0b0c0109030e060703020d030e03040503070602061005040c08040305250f060b060a05040b0903030706141b120430050406020724 74
    0x1070302003800b4200032a0801e40307011000e019540a454001c6803072010f400d055070380a00902c80800018401480800d1014070010000d040c012007906c1e006141c003d04205003101c0c0d14050740e080d000074521001070010b0242141c07480020545a155007406851700720000c10090148108001c00c0300003981c045114120506a403c00040941090300120b00e54015604055058840c0c0c0170701180031900020424407400d80c03e001c034100c4035110401d21040c2d07804030303200c2030226070039002180019018402030112288402202000d088803000c050743d0500a090302a40c100141910010502210703000380a0000815142e15192a2308100000d089104601c83c2e210040000700d80f00030150350170b00449100540040c014409480d082d003008003040c00681e825107060f080583c40c094201d03544001d0703410b18403403040600e141d551107890b40308141582c074145c0100040c20034100402860003078440ba41d6076029540d6282c480c0c1c10014040e140040c030740c0144821110a641217140e102c0243c006007421002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 761353435 1250 761352185 761352199
    0x9320402120919170d0e030a050403020f03010204030f021c170901180b09060d2004180608062d09031801021c05160b09030310050907080f06150309010516020f0a02 72
    0xf405170164024482e0003001846408001551902240d2103005007003030324001c07503442e4080d0303248001f018201d218130b100082c500fa00080e4000054a0300c2c0707a00c001d001c030038035645044421080d0780f50520584594094200040c0115a040103540c0c4580c20b00d81c4030044020a02282d800c0203400c021030300990248622850001521a14410842d00001d0017080301070b100c420024070880049500b034000340035030341d4655405a060103929001b405400e0454120802500300c85d201d00c0304c1c1c1012200540341140242000d05401200d52480310441131007000072901035074036010303429110001c19003610115411036001c0c668112040009502140b2540e903c2c0c01c0c0340d0f60b58100c20f110341d4061508070401502020504042100030500032008600c01d944030900d06408685032703810048681c80a540301400100e21400098111161850080e0001d03c0104030000c406d500320804403090380225213a841994541e803d101080d10940502000c404c803900181403480480e141241d40c42001840180c49101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 761354685 1250 761353435 761353447
    0x90203071a0408010e06010911040f05010320070302010e0d02010e060f1806010f060305010b030f04120905041503110a031a0a1b02030a020705010932040212091917 72
    0x200c007900300c0c0c0c0208031400c024003c443c5920030103525420240300341d0b181c042c24134020700c0814019808940c2640d6140c00c40e0b481c0395003031000460080004401c00e00d0f1041e5011103441d44410304401501116201c0c2c4c0c00490366000000e80281400d804003840000e580c1030194046180070082005540b203608052440324559032038070031501804c80041155464000c0400129480d1020b400c1d0b9000da481549003440180d0380c501c403114040c4012582d2900000f4050701003400641e42540d03103080b9400b1441c0501c0845e4440c0e00003012180800d2203844051140703a0b0400421070440c55078488070300f08440c02601c0c640ba41d1145c2001c4038003002c0c1c210300181003030009440d06d5001c1c1d10414901c00c000984c81c400014400010395250700440318080944200000000c1070341c030800c3c0b01c10580e00d800d1b4002c01624020300800f25080c0716041d01a0004100d84041d440a441d076201030107844440715001c59a5084c80b400c024200700f0100160795140000080b000e0125250300703080c0c031442c02c00e40e451507a108 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 761355935 1250 761354685 761354729
    0x40f020c030406050d140f0108060c090604120203070f09020d1401061b06060b19020c0d050c1005220e09010207030503040209060d050708070906080307020f04020924040e090109020307 81
    0x21000c0c070281e03215042c01c00140101541f00c51305007170503071740014120703038403500e842003040124096982d019612800070401400055004400e000b12588060201c440d403d4484d003511800b505c09070401c10509502142c1112508502c0c003854804600300d40c0b40c2c042c10750408100502c90280c51050724090b4118450590170040a03900900007002296501074071a52180e500e000310011289120300144101c1e4a002a80d01d010826030a03070541c800001c019840902040c0054000c030b42c0144010f001c414805c2c0b000d919881842c05103081264455010700c10f0510170b03003418210015000070070030380c81400800c0009070480c040f260429011901069103546103000500480106c8100070018007400c00005004400007078184280d92015034203201003501c9100c05a501e0040c180302030b5000d0247c00076240c05040546c000c101d0031901510480d0b413402c0384190b00494505810b41c0e000840e20000702000024600322070240c2004500000f440000c14640009958039198050000300138540c03070080c0094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 761357185 1250 761355935 761355941
    0x306060903110906031501060e0909010c0c03120e0a0c0303090605070b01091104032f031207140102070f0c060305012c19060e2a041a0403080705010902040f020c030406050d 76
    0x401c120b06e608050641e11a4030007060140c003440c400740506c04c42d00205280e500107016241e8a03140540d2015904103a03910101c2d40d00c5007241c1d501c640079a64118140c0c03c1c0406120781030041c4d000d0303441c1140003469031900500301040c0f9030024040082c140f0040c03002a6410182c0c904464600c24081642f642c401c0c1d44000c28840c99000a108901d0901c120100f4507000405400108114100a820b0b00c0d5000a260b01e9500c0c0c1007075200f6072241001031500040c041c0c40703241d5903010035000050070314a441d03803903448000000340d00343c44152020400700912a41405082d01400740c0c042d11100309684c1500c0f007510071906c12448844004c4000c00981400b10500b030b610344c401048082444410ba48180c0b410a90b030060302d40f034440d010012401640e808041070b00305810b001c110701c00b510700780c50710724608100c0003121840c07525103d08200001c00f04500c0000740242c03a00400000a003101c16204100c1150203100641d00e00c140180001c0354050b4000c41580d04070743c2141003c540e1069040b501e0001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 761358435 1250 761357185 761357203
    0x18070612020a020c060a03090c080105070c0b180f0f070605070c05130f050c1201050f030d0f05042309060d0201080112020a09090f05062202060f1c0c030606090311090603 75
    0x30045c041003035040c00783c1c103403c80c04040340140c2030901c54684903043d41d804d83d6022580b03040454036289071400001c1905c0c1074254019050002d801203504996081803c0854950354810640d0005060407a030740002c0c802a401042d940c00d05914204641d5030b0207407421004e1240c20f200f4034138501242003040c102d40202c11000d140c110100418a0b0490007644a0780080c0001604c040d006400420a41007544075000303107250003170044c505a94100400c4400703542c11001c101c10070000740000240c0c038000101ca400c041d5020b804602c00d04141c8800c1c4080914002c1a003885081040028400340c1d8104441505481a8466200c0302004d40c1c004940451030795480044150300e80b030780c000c0c10312102e031509440d82e0b441007041d50160346900b034640cc598120034105044084258040d0b00051810f44000c10700c0c1181e400c004d84c1011400c02e146400e41f0340d06a001d40101d5250310030043ca25505203d803030b000c1d110600300a90300d24110703113a44100c40840d0134510b004d006054042106650704000b5146 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 761359685 1250 761358435 761358439
    0xc09070c050c21010c03200702011e0e011b0201080c030702070f0b0306090c03010b0301180f0e0c0f060a0e1302070b0709061e02100522050618070612020a020c 70
    0x5000c400c11005540c40c001030040c14080f5503e0500c4100c8074902c82c0c081d80c3c80390101640b06500c0d0382c480e0308000c4ca1a902c00c0400b00d040c001650031020301d8541d000182c4403c50007989590b84613800c000000b501a0707030068407054013041e10703018000c01030707030007501140e0004c0d40380c41c246480742d0390220140d00d41050768001c841500c01300500000ca15031900c0041d84142020780e807004441d2030746001c3e51a507002c28084c070a0410f109200500c1405a420980303240e5108803440894030340e0325400b00d10122051400c40d04410303001501c07003405905202c0c00350051007105903181da2910a020700018440174825080707074819101c0d140c41c0444a01681c050754181e5410440c0202f16040590014040100074840c10001c10107554a0309010502c842d0450785085403078000c0d200d91128884081c0007060010035002c20640c0b00d0003d00c01c003046545800381182e205500400c203508140c2c1a01e2410380744501544502d0388240020322800b544000d04d42c1e0340b02400d00002d0707190101804182c0c1807200a5951030303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 761360935 1250 761359685 761359699
    0x10050403090521070509090a0303022b140610050d0e0a023003180105070c080601170c030f0c01050319152606010611070b040308030906090c09070c050c 67
    0x15504402e00f46012040c0070101003219038131641d0b1700c107002140008540010311034200e04244800300303019800904001c640385080c011505c10b12840c0010381c2d8001c401c40d41703a280e078800d41c44900c0d101c10b00c80d003070304840201e0341d4101001d1440d400400390300c258990071400540340c3c2c03210b0001d06010400703a07805660083c40d540060014000409840250001c3c640200b114082c2c01203a080c030101c00c40e00b09910400003160b84040ca40c0040d100340d4460313081121021000f190000720070030280143d0303000c1c02510241010903100004032501c0e00001e61540c034405d4001c101d04455915000801d291105000c3c24982d48a41d1080c010021034807501c1080c5402d60f082032052a5881560321150302a00d81190728688010310b0b0300100c00310044903980401c82c9600000c01071200a000f111880c00c00311840c01129009620b41010324200d8015500c1215641030100902081c2030301401042e41c800c021000510038201d00b000012450b20018128006100d12140c20100f400018000519100405402d02c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 761362185 1250 761360935 761360959
    0x3060f120307120807050a0c031d1801080120030112050f010906150803120105060904020417010b010908060708010620060717090d020a022803031d040c02100504030905 74
    0x40310f200155040d003c0010b8101c10004000b00d00490039100c14000e03070303035071030082d0481c80c0d03026643c40d522941c84415628951900c006c0517503584106140021545440400d41e51500182c10b0a50340310f02c3d0a000070300342014155440a0704241501e04684070090441614115401c0c99400d1100d0b88102c09059404c1080001c00e00500b40c00051610040c0e070103044d2a15036034a1115124000d410031108030140b0580100040d2628401074001e29000400051401c1d40d41c0c0e0006800c04540480e5049903510352031107140543c3c004200200610f48107019122918005c2070051055005015420521541190401d402c4540740c48a464011850302212030900700004042d000d60860f5010b42c1b00580d0290000c0c0190001041621009000741c009000c5800e2a03403c101e420b01003103200780904070b0461440200c0d40c01040c444002140240c940c0c2c5032800f211422102030001c00329146000d5814a200344003825400154041c0c800741c0b40c00009225140c41ca02100e4040f21640040ea01c021000c1030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 761363435 1250 761362185 761362193
    0x9010e042c03030106022103040b0612010603150c0912060903050904111215030a1412030711070807180b0d0c0b0d1404030206071101060b0a090504050f060603060f120307 75
    0x218103036200c5408881c8010301e007280803211f80804142d4102000400d102140000d0350500441c1d4110400512604c14000041100c90840d912035106a40403024042980c9070f00c019441607484000d8540341030f0301c0d840d007071054400301d440007180010304240d611803810050500c9042aa003480800070003d00207410b042e07895507555004090040d91018414010810340300f1a401c00b21882440a409801c004c080d980750b6508201d401c2c8001c01c81801000d01e03071000c440f0410015803050100340c032121464a010003101d440c00340160801c038102d41c4401401e003c0d42280942c00901c1010142c004030702810b0550124003840c0310041d0042180101074030100704081c1840140541410185040040203001c509001c0000760a407405809a048040070070f448078070030800000c2d005150760011401c2507844000319020f41c08458102c0003e0702d0107a0034441450030380103068000c000020440d94a0900c1f8000031214440034045074071070312800a402e81c26846031091a1480c840780e00c01e50380c4800050030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 761364685 1250 761363435 761363437
    0x4030b0a1e0506040f0912030e0c09010f0f0b070c17030c0f030405190326190c12050a020606101107030c080f0f25031b08010c0509010e042c03 63
    0x1860131310441c00c0000030195541c40e8420014100d400485002c5051103441c0f050f0010301100380300a00c18020b129a41181c0e48030300030390a00030b003210100c2e103080e9841c10305004054180c6401c0080201010082e60005c110000640001d0320a1510403826280642e40c006280d80300c5d403031460303023340a1200310717809205000c03010700102c3d203003034078000d0301c4030440d50078900100e2841c0802411109c130141141c0d2070707c4102c1c58550701c2400d000000341c0b40a044001c0d200c480d1100c140b0400000d60700d000244200032451003440c1248656003400c600300359010307074080e44401c2e0081a44d03002e1848004200410b078440c000e50124200c0d450141c03205980c81c0c0c28201e45a6010b802400054442c80c80410341100c00040ca058001d0b14007006003611075464401199100d001100c004148582e060000c0701103610100f1043c0b001009481c202110761904108a00f5100d84422410034000c0900c0f1140540c1d070803483c0c00c40311300001c45002640550010001c0c000c0e03010885007803180e1a8104d003000072500000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 761365935 1250 761364685 761364691
    0x11d040c05041a030f06251d0a030c08060403034d0a090f0503030406021e121602030d020610171204180b2e140a090501080c07050304030b0a1e05 64
    0x9180403142c082000c0301c0103541c87c0102410700021001090840e0140d09407101103040040100141c1c0200d5494485454175052500003541c0e540110081c401010f8140c442e01105041c4000190902c3d10310034145558100d08460720bd00225010598070343c0d503070300350502c25142c85403000c034562101d43d254002003c540050080c2d4240520030b4101044901c0c001041e43d007201c80035401044c080c6106003a804414000c0035000b40b0358803130052450200e050f4800a80403028680e00c034504412558010586084000c2e070100d01990480c80520103001ca60554280565410302902d100c00003481000518041c8402d4499040c40000b04000c80e1140c88000604080c07194071500743b2400d00040e081086c940c10a40070504605110f9044081c441c0022402c03034100c00250400100c140410b01058805030300c65170319000041d120710384c180440e60f0060a4036070003003000f0b0b07447c0341881303030b140e4900340e1b684114007019103010311410000b00c502c48603400c143c3e10428800c1d11194401049580280908415 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 761367185 1250 761365935 761365951
    0x1a0901092108100b03160908010903080618010e070507050c04091407060f0c0f2402040906080601050618030f031603081317030c091503011d040c05041a030f06 70
    0x203038000c15207a038032505503c402c2d0360000d40741c0c0d0300d59110103801804415182c00d0080c10b00000b010b0001e0303003260a101e60a6854026240e441c01e6203081c80400c10806074480a404081200741c0040c048200350100440e030140700b504080d0f84d6031009041180ca802481072050303a2143c00e094150b01000700401c030b442c0a006440c01240e401548550f82640c4a800c0c0481c3d14000400c03885940b0045420865000129401407221410007051841844840c00881028003841c40c0c000070300308288200c0d481071a0080410310b0103041c184d410640010b1440c80b4401039500f480800e118504129035040c40052064004841203983d2071098801082c0300154841e000c0d80400c41a13000250490303040880348191aa114021442200d01d910b10710802e07400281c607210f8811000e11000d21580c0721a800d5440354505214055102e42c5007603152094581c010761584011221071081c80300150fa464450401d607801202c000c50113203928403406840c0000c4004566040c0f14102424400b0707000852445c0c050001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 761368435 1250 761367185 761367197
    0x105040509150916020d050703050c030d06030512090102030904050a0e06070c0605100e0f0703110a03060e0c0f0403060c030b1c05070f0807170a0204110a030c0801031a09010921 78
    0x80f408040c0b006900c9461031340160b0441000c88004a128030000d08216100c0d0070561704001102d0704043c40c5030401450680c140380da0314010300902c4802c001210386840d0a05038a8984001400000d40341c4c0581304000340074903150800304018031565001141d60030a14021a841344c03800c040c00078840c005400b026a403140c640004036600e00701414000055071075958240449480d070410a0881d000c004054604143c0d0b22514000b80441140007007408030100c0d900490514200107141814000140c410300c0e14000400103621b48040c1d080030380c0c08403500f0100000c1c140e141800c064004d007000300402507006124aa0440c205042c1d1300100b0b01250245089881d12074540310342003440c240d90300412105a110100c03c0002e8100f4052807061800e442041d180255215404101500d4075240c0c0c2d90b101210208880c3e483d40d83c984664444582036280680b040d51554a400c0c511900129000d00c016200d080003444030708003508083c000c40d03402400845000c8010100c3c06072075030691070940000710 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 761369685 1250 761368435 761368441
    0x3090f300b070c1a01030804050d03020a02100c050601080c030618120d1b021f0903030b0a0623160f03020c18090d020a020604050409022e030f1b0e01050405091509 72
    0x4c54804581a65802a0744910381400d080820008940c1e03240204c0440c81180c81c882c0060b01c40100300748100c8007a84410a03450343e14508181000016041a102940209140c02e8155400651a9007000b1502c1c040101540070040041c180b44001008807204c1500040c494080c5c0c1466020030b03050b02101c80c00300011402944200e0b00e640003501c120040c0313400c51400300c200c0340f0380c0d0340400a12882410005880c280c140042500340006600480c0403d0310500008403440c1d18031184090001150b000b50300e000c4840701c0e0142c100f54021005405803042641c0e500800d8000c00c1340c5804903400500d8102030a0308240c030042c040710304446021705c81c010290008103850000880c40710480c1c2c02030625040c20300381010b002c01050302020680e0720200318001101c042c0c0746050740440c00030140303c3c012401c040c020800780540d52802070b2000968a0000d000c00182d05800d811000d0485a242400d2201007150040301c080c0210741080e03501100300c4040c0240d43e00c3c0d880300c8902d00c9070155a8808150307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 761370935 1250 761369685 761369723
    0x211203011a1905030c070f060b01020c010c1208100e10031103190809030c18041106070210030c03060801020a08010f0e0c1602040906051303090f300b070c 68
    0x400b50460781062412004001c0006a0150019552014400034140c0c2410219100c02a4030310030410207882e0180c2d00c0d0740005986d64107112039641e900003030900c050340d01069581e5603290065000000100aa41e40c00304404c8000c8407810030060002c5612840070381400d1601e140940e10b5888201c0341036807031003140b070304c203007408220604064910050302030000c00b1511100b100740e002003609607041c001c400e9650780315034801c0c40c2c1c020b1901002081c42078500c0c1501d8158070502400e850745125840901281006030303680c941001d00c4200500e40820070801440041d00a031480ba006046654000710310702c5001548103001c24121208a9260803525545001301c00c1c980d10140c03800e9180840811000c4820005001401c05492000c1d100040c0191541c403000210f81d001d07101030078940c03011503020040c95405403251000c0c02a520f11414002e2500c00404614510314041c081680e100d01e03a00101d034000b40849400d000c0c1c0001403003549141c01c0310014407120005c00110b410344141c100c091031b80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 761372185 1250 761370935 761370937
    0x3020114011e080c0a03080f07080304030c110301110702270a0c0815010f0f02070e0c0d0b030d120902120a06061e050618120d0906030e01020315211203011a 69
    0x10040145c01004060300390344a51031035500186140d103000f82c2c03c0088200107201800258480c40c02651000740f80001c130315082c024004c00040013842603040c00c02040d815040c00f012500b40c250304942c00300031150312011a11020410405601c962000a030804c860001c09410000745e110300c540c2c0b0307000140e6502c5580d4036040c5206121a001982282e1021a403501414000e50306da100d50049840165840108020142c000c41d054001850041012490b90300c1a000300075404400314007502810303921480c020006020041007004040d2120810000c1d51a8600c400710032100c0c81c0d0a4603041c0e401c40c1404806441944942c240408003400001c121303012062016058800041c000c1d0310f003160a6070084011b0302507041c0154004e030b046000c03607803400d010031110726a9201c541700c0311401407400c000641100d0360300c2d070756030311990040080203403a01b00042c401c1160346003151240485e50310014003151620070f51204088502c02d800f100070501c8159400755040303c507000080051044a04c1207074002e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 761373435 1250 761372185 761372203
    0xa03050307021519020a020f0603150907140c0601170604151a1207290403020402071a0f011e0602060a0504111305040c0f0b1603020114011e08 63
    0x50350400d2280d4001480c2042e161820314440304442810310284a4024607680d004841c0701c00564040c1940108604080046c01403007a0112a114258905501241d8454610500039403090b41c900c4005080d40c0d0041c81403451241d01c08010035180c502070201d1940e02c4d41c0a004692400050419034618580c4c00074002d03118651208100780010301003052503001e010700d00300002e07048200c03801c150310584031410f80c1240d041c0c400d0700074410280740800b00791000080c007124501c0c13045030710050b20101290380119801c03070b6415a40180e4505072800c2c28828051121a80f107042491001030012014406c2640b41c181d40c41c50881c2481410185483c0c6030240b4144030703000c0543c00c42d80018180e01e86a42c40b0a0780a8050340714135040032800400900c22080101005100aa894003400300703203d41064031001034900d648400014509046940d09a80580329000b030801c0c2480483c1410140f00713400110120090b00c0d40441c565854298aa14000c0341011000300c1000c058000188910001800c1d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 761374685 1250 761373435 761373443
    0x200c0f030c15070e100c11040216020114250309080a0b04061808030703240302032509050f0103120329061923040b0414040e100e0c0a03 60
    0x72066151880442c000000522a0041c046480030341103441d103e00a0409505040d42e07210f842040c003524080b5a00c0e40e604c02154003440c030610107000540c504030020b0702116024205102c040d0104800c0e412503200d040100441e08196680c0424114001c00c00b80305154441d0703ca0303850710758480105580d204101e050161103140008081400f01e513150340188155440b88405c0608000d4645510442d40c2c02a25440000384d910021032980303a41c6090b103412460340100000229902e5500000e40d5250110080079102d10001c02c0f0740141c0c141c0900b20001451091024402450300000c02090444240300a6a0701140c014003c0c2e5034620900c00c45820401e01c0c2007009a4001c000301000c684c4950307030495034000b00c042010392808403070b1054200c2e05040b56501c20010500d6900f12200b11550a010a840c000c010f2000f400380001100a0b2030503541d14917440d420043d40c09000502600c00c21400d40c05900402c2065200542c16030050200f142458003100d8942d282081880501c035402d22000d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 761375935 1250 761374685 761374693
    0x31902090c1e0f090d03020715083d06020601090606030203100b0a1202070606140108011809030324030b061206060f010e0a0b090102122803200c0f030c 67
    0x30211002c0c51002d080099200484641001d0903000032610107100c1d01c00644c05a401817404000d22040061308020748403c03450410440e0030f0107026104e1012445402000c044a200361401c0e04001e40740e00140c26140c0700042110469583c08042e485400a02400072001d0501101240c028080e00880380100e101c0e10b08080000d140540354085608101c0c00e110400c00d02d00c4900100d0070380c41c000780042500410000500700c6c5080c42d0040c01c00c40e1200c141e414020a038004100d080a0040004110703c402e01c0041789090040c5001c500030303d07602c4030a070300031314001d1040700e07140444440079002d8070320a0340c4031161601c0e000b00300071a030243e0a48401a940c80701001400c14284403440c00d46101e0181400014490b0900001e0840840e64100c03008512001c0b8801c0e04035a410090903200089440a4525165107800003100044502c4900c00c074000c902480a00524170a038403111071802044060001440d03058158521580541c5a603042441511a90340b410800401110201455a0020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 761377185 1250 761375935 761375977
    0x306150f13060f0f0e04111c0b030105070207090c0e090f06011101150603020d110f070b0703092a0b0412020a0801052a0702030d030203180a12031a031902090c 70
    0x201c40c0d17a030b81e90303d00640107511490540550030800d0050700c1400da001d4050306286482c1e4901078202c4a20402e85032085e030402c414013140b02c0c0c0120b14041541d62021020489a9020380180e40301d07521814071642020400c0100552010300301103441c06100240d0304d000424131695180d600b03807402040c5801c10380804480c20403d8070300950050268200742034020400030307054007004201d80c20030413001032003c9001652030b00308406c5004071a030040d000c0c00c04000c0030145851b03c04a503100b803014040e111003403a0039180c0b00d4030750350400070090041d562500e0b650b94950703aa018100091050803030107100014408503507007006000340c9101d800e85541c0c148a400228000e00c025045942030b0508150341040314070056107080c40014801d11054802594a0804900107810001c040c0034220258011202610001c1c088080040e01243c445c80c003c10b550180800d001c0b20126041f80c52685131040005203d45c101c0b4a2944440080c001c5850f4662603903030079000311a40c8107000e444121040b00140c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 761378435 1250 761377185 761377187
    0x60f0e120f0c0106090e010c0818030412030c060c3b040902060d0e030a0e0d0c06031116050c0a1d011a040b03040b04050c010c0203060402060306150f13060f0f 70
    0x14001032140b030390002c40c000d55a0321080c030440d01d409510b51803e94403114004005500240540c1d0001642050202c540d120307802c0c0300340c5034000c0c0e010b8800440b8140e4046030a1501c200c0c240e00e0619040788080010821144000d00a286448500640f401421030705900c2842c020b6104580e031440441c011101300b0a50b02080000c003401c020403680b101041c01140c1a19183e4400d4414070b0f13001400550392070400c02c001400c0c91551540c0607116142d030400d04000501c0744401281110610b040110342001120340e510218058000c0b0b40c0c1107084802c40d04824010001400c11300e8000588202d02460346400181c4c0c40004003d44800140308450010498811051030396200141a00000d900301603c40d81320707130810303441a2404e03954030300752500784002c3c80000d02000800f075000b4284820812a264007180e101c0c80c00802c045d01c5a1008000540385072112403040741c40003168420b4903690b05030740002040b6500048001c41142e030100d21b0206006006130301041e4010072070b0319060407003944d000c0c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 761379685 1250 761378435 761378437
    0x3030609070c08030a0e010b06040503031611030109111009050d083004030905040519090503040f1502070509040f060203190203070302070302010b06090a030b0403020a050604060f0e120f 82
    0x1201c0420041202c42090126118501450040da1520000b240f9201e400b0002800d40d00194015841050108420045a0780010072503d1a00c81c0d402c00c41d1030140e040c104401d00f41c0c8400940764140d401d0010200410100b07002038020044112590108010b00010440c1d480809018690b000ba4078512204c2c0841d10041c0a40f001e0841c0800c811184801139200d5944103000f103801c80c0050240c07506000c00c1541200840c009083c0c261400c105a02c0c003045180b4500b03148114a951050380e40780310400b482418400c50700644084c0251405180e07440000b031015061480000380140109072020587d480d041c100980182d411610200c84800d2a84075000258806480715140340007086c40310a100b407884c000396101c0c030707006d86005842310000c0c1000b1b82540c030080b44640c0708500c104942140d41d92a10030400659400c0240c1000a559030321b0180c0c5003015001c0082d12600c2450100700402c00141c001502c0300c075042d00248000d01d0300301400c650b0380e03d1505c036045140c24180011002e41280340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 761380935 1250 761379685 761379691
    0x6030b1e04140a0206070b01182a030b03060106050721120b0103020d0608030d11030907061107090213050f01050304030c0b060f0a1206180c030809060f03160306060f0203030609 78
    0xc03e5644050907540001e010b030f48072490440c1d081d5408030041150301150710074207001c40d2402c0c000780201070160140340e001601c600e4031541c01c0c00902441645075403003540041d1100350301504450655071181e402510540008004480780c0c0004014251200701c0c5d03008600d07000780304c0e4450100a401030b14a1001402c2c2c0710184904050b400d102c0c0c224800102e0251400610b58800a50303615044e0184080a0f1902450a03a1040314104140b050303550000480a0032a0740e40e103003030782102114101e40c50400031560f005540307640c008036028108a401405180c00c40f403003241c000c0ca0481104c0015259400200d0707003e0041501104440b02040d61000c1036644000c009103080f2503030007003d00142c60b50300150400c42c019200013603d041042900d02c299403102130b4100d1002c0481c1381d642c3c3e4061050f0b5141c08000d0000a021482400e50344807101aa01010410003d154030380c0340c500307091140035004140310000241410720005649006000c4820702c80c507182e0285245586107024408891406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 761382185 1250 761380935 761380973
    0x20604060209040e06040b0105040e03040f0308030402030f0f061510080708100810021b060408040920070809090c0406050f130e0907060e0108070518010c1506030b1e04 74
    0x10380d01514013a10144005172059105220859007941010140811a801040d800203d0b034002c0005020003103a045c0b60780700300c0ba030180841da529550352010900b02114064140724520800640c192101c0f000b180c076522030446058071010141002040201d202c405942d188003080c02107012648261042c01096400070320b80511001603039584c03a40e1441c0c10801c104110030301c2d501152050100107040e54800280d0406c0300244140e0610303031a00229403045201301405244d41d15407448000c400c01c1c0d03401d482800d44251190703e134102401c01e02c0c2180e0000e8a5284121440d00c005421615401d083d90306442d103d680316820000349081c80b44866201d506410071400703c140740050302c0c3e4014003200b445801e5010150072110305d0941e001d414007041d000480c1c10302003407008002400b81e0040644504032240c800102c80e60b014040182d0742600c0c401009004058203400141107441250040e0013140c0c400e6032040400d030b9540c1c518508034010740441d544000302c0704e00031038040740a10840c010f0000f65 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 761383435 1250 761382185 761382191
    0x7020111030f0406080a0b060909224407060b0a060504051f0804060c0e03100618050606040e04081213030306051225050607140d050a02060406020904 66
    0xa100501d1a00700d400c10341e406480004040c01160340c0030440c2d903040403a410040c400c45c0714020002d907050254403001400386d07075070800060b40c0c20400301d004c800446605000010380035040c20007074600555002045014140c00886505c1f00c000d400300030360b04801c424103182180d200500103400981c8680c4080d81c1c1c0a840e42c00442981d83d8680c01c103001410540c4800380c1c0c0d545401c052142e4400f08c00e2100d90600d885020094519402800c1280c1c0140c0c010350024050b4500c3d207007a17a10003c4600301c150188950002c900c203025003544408161840108020f14811351100d41000340c40c0304485250308240c05020801c011446404010380262081071028280402040c007040c0c00390088501d140c0500c00c0c46030362800d02d60184246070140130241c450414111030540116507a000641c7c0c180350a030700a1402c3d58503841059038807c05080001d015580d24582d905117070082d00364134246103081d40511020103511340c3c060022104120350030f801078030180d900d0740c0b102c0d03009410503d529030f00103407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 761384685 1250 761383435 761383457
    0x2b021c080408070510080f060d02060d090311010501090905030f1e0711040b0406061d0f1804061508070b0a050d021606060e061507050a0605250201110f070201 70
    0x1150202070320180c181e0b00c00a1048500c0d000c1080b0200c85d140900c103081c48220f0742031003010007141001e150321840c25103180096886074800709055204003080d800060345000310803410168400450494003002900a004c0780e62a010100d007156803022005007a0b0744108a02d4442450340800341c048502c484898058541400920485541c411801103600c0840030740c00a05628051040d130100caa400e131000c1082500b0254040e01ca40c8483c0301512195411000900741c1c1e5844200c0040140409000040c60900c590701c0b400090b41c05503030456002c0e04000d1480a04954800100200c80d40d450013001d00b030380b510f4034500d11540700307003074604c01c00c80100600c10401816000400c0d01c210b4041c401480c42c01c86c0d0800e0030882e8400d80200c007601c600729050160329030350492403440c1151000c170b99a0303a4208902c5c10300d02d011502e075401803c0d14140403c200304c000800051001c2900b41c00d4088510901c0345004074200d4402003105800704d5401e0043e4440d006084000d0b000c07440c418107004082071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 761385935 1250 761384685 761384693
    0x5090a150e0712060501230418050d0c0501050f070f1b050a0c080d020703050c190317041a0901090911070b011815080c04051308030a09022b021c 64
    0x1c005a00700d0300c25818582d10403c2000034a100d0140180b5910002490034a00341002031020844510501d10442e10781e4a901100e42480459103090342c3d00034203d4080d0600c0c1200504038840d40740b01990303a54030b40300000700c21403025445140f050314140d407240b05210070000192a850307048110b4403401d5521924030800580200320625070305001c0c1b190500143c4c0751800709440d002c1c038504010b086400c120000c00c001200001d1441c3e4031042103503a00c01c00b2056400e00312480c0902c2c3d201904900c290340e044e1000100c034100030019184010010030042c070904003400c4440c0300f200449030008806d40810803e0521030b9121465803104040064500240c50322801260242038212242401c440d15910580002d03034425861885803500c08400c1d02440c140580ba01d80282001003805a5100d40004c1c0315101c0034504042ca8035400003c194481c100700c903400300100700c014412801b4800390303410640030710440e121400b1a184c011112419045c103640c24846010388444180107090b240c0d43c4030304001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 761387185 1250 761385935 761385943
    0x40e0a022b1a06010c031e05130b04090507020313050904110405040b011712030a0e0a020d2009090a121407060e070b0a050d020703090302041a09090105090a150e 71
    0xc2d00440e0714880700d50030b4810803202e0768030140050741480ba08900c032000090300007040d1600e04e403003512480b0740c10030b542c1400d85542c424140800c90016555001040105130140944280e414a400c20002955000c5090760359114a9528654140c0001c1c000c2150b0b290134005a98083d106920007650b89000d8001f0a05030340c01610701701c810b09045401846032910410f1104d4460031b4140060104510007503c844051002810120b16180c603040c400307541c1c40c4200907031900c0790b070f02030041d90030400e40381090300c5a45c01c10010c00c016040344e00a002c255190511703c65005102440150109500c240e44030400c003482607082506102e01d01c0c0032800d0500d03a000180150a004000104000c200502103504010082c1c1154104080900c4028822a4008180c40c0d01c01c80b007440041c0c0e2842241801d9031300c90110351000754014100446424220080c003d4001d081c4815580311036662512120a070a86804541081d9240d1050080c080810450f4015000c0120304640000d5920720b12940c2e03600b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 761388435 1250 761387185 761387269
    0x220c140316120603030305191a010e120307030908060f07120b0102010f021c140f070c03020703061d0610060509060a050f070302030316020303091f0e010c08090c040e0a02 75
    0x40780d5030343d00300185602c034004043d00146c0c070303d5400c2094209d4035a070001e0f0514007a0400381001950081e807945500d80704240518044035004aa441d00c03064036004154080c1c501482040e1301900c8007044c3d00030301140806004800c41d480358803000400c40741c0400203043c1c0d007200504542d00c501c0111500d0406200030110307500c4607445101c40110a50560040d00d2120700c2c4a541c0c0c000da50108403500a0001c0c105421114900e8448410a180d0804924100f502d41001d0480c9242500700011003100a488070200c54012050312065030b80d8104a0714424000e00c40c0c080031400070032582c1098075011000380409402800c046041a40c101ea190409800c4294101c01507840002072103207002e00c0d810489041803c51004506d0341c50089800e940b503982e018440d0030a4240e644101da00080503820001005000100821104408000080c941d03942607a142d076181c0600807444041e814a8002c03420300d00180750041c4000501c95080c4030711000d000240000820300109000c0b1305a03219007040702c0f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 761389685 1250 761388435 761388437
    0x1806080919080d06080714090c1e0405010e0108060901170316060b1c0c03030f050c01020a031e11120903070512030601120207110d020f220c14031612060303 69
    0x24079951007003d0003088070440e40104135107911119003044044031000040c90287d806682200960300c401c240c3d1b58060140508502960301343d038050a51040d404009041160700981c0c4503a58118604019602500180d5126400010800050203507105164100c2e4185410004a070300c1c1901e0040385003e0300101041c201c075140e86812200c51f641c035000049144225140c1811888815180d4070f0380035013400c1e40300050a02000102092442e13002e00d040e2085490580000d47d502d003025480180285541000386801d20508a10785d942c0d41260310518901e061042010b62820020240000000c60002c0c11655035210030020240022018021001c042d005106001e440b03003821400503000d44070019000340054070500429010504144000c2140202581d245528008134000302da030800b84c0d00c2249806c200b40072403454400c16800340211055448138010052020442d0f0101c5401ca00041c10700110002400420840945110041092501400c3c505031045a10f0105400c1d070b0351503402130b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 761390935 1250 761389685 761389687
    0x603101a060f03011404021c050a020d0912030509030316140403020402040602060a240303120f0e07030b0604050615030a020d06060f11010b06030112020f0a080a050d180608091908 79
    0x4540d14002c117004040781260300350704000c001e060b140610802c40c070030281a0341e22500410720801041d4100c0d00010b80041052120300014148081d41c0340c068070603903000034507080010351054400720680c1d00402429542c1049126011401c450709085000c0184c1041801c11000005995500c000d03c010111a005020180f804000d06408c927621720105040182000300190b114110014013071040d00d605042a8000c03074482c81081005082c4141c000c180e50780390549401c1d00d0720700044c50f14110f0340308101c0c0b43e17103d90715034051009848041e1000740e0000d07101140c544018040c80040d688c000c0701d440c03006003402000c8a0100a0391003d40c000000710700d9085c2e8072801c4a40c458420185812000002e10001c03501501084140c401403060711403c10f403180c49a81155610000f4050f4000020300598a407511041c013541c8a601c114011241031160850074141103009103da81c4010388008400da100070710300802602c24034030040c402d4441c0c0c01010b03541c0d00580810460a6850f0303000e84041c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 761392185 1250 761390935 761390939
    0x15030309100305090f1c120e0d0207150e0303070206073807230a020a212a03050a0c02120f06010902040b16170a0503060a06080603101a060f0301 64
    0x400c0c01d00b01d00319845d000381c0c6c02c90803829064148404200304d075800245003a581e0702812284a000a00d1030001e1001d00e40203d90780c032944141d001444a00f6070301250b40200d8031166200090f20580d20446882c0d4240d001070000d0409450100e02600c43e8500520346068400348040c49498138030390001c8101121503001e02503804160a20800e5544001c950402410054800207445040e181445010041607000200760003118400e111800c101c6501580400e4464001d070b030344603100607140d1104000184078130b40324060512800c2c15000511403480c0708019404150320304803041e91101030310a0030702c00450304107801a1100c0861a078824400380141c0303903820301604c009043c1072069015601c1c40e40180400d00c6102c0b860412980300c000949803900080c3c06c240341c504000100c00041c040d0303c4501003103041c980d0740c01000942c81781c0011600c4411031505c80c0025a940c03107081d114160158800c524814404040f0b50201086070101101000300b0f4502c240050142d501400605510140200c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 761393435 1250 761392185 761392201
    0x604031b1511060a110d020a0e030d02030708180103150315150f05090a331a0403020103090516091e0c1e0e13091101080f15030309100305 61
    0x2101c05214686440081d03030381040801641c611028000020881d901d0300080691501201154080c0b403101c4800e5448280442c0c01403c444901c10000d4020300910080301c4040380301208649481e940304200c9400c0c680e15081c0103074121403502c0c0e55414550394888031121614209490401103110f0001003455075a00d1500c0d50541c4c1091b071050381801c0800e003040c0000900c010840003512001d030b82c840010f654100c4000d000c0c07c500280081c2d00c503000016020080d001007c130f138202705401884d2458241e03944d00d440c8105000245030b00f000350030610007400107602c00c3c1c114602d0140200121101c018001c038070018850080c0c0d00406240341d4940950300c010081e01d80880300c6001e0301808005884e2900c101030040000301c01400c200d141d000f0700030f1920034000c0004000d00400581a01c8112204e03c200780c0003480e81180c10f9903d41c00c2082c0034510fa61040350b090b40b007541c2c00d0500308040e40754130030340341840f6600300d40c404c0c3e0501040c42916070585442005c0c600140031030f03030003160508100704 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 761394685 1250 761393435 761393459
    0x803010501030f141b0706091a01080a11120c040609060603060509060a12020117010e0f0a0227010908011e0e0318100e120109142107020604031b 64
    0xd090f4080303410012244980314503030100c07641c0200d412074001c0911700a8200a240c510414000529071498460120f092104c4211320b8600151250f188a0b41c41e42c07618901e80e030300c00301d04800400c0040c0540501340c1500748444246510642c0001f1522402180800241031710110f81015041d141d48400c100b05d680d5260040000810040d1640ca18500b04a07001c00c00013200b0340605130302e980c2c54410b00421a4850008103060440400c100e41c40c2d961200304440c07080100b52052082c401022010807002c25961080b40c0750346d4000701001c5101d600c9051181000b00000700071905000d070400300001d4095082c0501000281a0f80081e50340c000003550081c01c0f0703030010005010700d0780248008010f00c1001401d40e210500100d4145c903022440d484204c803000500d609240d048819100f40d074000701c0054205202847c4180c402e0b1040e0007182040c1566114640600100300d0050801150760010503002440480d00280240c1c0c81c050300ca84034504280142c4840c0c10401c00200d04c10024880f10720 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 761395935 1250 761394685 761394701
    0x7020301230c0c031602060405060a0f0e0a140f0103110a0203071203060e07030f1107050a02130506030705040207060f050c120901110f0c0735060105010207030813080703080301050103 81
    0x102e4030608200c0c09800d01e0b50b40f4020080318a032405d0a001c41401556960002d40303004000091805a4840030540001c014030b5901c480300740440e60a0503104210b1910504184c207032650350803e40d050071200c104029a882000040710306040c7d8604038074100300c0d04400100b9182e82d958004507517551702c0345010607a60b504540c010b001c061078644c080c4040e1400c20001d6410035810f10b0701180c585211141e440041c03c0c0c4405408181c0e40004200c1c04000000c141c510300315008542d1000321455030150001961000c4590550542080c001840701e032815034090075039980900700020f2001d103d0104002142c50954143c0398241c03004c908440c40074280928554480c21400003441085001003103090b56000d442e04d81c0701031020118030120b80c1c60003004400000d04004e184001c135080010701d4090b4506013070280b08040103084a200c9101d04002940030704036001031b80103040031441e680b80e510403900880c16000702182050000142d1040401c00c02028500039031085580354940710001d82114010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 761397185 1250 761395935 761395951
    0x6140301020f040e150904060501060318020109061101150e0108061506041a1207031d1c0c030212030103030215090627031608030a0608030c0d03110702030123 70
    0x410408010708494015641102d00ea00a00c04c10380d140e68118200386548840702035000341004081000740000f0350040ca040300c0290b04c2c100128081520712100058007410064041040e141007040802d1107140e00c0b00024541b5000050b21040c090304520500c01c3c40d610006001c0c4000700144a400d009104850308501000021000c121300140807031414000d0344588500080801e104030610303001c0004a0340f0800002e43c0450340b9250038200a0003c16081c111510800310b4407040311031a41002418040f40036020105030880c01401c9021540b100c00c005085085003e06070701841c4400740301002d5030103103220360007804400c220040080710500f00145090340b1640441c0034441030503509054002040040600103000d402010005032940c400c1100c1c1480101d64485202c003404100c2c409140035110000090000a64900f40c1650300c0c021444604410f41042034515180e034040c1c1e0010500181c048681410500250000bc5c00c581d0b1200303441e80060301680c140e03044040010f909550000107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 761398435 1250 761397185 761397187
    0x90c060307020c0f060c030c0109050f0d020c06160b0106050c01050a060308030f0405010b0a2301030b010503011503091401050702010b0613091d010903050a12060b0f031510030614030102 82
    0x1c20002075031000036400190148074802079841460b141c0e02c0c120342c0c052031038a00b142e80e15081a09803500a10608000303440358010b240c880003c003000814482031a0b202c50b401491440a03520070080d150f40a50200080105004070820021300101202402484182c840a03121070700d0340406405d4170401042c00411601d000c109000040410f000c0c0c982080794004c440d4400d5480303107400350051180d0380840f5406580711800141202007414412107070f04100003201400c1d03000c800154140d40750700d03d411340442c1c2c0c148014080c0940b16628844162100d28021546524546441c1014903010b064846265140d10801000a070240110603010001f40d441910b486140c10640c2c0c1c90b402c00740a0313303001a854aa16000001c18510042008540c0d20001c1105201924014095510102c07105e00403403081500b2030390510b854464401281d00d004081c618143c0400301c02c1d482e40d130004160214000c00e42001400e241ca0b9009038402c200e58a841c0010420304100740008890150f604851283e80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 761399685 1250 761398435 761398441
    0x30304200127081501141201060e25090b0d20121015051803100603200d11090402030708030703090f080a020d031b140303090c0603 58
    0x84140503561100d652003000034528400600480320b54100d800d40028103149141035003642620404210100c40504080b10792002c000300180140c903200744a0a2000e09000c9210622410031b4400e211320440c40f100002406e03602d03241e00d181a900140e40c20149030303010340742c0050362240044041068005a0401c5501c0f07a10785212400d80d031040041c02100e030b03a200c2c500c0b5030803c5140301004151060081250b0303100d2000502e44104668111800300107030000c0b04002078030700c803150380b100c0c1502250703640c091500d41e20b08890400300c80c003845070340e8043c46410142508960107110342c3e400346121300340c42601b803e1040320503411f0f00c0190321090710840218130303070708006075568041c680f40c0102078403081c030696503600029042c8100e562080c421400000f40d28410554840303480c20903284d41450101650b82c560086030303501c01020f2002034218006800040210303004a800b080b035000882c072003413460030711580c60140ca960140c0c030394002c1e40d0001c030500248040900c404c0892243c00d41d01c1c51b056203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 761400935 1250 761399685 761399693
    0x60302030610050c01060f030f0b010e160c11091302090631090b07050301030c060c050d08090f070b09090609040c06030b030c1f0e0301112203020d03090f08030304 72
    0x41c00c12546501030081c0040c01e801d41e13000070b4200720024258940b10a2081c1e1f0703a4207145407400a441411281503801d01b00100303190b40d030001c40c5030103041c50020a00260504600c265940748001c0000d03100c0340e02e000441c81c0a5a68103501d14801e81210a200c180342c2d03031620500410b802e01401191207a41851816558001c0003c40e004030851030b605607075400380e0f038000000300910569030040d0400303640004022500b60080000c50403070748a00040c1100994400c0100c0307a049610b20010300d01d41040c258041994810704500f82c0021541094031106030108a00170b103440581c1d03202c41800c003004150071203a03150060207203900150030b5030a58002c2c074060703560b82c0003011903004520030316655501840b001e807000c101c00301c014200640710040b81c00e020001c1e05a0915941c001000140f209001035209040c1805080c03054868810943d0904100d004407664007540300a8100224245010000140c0e039a20880301c11b003802919a244800d05014248020800d0f54000031515801041400002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 761402185 1250 761400935 761400949
    0x5161d0901110f0904090203150f0c040605030402280f09180201170705040918060e2a06070c0f15030605010f032d020a030e06061c020303120a020d060603020306 71
    0x780154030b0301c3d80c1d07036584131030000380007480e02400c00b94141c420f0000340046003200170b01581c01221240520400c0e80d40d09400150180320740d029940003c0c0051020170010b0a100b241d000c8010301a100c030a5008042c90420410048035611400c084100004100b00754103203481062060b040d0400941004c182503000640443c2d40b41034060500d1500d0000200b03c83d21800c2601e002c0d118500c8103022068030841c020080c0b240e40202581c00520342902024415000522406050745c0d030380c3d04080c280d1480031040c4190580118407034021030f00b001054001130040040300e0107059210320008405080c07031a22028407903120800b07003e0501e4500305204036a040303514031901c401149804030382d40c502d020300701c0d505000107009024070070083c403210101e048458001d400518a0755a08002c0e551244504a40d94141560f08503080703c04828006601562081c0000c504c9001500b100c0c600f052035400304640f80b600f110b900011590104000601340d600740100002404186410b50450515000144107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 761403435 1250 761402185 761402197
    0x90504150e041410060609050d031706120a051b090405060a0213050612070305130b010b030a1103040c080c0d12081f0f0e010b070305031305161d090111 67
    0x2000341072400202040b0a0321060042161040d0030703180c090800321049400b809a0703000f45004600652008106410001c500f81885a0180e84811a40580c211980000700c00a00701790340103a94411101c41400d010010301c042c5904c540010800b0003c1080d4512080310144511442080600b0a10010500c00a180c07900807034800c0c001a0717120081055220152803541c041900502d020400c22850403410741403520070b8916442c2809282c0e1030006120044884e03103c010603162051006100140140340a1988580d071312200043c0401001000102038204a0707048a06050302c8009102c030072010b11040c1900314003640c1000c4c1030b00290780e84000c0c455249281000704442c64000604038141c01d0014684100304258151120703465422010030740203503010b54400800c58030000650006201c049658503505aa11241140c03100782c40340e075256071105010388040c40341d545010f4a003412a10100001c0c0001c3c014007003403086c4280c005003403000040920400d6454518410b80720701f603070821101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 761404685 1250 761403435 761403449
    0x30a03030b0103061a030406050907080d05031005060f1e030c1602011418120d09180b030607031a0406030c0b09030f0f03040f0f060c0b0c0705010c02060709050415 72
    0x50046401c0300100c00070030041c0c0c0301024465425025180d0200040001d50040e40a5102401259a00c0c05000c0c1c0ea4451442040003942c010992a030101b031241001d150000600c21095035115a504005582138000700c2080300f200a0015200510600e62100c40030315079a940d00140c21740c544035102054501502407840c0041401c403407090110ba105900740306c82c010005441d0703901c99401b44003617064000d03400f034a94001c001040141c4041100064515505803050382c0d07039a520341c1480610042c1851088943c110542c0351500c9100e42d036024402e040c403a480941d4002202e103c1011000b17403c0240d510814021480c10300240081542801d99205503141d46404070b0350380000340c02003031030842c0c6e021600c00107004454402056a001000801c110740070384100b4211703070392075503281e2105d00300601c6480042183c0046400026813522801980f03c851545c40d00d0401119441d1a03003919070341020a0010782182080041b40f9800242c0440648000d60307042140e04043d03201c0300205841401103003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 761405935 1250 761404685 761404691
    0xa032c0609040e0c12010c02010e070312050a090314150106081e060f0a0e04030e060421082b05010807260c0307030803100b0903100c0207050a0e04050f0c030a0303 72
    0x500458020008005013440c045c0c51036043e15412098103000b0460f103001c1e0740040d402e00c0707880c00c00392000058450a89800000d0703150003450819045c1e0b841d501880100040c00545174000021406403c10400c1e6803142c08040d2500e08811000304c0f200c104c05030410f10038043c2c500240001c0e0700c2c216105894500e150740302e4400946510000403154414102c4103030348a0500c1c3d1020820200501032180100c3c0701c0d8a580d00314000100800145000710701800f0b0000300c0f00d00400c01d000d01042041d40050f80a50005850301080c01a40c188007504003c5503080c200c40340d1604140c1605071300c102030040c44110082d000c59800c0016030100707640c0c00c8203406014800e0903003003180004144030031040c00c0c1c40201101d840f181c0d24a448403031034000306c4031103088641440b000074108412000707d40510780000c1c06410810354000d040d60041845a04920440c454241c0115039911110648806801400eaa0030703034a1038a80740c41460318034101d15a52413a0002000e952140d10005510003140f549800c001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 761407185 1250 761405935 761405951
    0xc051021020f0f09131806110f040e0601090b0c2e1407020d170106050705160f0323061b0f07030c02011706030d03090303020c0a032c060904 62
    0x28080e02480c5000640b01400007143c9012034003810092000c40d80c10b03076000300301045060122017107031003d80c141c200d000040c01480d0006030f80c0d030b0301682e591802d9041280c1000f103a80101e0500340c000c2d1304150102d00b0042e003071041e50342e0041000b100078401840304519001d070b1941a40d891f40f510140074094852030383d440c48001e0140410014030500c1a9000700490458101310f40300d0305006917151005805500d9403998601c2c0303e10401c000035030460b440316030b481c1d282c9902242c8541c0401740907a01802188052019000780301140d400030400a220303c100781d811814450907018050000700344015200c40303041400d81c0e000c1041503000320410b00700070314a255003180c440144030300320078034021820001e5502c00f01500900c00e10076030780c000eaa40380d00005140d0f072404040c107001d80760305505600c030401911407207100f03400c509001ea01c40c1c0b80160034032490b030f801c8a10b001001c1e070046000c07600420031010b029503103103540140c4011051050062610700000b01340c07079115800c040b034001d039118441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 761408435 1250 761407185 761407247
    0x50901020309150a090b0403050712060209030105091606020102132706090606030f0b0901090506012a14060f0402060a1b0c05030f030a170403030b0607050a0c0510 72
    0x580745000303406010f950780030309240040c3c01a58800c0d2101c8000c80e12101020550b103144a0548003a00e0703201c070007030043d181860103280340240c502c1400c5400300d8003084003240ba51400c0c01128042c120100050140e20341101e00c001800310341d0303000b0800f1603206200c4140c030f0600110f02c1c0b00c01c0f1402050a4000300c0c3e014001c14141c0441d451244220a04081300010082c50942c840d030215005076500300610307680c40d55407805070760f820326006500140c40070060040052550200b42c03c03030014140f540403c42d000700d81d80c4805100340e0800c411125801000c1d0244000c18500f000e4103507000010305168900b00c1d205440001c0c1c0500040d004801c0450f009881c41c2c0100d405a40314000241041507040541c0741042e0300c4684d40c001c6900900407498000ac6881001055a4441c0002d4880b250210201900030354080c40003042a030805484008100494a80600030103103107020f03030080d040110460600781da60000c40d6008034003800305c400e9150041076110001401d28654101d440c141c40103d104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 761409685 1250 761408435 761408437
    0x91b1d0609040b0609030703110901050d0224040807030302070e0c030108190609080f130501030e070302092d0403031406091801060e07050c1203010b07021c170403110906060a0509010203 82
    0x22091b5014810350300d0100a1242040420028881c220740b0301040e43e0b00c42080c4600010b5a2800035001020b44414254641c940403140700310301c2854102d142055601c6481c0c910307091aa501c2503016030401002800020055034036658460b08066a05280d54585080325640c0d0920140701c0d06e284c6017002c9500d0420010341c11900c406034124117a540c4034000c1c00c000070a103501c1032043c2c41c01c01401d641c0015040d40070307003d4001411120806400d00d00d1541c0c003440782003d0000e04003203401805445103120f00b055000c6c0076004040031103a04415290a2030003600300c82c0c404810301c0b842001c090070003105075200700308558417600030b11507911000706060b07000c0e01500c05500302c031865000507400c0000d6240e00c88040c00030f0400d10000c551896086c9031145c0000d21080c0281c0300d407001c0c100003074809030900310b460140c40d00502110181c99030302502e401e0b080514940c0e180c2484500081d0800038040071000d444a000001c40382465141007074070028941d4850320302d181c1d09114004c104400c251307000740 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 761410935 1250 761409685 761409697
    0x1203040609080709092402092d10021c030b04090303092607120e0d030503060406091a040e100606030f14070206071d09090f060c1305090a06091b1d0609040b06 70
    0x504180e40b0080c0a0227410008001501010808400c00e4201c1035517281c4501050151603050f006409074552116400c060500c02c1904001071503191240d0003001d4070340380304d0054658080d5400245500040c60310545010100d0315100014800602240f018507401007111580ca80c00900400402d5103400165680000100b516034807400315070380e4409141d009801075100b03840448040013500c1d01c9000600480e44c601c0d82e0f2410051a030301503141141001d5000c01b203040c0840c01100c1c006090b000300101031315040e42082e80025124900c1c0d07401d4401d680039a40001080e0000741e6858034107910025601c0400030440c3c030400c800d42143c005081c03040c149840869801900c0c44116140c10711025941d1000d991080303007076102e114005030800d040d81003030320741c2007041200300d4010510782001c210b02a200a0200d00d0526510000021200918403e0031055103090000c081280f81600000d0b020445074810761076216990b65540c0081d47e50301c41103c0ca1503170b00b21000038680894a000c12401d000e10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 761412185 1250 761410935 761410939
    0x903110f01031410142d01020a230127020f120a0302061807030c121b090b01020d0906050d0f0b030303090f011a010518120304060908070909240209 65
    0x81802040c0600c1ca49400175604003080c140e400d1800241801903080f580210f2004054500751003e019080c00e0b040f0660500051040714415030f003075258584c1c02004078410307941041291400c2804098203005402c0654449400c600a40003030071b20321142190f0700c1c1c00003441401192410640c507681c010080d000c840c080f0782200d00d0900d00f0320f00a543e80344107464210702424900f108a525040000d5a9402c0d40e0b44a08000417a600d482c0420050500c0e4403801c4072220f64211035051003c0c800c50700800104592a40450f0321508140060704041a01501c84e08000d82850107000107500801140c186035a83c4200180601150128000601e0312909096150100100f07001c901040040c20481c0011000005c1052000145e4001d910700d8586002e140407650920141c900d003400303245050703a5410080c0003200300c0e8201c01d071701600755802034110700d001c1040c605d001d01c040a0b0410202c0d003d0b041b001400c004000036510f801c100741151841c88021452841a2075603100d1058050345c40c01000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 761413435 1250 761412185 761412221
    0x60e010516060f1505030f0304030b04060b100c12030c09120503090907090e010801050906220f0b2e140a1703030105040f1b2303010305030a0905010903110f0103 71
    0x50fa9420300034250146611500b004080008186860042046894103511700021840d01380f0795900c466103210020800d0354041e40c0c814a0100581b2206074480703c90600c1d82c1c500c0710001c113919000305c05200803400700c0308140c5000c01c000340d2150494101c40c2540d210b01c0241c0d0382a06546405484c5205002d4483c0c0c2228046080c042010340141d4003d06035003600a8144140e078031441c2c418202c41c004c940580d442c0d03010340b01107104121011321002ca0194800212103003140161101000484159011181c2c11a60b408000b0301a6400704145c0e84c0c40f00048880100c270300c0b0b0240c6042d000b04a8040d4007513060f42400d84000603a90031501070024003a0744603c007120840e2034001e94680d08240309090003141451003500a00040303214458403541c10450603402040104030844228889049200a44034480c40d00f040310340c0100302446c02148100d00071507880a4680d4010414600b50703108505001d8000c0060000550081c42c00c030b0f001c68140e4a03410355540f41c90048002c5c003180491480104c1c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 761414685 1250 761413435 761413451
    0x1206090f131b0b0418060e0403020a0807020f03030a021509070608010314030912071409040b0a2028080405120c03160609031d13020c0319020f16060e01051606 70
    0x5010400c1d071702c1c12408140800141c0c0d82c0d01d003a041140e208580060041e004485c2881c0051101e5002e08003aa00140040d41040e148a010924507031200c07450342c3c00760b841811560310400711400503a5114101201610a0f180703401e40181c02c0c8001030000401061015220481e580400c000b83c500050303004200c2c1d1030f14150441c039151078164034003c11001d144180d096042904180040034041c80e8414599030040d41d0342400b003402440f030300d403202c40344030b10b12410701800038013190150141e406540d0140040206000c4614200c019446409013800700410800010802c04214980c05203000f81d071041c0d82e003450071030007401e503c05d02c4c1c160740c80c90550381c1d006810710100e544860a002e00ca5201c0b647e2034107140c18000d140e12114981c02e54064a6007490091580f800c3d00584a1841d00348110303070900d8a030b1980c0c0003103403a041c0c548800591041a00702c0070741030201b2111a00e11a28000c80d0f0101d401c01000401040c03440b00d090b414440d001402040d00707003030039082204194200104000e040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 761415935 1250 761414685 761414699
    0xa1a042303190308070314040204090204090602031e060a0614071a0106050c100b0f040b01021905030703020d03051510020a050604110102100b06180a0b1206090f131b0b04 75
    0x50001c2c0181c1c00074036040005030005d8001e11514582c040c000c0540c441a503200d44c05c20020340005c2c4c0d0b00303c0e00305485000b4400010550300203036001e02d110000899103150b00020444a07a500201403034841d03a040001008034980081ca40024400c0303080000f0382d2100b00d424130003141c0303c160640b81511900200009101c940c480041d0082c3c4410006440c5040c0e01e0325414016145a00f0301c41e64000408022a100c0b442c041d405000321038018015101454a000c1115041c4055084180e4070741d00000b0b455020140d041c401800002c0c85810100031038100306611150070703000c0d09140307400344040c00c004a844034000c2160f4460180d02508480c3c082ca803915020a108001c850f9031800752160050f2200680c0c8503000d0680c0799900500861304100d91005820140b20002d9822504880394800200e0080000710084c4101c0c2c0400a01c04007030304000c0c040c003507403080c02840d81c04008410700074025000c101c520550a280d801440044061012024281181c407880c0d200500d401400100041c000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 761417185 1250 761415935 761415973
    0x150408010b010f0309240f091a130807020d0c080303070c02150c03030a02031b040e0603100e0615040b1002010e0601060305250e0603090a020a1a042303 67
    0x1070182aa00c1c8048259652425400e54071501d40c0181680b5015108005640c8071040103449203500040101d2000f4000c03058008452003c0c006980c1048481e00c000c00005e40200d500742c00c00e40c12841e55481d0141c40d225000385005412000f485000c11280f94010301070300e84504000340009100b582d560381000c620141594042d450202d001d07403000041c03d42d260f040c01d0191184012b40c03401440c5940c5e11000c0d00380095100524000c0514a01c903012007030b04480c00c003d040075000307180840f56141001c00805250843c0340150240b0325040c51107000c046070300400d1aa4004d00b01040c0070f104450a00300040c05460182e01c0260050424400d00060f1075054000c2c118000d001001d85a41e030340c03501c0d8120269402111a01c0c2003007000040a0031416941503901561007552405280c0c0f64a98400502c4079401a6544c100d20b0703006d4804c070703800d500d8041c071500002c0684a070003020b141c403a500202e900b8001c6108024910800c1c500510701014480755254941400809840e0005000c19540880c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 761418435 1250 761417185 761417201
    0x610091112010e090714062d0f0403050721020907031e0605180f070c080d050a0509010e0d0801060309030e0a06030509190f080705030706110301051201110409050615040801 76
    0x1e10031742c0b81c0018454000541c600071948040e040381e207030091540d010a1003002041081440040321910408201c0c0f0510141c0400706580c41c0701e0359103074a5828202d1030a8039a4014400ba22082100102205603e00c40001030b00c0c1c1c140c420f05859500c1400c280d009140e0018401030207099049410054041d603070208090380c00c11507442c0050315a0b0001002202c40440316092415034140c0424030190240d0001c0c00c8003803107603107124585030080400006450050b603c00c1801c9480e041403000c003404c00e005200d079169182006007000c0034120700c0200040f1040c4901c500b41650f42d00a1000e041c070903080c0140c01d6101a06101040750b488070300600504007211400a18080e488000f503103551004041c49007281c00015000010600b078880c4583c40d03102d01c00c102d641d80b201f040501c00062140c050a107445550244a603240d41c5400280920300c4002c0b43c0300300d603d03491f0401d018580c980100513101a200104e4000480381d403800085401511098450b840e10b49000c900081d016005420240c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 761419685 1250 761418435 761418451
    0x414060124020307080d050405030c0f0a0c06080615091c0f060501060809030a03020d090b090607090501020d081503070b0c010507030f140402040b0429040e0610091112010e 76
    0xd40150700040382c03203002e0014001c3c4061002c1183d0b0700059116080f464015010b641982e10b8209119101441d10451002201c1540c00c902801d1040c0129540414020242400e080c1858034054001491941e49694540d42509020a40038082d45600c1214803c6941054098032100501d0901460400e800b21084174030b1403c01c40081181031041e007c4a014910620085061560084d4140c011390003505002c010f06aa85018130042580200f000780074541d000c001d003505042018005201b404140c210034150b61148080304a602d500144403540450780340d030856840500000024140702c102d030f0000825000c0803031420307001503041d0b005a006039410f0b10100007845c910041c20065a0003104103800c200400300c00200981001d070410070726003030014000546642800d5980132320100c2d544d22901c1d07c0902c507820b503510b03040c02d100e1721440d206040300030641407820800088502005000703800005846500080c40d060018081c1c0e41c14000d4840c0390f41c242c3d03840d1510000f1038070086030056 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 761420935 1250 761419685 761419739
    0xb0909041e060f1d030703030f110d02030720032b060e10062a0309170307051204120f051f02031e07020c0609031c0804020102100c020c0904140601 65
    0xe01c3c2812080100c1e00e111100130b0141d810480103072003d038024450641c030101d80302c0d10b80341c4c51468624124000c0c48090b00e14000142c036428881d500030088100c0900f00700031048407006402003d00000140d5941e01c6c18180f412107080901040c02105c09035060a114056003084e401062000d0f0b0704141520603100e0394451482182c3e911030072039054024051641c107006070420f0f0107100020015000c1d803a030b402400d0000406540710001c00344071007160001e2010f6000814844100541071101d490201201c0c80070b1418103060441041c1d02400c5500001d002800181e09a81000018080c0d1a4800002130100702100a04030408019500c00c6880f0140303d504004695140f1481e010310342c0c0a41425401000e110100300240100780d401030f4082581485881c5248000c648900c0541500c0d40042e900c0290340e04091001918021003110411181c908101685100300e50019640c0740a04048400540e60348030790620f0400e80d017005407010161f000305400403c0420340400c46917603183c04c40310381d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 761422185 1250 761420935 761420951
    0x11503141e070203030c0f0901360e10050f0114031017030c120c0f1b0117011a030601050d0509070f090b13020702040209190f09060b0909041e060f 65
    0x4a841e41710840300e080f81d4900074030403c0c0d0f0861200c00a0b0024800604002c01c1a0044400603900205062000c052443d400181202e441d95560490401820311802100d06410301c0c2d00b0f2401103505a0180d280241d0710440c03001e20580c4548202041002240c03009030b541d09003400f561100d804107001e080144a036009600c0c003448c40000450360507450980141002e50480c1101002c00d5000c520134448920a148859050a60510100a8045401c0ba8144e04c0d0f0315440300151103040d00f2402035010b0318000340100b00f145842403000003444095240d407030381c0b940d404005031018010240840aa10329150402201c130360005075460a0b58241c1106641d410380d555410401e80740c1c03400c40160840900c0380f01107104c007042d402814070548010000740c1000a4903000c144410085001c0c281d0104d101401088241d004610710009408000c10520a071428440c1c1d0344136a1107a0120f1602031048800090705202c4100346100d000322001518071f640c03045500b4508083c0c00802814030495148c0421 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 761423435 1250 761422185 761422187
    0x12061d010e070b030910090309081006051f090e1308160302011a0f09040f05030c030d0b01020a030f0e0a030203030f070510090b01061404051f030506030114011503141e07 75
    0x540f072017907020800130890f420f0300444d148090f19009000700c2c1401114100030900d90b80510089071000d900060020700c051409041001c51246000b102c00042003040c0c603940d549d40d1000c00d071020354110900b0050365440d04500c1070f00320718181d034016040f0040419010320303501c0b03035100703405031a40a0703402030100740c00c2d1321640b04102d4152400d030b0354002000c161409032410f00b0340050781e2007802464500803800d800d8603014203603031040307403040e2164000003141110305400b0704c1340c010081c000f88020055150303183d5004e0015607840030070409111030545810055902c610615001e180d010301035075240c0644007002e0b00319410481041b20140102003d40c01c1d140f4851181d805600d800c102c55412603440c000c1c0c140c8041c1c0b1400318105d44d2401c100404126500c484c03140705015134800d40e100c030015105240041c201e9901900241c4a07074100b0005038014a200341e445410b50300840703034819245040d120141c2c0100212803d81c1c030082e110380c040141c00d0a180c50f06d100c0e200252020300101e980d904c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 761424685 1250 761423435 761423437
    0xc1c050703030c032c0c1804050d0c0503030604020c010f0608032a07030326010b1c050601120f0b0a031a0601050703050a1206030b040b07021903050412061d010e070b 73
    0x5400264041d10941c1d155816017802d010007420100f88180c901c0c00301c405000c1031112044100c4900005030740b900703010400c141005881c0c4540c8103854800a0007031103541e603d807070348009882580700d6600428180c01c0844203520249d81d1150340c040802c10710f5590f0103d00e0301c0340c028411000f0784810100110350101c9401e0040c54458001c080a061a103003103640c01da40c014034055a030b40710320198018a8460040c00f0358100d002e032a024882039100d46007412980d111441035200e41440c1d81c00c25003131254590b0001e5220145150707411b0f01040c2e174420101080c00900c000b9104650041c40040d00000780304c1023020740044640000590070b056554038005480610407071310018000360f01002802c031003038840c008030200f05c6140100465666684d4888a4070310b82c0c00d40d010780e00d211a8401b40070000350104410201c117944200e03e02e109804a86001d0803038090392180c8410f030300842003840c0402010344c1c0040f5500c190820490390856510f08114004c00c44085961001e2141240109600c40740c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 761425935 1250 761424685 761424701
    0x5090d05040e0a180c030c030b07050a170402010201150e15010f0c0303020313020d08090f09090a02040e030f04060f02070e0415090f06050a14010e060a0b0c1c050703030c03 76
    0x1070000140c0e0303c414801c0c00c010f1841c0c12045a454403504501000607040008540055006a1890150b181942400d480c0d94002803c3c0d8800d0000420080c3c8003e0f800c00fa03c4994290f15030718880f29990385000503405000d8081441520084101001c00c2098100701458010300f428454400c881007035000540300006400682404211301030320b00c0001034401d4000f140c0c807030724041c0040d42030b98140e4041810388000728000c44040c00042640b40c00703801c00700c00300c100c400c00845130701d2101c1c2480f981d020f403916014807002c0d001e103480700078003041c0c0c2c0c00420071200540380321aa01ca545030780c1c4000c000e00c400180c0001e480140141d4a0018001e9a07401400e40036540002403a418500c0c0c088a00004042c8031208035000303035036000180c02003909840782c548500e8140d44045821a601c00134141104d4050300310601e080300d54400e020054660806040903900c3d50a001595500102203c1d85001e01e0b05450f404e000c4072a1b031905002ea64003001070840e280c860303141413205240c0040140e05403203642c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 761427185 1250 761425935 761425949
    0x110d032307091814010303050a030b0f09010b0f0403050f0303100605040f05010f0c020a140f040608060c03060a030c080a0c050301020705120f04330c0803152205090d0504 75
    0x2d800140007030222440b0000b800c9510442c001100c400f643c001400e098800d90080d8041038000c9603038030380280c1501526026040469440207000703810310000380c280380d045c00340c0140c150012079100c0804c1d0440003154003841c0c01c41c046070402c80590206603640c1c1d0045a411200c4100312100140e0540104151030035a444094039121a500b00070044842c0c0c0c07d0042060100300e15029004050b88546d0100405003004180701c0c0da41050001c00d1000080c413034040107008a141400c200050440401d82c0e0340c008034248110f030740d2510750030002104800c003034001515201640900151808000802640041c45081d0391000c8070758400c1011308030b000d00300d00900160001c05440c1550032900006196403101c0008075420140c40c0c0b40c1440e6881501d8501825442c0e460a149250041c44903da0b10090500e24100c0440c5c1015500c3c6234090001030183c07405010b0014415109581c2c202e02d046062290a06458503611909a000c014181c20340300100280030b04409603012500c40d2040710306850031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 761428435 1250 761427185 761427197
    0xe0a0b09040e0a031707140a0207050a06020a0f0b13021302070506070c080d0f061e080f241308032e08070b13150804060b0f0a030303020703110d032307 67
    0x1d0421074480c058001b40200200304000b40502082198003001e0030207150207070b0042c0310090901c820300401f00200c1d00031005540c044440d020009a0102c4c01c4645554007401c800d10a4494200546480e50400402507110220101d281200c2d205540a054003500131411215191500d0405030780c412040000030305900f6040000100e07402c125004010318203040500010660b0351001e1007d04081c101c0c0e031003500c00c081c808080007a44c200704823420168140e103020300407160041003110220312850302381d59128500c60002500081400b00520a803640091800d50f03a4a408c2e41c59501000c44120520950388040e503801c1c0070894100e84103030544000d2001811402e04000e85c0344040c1d0850100c030303c648000b40c040443d02081c040342e400014001034071402445d003070510b00b0206860846101c40d01910150309070f050a951441c1c3c6032404c0f41c1c4c140c100180d03288418181205d4020000000340054420201c809000c164980d1020204d02c1c00e0290140782e00100c4442c605440328155503010010711 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 761429685 1250 761428435 761428457
    0x271112030a0915050315241e040b090d15020403080702090f07021b0a050a03050d08070203090307051003090605041506170a23060c120106210506010e0a0b09040e0a03 73
    0x8000c8181b0113900c000200700944443c0c0f6080c1c0e6a80b5801031045001c00c074040481e4050b03407440b16a90030510700991011040c142801c0440c804034900a110f1514465808124a40d00313121030321041e1501d0f841000030540d0b9503038803801c10012a5000c0c4400700c3c01552a08000758001ca10200701c1c501031541640600740030084049903100c0081180c80c115032119084100083c20340e600c20071fa10003940b18002078005800c0c801c201814256000b01207000707541017000190a030741ea004c0744003820b03a442101c000d680140640d40440c001d049003440102030519001c184414041d105000d0080031180640510109032124401c4400d1003095141d80b555502c1300c4d07134100014032030050307000000745400c03995244070496100442ca003410a44804502d540b00040d405080b00d00a41218050296410007a00c07060f080010385030224840c8100556040da1240030030303416842000c05120341b8000820a00ba0700781c031340703100d42082d610142005102d40d10701542d40c18400c0e401709c0c0c940070443e059107a5020300d030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 761430935 1250 761429685 761429701
    0x60c0730021509040b0607060b01080f01080705101103070f0c120f061a130c091706240402040f08010609180818092701271112030a09150503 62
    0x2c0c000c40c0883d540319407584214074443d22007801900300c00e40110b10104042c00f00700009403445401800802c0381e8480400180102d00c40059441d08890064440101040c11007008507068018200f15100b117000003c1c110082c03005a1071685d03103080c000c035100040c2c1070b130703d001011581b0400040248450040e030300c3c40703000c190301e03521070300c02e44118401000702c610092002076028648105c0c4500031584d2002410126540300906030091300c002030001c8888030014869036910040103040210f04040c0c3d001484900c0d6000200c95110310380900190344480e143c403200d0740640128050300e8034a61900380d0000d48000c1500030303c0c03403803881280f0682c00c034155034550b1405580300d480b003004000505404158240c803291000e81c4105142021858101080e5000340700320040e2110360001c0d03a0400703400b0075400300d40400060072100c0e0b2881c40482c900c06885c00c140313084004008203500003a290b211101c990000b100408000c0f4a568a0118031920b8049c044030ba07100040c8500c0c005127003400016581 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 761432185 1250 761430935 761430937
    0x120d0905130e120c06060301020a050906030604060b04060c11040207080f070809150d18050d0c0c03021305070908030a05070209060d0f03030209030d031415060c07300215 75
    0x50180310800315103400c80e000303401d00c0c1403c2180c280c0010200025140e42a00c0309100315a08030804400a600c1c0880c0c5030b20080c058006c6891542c426131000011030310654175079002c030380200b074400e41103601c980c2c4d9110090704d01d90340c0b048269102d0075101c00d440d102e89400e2007206d5600f50301140088c00c1503d02c10a05205400c84501180c10040810099032a81d48080c0c2c41c5442100d040344080d034900d00c080c1d0b007900791030460030011414964210f6450000310b01003401c0030240d40c5071a0034280d152050034034801c62035aa600180d000411110b09001c44400380e00701da403080f611500c5040c18940d4071014075549104091841000039014407c080061402c005030a41000004010145010041d181c484503804a804200c0c0801d6000400c410075090034400079200b040b6a04080140000c030b8100650f030420002c1400d420580466003031101c40d95980190360560645008890031a6103c1c1d203202c4200100c0cdd10740c00701d0110106032202c0484e0f60304c0e007110101c40d400b5192508450900313040c0603407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 761433435 1250 761432185 761432209
    0xf060406031e0513030e010201050f010e0a020f0d020d0b0105040f180209041a040f0b0d0f050f030307033809070302040510030504060e06040f0803060604090c0806120d0905 76
    0x7258200001000908120300583e401005020b08100b401d16280c500540741601c0868014150b90504041002c5056040c81142c1102c40c05019445183e950b85981c1c0c00134459054428110034003c1004201c1d6401ca48c0178201100201c80304001e800b60b200c0064500380501d01c9248241d10041e48280803040002001503061010480f0150400b400780300020261041e003600703000c00ca20200001b0900d0714103401078070010300151500b0412a80001c0c0820300710035001d50081e00c1380a00368420000c02000b00000c0c00c2070083e21050382d459082c4803600030701400600040607120b110894600070300c1140301e507541c00d4041402c01140c44e070010b05010320440b07407c010140800d040d804d00c80014940c0355a01304401038039090342c0c0002c1918051070001c0c1101e5911542e06a83c5e8401c208100006481440c01d00d107064000c000140c5980c0c5460002c0c7c0b09200300c0d0082c0700c01604180112081540011410b070081c40111866200c4c4a04007000c1075841c3d6800c2c68440008242d400704000340c3c1042d01500344 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 761434685 1250 761433435 761433461
    0xc030f021201140a24180e1e010b040317072901090c09050d05070e01320108011a04090212040201021c0206180a1709101112090409050a0506060f0f06040603 69
    0x982d14800b141e01b000208040e40081c0c9940707104400c0200c0980700e14505030f640b05041060042550401c04e00c410a030244d4040146602c0e40f15503c9032648035044151100302d6031003590032280c40c080040c01a130070852182e105072860000c2001040602440c01025110409641c1d40c0b604545000c0400c004c0038612181515680202000812088005510b85018041c1b4290300303403980041e098924800c1496040d4691004880280198a03a83c8540c042e8115000013075041d180d13542501000605120700e41c440400705200060f80d655260381008140d100364000d80a49944040e0440c809002e54001d901c41001078104c43d0000d4030300980e200c0381d2a080d09281044503083c0101d5925195240c0041c4200240d001c400f0a0021151a1030b0038180925902c4e45082e20024a907000516030741c84402c01d00010241380071031420310b5a225507101c140d503a608282114806036450401685a00040e124240220104a005030460030081c03c2d00302008005405903240610705002240200b5004803107007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 761435935 1250 761434685 761434697
    0x510050315100521091203040f030f14040f061b0209190f02070c141203030a0b01120c0804020f06070b0c2101030302070504060f0b0d0c030f021201140a24 68
    0x80c1418a81c4521240e003030400c503040e04080d05041114914084100c51159044a401c00c10400010409c2100d8243d05503d4104054180000311003550b448055003410322080102041c00035000102140c03c0d81164010f03224444030907103014000003254400800650485421008150b004214802e4403080703d03050341c80000d410f4130f5007c00320143c1e80111801d6400c880c1250b4284074252150720000040a0111003c045004050112076180c0c04014900894203540e8412001607034082c0d100f007082c0386100d98040007400503004024011000c00d840503402090300000c40b404600340310b0125201150420340d400c0c020f50307640e29a141640c0c42074141c0c0407800e8079400c0d10a00c910420320b034140a14401e40141001c14204000c0c001142e400e6840b569404111000402c036184800c1d0032242d5000b40803c01003840a41c400007030300503100383d401c1e5500b01440082c1d458101e02d5a8802103040c5e031101c2d07200c180802400001c124407210300703020b41f0400210300306460548021451200c075905019003015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 761437185 1250 761435935 761435947
    0x120306061d03160803040f0803070b070c051c02150105031b0d170a12050a0b090402010c24060602070e07050f1e04062015071202090d060605100503151005 68
    0x4124125504c840c6681c3c1c4081014000c040d04140c020003c0c040c0d15000f51304284090700c1d45a0f02000c054449024445100c00c01400c2c00010720001040c1c0c10103882d81d85411040c2c0000035030b650b005164064083e2004000802c0391300d00403031401c0b1500f60320140310740074101800402901c0005070781d00b03c415202ca90074070842c00080d44064181c010303403525054603032100c0c3e40e00d203000d44400030040c05040d131902c8040402540c800500541150702840c09101e02d58607031038040c40c0000812040d07022481440900f282c0c4103055041002626260703420350700b0b180da41d64201c07140a40e0642e800404100e060244c8100c0d00c0c0460701800d620040c40d80300d8a0411800049100d0f254819000034001402c2581144594158440710001c00002c8030000c2c2070700204640750041c4240c014001c8000c0100600416049034801e030151002d070803000700048546101c030f18000c0c00a0000d803042c240956410424500c0c014010015688220740b11203c40d2030800b041010485000d00383c20b62141402014440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 761438435 1250 761437185 761437213
    0x406181a030405150603071511250603021e0f07080c0106060813030c03112109040c210b010c120e130b060d090507031e120306061d03 59
    0x102403651564640441c0e030303401d0034200241008640d4194004000240050000e60b4400080e0b8500711100f0001000311800e80407021205040762010040c000d1050f107590012883e002d041e00e8540100304812151119511041a400d03030089294207022000c480784c1e15460740500c9001010281c2a241000745050526070302c10340b454022a0840100d41e40d145010301c4a1030300100400e401c81c40c000e5000c13a290015a03801450809680001010880307000011040072404019440c03510381825010f04050502340e010310341c1034005030001c610580c1040303c07580300b8138000c0500f602560341c550352040c110120021032101a05140d24030390b0401801510a20103d10380305c0c02a441c984055803421605140e800030444c0b01c6003d010031000b407a00d48000d40d001d82d5141800c5805140780804081045003903400c0c070350f045c580e440e80060310100c141c20080107004040c0410035141446030360194a8110300c00006c60807249640100000315401302040a401d0300d60800c0e16110700401021a040d041c00c00c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 761439685 1250 761438435 761438459
    0x31802190e18011104080c0d15020c010504060b0f0d030c0f060c02030d0b060f16170703020a0b2a03040c0f09020a030b060915030c042324040618 64
    0x182e404925244010184030391402805600ea600006010082c01c0500b0800e072039031204d00307079004030b885882041c00300d10800610710403071844a080c8050840d290642001094081d110460702141e602e4075010041c3c04034540b824101001c0d11001c0e00c203035800c0f102c0340d40958010312980c00555458000c5069000068902e0040342444c40d02a07015548480c0c8a00754a005c0e20241001c2500c208401d01602c1c0307500454400b034480340c00340901e00084020300fa06245502076400c01c00c074805183e00040d4401030540000b07007040858440d055051255035100701d084406050012100800344c14080c0d042c010003c031201551300b2a00070541c0c0c800403555103950a030345003495400450416004200d0200c0c05030140b0034500a2103055550a00d05000c0d0380c0020300c2d2032080320041d440c50340b01101040404140905560150500503d950b010081039042158040d100c001118801c40320314241100809109541488081041510500301810004152184031003003248220840440f080010f0030749001c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 761440935 1250 761439685 761439691
    0xf0105090c1630120f09150605090108010b031b011107150201140105091b0421110303180123071a01080601180f0605060714010c031802190e 62
    0x31403880b45000200c80858940d803003083d00d0b06040300602c4031112000d60440b45501400034032030000078018a007000c28500400e60850054180c1200c5443c40c159201641d000302c0964004591400e8203a0b65030345440c0c02ea92203c3c6245406030840500c0d4082203408031102c1c130402c401414151240e0341014440d910703288440e440400c04e108811880d0312066020301c181501c8030f000c0302c07002c1c046604080c04a000c480016100d070a00d080d010108800011101d011398010b091300000ca025007009101d512540103032086010349000c41610707050380b400d19001088a180c40f11440c11440b64500707090054031410f04c1c0c842031481045141c40052081c0400708001d20b0307901d2098100f100201403601e04a015460160040e030042d81c041b40050008074203950b0040c10101400c04c0c0400d8030200c2803106000b4003095802140c0003c07000c101541042952112807030080c800c1002040900801c500440079240e140b9118800c0d068188060300141c01d10360003040300c40403800c4038410480e50320719250401e50821 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 761442185 1250 761440935 761440943
    0xc0f15180201031a090619170a050d030b0936010f0518060a050a021902100c02031305090405010e0a031709030702010504181508010204030501060b030f0105090c16 72
    0x108a4a8046680601c41d003080ca07074489510b0b10b640701c40e1001040d01d00d01d01401c86031141c8914100380c0c00710103894901d08003070048641a40007006c12440c040340d8600109c0012581070103080701c01c1e02040d2080c4900707240c60100070081c4038540c0f0303081d04080c421007000700300e81d64007140c60045540700c40b101d18120003240b00710400094008002c0001d50b0807605c0291082040c200002d00482888400083d0540c00c0070445100240c282c844664040082c0f00c0d901c0c4030803c03400800c100d0071f00c00f50041083c1e100c400100c9000d201c000c1d0201030480c4c03203216400d0305050003081c401e0b0034070480c10b2501c600d40d4030606c150000106000f0001d901391030003252202c100c00003a4440c80c5120381074070860040b504921841e000b035041c80820f50003e402030040b405406c0d450104900b20305981d885d5500084404c1940c1848a030940d603c03620362501079800350006451035801e00000045005003801124403a52801808200507401e1408000c07007110041c1c0025256003042c0140840f104229411001c0f00e403003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 761443435 1250 761442185 761442221
    0x801080628060e070f120b01050901110f010c09080d030507050a2a08091804031725020607030b091b0c0a1707030801060503090d0806030f060108030405040b0a060c0f15 74
    0x2a05c01c0041140f03940b001a114014140526240240d03080016501440e80c00d0030000c0a40c0c00c0503004500d840114042e00140d982407000c02e59505400880c4a402e840103c001c0c0c82d000c00a03020154246c0303000787d0b03104000540410803030f4540d62007000c80b0442d4140001604070181c119503103410814406000541d85900000780100b51460034440c0c09036441e150360200b0303080303280c03a03113010303000b08014903203190002e0f0f00800246400801400c41c4100032000d00100c81d0b2041e807568020b60340e600446105010a1900c641c2002c5450680a5180706007a100c0c040312050104102400c100e0b00b00d0554841380348200840000001c0d44628030a900d03c202c004a140c544409090007006524180d0020301440002c10034010101c002280c54001000d0714100b60341c8540b078200210345084101c52100761140070300c40c0045013105d070100040003110703070803902400300d4001c0c0000c200040d00d89104981c00711b4072400c03260700003803a0720f0f100700701940c083c145041034010021008029606c03100e42650b24048 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 761444685 1250 761443435 761443457
    0x102120d090c081e0f0723100e10030b150a090b0408010c03060e0c162604090e0309010519020109060228090803071106070807120801080628060e07 65
    0xc407034800c00b00085074040090a00e0243c1c441c0e07407911401280102c0401c41f407a9100d500500560050006024001800362001c3c100300c3c082c0140b801c118050715503c1b401c01c940400c0d00c01482405101c40180c0d00402c01c6a0078480c00803203101c1030b0b00c000f45600034809850340000703002c8041d1000d000200380a000200b18040b540100a0032912943c00c240300e0400a0818008108000c4050b181c00b400020074814020155080414105402d141031090040112a00000503c00c0c000a8401c50b004560b042c0712a042c2c40385219168000d81c2d0a0300c0c001102400552051001381986a0182d1012300000503030707001a440740005e907407000c40c0b0340e40000c0c0c0090311800c601c59000400c00c00c02c07110380ba104068909000b9480d440f8410340340090483c1840403c1c2c0400ea03a2000c04440c04680c0c008000c0761f07281c83c0707031401c1c0001c1e00ca000075550109803001c00000e40701d071001c02e1303451080d00c20030000d244881c0c1d019a10f212850007001e0308400b1079900c2c0808144040c0240805008404940328200001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 761445935 1250 761444685 761444713
    0x1b2203080c01050a0c080a1e1a0316030b06130603051c0f0905061c0b06040905090601140a031403070f260906030105091803040b030a0506040207020102120d090c08 72
    0x110051305001d0041d04e000400590341c1e5201c680d00c3e4108010b09030100308896119045001c4c500141c40003400c89151a150100c40c800c1080a031803145400c0c1c09580c04003149032aa4a450700d0280310180002080200041442ca400f0344104a032100c030481c0050030300d450303440380d6103403900111010080c0c0902030030100405400c440c5c2c1e8125041c16140c0b5840c1203052801042140c05103004500a10390340001039107400305144c0080c240360402405294031b55030f0b95140030000c3c00301610300754194010500049019a1410003410140720058009a552071440e510785105140c5150050100e0105014100014660069444009000d030300c000410300c07182c42014141341c201780002e24241204001901d2a0344501d0162411603400702c0d4400201e40d41c640f9600000085e001000c1032074000000d000c6605841140a540900014a81044140d4452017070100301d108682d0040e0140e482010302c1d5201151030b00c000c00c00314080d1100403403071840d50764407090141036581140307000e81c222040b00c490350 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 761447185 1250 761445935 761445941
    0x2030f12090a050f0a0605030a140907090e0a08070b070c0501020d0c1103040501120b010e10050d0b0d02090a09030216030506010509060402070b0112020406170d03141b2203080c01 79
    0x9030808490b21344540c9103002c0001c1c1c4800741c9204d00800e204002c0009000c0f590540e00202e03c801d41c00b00500424a0a403160f5600caa141740a01309040340741071903201040200040c4403041c1c55202070040d140030655100ea144403e0010003145c20880550201c03400900e00380050800c2001d41580400c02c000c003032202034050f005400d500015640217000400c1503070b0b4480342d03845d00b54100d41000102448500c0040300e542c00d20100594200803642c004903142c80d4080c0081070b42d9000410308005680c001030411420155504001e50701403244000b280701681541c1c041808140700c0d0044404d0005e081155101d0344203541d1045c1c8203904040010052400c0844c2d503940d0045048800b1454482c04d40d440740042181070154044880e0303030400032411074a5036405040507124035101d40048014400740a9554070b01080118006030510503108500c000c2e0f0094039001e05905500a01e020700c0113056030080c0d400c001e607c1c514070201c0d040300c20b00c05520314489602035030051021513a6490182481425 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 761448435 1250 761447185 761447189
    0x1050702161e330f0e0f0414040f1403040f050907180b0c060105030a21050d0204090c11010b030d050913060605030117060f06010e060c010c050c01110903030d020702030f12090a 78
    0x6101c040f140b244545030303002500d6007610600300d03a80c00d440d0711071b030022800420308c404125083d500c21505020501c40080e00005507030b40306590741c003000711a10300c5103503c0e030195108641c030b8041e8680b0140424586a00440da0004071454110380914180900116402890307100da20420400503031030051030000d00005014060540051480004603510020700360302070401110986805045a55458443d20890b64079015005081d5101c0e9150310103500101448104240814042010a80d8071081030041d10f600070700080c0030745010403086105554582c40a000541e00002c0740c01311120944c2c10b44519400b402d40d036500c09449604080c0081180c81c0c0641403400540d21100421520000085050b41c1c490b40030f02e0180e44040100380440c07c24010b400c5280f403154200500d0a040a034040b02912460810340024484c10150040c00829445030281458140d04200146810b51700160020503c95102408581e240c4462100701402d002040900000d07015002550740d04a26041c95001c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 761449685 1250 761448435 761448437
    0x50f1204090c0302070b1f031401140609281e02040302091803030109110f0c0d020c010c0507170c0a0303051c0b030a0b07020f0d1101050702161e33 65
    0x11508941b80c550a1401c030004260142c000c02d8620030082220400011b08015680208007031500c1210818407406484804543d000c21000080000c015203803009aa43c0a04201c081c1d41e441d80c2182841842400200d5450040c01500c80c090001c4c5404110030800d102d09580f0310050700c80b415441000030078580500700c40761402d28880b07949103040010007228112184250005610b00c00d08a000c4298081e050100c401040c0105200d01b01000105191003c800140c0c01e03100aa0b41c5d6000640d481c09520201034500d520000b400c2c000c60442d1828491082c0c580301c102c030880905803001502c40c4449400880005d080817030220004c1d40154018020300074401030078001c03050290040f035660070741d928000d8180c0403854042030700c0d0b0303000f880300c80d0300345001109403250f5400318100a01550343e65040d00e249986440005000644003140118101250311541c544a5282044010b4000c0b40088103040c680b04005000401101c80b1410f90302c00e926960b943c0314282203843d022000e0400e2910020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 761450935 1250 761449685 761449687
    0x815041b1710030206220f180501062f0a0b0412030c020102070218060a030c0f080f07080a170415090306140402010e1302070206041e090b100c050f1204090c0302 71
    0x840140e0394402681c1050002881d190300c051a540051501041141d104c28140d00003558080b900100600c0d03850504e8140d60004d105990b40c5880c12111820f07140201000c100145215000c3c04251810104640c1101c01c10dc540d0491503403034841402c203040d90210784c010615000500300b40c1d014018000e030744451b80021410700b034142d004943c81c0c004040f90310703034604c0c8031000081003070780c60380c080d00042c540291012103a99103402001809107068050080c19100c1d6034100c03442d4481c001015415510f13040c0c040d01070303500180da540346030300100303030740030300c8130542400040f4a00c000c10500550f5402e06540d40b40b140751035410f08004442e01503a6103a0410840410000541d0300005920900d00c0103503041d01c81e40c4680707924003000b030042c20030007984000e00190020f2008028452089049112030f9180d1140c0e40e50049070080f18181490f054102d04a860008040d034007501215140074050000e650303180d40705800082c10000c00c3c8502c0084044041010310078907201d4401c004441c500c5003070031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 761452185 1250 761450935 761450939
    0x130c03230702070e0c04210f0803100b03010302030c09060d05010c1d0d050c01110f060108071d071b03090909050d03060b1602120a02090f0103060b100815041b1710 72
    0x5a15540708602803098104021300c4894504484922500d00301074114084034088d400c40e2800350308a17802582d2180d100c602d000d0300841c2a03000401100d04907070b070040007081e1907004401489280b200040040780d005140020240101d4000e00400ea140ea8031940d03400d41041c01082008100c603642c0c0c4e003260141d021080200c00142e40065a01c000070f509007490212070310260f0a80340307014148a01019280138120000441102c00120071090714a92400a0828440211008120501220700e40009480289840b6051800d501d26111507400f901e41002c019480b5810481991180b050441d0280e1001c00c0044942c0e502d407181030003900c91b140030286450881c2080c603944210440001c2e10820422907400503403102000f100c0300e200d130f0140180100345005150400525424402550007605003a0f0440742460100106007034500ba589800825890f07001110000500040c50365400954580b181c81602121203c1017002c0c0c0210b540d0703244004400620b4040e0030b1406860049110568182 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 761453435 1250 761452185 761452201
    0x1031404150e070f08010b0906010c082704051e060402133803010311030106030b04151d0a1e0203070b0a1707090302030c0d02130c03230702070e 64
    0x8001e201a050540801c403482a460020b061070481d03131113161004da05034800900303440c042d0032159a1400c101d4014221f030342ca00d0010340d100c148606000b010445e080015050074076507040e04c0c901404543d0101c01c40b01d108000400c0440b0415034421041c47c00c0d6002552000c464480d010b070f80140c040e5000c0d4141249402c80e01c2d848155030180c400421000c880081c1025200030b8207110310700b44100340302c01c04207001c0d4003604654020f01080c1c0f07140320814100086420140241c6048036071044107218556181e490788409480e51a648d44092034641c0c50346911071000e8210b00700a201000068a6402d1040c5007138103080291401c2a00381041c844601c0c000b5a4000c580d0b40d046410240419558035091141182d0326a0b004001402c0200c10500f0b0101555000c0740e0042074034800c3e82240e014072903140411400203400400294003502c4409812480b910b07642003c0c001044604000c6640d40c0c0603022a00e202d800e8a06c0c2c071106a2041c410040c203281c0c100701d403400500e1603150b402218105111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 761454685 1250 761453435 761453453
    0x50a0b04090b0712020903030304030f0f0c1a0402062205010314010503071716080604020a061e030c090306092a06020a060903213c090f0c09050601031404 68
    0x20010a1100a411404da84c002a0b0101e50700c80c0001404e03a41c1c2c900e000d00c0d001e00b06013485000c2d2000562b40040780949540a2a03111111540046000307081801c90405010b039120010000c91708000180000d64105c22182400d128100075140000641c50910700018100ca0b441444125644507500040215840119591303081d90040f401e0310b041c0d481e2400070b00340f611500006003896503522080000360094081146030140d03200700c40010509a032840300721200d5041d540311405001409044504441c0281d00c406000101802c041e1002680d9403581c1d411206000015207036106680c0d108030744102c0c0071444081b131000602c03489001c03e046c190300a6454044d130100901c025540c42d003003800d160103051800fa82e04c0aa0f1604e009007281c246c41d95010701519401907289804e2a950941119241c0205a800c1c0074001402034907400c4c04c1000c03034003400b918031055078001000c0d0055804548110031b245c1c0a010070b4031001c03509040c95000102200c8180c01c5011450310354000340000201e4180c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 761455935 1250 761454685 761454691
    0xb04090c0308280320030721110c06100e0103200f0409060c09050906061c0b122a01080406021b061501030501050f0a0b0c030c030409050a0b04090b 65
    0x41d032081c0c99240c0b02009104003d0041840316120340895480005154142c0150300301c00001c41c3c0410070002e1070001e48646000c10b48145002c254004081e8007040c0a01500b4210b4402d5038001242005585078401d810381c2c0250388142c4a0340001080003c1071041e402d0f90310080100c140821001d62650b00d0304822030815026803249048020304d0300116641c2c69009043c1100010400c201c0003150389080c8000706051a20100401e00e981400203491600e0b02500b4421200034064902e00200341e1008001310104200c580c0e41e150313603a03625141c03a848488004c110b2101460041201d1141507955100902c0403061982d03404100310140034890341e110840541180e8451005600d8031003150301803447d036000132a000503500c20322007006941d00c2c110008060b012030070f8904100361790b02c41c02803048400c41510b10b10b07000040c02c0020468101c0b11001001d030140e002d42078909166104a03901d0569010368401d13010780b503e40007030013000006442151603208080b075007007007504400c3d540c12030408002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 761457185 1250 761455935 761455943
    0xe070f080706050f0c060133120f181101091502070b0c030720270c090a0e0c3c1608040e01142d0a1205100b04090c03 52
    0x400d00000913464141694043d51a00c2c068450130768482002d521500e20344843c0d614548040398160781c80c04522240300080c8041d0783d0b5560204111183c580003d4045034591140c4c2d02e40e00d40402401007500801c12011a11610414106420180004204080701c1c2c110395850f44048910304200f5400060180880e41d00612158444508590450560080080241900b12804161405c00d44014000c0c200c62404807a08403031405441003082107208119480c1c2034000d41807000c904400075800c060074031510000d01080c505c81d00c07415071000c4908141c0360000f101034089164180318510b401c0c40039828240f800310704680018a40421502c100e0710003c0f050102d4005809101a080c200748040a41d4118903c190364558030100800304000034490358100c260b0b000060802c52503c40c8120340c42d600c20811180d035081080342d40500e540791400c00e01d90710482d2180001008440010301d01e001c035006001400ca8405082c807068180c4a07035006884c861441e010080b03000804d40d900c0001641c3d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 761458435 1250 761457185 761457187
    0xf0103110d050613260d0f0204080a050d0e1f0c06020405041d1501050d1104090b09060405060903091503060406030c0b0304060c03090206090405070e04020a02010e070f08070605 78
    0x100101040907808071400160182c0116070400040d18007400022641910810601c001c0000c8860b500d000200c02c032070006150b0200300114003084805070040d10b02c410f0014001072801da5681c030681c0c80e01c640700304103c855030000b40d01000c10540050160102d04c009a0f040c801240c40f00c0d2003031010b9400204e681c0144000c115054043c404039038141e40160001170010000c4071400c010040e5088503000d0f11105600c00c4207404403c940a00034014120707140642800f000720304641da00406c40c0105a0005d40203917841d050000816010800540074100a0000d0549402c0ca414200c4c00c00300003d103c029154010007a1400700e484801c000ca02050015400c42d0312600e59030001005842584d001030b15217030600c1800716548160740c004600072882148200105140c803070081d4180c03005001c1c040d502401c140075074291030815811165008450346000404012200001000ca0300300141060050f9510001e15003d07010412000c0c0103021028020b60303d452030800303010b56a0340c4501a12081000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 761459685 1250 761458435 761458463
    0xf05060a0201060317120c09062a1e010c020c060f0d0e0a03081023040506010c0c080708010b0f0a092705030d0609020a080c0901180306061703030f0103 67
    0x1c400e60180307000e59800550030002007003040340728403142c1110001e00156a649000300743c96a401c0000c880f81d580c006044e10341801b00505900180b21140300b52000c00c0c4a102035198142d00c401e100e564092088016280310419480d540c1508641d2520003480c107542c0f0408071449280d03500b20545000940c803c0280d9a52100440700a01402c000c0013028654826140d2031070400d50801103d5200f0b080726180700b101e096403415000c0c0310743c0b510324040c0c8130325003584007401960405400490b84541d040c14101c0403013100707a682102d91500740c2c0c054656600a000c0920000342c0a001d0074125480440d41011105d65a500107520a0010321412941c2a6030300b510034100e4124900d18442c45004000c452001c00c0e075410a40c0e01c0358010711003001e085e4504000428000340780d109036180040199213482c81c4c2c1c3c3c1e4090146882da48000700c054113000c1507072104d480c0b0000001185020f144035490104641f45400320f00e0b500d004829a950034560001c2c010825101c00f900219030450b42c124454040c045 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 761460935 1250 761459685 761459687
    0x24220e01020c030d09120c150f0b0909010c020f0102090603060402161e0209010e090307201302190c1214070204090b0f091c0818070815090105010f05060a 68
    0x4401d55502d000c6902011582c4114000c01c2c0c0d2003421224004d81e0425940c041c0c070720f0111051008024010041241a4403031541038000c0da10105402c10386040009402e44070f800020350100c1d049490088981d11082c000b42e0041e030511a44042081000080d81452813a8000801ea03000040400d40129800700d80f03c540704402e24440c0400d2500410030300d04078421210740c40614565080240e0041103810000500004005001e602c283c11600c040c5052003901d07540d1076103200c010702c03000d001c4085200c1c004c0c4069407498005450300701d030318034010b0f40c400b651200381c0180c3c160f01d440e84045c464140100320115030608000c1484003020b18011540303c00300a1049064052000040e4009140100307031410054060750303050190001c00910300c803565841403016074841807450098100000302d628044101e00980891381c116131590002c0752212186035001d4907204540c4e00030341c2c40e07901000c0501d1641e078070f000c10306411a0560000b40120360411480b29030804480c89407a01842001644048032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 761462185 1250 761460935 761460937
    0x316050c0c0a1e0e0403051c09081912020304020a060c08040b1305031b0609040903020705130209120d0f1b0507030506010521060705070213020324220e0102 69
    0x50940209035180b1243c6801c01d150010f003150f501d61520030390200010404480303040e0034034469503140e40c48510f400d40303000c0c0031085003881105036076950303840701c4203580081c502d0006480f99940e080c207400c1c60201a883c000307148035420a4541c8400e8410024080503840e541c3c008000e5a00a051100c1000403520b003400c52032145a002003201800070035018640c40241a968003202c60803000c0fa0030700c4c401d0411000f59500c3c1e8048255004000f042400c901d070401d5000708520030f000f801034a030700720307520750100300b00003441703a55481070390760010702480207103800c2180c4003002d103402004007000020b03004040d0940000f41d1941051001d105041018102075100d0f18140702d80c00400e030340b81c00365607141044e903070701080c091b90b8819040d1041030f04900e20035444888080c05114000c0030180c480240c141d0b02c2e0703880803005a0701329000c000460343e5403000d40011f60069841c2101484a02e20b407980000900740c4055130684680d8860040d0396043c01c4440b9000030030950890005550342410b02c0305802 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 761463435 1250 761462185 761462203
    0x6070e010e0337060b010f0e01080f0703060506070b040605010f0308030106120906230a090503270604060807261b041e05180c031305100504050604060e030316050c 72
    0x52070000121000804c5801d400081a143c400e0300c03012504e01c5182d000351100043e80003401c0c0050310890008429079110300c0404d400c01ca0a003000102d00341c0352408103056601000c0d09540c1c00290505000400c2900e10030640144006c0b4410b400803810f59440052500c81841a0010014410340124400d030003070b44010074144e0b06c101c08000d4070a001025a10404041d00580da0040210300010303d01c8001e4011040d0392503008028515291585000141601711186580c0b41814903031400c40103910f4a04c0240081d040c15100ca038107d240ca1000280540c05500010100d0b9100103c246c80e00030750001c030580c108507044058070b1190b06000f50100b560046901120704d4509006019000d5a0842040c4082c1e0300181d41100380c4d200004201585200140e869034107600081000411441c807e01718400410b00c1081660402d040128080040e28405d541c141c03039036005001400f040042c01d00c41c071034022601c00042c508504d4040448007106d0f1010b10207505218002900b000d0040050018805c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 761464685 1250 761463435 761463523
    0x7020102151e0403030507020c0906030304060c0c0918140c01170714030c0405030c03070e01151103070b01080114150f03031306091809020f06180901030506070e010e03 74
    0x740d143c182802006482e00ba074071000036001e0480c0d5611103003050300c0715601c2400094021864185404001c40312070540e6007041c0c0700780003440408034102c1c12034003d1030440b02036250150003c3c42241017941501d60600040a03113035025524034101640c2006030f020001013103111800e6150754a010690f40484998208156041d0000400c40104050800f03813050324400c0c1d0469103203040c082c0900d41e0311140e85c054820020b5090004100120594a15460440d0075142000548010314455490358200d100201e540301d09040061111b81c0c024450854180742410b0f04203114141600884941060800464014103d041c0050000d4908000b15040d1034030a072906550160b445900a040d10000d00a05a41d00400300d454944150b26004030014190010315101240ba640c0d000c10a156100141c40ca4110354442488201a900c1c4c41031680294011f20180040d4945040001c0c180c0c00401c80103410721039000340060313680d203000074148866884c6511074140b04080d042a10b01780c240e800c000b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 761465935 1250 761464685 761464741
    0x21804110406030e060603120307090812120a09120e010333080706080a0b0109030b070206100b040e0c1303020a080a060f05191109100c0b010b0702010215 68
    0x300d203001000008008075039903030b070f0304204401060050070348070070050319001d506034400104c0e00c0e00392801c4070041d0341044041c01d1017644036948810036410103900841401c8040030100341044190f070051051a80a50f8802042000b03040300da9603003800b6214250a0780410043c0007044099074080c0d484002503150f24020309480102d8250402c0410742035508083c892a11800002240c90000032010107032400d42c0c4514240b40d440c00100c0006085074100b0604015030400700001181c080c1c00b042d40120041d0b0b000d01710305e00e8040300d0714207032014a500c02c0b08010f004002c1000700d0743e0f8904900d50000701180c2190340d00c4d600d035010681e0030b41e01904003940c050a480c0000070000d000140800d4214411481804120741e1800014120b80083361440d8028a562014540404155000c090010152608142003207036101c0458540390182000c2c50204a0000291040c0701c41c0c200c115004011818031603103080442d60000b5241d810b800e082502d000d0701000401e10030180b40041c5111910340da1031003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 761467185 1250 761465935 761465951
    0x1a0c1b040b061b3a050f040b190905011205060406090e07090c080103021807030e06010f0603060902160b1803070303021b060103020108010b0a050c0601030602210613021804 76
    0x9541000050b4601d180380344105880c045084c503d0380c242a4003490445400310064090444080103225040e00e020708010040100d0303010300c43c008010308003400c130742550b041c0c4800340c103000551802e280d14084030a00402c51010880c507030307100c5e140c0711100a010201054540304d10001c100904641e400c0640d040341071580d45115501c00050000403500303841c50502496050100680300c1e580c080c04080d400104428030000c2d01c0e1421009143c00061a140000d038800c001d03003149007001002e030000112220f13040420048140d050141601415034001c0031840c2200034820000e08244048008000f10100000504040d01843c00c0608044021042e070340e55101628000b40250300030a842c3c2500341e00c0c002c0a003400c020008070306041e20b0741030319404c0c003a909021120200d90400085801045010401a0031001080c41840d000718443d034805a203070b21080380c060b06425080562111001001c00030000517030f8a101e04e4811255220000503510b0000c0b13040c0d4401e40101740d084541050403e1740d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 761468435 1250 761467185 761467207
    0xc06080402091305030d0c020a020d12200304060f14030a090605090c0f0402090d1b03060509120306040b0103091a09010c05070308041b05030d0302041a0c1b040b06 72
    0x14452059200302d4072400c1c907503641d110811a009807070a01410070360090002ca410b00a05901c00592aa928011202c811105500060301c410a0903012112001c103014800659604080d00c0540102001ea032a100000403c0140e6030703d0146100b00d008002c0c07280d801004107401000075010102800485c00c1e0742e8070b0281d032020b001d000e00100032211585004001040030501040ccc80030300314401881c00c0312220010707003040080c3d00400c1e417417507000e904034401e02c0008555440c1800388001102c1c0c034807203080c84c6003040c1c001c0b01d10007010001150000501e0001d044103050840e41e1080045500052000400e40124020582404d0081c09100d004c91502c003000082c2c01c41c1c074403400040b0020302007040e0145040f5600c0c014044010b000c109200c000c240042e02c991065140d070300301c8840003107206603501c0010f80381598480c503602c0440e500003003c0c013003800924601c20700985040c81451501100043c065031700e00b100104120590402200031030b03d55195046540071000082286d80c030f441d82005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 761469685 1250 761468435 761468447
    0x1406091302091005011206030b070804032f06071e052101120210020f0c01050c1005070c03090e0103080328020a05221a070602120406020a3b01020a0c06 67
    0x30f61740412494036420702d13035500314050503050703d0344803c0d0405680c6411605841c0c031040a407049041c00650f44101214850120001800d281c58010046032100c0c401030180c00c0c0031b0302909490801c0000303224880c8a0f000b90002d007a01503210300c1d00550b01d518240607240582c40300081ca1a00c141c100d4000100da1044000844265000b04c0d603c000a010065007a80d40e00d21407280340780309800801005007150300801c041d140c850783c000155010700058499403030881703000b114808040b8105058400c149a03000740824090410072200903c1c1d54150340380d130b40d01408010114012076441e80b01003507031042c0c580704010240180300310554594446040281c040d4024102001070f03c5121207402144075110030140c02210042b5219a40ca000d01280e18056079000903800c0e04e200360200b200800b8024101c40491013540507a0b401a2280e00f898030003080d8010440002100d404034901c44c0c007a07080002c011120351140080040c0517241c0c00c00c0140d050400d04500a44001d02202c40000c0140e0000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 761470935 1250 761469685 761469689
    0xf050a2003060106080105060c0a060e21070c09020a1815120b06070303200301060305010905010e1530100e0307030e0f1507050f0106080114060913020910 68
    0x60908400c0a2640c09240e610320b803d104040000e9a1070004011030300304135000702040a8200150381d90100c0c2a01c94209456400b000d041940c0c2c42181c01c1d03c24a50a8a108a1903192040c4954500502522a072041500d10b000700740000340c5c005100800a4000d410742c00009039240042d0281d00d594a107007c0c8201e5120594001080d00e40c4400c0031700005910803a05940401050b03517082c2003440e1012401030801940758141400390302000c02c92000840c01850084c02da5503070115040d07041803410703c00c0d00c8041c1c0c803503616519038600b808a1325a1000c40c800c0030b030809070f564a400000b604921006106004100d88000e0048907048100c128041100b5084d241c14190610100d40e1200c141940c07840f0b4050040d0000750101400d10146c40d008000d50a01c1000412014158000c5181700120f076008060480e81c03517002d80c40e012081d0401f030140c10014000c00000300054031101e50042d40358080140003e101e07c1c401d0000600445001045410b080d402400740c100f145440c2d0441c2190030b10394 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 761472185 1250 761470935 761470973
    0x6040314010609150f0b0307050f030108060603071502030702040b0a26010507020c03030409020c011b03020a0807020712080306030a050d050403050f03040f0b18030d1205010e041e0f050a 82
    0x200a59009107009040c130702007242d161412540842d807400d9540c280d01c1d00041c200800300102003202042140d8030001941c0030b004c0641c058070050400100701454141c403613010040b14100d0321501d4403002e0700401510240c0c0d4040c0d50200300000313520001902c8502c580c02081006000903614039495065081d00080d202022008001544408009980d6a0000c1004584c10752041000340b040040d60340192034807890303880010440055051017189078410824044001030780c0482d80d810303401d6020242c1a044003241c00500b040d6800c0422a0b0300c01c0100351030182544000201040d40e940f01081b4034001c09810078107803254a0002500109550701c9803109031064491038803140b98800010085a0480302032342c65801c0050304d0400c80b080580c000044441341035800440754040341e20184443c0f01d0051642e611048207006100e456412104103810080c2c0b100600c0e0100b000003400e1a441d50a03a5400c0f1100d030f0004c0036070745000005000080c90007440b50007200c1c0403800b004100300b00b07180056a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 761473435 1250 761472185 761472191
    0xd1e1d040e0a0204180b011a0c072d0e0112050307020316170d0507031b1703070f0c02030a03180b0f0316110a02120a05030c1b1c030302030606040314010609 69
    0x817a4000e44000c80703110401030190041e6000420140b14001c1c82910201c11904486040064202041d070608500c2c0d40700030a1009101c400700c001d40c8000342e01070400401a218008258144491039044a03014040d109109241014900130310a0030001e55207890360040440b00c60807411180000d1000c040c0c454030200c0310340458070065030b01300411040c6018400e580c406080240315202100c0e000341004083c031550415101c1000400d2040d10900700c0d840405452a0752800c08400c02030100c90480042002c0000c02c02e8103400596010400d11141e075011729014084100e40207450b20051200d42c80a0200d12001506030301144a000286120b080a810640030208010f00305031009501e0032044200d03900a40800d400510b898241c03000840e8509040b280c82c41104c1e9030700d918580c4130126032074030303070b80151103090301030348440c4c861090224207035802010ba014000003010b02c441d000200a041c590040009007554a80b00d06039801150413488404142d505060750900820860161001080c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 761474685 1250 761473435 761473451
    0x3020907021f0b010f170606070c080a060507080a0c0c060e03040e19050a0902090604270b0f090a0c230607060f0c09051e12010203040b090d1e1d040e0a0204 69
    0x80070700908000005070307500c2540141d42c1c04040008a43c040c3c0030440e08ac50f030106000c14011f5080110350340752031042000007400d05220074040c0010740014100e00000e8103040702c02c0040c50f8840d10408811b82d00c0400440c83d4515a1640381c154056078108910189101041002024402609101c4150b20703840810032074540180c0501500c450480c0a07420000d070501290b0242030644c044201300c0307048803903210106080d0154181c2603860000588502c106001406481d102c0414415084a50348000300b8801d4034960f00c04211075807511a50b0160805600d0203840e184a80100760440100201f1041ea105c82e907141c8074004100c0301c4d507142c510a02e00751080440038082d83c21303901a11401001018800101481c50b03034804508180300c0d800c40400074583d140c698090001e5401107204c0e20302c0e0b2400d480c002d2151403402c8517a81031841000b490700141c80003012080740c59500b005840c6006414243e807440300415000308003d81c16000b40c900f90000c0800400420380320504d91085405100c000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 761475935 1250 761474685 761474687
    0x10e010801060b0f0904060302100e0310020306101101180303090303051f181e050613020a172206060609320d080301060503041707030903020907021f0b010f 69
    0x1000e9006035084041c0c01c204903d80d5810780005400174140041c4040384154403980842c04680d041031228000c600620444206803909000103402031030810800c50540c50448000340541d90f140210109100011403200d00d512401e40100107401034444400c2840c502520b001401003407101000c0e0000b1349407801040383c0c4014680d000100030044440041207608100b50f40810620392000501025601c0505540e2a034841c42048044405042d00140030314084060125050320160a00c450310310401c00000e101741c1021542d1080b90b10010000d010b40e031000b12440c078441c4070010810f0700d14240441d0f80e080100383e41041c019074643d07a47d4409019598015110704845c0034609035001003030a50040442c5858542800c49040001d20300f060480c02307901e40c40010f600a800403400158000104400d01409010501040066a04a078036000c41034900230000580c0c5c1c04028810300c1c4160104403401d01c01c01106940481605400840320482c800c218002d0942c0c50205002c40d100180010740d40e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 761477185 1250 761475935 761475941
    0x906020609070b0d0e0f0c040b0102030f12070e1309030905030c0a0b030703180b070912020d0b090c03070e01050906010f0503180703061418030406090509090c0414010e010801 77
    0x60514034008002d20342c1410b0030701c0e4564200c00c2d903807518541d480c0145000c0c80000c101c0d0312492400c0d00701511030854044184400d40301d81200850655000b0410003601034001e20459218540a6940315010349442c0d400711143d00284001c42d510001e0001040f44499459000e82206072080d01c603c4d0303015540d542030546600000c0306490388030700350030410848900d0000046a001490b0318002420b5440c40380303098022110194141e421456400070041e110b80c11140d4180940800c100258a9408507070000c2e4022881510040c07072000000d0100ba115401003000c04c0c09031800805032004203403a0714440542c01c0d42441580e10500000000c900954058040d520010490340d640710b1444e41c0f5040b0200f1030b29000c0d0310070503141c0720715100040030a009100310324078200d140b250f011083c20900181016568425010b128a070400c01081068903001580380c411680b094030501c3c0e450344e92880450402c0b142c54081d90b04039003030003103604582003e00d025606031443c0d100030a601d6602c44c20b01c1400c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 761478435 1250 761477185 761477191
    0xa1b03030252140708070b040602071a0d0902180a021809040c060804170409020d05070f02060a150f0e041407050f010e04090c06030e0c0d0b0a0216050f0d09060206 72
    0x100042c11910350011521141a000605030502c04541c00346a85a0409182020070b90003079544443c00302e81400902e80c1841000e000389401e022202802510942c100b065106044031084503640e180ba100c0b0854480d4a20701584021500d44160546030100c3c00801079030024110a08500e90b0441740c02642c41e01c07100c903074051303900720b02c00f801002e040c00000d9610071006401540d0799251440c406643c80070034070040015000b0042d01580714100d50b86688155100500071005000045d682200c0b201c1e40091607076448050b019000ca28020380f44a003802d000c14580040404da9019800030800c41a4a14103502851140684203851001c4024042d00e5680034025a07a00030071116014555610400a0396010f11004000207a814200ea41e203120344880b42d800b1740c0c00f103134440d0b500c448101d20510020849050558210312600341c140e48000e64410010950201c596010584900c45811044007800d0300d0750000c00c03140f02c821405022540c0d00d0a00001c100011703411031010070020f20118451b40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 761479685 1250 761478435 761478577
    0x5040e01140a450507080105070c14031608030a0b0a080307050d05160605040204110d05010e06151e0408031c050109020a05090409051c051308030a1b030302 69
    0x907a0f90801c000109600032240f098500f0300c5280c00c0407904150a200d80d070f024909503101c840c01c2c02040c0c07909180c2c3c0f1612040504140e0000c1c02034011003000c0d0041c0c00d002a0744400100c1e070b40e9458080c80320003840320422654020482110108100300004020100b41d40984210348072000001805c8540d84160101d00b022003c4034081c0c031000501d00d420068200348004d001207820f05004144107619040b06001404964440004118402d84c07502541e4211200740d030500c52000d42c20040d0061b40c840c000001c20468001003280200d01d00010541d0003030103405054031781c3e4490012480c071071350016244200031289044000181e03001c0c0c030300c200d03100f00ca07441d155207007080c0e0603201304030003050480810743e05401660440502c4a901031903001c40b4403500e4032029100c000280e0408064800da03084041207604c1082500c54558004c9440040c0924103102160300b03800516080b006809011524102c08100d002d25404010f007804820050002d84a14201824542000a440307007080340c0c0b10030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 761480935 1250 761479685 761479781
    0x4081501080304032d051501080d0c03180305060405060a0e030412020d0323040801180314070305071709120d200304030506250e030705040e01140a 65
    0x1000a004400c002c1c0022551034030045840070482405c400741052140882e00380c0c0201d100601e280c4c0102e6842809030013041c2c020051601400e40c060b10101c0c0514001e0180801d200e52a60350320b03802e0590b00c2c06160702509641d0203081524016a84030307000d840000b969030809500b0345940d1000810356040b1007400d640800d05c2c6400d90280101c84021b40c02c1642081801103030b06d8102078400c0210105240d101120982e2280740803078a43c01c44081c1030711030102e04d0380a4180d0001c00c0d0702104204d0980e00c40714150f80c3c0c940d201c2c5010350b51440781000003000740c01d4907a074041e40102600c010b401744140540e1604000fa000c583c1d295142c00f00c3c5401200445c450040b94507140c80c02d0400c01c3e02400f0400c003140d1410303840b9101c01d840c2c01012651260541d00d852440103c15040032281601800c0509180c0c42000070040020385413502e5000d620f0081303507601500c0d4007203002500a140320485003940341e0b1403801d015085001400ca111150000744010070200e9801e0200c0d01802029048086450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 761482185 1250 761480935 761480939
    0x91205060c090609030a14190b01030b0601120f090209090105102c040503091507050712020d0210020c0405070905130e01090b0106111005190e2104081501080304 71
    0x100c0c0722074000002c07241d0072000a00c844002602c0c20400805618005c010550fa08400079407010701e0814050412900c2208411603940000c2003480d58506403070780b00d414680c00340c0e0b4200040702c119a4a800800350942004108201c0842c60342c02883c0e04c40c0256030364000c1e6a18055403034280c0f801502d2036032190b400c2000c208a80307241012440b10151181507208085500c071507892003401019181500c1c00e80000412030789034503200f1018004804554203c03801d0140710749499407030b0a424410807d407030b088221480215500e81c2e4880105585c010040701d490000b20b10025030300d408412a4a010743c0c90030002c41c0241d40109400d0080311001014002c01d21a0810710380d001c5d1124200955141d0340310201040081e004200c100d0290210380e44486510005a0205182c000901101e2000d82e14060510500c000035400c0140030106080c4003003003141010380b541d4904841c004217009855203030751402a00c80c2c0e1580c001c004032a5121b044820900340854500000300d403c0c414880c19910401c41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 761483435 1250 761482185 761482201
    0x1030b1b0f071704090c1806140d09170307030c0e0429030102040305010501240302040506070807020a03140d020705030f060f0403120c0302120714040b090a0503190309120506 77
    0x4941c459003143c64450b0619989150840c2a554911840d10210304800200f11050440420003001001a840e160082d0740e251044114280f00d0041b070018541d0300c80c5030820a000c040f552001034490031812080e03980c500307501e0003002040240c3c40701b4001940741041980d64a041c3c014182050140c11440040721501d4104400c407151303c20007203425540901000007c94002e1040320300030100030004550344902c41c0c0c0c01810880003404007209161040c0007d00a40d03d0740c0702520170455100c2c08507648c4400500004201700065800284296101090903480850108a130850b0081c07980884138400d89943c200b54a540c0e0b60b4446c8a11503000f5400508981c8040141c6074102d4003078207040b651481740070041c101780c549003001c401c0440e40014038100f5142c20041842d0384000c01c1e00e80000410000c288402c40c0d0301c128441d0f0580054041030302c0f6010780d1024507a10017030000400720f88407054030341c002e04ca40d03021020b010740c0402d48488000071303500e40f55099a0505030b8850f014045a03620506 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 761484685 1250 761483435 761483453
    0x10110712060e030c01060f0e0c0306040203060103151404060e09031813060806041401021e0904180609020f0109061e030603021002151023060f0301030b1b0f07 70
    0x20703034020b034541c0c1400202d100180014140580c0000003c20003e050851001c080e03042540120002590307401000420310420080d285c1000c0708440140e52a185c000040b80686501021515201c0081d000010f080e4640d070001c11104105450912141d07548224030200e0b0b0404449070b440c1504204103158408800307a84250400700300500600078120180564822543c564006000e2030780601d05000601002058a51042c41d03118001d5107058003440c4003241c800740300320b00c20020f40c1000c600c000999555401c40181e041e1020103400341d441040c2800c001520558a050b4010100001e5501055102d0aa81d01c140c40303043d103890a94200030b1200c8210300388507242d00805c142d82d40b070001c4016540e09190008400c21a8020301c01d59254982080d10300350f010b030000f4040050744e902049801750f0400200524401f0841701d12182040034003081e0540305064860701e160701c00000200801500e4000b550113415103141c7d1a41c0f070000c60103450100c0c882c0c50b062040000b820b22890001500d890 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 761485935 1250 761484685 761484719
    0x611070e0406110403030201054003050c03131e3614060414010f03060203040804050306040f11040203060a030b19020c030d15032111070306050105101107 68
    0x310b00003800120420600c50650026001100140d450744240b0940382e200316826801109200d1900c0c00e00340741c0f854501c0c01803545480c030f170120500c0300107600249401002503d10200300c41c0e041d2540c0e200d03059601900c482d1a801050380349408031300940400d8158011f101e003a00c10065219800d02c0342c14586000c880c2e0700e01444400d022040110000710000c5028a070713444a800ba10300c0c401401d01408000544001c0c1800e1a01c0b218042d0042007040c0716030300da040840b0340250340181e503902c40e428500403501c5990803103074040c0b240303505110412440500100100340a1031110391456010310401050740f00a03103c0342c2d40080d00c08020700101e281c02d204550010052608038510403c0f81c0c844205a81003610856101c5d000450105000d02ca02e014449900c40469807900300c1500303541c2c03000489004000403440c1c511a80242100d50382c020400d900c1c42041c45001c031818941d8a00d0140090709003401201e0180c180003040c40c05d03160080403141c070401100d101402103076042082018001401c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 761487185 1250 761485935 761485943
    0x406180b0a05091e040911011209020a05120709110301080709060f03060b0f0409080c0d020102030402030d03271b06020d022109090f2706011a0c0d03060905010611070e04 75
    0x1c135400b4040c0d982d01d216209a8038410348074004120366607400544007441401529415030b081801c2007005aa610502d201076640486418080d003584081c001d11307080c141d8200d02c601a2030480c42a10f8181d0f40c801460499156004498107030b6111000030003954881e100e41ca1818008c0d120034000109541c22a14003014080c141d060420541000075043c0d0703000400c01e41c0c850400050f51205498140031031103001d410340c0001d5145080a50100e541c480c50001d0210805580307c1100011140120311586c800074400b203000400b80781410503400e44280c01d003030011140b00d5880002134060012955025510880d000341c0f85074000c022241e0310401c000059004032100411a038881c3d5511025003602440c0800c1c220404d6103040c15204500185902c01030031010402828656903c13000110a0305441b13000b00c1080c810713442650200098000c10700c02108a0080194810300720750326501040480302c0e41c1c00184400d9038ae40c0c0342541c19400b81c41d0b0203010342d0003103101071003590034080342c03c2d4000d441 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 761488435 1250 761487185 761487229
    0x1309200f22080703030f050f03151f021e03071a0f1b03040b091c020102040e070201020306150c0c04050403030c0f081306051012120905060f040504051b0406180b0a0509 74
    0x181805908d8207610417038803104003500417241d014103810021307440e034080640c85c0c090004054020344081d42d20391404444d00013a40b14075146400d0803030140291212168000305c0c1407113007400800305401c41c82e0204da00c54924566040040c9074445100d15212205015040e040d01d1925542c448102ca418024840121441000d00d5401e0080100b21451620038203035000507165418004000c1c1e8510014000ea01160700600c02d004441da20100d201c40f00f405d045c4e4400d56118400045a4140500c40404a5010740b8200800c401c2c160150070004280307440c1d5550201d819600380050b01c0c078035001e441c0a811701030444600c500242c00c030b0780441e800c6460f000805c030a05a450385510143e98401c0c0e0700701d40420401141c10340b5039404c00b45d62000790200311810780c00e080900306003010070b004078814244910703202c4021a0240d0300350850a02010603480300a50f459448000103000a406402c2c040450517140c88001800d0b0901c1082c1d41e012246a40e80b03c0c6017150650420860039071241c542c05802403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 761489685 1250 761488435 761488447
    0x50607032703260c0706150605092205070c111f050702031f1401081c030506060706110901020f0a08030103020d441309200f22080703030f05 62
    0x4142d43d412441503036048035140d41c62840d89441c400741c410300c65505032a0400d52105000490300101501c070140419220303000100f2900c11007400d241030f013464030200185000c09200c81c50707502160040000d400b520071015098400002c5c030003041a160000c1454400790110602001e204500411a0070b0006003241c1da06581d50384d000d82450580e030340f41c0400603640c000984007069485401c500400c2000080c08407074291400340c8540021080c07207181019030b103400240007a17441c241502c3c1c0207a00100c040051403007030541039410340c1c40034032010701512514243c2108401e00191401c80e003540034003490300316440c50b802e1200b50f10501c5011140c1000140d01581003a510b8009140d40c402e04003210310910030034440201484100740d140f0714810314100842030042d00000201400c49040090004040c0c0074132000c090180100c19407004800b900040c0128480d02001c007030b00704010240c0c039000481e01d4140e4040380c0b81d91a807140603201d800510b02040803a0260910345100e0203e82015842e101c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 761490935 1250 761489685 761489747
    0x40e01020c1504020918100504140109050c0a05040603020d0f050106051302071209030f0b07020708030c0105010f090603020a03080a02031c0e0709051b03060f030703050607032703 79
    0x14482c000101064507226080005500e040030f08160002c0400c880400080c050440c20f60f00d6841c000705126071940c452010404011480500d01c0012254400802c81190a85403958032049000760b6184690030b49507003c40c051509124032811aa40140049403101c0a0350354804402a17158007601e80c5d559030500020551104115003070a01800280182d8504071482d18010f080d220708d4600007001640d290601c0001c0100700046440794011001d0046942c51000881ca026120341061342e250001194004000005400c0181a5680201c9041903551500c200ba0200c800d02d21010b54009503032170701000400d41c000d00522520320030b03106681c6441418580c0000c8480130001801e129540c6d10f580801102d401e002c810b02501c2d200e40284240c0c01d01d048442071560320400125200030f00007010449a5903002c070305440f00c10026064690f51560307403d0440e242c2008031402404a41040640b8618003864841021018200e01124140e160341e80c404850440e4070791f11890046c809211541188 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 761492185 1250 761490935 761490943
    0x13060203030a0c03290f09191118060c0109050f030414030c060f0a02070518010305010f050403022a281a0304080904090203121b0102031e06010c080313032606040e01020c 75
    0x104280308000b1002004016138000300c603009c1540005940060060404421059441c0914044100e070300d10f8980c83c4001007036004058120700144580700701c40d20b0b041c0480001c4064004c48004250081c0042c00da04145030700e60107004ca078a640b20b00e081090101c5001c154014103040b030151300c1220303040e9880c0d05c0416140c10354102d01d040d20b002072000400400c032007400351000b0490b12075000c1c817050415030740213540c0303203c1a1400400c0240c0300c11141c0500303400d4189039221080013080c4420f07004e8aa10541402d0001003000c201070104a40041080d6004411030780d84502080c454920310740e16504c1e000d441350440e02949038820740724000c2501580d010400c032803070b140703056164990700c5481c803070584520121843c09026076401030042100c4006012a41d401e41d500d42c2a8481c22030f1b40303500041b580c2c2c89100c540240011000f0050001c14040120004030b4107201c3e0702c8a1401541071b54401c003400036141c0c0c910007485111b1000a21508090300082d8050700528009828000244210b40c14 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 761493435 1250 761492185 761492191
    0xf0f1527071202040f1503060209030f01090f0302070b0a090b0318030a030c032301050f011b0b011404020403120f020c030304030506040b060d150c0513060203030a0c03290f09 77
    0x56030ba0719800042903140a102e142c0f0761030002d01c000c10803140800c60f140c1d0350b4a01c40c400038101c6940411904410b4605000d01110381c52a50020000e07601e6030320300b040040c2070b190b00035001842000b001003154190001201c03c4620305840d0185c2491524100f0501984001c141034030444280d1008000d076003040000d081c480c8029200410109180c080c000d00300d0360f50850a2007107030348565540f203000c00007040050643e070080d40c0301e4401d040b941340144c2c0e948038034000c120300b150030400303a1105105a400c4032070705031242e001584c00000347d032030100004c0c0e001c0e5000c060081020240f035070810341c0c0a5034160201c100c05005840e5403140100000e41103411a41c401d5415070018400c22080008010a081d80000c0c11500301644c00e2858803030305050000400901101070b900d402d800103160040c0280c41030808200c811213003503925540029101c1d00299a00342080707090220003a40b80340280a41a44007560101c0700c511141d104551241c400c044c0e0007511b0300066a510400c20b0ba13183e1040b0303e84 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 761494685 1250 761493435 761493449
    0x1f06030c03080c0d0305070f050c01110f0408011a09071808072303010e0304030f1a01172a130207050105070306030c061404030204091109090f0f152707 67
    0xd00c44503540441c505004e4500541d00425140104104000d5001030485802000c185842621440300440150041c0a0030540700e1070102d003c50400d0324282c20780010300580701c40c1802070011141c1d011107640a070502000d0642e011210000044505100e440039085803414007144100d9555199036050030000c1ca60000d00845542c000d8030710500d0f24021000c0c8221000350001c002000e10788081c80e44034020360000802d002c2d010800041070018080020f801141074040707201041d40d50308041c0d4031014050b81644514040d8210380340102c2110b8070601602e00c21082414580040c46c010065101240d03c0d10078105582440340e10f000c10b409104103417007003540313480c0000c403039096040984003001d180e40020204040b0000c00007083c4083d00a540499a050301c0100b4003050764580f50115400700641150007200a40810080801c006940c90803094540190782c500d10703103248501e031150b00148841c1c540800c18008203296694505058101c0f074025513001c02e0400001c4101400c09510364440d031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 761495935 1250 761494685 761494687
    0x312050a050604111303240204090f0b0402071208091014070816021209041d10060f050604140a08160e0a0e0a03210603031701050d051f06030c0308 65
    0xd9400c00c1d1107804c04804510b0320040c00e0079842000b040d0300c05000d000007040c0c0d41e01801d1030b03030014074a83c1500c1340c007524a900175904c498464803003d00070044a11607070203140c00c0c40c00d481c149041600c00c4905207500083c1000b40e0008400b0282c07800782c00508003032103d100d9132005444a603418450100c481c0c08844003d0b01c42e003424032000b421540060032040180c0c00120341805403039000101020f511f010700c82071585a602d40320000e002496101061401140b581442c2144e4070b002007a0070a003050210010041e050f02c0309428074500d44103000e02134001c5000c000a000308a80c80c02a40d075201ca0081440384800d480d41501401c110504100100b0265203030810300000d85080030455010030b001004202a110844501e6591440313030700d0140501c00c81c1d609003203800004406d545c845803413510051103c6aa00e160080444001c40222200c0324629000420b891400d00c022121032a0001d0041c02030124541c400b00840f40510110911103648072000000948200464401140144041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 761497185 1250 761495935 761495941
    0x6050907050a02032706031510030213060815030313150c020a0e0901150b0417030405090f1906060c05010e0105040201051c020f070609050d0305040f020d0312050a05 73
    0x10040002010304020140441482552401d603800010349a0310404c00c240c0b6050001c8504800d91000c103c00e02180d00f014000081107001000350f07125035603c4805480404218080035801c070300300d000c2d841010038041120603003040070031b100d000f001e40c11000c807090740031144103c2400a17203190711401c078422180c51106d400b042141c0207403444045218003810060303a8510380307500190f604502d60048506c41944a800724192680940c0041c40d0040c00f0000c201d01240c0710441b00c1c407903030130500c41e088201c3d4440c42a529026800302c156012580050028003107500c910105454480300200ba03a040780f4012280102c9400b100d000d8800144025250496041182e081450030758071881c100085580c1044107110050364018100c1b40f0001d1200404400f090008138800c02903c02d510b400050380300c011801000313000003075000e842481c4c852022a501d15213a4007050b42941c400b22000380510101c0800b40d00542406089503040a00c00d1815000d02c4885046c6d0800303c030000d07215201e041d61b440f020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 761498435 1250 761497185 761497189
    0xb180108010b09030a0f1a07081008010608072c010b090a0801020c0a06020a0516110103050f071d06073009052b02130903081012030809030d0f0605 65
    0x34a805841031001040c500a00500402d90342d06400d00010407925100303110806025040441c40f00318403807191034200a00b030182005050840c155001c036602e007040800003030b10301c50520440045452580140802c1782c0f80a01c206034801c0081e035540c03204000b4110a076240d00d03e01080c180130b0903103100d03c44d40b185e00076000d1007a2160603400040260b0b10411084800020015810740f9583d032041e0050307514013100c14100c0300b602440154060300102138600c0da0400c01e0f41220301c4501d20080c0d03403c115651340e40d900302540a806039880c00105690b02c50300c2c40d036201584181140e8110161916250010542d0f6511840103241300606084200b041601501c02220b914480f040c0c55524120720741e42e09220004419400102095100c1c01c841c40314641c0280b542c1e061700e4101c5070001c184c20500c6d111908090041c00c901d040c00c500080c03401c0005041120140100020340d558411400c1d4001056907003990303404e201505160841c4014011500911031501400c103a01c40e10030700200e007140ca4641 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 761499685 1250 761498435 761498447
    0x40506011b0327060206240d030503220f0f020a152d090e090f012901080c03070305071101021602130501050609060d020408010f1d06040b011e0b1801 66
    0x120b00360306030f000703030401c016050f4001a400d070040c0154201919284000c8404408600c50356075068210640800031400d041c0c201025600c100005480124003203402d6905010710030640301c009058031034013541031010900900e401da10032840500b805c4845034907204425100480b0a8003a00080c13421100c0c0f00400200f0810004034100307032481020715441958000c0c040d2192030094030300034050000017419032441000310103441d41c1107100070032800c404850361907298880000c001c0700400004000016552042c203402d441a140c101d051802c6449450044018201c054050030801074180480101580c1c01e100a01e503255551116603050200380c8140708958010485407101949400700401090701c0300c40071106c00c030000b25211781e8ac401c2650240b000074003458000c00d10717640c6000340314a40c181d00e90b4840106016000d07820030322001203844959854400311402000200040b0040190010a8801c1c80c40000850000241c494440200707103d15003011505803104064001281c40651f0408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 761500935 1250 761499685 761499737
    0x30c060f1802010210050f07030902030111030406060f080c0105070b250206060a17070311010c0b0a05100e041a07031808030a0b0603040f0b04151e060b1305040506011b03 75
    0x5d00e00303001c603252098104400210047c0b025080c5503c8001031001c6583c02e5110321805000a02000c0c0c490816013410360041030b00740203c106141c10108040b8500c4c0340042c02d07004e0307500c050356818a001210394610003a6000074200c44101030100c0c3c00e0440440310013215048000d90350b07000b070095240031010011809aa81e021200402001440f00c174140d1010607230344260ba821982071038a1520100c012252001180c5014054401c01424042c025290742c010f10700543e4922580703c1090313190511001554020b54008041915100f4114100c05d980304030907512505600b40004c000007c000394400403002c07240221040e40c800010040200f50900c42d216184800791a52811031802d1381e10b60211600c4528007500c0400d81c0400902002000e1142c040300b01600c5006005107410f2001b0200f560074a40690409142081004600b000620082e18a10303418062599040ca241400b03010040c800941030b01e0410031725000240380d0201841544481d54481c4e80c9101c6c0061a030207503c0a424290 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 761502185 1250 761500935 761500963
    0x10e2d0103120e310b0319031e020a110f030303060d060f0f0905010609090309060c06110c102d021c0905030a08070f1202092103040812070c03030c060f18020102 71
    0x80700200c00141c400040e00700c3d00c7e035240e1008102d01c50040c102503c10321109a40d90040f50b120007140605c2035404509003c10f20710074200b280036201030800f00300040b0610f0540e03982541c4240000361032803607c0402840e04501803039000585c2c00b8030b042400159802e0403442c181c456180c048040401c01c0034494800181102c401c10040b02c40b9a40e001040141e10344102810003108070700346020300c4015800440303458954684141c2c0c130020100d11680300d40074080420641c92400084100380605159400509200c0141c8101207130b40300d80344c3c81c0094119030f09813181d01900054120400c0030a00c2004070a5000300c008640700c551107903000b4000d21700101024100540b0305a294071030b80c6c10150000c0100e55408002d600c40700e441d40402c07540c40e00e40703003071500e0506110030241d5041800300050040e00c0c40e900030b440c884221455560000e00c9605002081100203841c10004607100310040b480c040c1c414100030500d180d881f5a6131081d21075044d4810729882848407103804641e01000114015120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 761503435 1250 761502185 761502191
    0x50601060c140c0a0b0c01060503011a01020d0f05030a0207050f010515030d0c080304020909150c0a0f020109080f090d1b060f030e0a060c09090203010e2d0103120e31 73
    0x10a03c0401c4a20b0798600c91107880100108885045d00401c1d00040c01810014000b0030071034903581d01c0c207003109030070303da1803400b5000c0c030700d108017109200c0d82d40c280c0c00c518540c5906207940c4450840d0802540450004e072024011150f04005107034080c0611402000caa182c0307200607a004600705400c040d003861a180c00c2c8242021601d0000c0d41c00e03002d0b2540550100c4880b0401e0380ca142000e4140483d8190b50307859091100304011400c0d0380e40f03010b003c403121a079440c0b1000781a40c2406030b088800340c620142000c00c0911a03245803011301c10052800080162000750703800d81d6a039421031140d080240700c6810341040d8a041c0081d50b8400000d240c40183c030702e003c1c0841200c240f219a1030396600100a040540c5a40050b8001d40c09403001000420044104541e0b175a174810800d070321400240d41d0400c1100c0041038031342400100800e03ca0741001c2c00c2010081c241d1850741d81c01900303c465040030381070000b01840340d04107598a10001d1080b59043c2002584403e4044452050340205082181c44c646 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 761504685 1250 761503435 761503453
    0x12041203030b0a060807030515131a0a030c030f05031b010f050f0106081902041e0305060c07080f09010320030f06010527040b0307120b070804030806010c0f050601060c14 75
    0xa44440c5d8280c200401e400c0010740d984030f0f03061414a0701c1c0001186a006440080580901d011070303408050f030b08240300d00e15a0031000041c01c202040c1c00920000c2c10003c0d4802051000c180a0001e07030000074412000c880c58841c92848880b4140190001c0800c80c0e5514107020000404900801c1d0348030001d070f940301d102d56041c020003414101d8090010710061100201c07100c0c0d1610664105c034013a00c200c01001e8200744c200c12070341d5084402808100c66500810012500340080d01094582490744108518203107540309001540340e400502c040703410140ca801c40c5044000c1d050716a828410000c8850390b035a46071203400340d814a603010f00003d040100030440c41406501f0b4107200c440b8142c0d103c07112100443c030003001602034096407800c1c960602440f03800040300000d81c0c00d440703041b0b03110307950490150343c40c0c280c1920703004002c0b01e0140210344501c0000b45075600c02c1001c0c0104074403414020174000101c0d1102807034050260040c60101e18078080780c40c107101440f00000f8118010b0700003402000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 761505935 1250 761504685 761504687
    0x5040e1f1d0f101415010311030a0b1f020a02060c0a0c030f0b1f050f01051309020307020f03120615130f050a0b09060f031909080403140f0a110312041203030b0a06 72
    0x12200038410000c19850710b61414039070b1f111307401c000b00c260301c80d0000946038100201d041c2c0c010114942424800c030303034102040c249044401051000c41140d80c000d0122607000b0f8092140c29444107540513024090380800302c1c006200105440065030142404402000c014a801112107e000c0c200c10700307540000c414600c00010394298007080e20b80590b00038407445640c4005032981e0044c1d1041c1a881c140505020440c10603039030186100c6c01281d0b0031121120304282c05507440788180c5c161410400c00e030600003041818005d072402810000b4808245c075114000d803060796042029000a02e608030040820001860211f10b031401524803602007a151070912000140e00703210b4104100c08045020000800440d503a4082c1100c41c003070780c074041c4145170301c501d41004a64000d001c21145507490300c2d0380f034829000c0002c51404182d2148000c040c0d0f00340d19140c04182c0091050b81a6041c0718a0300082011819180944000c0404048200d09905a40341c0542500c505c62082c6004032400c4034200201 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 761507185 1250 761505935 761505971
    0x2100e03070303032f0a170103080409090305040b070b180d0c170c0a0c15030b0d0605090313120b060415060e03030d060b0702010905040e1f1d0f10 65
    0x40780e150600089000440c0e903085c0c642500c2441005035040008544600c8207421310050500e40001c2c1e45030700a103c0c2000c21041c401c642800b014042004c180001d00450445510850540740a0305101e81440c1e035a25407100c031540045000c461200e00c0c002841500341040900088898000c03014001c01c60a4440003864500c11640c00f4006035003064081d45660112000c071004003541400313580548915007020611601d0074400c05031300700c1141c1d00d1024814420300c40c061409000400c202900e001d26154480a004003509443c0180410000e1241000d004465800180b02c03403524908980640d00342400e01903001400c8502803810420103101d03035810b4842c10303c1030381c1c010b00780003009a0300d03200424958014100028107851900c103022030b20406a40c068104a4400d03600d0089080c1c6880500007950303066080c8a10660000220802a44411000c00c24100d0b0100c0c0005140c1c0222003002c2d09440920101585500000100701508030309000f00100111244002e00c894000f00c075220042c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 761508435 1250 761507185 761507189
    0x30c0a0305130503030c030c0c0d020d030c11040e0d0801230d031101020f12100b0a051605100501060815010e150c070605180a050d14190f02100e0307 66
    0x8100700040d2103141260440301600291030054200c82c0c0302c20404c00d41c075940358000b00c850031031803141c4503640c01145480308070b10088607405055070590142d00c1d0b4003074a080750315010840b050700c1084803450182c2c442d44034074512620000300a01201040c3c0d0f201900300f21068100380c281f00c5046c541406c00d018807890100100c201030320f0000c0162114142115601c4200a441400b5400019420761105402c0044c1003290a81e255102e21a12119010134000c6014801d1002e410814400500d000303000742d028140380302030440401d071110349540e20344d0304020a140b01c0151842d42d80d00148844d0b03a00141441d4004680314600402c07100d4200060030403030350b10031114407800355040002642010803060310300c59103110044412442d15a880130f0724603005540700e074a00d80c80c404102c4c500c510f840c0304c12208540015204000701c2c000307034440307484914003d00030480d00d2191864400164200c40b003000040c2d401104d90041c5d4084500c1040f40c90174100114a08000d98040c46c0d0700e041c1d80c04a82002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 761509685 1250 761508435 761508437
    0x510518040b01030f0314030a06030c0b0a09091107050f030a02061b0306090a09140a020312120a11070803100303120506090708040303180503040e0117060711192003030c0a03 76
    0x110441341c0d01d0101c5040c043d01810202d41d031008014003906003529000b4800b42c034810500405915200c2102515900410f00508001840740b0400c010380c142a80c000b02c0340c1242055002d00c0d0207621749600346000c51410450840354000144040545d6040c020f154002c00d100720b0100e045c0f400b042e80c806d454040030700500e105104c4080031504441e4180c1c0100b5040e50300010000c1c141d8007001d446625241482c00030b90090041d026940c503044d01e071808a50408803000c09155480e00d900051034001d0048080040030150100701035004100510081c610601028180811686c11454000c104082e420501c455032824001032161176a2916102c541c4031200d0315240c1d125a4070707810708402601460044000d043c000c01180d405200000c40208265501e18000559070390303850300c91310031801c0700c42003441c04c41c0c12007008a82c8080c0301c2d81d03000c0134098681c0e04030b03403001e032000884404100d002a4112400110882502d2400c1105d0000103960a0110050350602c644c01302401e8035441d840c04024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 761510791 1106 761509685 761509703
    0x120f03060f08101407120911030a0c06110a0c05041e0c0509040b09010e07181d01170c060f21090102090112510518040b0103 55
    0x15001d8036203550b1b00089408004c12003001820281c0040703500d405040301c0075005640801014500701d0241242c0040d1b5454844003400c81d4004104401c6260000104403001c900084500000c8071400e40e0081170052036040003070a20085080d030604124078009041d500943e0141c0038004900068508202ea0034400040040301c1101348203074040c0c90b0000300054881481410400c4e019000c80d80c1c20480c2c1500c0d44080360303011440c51026001454408010001400c40340000d00701624400083d15040001d900030030a03d00c1805503030b0503c40c0303000920341041486206c0c00301d950107100801d44014244102c1041c080d42c00409190b000900c0e100e40540d0030035007481420764030840d02038103200c403204440d43d95050208101c514198201d08000e203026480c1c5c880c40c640d400700b450b04205140d041c100f42c100a0000c0640840170350041054040000081a0032685030549800807001 = true := by decide +kernel

theorem cover : BRFrame.Cov 761330935 761510791 := by
  have h0 := BRFrame.cov_init 761330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 761330935 ≤ n) (h2 : n < 761510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
