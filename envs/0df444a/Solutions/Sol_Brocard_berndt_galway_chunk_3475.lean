-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3475
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:46:23.519982+00:00
-- url     : https://prove2.me/submissions/375af722-38b4-4ea1-9854-35d74c791c30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 624820143 ≤ n < 625000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 624821393 1250 624820143 624820153
    0x40b0703051206100909020d0204230a080303070f051605150a1a131d1006030c0503012a0e0a0f031401090b0a09080c0a0503030118020901080109020702040f050a050108 74
    0x60301c200319807130002504000c0040c030f0526040c010031505401600c0710102154025040030345521034413003001e8200000081800d1120781001103880c181c45040010042200034500d1800c02a600a103c030b00c2c43c0801d1004c1c0f0900041842c021308903003280000c6282c014090b500c004021760550550000151103034482e5038103215410304426a2021825101d140c0101044065200015140007a124940d10301001120360898280c0300704c3e05201e80c10302024900d000098040c21494010400e4000d40c104900030b81c5407040c2e0240900030034510305200d00d40c02c0c4014081e4041c0c510120780305403122002d81d41010301c0650010740c4107403038000355017980c0c441e0851100c100d01200c0440c0c02c8401081c00034005400d100301042c00407125034000301c103007070148a10525080814165a28151420b00c01305d071594070010040103100540b104840900090306815840c0120060000300005c806000701d020455000602d80e0855459030322003007200781e46241c24003c5260075100c0c10002c00003445103412500030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 624822643 1250 624821393 624821401
    0x3080108070602190b2d01080f0109020d030e221a040207050a02010315050316060f0215061302070605190b0a0503030304082104060510120201050d050903040b07030512 74
    0xc1242613001072a10440c105000c91610340d9009410040c0c80c0006045070002d5a0001c148038003200c02000320040d500020342c1d403504c00454030f4151404144051645003051440040e99000074800e051901403426840202d220000124030700f00010402d980300300c110030f2a20401c14180c00c1080040d84507075a00355400076a07c04d10080e442213140083c400e81212030b40c1001980aa40101070344025505003844094462001ca0700d008035681c1d6203041011010301c20000d941c0d000f2000408103801c2e00c040d1421441d050340c182e40c040405004107104591913140f1041c106507650542d102c0d180c2044061041d820301c0703444105249954484e001003607007841c0c1e480712181407200b0444202d51000d4001c1d0314507500d90b19011941c0d0486550410307210541907415a11810441e50f15004500522000a10b410414180380040c0c48651021181a9120240d503000d40e8104003522018410f0702808107203030740e0b00721201c0d00703603ca02c0d000010100004034001c0c05151380070f0040d02d8203800e00f5031090081d4403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 624823893 1250 624822643 624822647
    0xa0b0a0605060304081c02040506042d0806011211060a030e0f07080304090b04090212030d14060604090c09030c140102010e1513030507080d02180a061b031b030801080706 75
    0x3208450242810100300011b80d568900381c3c1c100950901d0030100142020713200c50003e045680a070303100101d500311a0030309503032004612002105170b400010145401d280380c01a141c8c1c444005104801500800d4131010081c04003030780c0d4420095900074041552002d01c104c01500030040d2540348071540c410003402d1095000005081400e491500d402941814508140600030b09031001449800c140c0320059400140c44000c07101040791158030240d520390885e10300303003412076485800e180030002120050048640b030710340807101540d1000e10f012501d04040c80741520003004903030008042d1609150000f8400c42c0f58206000d83c001c00740e000f0b002c40c107070503c0703481d5498003805207066008440d080031900c500707141110b4800c520b1081c209181002e6032501c1d039180c580c000d00314074200150000b51500e01c500303180305410150311045900c06842030615100038480849092800c01c52803160716402e06240c0503429841600170524041590b4034114a00107155804c02c0c441d01c5c2d214230403000c02040642c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 624825143 1250 624823893 624823897
    0x807060c0210050906130312020d02041a040509040b06060903121b0a0c051012052a03240409020307030f0c12051c0e06270d1a06010e030a0b0a060506 66
    0x1444c004003107548070b001e1203122041c0f040c6011800d02100c01c803c4410390305c0d01d0010f801c41508090005845a01c0c042d506900f903101d0301c211003080c9608001c18442a40c0301540940c0007a04020503040f180d440101181080c401d5110513a40341c450358001c0e0a03200b034100010301c001442132141e00c440000380702000d50b0301c49801000502c004141a0709200790700b8851081d10058000740344c0704241e40c0510003a48111403082c1d03565024095918000e50b00c1e85603103103010303404142c040821341c030358909103014112404580d21003e1440001c19a041510b035600c1c0c00c51401e4580040c281d8050341d580b0300d00b14020b0400400d044a0040f02548001203c08040e04100d071201d41001c090508400209408e011000342c11100300180001051302c12041d880340317030243c14141ca17440c820070f507010030300071807101180400d405a600c10040081d50600007504484440c5900d5401d103441c0050f5201c400c0181c901059203100c00e40c1501c58100f00c0b40c14040448825030003030041c60410000301d5200c1062040d18 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 624826393 1250 624825143 624825151
    0x250501060b04050604140418140c09071b141005040b0606070209130303200304020415080d030b0d0611040905060406030305031816151206050f1009030807060c021005 73
    0x28085c070080150f08110508040043e000810004591032a56202488510b032210705440500d207522400414960810072240f0f0400111003868175031030110802040500510725100c1d0b04039480c41000c0421180c0c2c04030041284058047d640c0c100c0116145100526040364151603403c50a004142d0a0824000311511260054000c100395541c6c0f08504804081c0c04d2001c134100341c0d445950b41c0101401300c0e00c0c000010b8410311807a43d2404c0c00d004000036a441601c01b88100304002204100c0151300052a600c2031000e403d0200700550004001061035070020400b030034a5007030110180020100000400669881c07000c00c11168440e02d0511084440718003006000c11010800f0800c1840d107a40f03803602c1542801d04842c1c1c0000074003401c41000140d82d02404004419040c44100150404902003208030700e50400c202c003904d407400040204510500f00c80c050003464500c820398920600410002e1034015a40d255900414a4100c0050407160120f00041c0601d04a6082c4a0b00a004c0c481c02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 624827643 1250 624826393 624826399
    0x7091b09120f020616080415120b0a050f060f0408030304140f070303030504140f0c101815091505040603060509061305092407080906090d080c250501060b0405 70
    0x103810035901340030541d402034180344540d0000c0039095000402860040003d40142000100e07038140940f000707041c0c1d18010f4480044036042a03034004145d00e40400c00c000b101c4040769243c0d00c1040d210042240351142c0180103030304190000c0d0104400c00000003c50107184104c444ac00d6448110110940724009000454500c0d000041c003000883d02c640c00464000f1f00074400000e6140c00c503c01c803498a0090b64021141e81c02007100b0500030714150030b071207010301420f090284c0302c03000b10151004030025030301840d00240c542c0d90290780428444c1c600903000d046d4911010760754158011014000c0d412920901c80008d09001011800307040c49880940185400703041c107a00903036003aa4041c00340200030a070fa0010b11440c248503442000f00c0c03540c1c249040d4003601e02e484a040451008103001e03802801451940d1142003440840ca90018007d19920424a404600350f11105140c0380180701c0e84a40400325100b0402e45002001c1000c6070407215845100204590703541d841070f0304910f01680c40350580c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 624828893 1250 624827643 624827663
    0x130b10140a03050d23070501090309080d0801090c0504050a030311060114030c10031b17180a030503101206140a1a0d02060405120a1101020a0c05010c0507091b0912 72
    0x2d014054003224140d41c0c20040f1010100f501010500d005d034000310406d640c0f982d12100c50341c06064014a038600600301d100701901d05404041c0d405032440d0818450340c5007240d900c0000400003440f61096070050b10004051624a5540f4140246024658010017a00380515000000d054044002d030003040c800c090050f024410180040060054421906000f4162103001c00c000416800c1d0041c10308160315110325400905042d000c804006008280404040300300d00a40c01040d000542001c45030f525140a03541c940d00d0701c00001125074035620580100810501c01010403515801c4003000f2682c46a10310210b43c0c03010700c90b40039140c0b0345803080d50031011064501e0712403c2c000e1005407114005051b00b85016959404601c1c50468140c4800c1e07541c004025543c10454090406080048244020b00c02c4291a88036170711065540d00c5141c2c14004d00040590400c10b06005041c0180080d050030040851a2001c0b400e031200b42c0d2101c80002002c503080400c2810307504031060403858101070101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 624830143 1250 624828893 624828913
    0x1d1c0e090402100909020406050c01110f040302060705120a11010c0e151b0303071701090c05090405060301180305090f1804060c120e1b0402160b130b10140a0305 71
    0x11816014110f44801040811100414942514002071006002e03d640700b41d6213001c0280d00900b1100c103da80300c80300d00301c200309415440410b802506d054980440314543e4900461512a2604001011400c1050004152113040c0c030340040508100340c960400a000c0800c2c80c4c807040b500b9106103900c041d401b403030400c0745141031a28180648013100c8042032680c0a82c50382c1d5181491604105c82100000b80909548859804031260003401029040ca00b4014001940b001402c180140500507015036039510000d40340e9075003500706032422a00c1045180e980d000905009250394880c00543d070260030002c108244500302001c03807005270a10310f8401c3c080d40d00c465882c60b0140c408030f40b400e01001071030041d00c1540038191040b4480300304000020320414441e109007248002c004103289220343e00c1804110b044035180f11f41c2130070440d4400440140c40e5110030080c1c0e95084a41c4014149641c001d04028240142c8050030003031707440c41801181030720114010003400c4400c40c04010800c2e04190104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 624831393 1250 624830143 624830149
    0xc110607020d0807120501080309040e070e06040c03020702090f01031403071509020102120d05041a060d03210e07050f03190b0702070b0703030f0c0504080a151d1c0e090402 76
    0x140e5000091031401d50b10f04107981130355100744d031b0080e000710b00b0640002501c2c0390107282034840c006144810318050a03a0070301e00040d40c04140300050419016981300c4056a1038584a0360448083d59401005400d40307040c1919244540e190901080720010100c400502c0311900001c180c4125545c8610b40943c41c9401d011074401420a0490403415841865501510290084090425511b0a1400142e980780c0341c00d0440000144814005502001c1d900340800c50300c50052a400c00c42c1c1600304600340c1000b581e004240c40c95140d00200c0d2f1b0900d0400074903a80e450110300242255411a10705481da1425401c1545541d20901d45d0b04215440c0003d05000500c1400072591182240c01600d85182c1e07589a04005075000300000c03400240d44040455008244d40700d007204031103051805034105401c0c0212182c1c4c5411225000d01100d4007944600201200e035088021341c0400b207400b4080360b04822822550700c400c11b1742080040f0b0304d00c0344070360007582c03081e8090101680014210000ba0b2103540034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 624832643 1250 624831393 624831407
    0x606210a110307051210051537120b011a03130503040b1b161a09060705010905030306011b080f07020120061e010b0f09061c0c110607020d 61
    0x20160580140c00d0f00052036070380d040b0199021000030000d00301c4014088080f00444400502d81c0000125103511680c45446207410301d001d0210340400301d5080003280090310b8410305151141240d0a405850110343c4190802401000604c00c0e0030fa02c00304c0e40c803041440442d101c2c841100b02c3c45842440002c44aa1001c103580d111380707015800340c034906912020014520340c05012405910444182d8000421508000500d4102b203405200443c1c142802580652000544035400030304001040e984081c0d03803484200d0355081d9010008009200080c5070540d201d03041222a00e022906100c0c3d048800290003c2600b649981f0901592426140304548206900030300005d0341085403180b0f00302c1014001540d02c0d60100840001408280340241001d0010740e220400407140c8d01010004100409104043d540303100c0c0b05146264171110b095011a425004e030543c0341491b07100e80c480009159510742d01c4013108201c0c0d950b5160510060341e000503a51300c8107941c102c005a1000c44c100c0351061040c0d11b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 624833893 1250 624832643 624832673
    0x60c0a090806012c06010f23070b070201051003080403060f1d060a0b101e050f0d0e0c2209030905040606030f0c0206100b090a170606210a 61
    0x6080100d2612240d000e03141000036080010348511303610040541882c800241d40141c4800c054106142ca4205c3c0000c0034018803122003428010160080c04039250081d0140014074410881961103d900e170606042040d010f139051400341d482c183c0801c07294841c04000c28241e9401481c214a000e1940e03403210002c0a50ba860340a10540d01d40000c40b9032768900d203004542c1342c0800010070480c18001418000c40b103010f0302580c810f080000d0584074068004841003070f035101408001c2d0311034403000010380e054452000141c84d010380c00200800b140c1426407105810012078411598890a00b034103002000300740894403060020601800840c2c0c4d1440c0e00800c141e41c0c82840c0c1021000d0756107000c1000e98030540c0140300070a0b1943c00e0140900d90612400503181c4291004212034282041c402086460600868601c0480010740c200191038081000c001403280340004110103003107841d100d4440d042652040e10444100c0030f554407101a6148000c08528442c0c0541103102460383c6801200c02c03001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 624835143 1250 624833893 624833897
    0x1202d010e240c12150603070203090109080304180f060b0307050415080403140a0c0c090606173d060306081501081c020705030319080c0403080f07060e120d0608030c060c0a 76
    0x840d00b085c864031488051401043c0980007140c542c0001780014010fa0b0803600515000d034401c0c0320030404144240b031601030002c0c90603000182d03075001070111030240c000c0b83c0041083e90000418401a00e520000030821103032903060801c4d060006081c1140d660700c0a46028000803011240c100fa4180070600400d2030080b5800c000d9a134800760395504007000741d0796100701440c0756501410080a9000520480381080ea01a020b000e8078103418403c1074140c074244841c0da0102c500107401c1d450040d104041c42084000e1a4100101d5994034008001d0306c6240514002c50151061140c81d0000c040280c40c180c880d02c0010b4030854184002200b006014005040114401c80e2400039039900d0600082c030030940c01c50310901d010140000d0103000040040c2104400005c01c0101f01f0200d030840b81620703e401e0b050382d40550388568030b0800c2d0b00a414510003490041c0110541d415510b078030f9400401d4501030100d420b0085030b0381c3c2c01c4041e07102d02940884103013030f40103900041d00842651006280d603c041b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 624836393 1250 624835143 624835171
    0x50a03180c060f2003070b091509011b1715130501081513110105090f120f0c01030207031b020a031203060501202d010e240c12 56
    0x35107511801d080c860340520041503941c1990210207910041c82c07180c08003900c1451114100f40c2c0007050381da126151001c0d00c103000c03031030118440c100c050010131500011034100b4991420210307d101c1c020240c054004420180d224000340b00a0f00414140400034541400244d10380c1c3c1712040c411030300040620080c3c0c842c09021005031400c1c820301c5186d028050007001819403a401c00c03c00141040098000e8070340500c24003c0034005003054224010f20070080c43c0c4a07854040d070002182c400c0c000703200d4150b4030445c0c03400c4690308444005410741048600720210b4917000303141c0005404900c115240600001c0071000300010920201000c4403895201a050507000d03680c940b00d10300d28140d4801d540e400607440300001c00c5550703402030315051515141081240003105e802003260740c2d5400b44800070084580385450b041000782c04580301000000d960000e0006014a081c141c0d10741b000404074480315041c40144070301e11682c1e0212540b04050380603001780781c0b600582c0d01080000d4020020410310b042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 624837643 1250 624836393 624836441
    0x909071703090a0609080d030f111206030105010e06130b060d2a1e080403091a0a2d08150411040501080f060603070c02010e040c0c0b0702030a050a03 66
    0x400e1a8604081102201441e01d4908400030040180d01d260311143c100403214400740318801d030200704e1042c4180700c2c1c100040c80800d120060400fa00d44180480c1680502203180021400c5d40b1040d28406c09045008110503a203074410320103640d000751641500414950840da1413034150307520040d0303c00c0d4000c26035814a60354201c40826100000ca131081000444406050309070b240d00c403440f005111504001c14081181c56a003841e0400c242e15080421078684040b40a040c080c2047d503000d8200f0b107842c004180e6620000c948681c0c01a4031000014884204842d9400120320f1607542c03044103010304900b00c141e400011584040b000d0580c9441401d03c16040215688920618080354402c009084d119440d0800142108400401003107540b002c4604008084e030324030003102d0b4000014140b04800600600040f01d407403031006902c075002464020041d08444d00000948005485604070354065500c10a0890710790040e00711590105200b48a07402c0401d0090300091080340d040100382c10b69445c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 624838893 1250 624837643 624837659
    0xc01090212010207031b03121a09070302090a0b0f04050d080f03010e01090c030507021e01020706020d0902040c022e020f03240a1d040c0b0f0c1b060702090907 70
    0x414951040307007981d8001007880c101504040b07005184032050f882083d008001c0c0c2c034058500c01050101c140101d030342d194012946240140d040d052a18090104050380c6000e440c050001e41c46100d10038420345510400299110086080359004104215160b003442d20345014400040c1c01110200c40b905418802e0000668150b40610300038000c070800d507405035140070044001c0710920951141010f05100410240580005003110820101c034102c01c520b10000c80e182703009001d0786100803c1140005212144d414044e00440710041c02140c042180c540500800e036a07034101e141c02e01d0350394800d0100c80342480342170080e01050220300300400351078071011503c50609035004441d01c0850800381c0801100c10810040c0710f02e0604000c1d0f44100b80607051330850003454600058051081011a0001c5d080160044460004107904595a61603040294580d00c60750001013003080d86200d01d009808400f18006901e2400b10000381c00289415501e400380262000010701d1941c1520a5100c0015585 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 624840143 1250 624838893 624838909
    0x403150c03050606040b0a211a0315011809050a0c06030212060a05150306030109120c141501230a0f05090a0902210f10020d1d030a050c010902 63
    0x88455000040d0000d124500074007201d03005003019010301c200780800d00c00040340100b2104400300604024a80380550310400c000c450300c0e03607040c1e04894100b95000007011290141031035100011416503400c1c0c00c40420710880c411091040138001030420640c02000c0c5030300da001c20640340c01041501c900c0501d60720303040c1c07445a060b4000d10009034000713050b41c0517461118205401020488000c0c401710b10f0304001400c20303000340441005902d00040895030540d004d40c402d90080350301800c0704c039112660300c00c06009002c3c1f081058807441c1d0650006001c1d085c0208059110185003012942e042e400d0544101d054103038011007201e1018038229130031240c0d0703034600c107140101043e410303114003241440c0a004182e4405000a14074500780942c610040c0e54120500710002c0490301030300d1180c800220940d20700542403094042d6401584c845003503603642c0340c0041078458542002805001750410008441c48800c0e4200c9801d0342060040241c620f00c110020310405d2554030001c03c404020f500052410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 624841393 1250 624840143 624840173
    0x309120c1403010b090c09040b0d0507080f06070807050c03073201020304080d0207050a0f060c0e030c1f0909110d0b0306040c031203091a01081204050a03060b03030403 74
    0x20940c480e10070084420181000110a03800354024481c140c050070124103058030281200740d0880c3d01090304a070a480304c0c0c0c0200700200008080c8155243d050038402d844444600518031a03002d800304021154600051040c017a18055840728403d41d1844801c50325a0085c0781da818242c00104403010104d83c044082da010603004c0c5c500c1c030b2406101d1b0442d60610010400c3c2c0c1d807031141d0061041001103a911410b603540c10180003405661400c6902d00582040c0d1103041c01400306200422503c140071300e86d0b0002e40c01d1581744d1500d950700c0c48010f04042c1d40d00c0c001d101e603580c001141d030941800741081d8924a0200c1e10325050200200c1d88981c4841c0c01e4400214115a02010105048914034154044c00c0344d010000c1d00500768605080c1c5964000c40c1650001408000d02c0100800301c443c400d0b4004241e0720303008200700c0d5107280d00c0002c43c00012802e01c00c2d01e1540c440c084190305492121700444007101c0008120f0043d00e899031380c03120090b202108503d54940003e00c4004041080b5100340351704 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 624842643 1250 624841393 624841403
    0x20607150b10020106080c1009030b04031205010f24030209030d1110020c0d110a0b07120b09070c030c0611070819180303030213051309030801090212060d030912 71
    0x22544075205000c1240c82d81d1418204683c113010b8100020700000c603003400c50040039242415010720503c0141c2d031a641c0f507800180500e0382403007000203240c0e0143c20040d08441000061206036a04c62005414418602616000c502000c00c005071101603001040f040c554207050150a00745040c1c002420143c0440d8100003098612401400c00c20050100610740841d0074000c40c285030000800c29595030000c8041130a01803802002450050104600022158040d02c00003580c5400703034004150005400030100c6072410a09181e10a16204068521130805641c07000440301081d241200c0c01c0034000301c143e4070560b4441c0c107e0032110400380144800c501079501290f075861002d408110740c1c0060036082c0e003041a152500303054443e040d40010212030f0185000b41e15240c4840108444024961280d58000d00c1c3d10551950040d4070b0b003007041c82070300a48449005a0707031549114107078802d84082c24070a10001000866601e013085081284034000d281072b040c0c035a1122204035000403210000c3d11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 624843893 1250 624842643 624842651
    0x5070609140109050c0301061401050a09032117040b0606090a05090106020d110105010e010608040809100207060e0109031110050408060a090b1e040b070e03010f0e07060c0503090d02060715 83
    0xf007440010010303e145500250001c004d40c41c40c008032000c6005111141c00c3c104800003910f4032925220302c00741c0f4040c58000c0304481100355003500000c4114100d00c900300c0450a444018000c00280c141c80382d100d584c015170a640700d41c1d1220200300441c0e01170b00c00107510000c0c0140119194664031192030180419400500190010b40300191810491080302140baa05000050145000c90340c11541101e0441c24000700c2ca07280c0e4642044270f800713a006d00b203401c0503c82c1074000200c3c0e80006d200b41195043e403a032404182020004440305061404090b00d00804604446241c1c100400801c400304828900142800d40ba074610380d040090507156a81110340310b80e100300a204096041ca9045450601d013222880314442400840310f200910140101c0024030001d080c060007144040c45481004008120410b24110410007c1c240e203c043c0349244520000421414010066103070720541001c01182047c41c81030401c100100d070150101e0700154103000f40000505421114a024507900002007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 624845143 1250 624843893 624843911
    0x1020f030a0e070f0e180a0c0510030e1e0708070303210b030607030e0712050a06062715030c18141515210106020606011707050706091401 61
    0x25007a55840d4144845039000008108480b85091a540d0211040d000040178203554002499454101041040310305005031008031003000383d2290204103540089802e108110204c0c0740840442c0d104100d940c089074001e05211610088950265203101000001c07203102c252150702203070400040d0340c000c40100d41030482c03004890b12920404c8510742d520f10f40400034425941d000a64a000c00382403142850f503500500000400180310700310150000c00e01003120654203150859440504c0ca80c2501c050b03203000c03000b1494202c041c0f40314101c441d2414040b081d5401801841000306520080c0050804a03080c00000252030007030200010008840c2820310001c00301e0103042a0341d040c4c5003603020f9116601c00c00c910304142004c41c2c100000300f92076500342c091682480807081d10824114410a80300007010309503141701204541d0580d401c0d5400e0b640030ba142c0800540340480c4440340c20040e15121400030fa07107140b1420281150b540110000f00e131504070b0381c03601102c0401000c440340c4c485e51560f00e11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 624846393 1250 624845143 624845161
    0x13060e030d0b0904240e2d070302033a11060601140f070c1806150e01051213060c0509030705010924140c1c020303043201020f03 57
    0x4500007030403d032050207a929099440c509050304500709005060101510900061a50384c84909008102802c998103c0820b40300b00040c580c030070803134442d03e0520010300090b41602180510031a075000d001855508000c0d403220030800403001c0505081c0c5030100d6148248240850000e09004490f01c0d4004500c2c9250307025410130700e00030704480c140301000c0ca11000021900c001c40740780c004558000341c0c5130751640c82c00d8201050706501a00c41211207141088100c142603201600f280c034000127104021807110f1080d01d541e01840a85070210b90b00b807110028158890101d41e900c42900009600300b841a65142c1c2e04407040035403c003001410100d0302031724600b01000500040d20302401c150780c14078a0403001c0403080b21203020414114002d611083d04207802003002651400307101e030ba120384401610b188c3c01e43e0782c1d41626200e0494401451220b240703500100482e4010350300140004042d144281100381145640c0c1c88118282c000f010346070000ca02c2c2840031342449442a801c441e0390342001d00d24 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 624847643 1250 624846393 624846401
    0xc0c1f0b0613050f13061e06020c0307090b044508030f130210030c030b0d050304170c120d030c05090d02040905030f0406080a0c030629042610060f06050313060e030d 73
    0x8c0b020340d40f1000000980750340002d01e010403210781d403030040b80d55409080401c02810b003111400908240c01540520103608071503d10307401502c04401c030a5101c42c2c240911485c4001080043d03e420400c00c0416540213140046660051401021142002a650100302c18410040d94003001030360b120307105603c0c41d40c1801805a5203001b2501651203064603100c56440380300324030640c0240102d0000c000203480c41030110030040a40101410070b00210240000d40b81c03083c000003140000d1402e00440c400500800c240c0d80d2006c0b01814201c002d820380c2c0e01707000082544600c2903c26220a10502103500c603c00e0080000e080250ba550f0181e0a003481801c040e5070201d00203206040c10500c040c02843c4200c1ca050039403060111031400d40720842c0c09010340500c602d401060213000100d986c800140c90501111451614580489001c0c1120880f0300d000ca40c124050042c61455000c0c1c104011807241c0d000d03540040c56264a8031300407d4a94800c8211012101582c00581011591100c2040d00f441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 624848893 1250 624847643 624847649
    0x4060518160915080123010e040c050d0611270603090d050f0c0307060618060803040603021803030315100f05120c0c1f0b0613050f13061e 61
    0x300600c0810001d0315000141595409030880c0c19a852401a2440d0001102c202c01410040000c1000c81a80c446c07801c004440b1060b030070841c0304030600000b41e502340f49041a10654000d040969100d081c0340412824071000d000c1910359540310f00c10707100d510ba080340c0100048000d48100700624601c5040703080d0402d0000d251301c3e10030742b401d004000c0500c1e4003044482c0d461070586060f1b80c0c1c030036000030501d980d401085503401c15807102156103c100951a4070200596034403055004019088800100581c1c005015030b10035604144420801c2d01d009801038030490543c1c44940c1e05c07510001021a00e1900229104030070b41e410182c2c022014245882a441c0c0b0251600d4100410300b40c070708014099100f0b00100060f907508080000ea00d40401d00c060324000d11000040d0b50801510603400c0000c08031492604c41d8040c40d000c002005403900c40c084592000614088110181c508010422069680b42540b0b170003039040c8680d40807100300e9101d000003a104da040031410300d500480a01190040d00c0d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 624850143 1250 624848893 624848941
    0x603100501051008072105040c0b07030c11030a140309010f14071e06020309010f05010b1314040e06091b0906011704050102040f0e090f0309130e011103040605 70
    0x400103100980b02c0c4054180c0c0c80f600c2d810300100a48801000300ea50070400b52003050820001d50002e42c01c401950071550140d4024000d40c0c12454035103c0e024024429030000401081c1203018180001c5c2030040c4006d04c1000050644a01e8142511084803a5840c00074280aa80000076a14015a00801c2c800f001c4141481c10319484c2141c481030310824410700c00080d00780c2c0c0c0d20000e4a500ca1107020241040d55900840c10b546908004040034043c140106042d483d682c100000810f0f043d1030340b015540c5041130640d101141600d012145d40c48101c0e40880107401948035145100b0000b0304201e180d01921018005100b00c1c805656841055103003070000d14452492442400603d03a032080101590b826480f0302d4042c55101c41c500030380244038036070018100000385000000e00038110071000344903004a4094808102c0c0c044142502c901c40c260003991310010840e80201d42d09096448111607102240c00050a5200c14107140842d410880341112110b8554003000b990713545408000c40180852 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 624851393 1250 624850143 624850151
    0xe0a03050706050a290a060f0228170a030f0212180c0406060201090b010905040302120304030203040504111b0f060105010509030709090f0b0106051314010201091a060310 75
    0x1a5500811510500c2400b8004a803180b0100b101e0a009074000c1c00e211500800454081c400b12600c0807014280071402e5102d101c51400029a0078060144483d0361070403a07001d403d15040c00425a010610700712035a00c45001801031510000340c81e20788900d06d00c42030740d01c1107846183e102d000505031480c24040e94681d42c0103002028000c5c1003041115006640800e180c3c48040b11345c107d641c5001100200320b58000d0401388000780680d019841007a006000b0030600c02036a80b90045030082d42d0043c0c034000c0040e40541715840e401035508002d0b68010f4800d20640740f4080daa84005000c1da00708030800c4181242c00200c1d5007141c9000c0c00503025003000c00c40038142c40f81d00c0d00005521213038140300351418440009203141055409000c15809440c20788010000c0701c0040c140812601e101034411600b421000c0f0000c40d086001e242510340340395440c64506501824900400c6c0000d401d0390700281550b49900009000450034002144100c0420824851500e8140e0402d46061400400d8140c254a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 624852643 1250 624851393 624851413
    0xe0903090f010c0510090809010318050c010c020a0305073f0213020c010e01090209130c0b090a260d140409180b07020f06060103110702011805040213090e 68
    0x1d041c200c4010710409080140d09552541051400c0c581e0300101c1e528500d16110034001080380d460043c2c204a0070aa0301045050101d00841c80103420300c22000c1c005502540d00c6403415071041d5182802c4038400b0340030580546d81c0c1e50300c4c5c80c40d240c01900100c03c2003040b1401510384e0040b03807442100807446c030a461040e24603c0351010002c842c001d0b00c080d005040031804400c110200350101c56040b03020708000c008400b141c03c5958020b1458440032031040000001146000105c00440303120107811040c800520351400700c11340710b42d43c800c280468200d00e80d100002000707005018801070103040308960616200300225490704096079910200140030010390350804a50404040d039099031200c0000041e03440d280319254000e610b0725040200303100b05100402c08140d0740410318104095081e41101c0c00c503261580158103490038880b5040b55101c09100c604055803003542110a0791800c1e01d00c10803a19162000719050368400c070f0b01511102041681005040140d1180111516151028181c8864 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 624853893 1250 624852643 624852649
    0x3020406031b1e0306150e130b0603010905070c0f110312040f0e1e100f1203080f04030309122d0e10120501090902040b01020c060f160c0308040e090309 67
    0x1d28000e80c10200d16012103000f03124003d91010b000f8140000002d40000402103000707104004041110b802060310421516036240c0e903028522002100502c0c10b821a030174861800d0050100500d00410003684140d1240410b401b02841c40402d8003401350440c0115020003890703c2d2a0340d030119100f000c5000c01040102c0c40c8480c103010166403410388550041d07180d90358016001c1c0c400c114a0440300e10b50310305010700b4a003417442d40012100461409903500381d49900009004e9040d25000c0c1c00304ea210400122900d0000f42556401072203810000703a0b921090701c40b2407500c280d070354140e0b010402c0320907014000312080d50019501c40798400003640c0300a42c040300030986c0c8030b40014540070f00c0c00c0581a00542d8003a00e030801c01c001d49000308110640e034038124a80030300b40302d00c000e0b40264606030050002d5480071401103503440000e443d152504601140002e150b500c4000881051008450090009048204458001c50040708880c0e107070ba040c401501645440505480555031040200705001d40f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 624855143 1250 624853893 624853907
    0xf060f080c220512121b070e0f010f0906030f0605190c02060603161203082806090e060f0402060f130305061f06020a02151909180b01080103020402090301180303020406031b 76
    0x3c00e100c05225071b0300801c0380c40c01d485d240c140c5d0002c0910b103644404012a204003001c003d81210700b80003030162002ea4600b5002c08643d11400043d01c045100384090000c100ea80e0401074000d40601c05900d041003101521030100c0c1c010070140001604407005204c0070345001c009941c1411010a0858807442c0b6003809014401ca040d10002d0500809a0028806c21402d80c03860902d012010046410b5010402c0c00b0380051000d80280e0000c40c0c5007a000e40300c0a000010900c0c03040f1b2045061543d5504c4a40801855800c130003035034443c0300420010311084001d03090042005621400c01040c4a06109a400c0441301311028030940c56018584204041a4000b414030300b03040c1c05907aa01e58042d60441901c541c0e00c2403c240200011510f206040e90f0303035000424600302c1c1c07032001d80b20510507140d44203c01982ca2012401d0b000407010001400549890381c02410314640003400000e05143c44120182c1145402400741c004c00d5001c5020003105403d03000c3d01450980c030201a04601781d42400142c011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 624856393 1250 624855143 624855157
    0x912130e1b0307090515120609091e030310050f06030a020c03070606060f020106080c012001020403020d0f0b0702150a0b030106030b0901150f060f080c22051212 71
    0x924080046072118144a4103880030701484a1016641e1504080c060f114015900c105406086603140b42c0810f0b103604801e0340c2001c078040c01c0700402c50311035100b00035448c907025101001078050480079400300c07440d2500392048402d02c503000e140c4034900021400309189140d800130b4022000c0810f0607150365241001c03a507020402000060f1074800c0c000b401c0307246024020300200b25610b0500042a51904400c40d404002881d41c028003600341c80b039609030f03155100c0680f12400303e6440345c000d840180780c00d41200b45c141c140c2000181030a40c1d9400080050300c200f00141d44006001e42e644060010248005030310a80314001010a51240001c0864640f002481c00e20003540e0780781ca0500558087d0801001950000a9084079091a80d03416001300401642055800704035400020000440d0b101e42c0100c41c0c164440d56201c2c3d080c0d030000d0340c5582c8000c00d03483d0140b0042041441000f007200c1048815240d860715903103000d092170709104034181c080d0303005044d560000d003440b214041c40d0800c1f2601c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 624857643 1250 624856393 624856409
    0x1020a0212160f03030203010315290d05060705220501020303010909061503110f04051005041e0f060906080303042d05031206240f090f04020a0305091213 68
    0x1c1e0312404900701c0d02c01001e4030401811010b01070000d50034554160007841c162802507c10001c4098100c1c1d40904072488a0380d54901d4910001d11100b00f1f030b640700807202d06680701801450381e242907030303440c5801e00c034003251800c011410200d40b01020f400b0201c4101040c1c0c98a103040ea071524101800030f5034900052090000d190349541d030603010400c850704510301c00d141a10902d103009441c0d01c0c114513203d050280305401050600511441840c05000e024080c64200441100c454140000c0c03001511821072050790595800c2441c101c807440900c9520410116001c0c00100d03942000303442c80a94549610112182e4014000d000114031421104c048400143c1400402201d1120054104010380341002e02240030110f0228580c1402042c01c5100d500c007190487c84a0705400701141c04104034811030282000240200303a00c08140341c00804081500600c4182030010f900c00140036a4040761801c00040d44503414065040e00411658100b000d03c0a44c06090141030542070024815521403e05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 624858893 1250 624857643 624857647
    0x90f0c060f2307020402070b070806040b030a02090c03070c0b130501050f161809060b0904060602030406021e0114160e04050106050a08150d0b100501022d1606020106090e01020a0212 80
    0xf0440d03079240d0450700c44542c0200032040b18034281c07202522100c000c170780700c50155091070002d40d05860301191008031254014007007030054440c18407213000340d00028080801d105980040c0310124450310411482940000c0d070a5003600000d207411030075104090911b00010b0900c2e0305200c0080b040d0078507014901000e10780b107124022078584648a0090950081c950341d4602345011401500f101c008200c0c0700d80541e81032000c183d40744822640c0b48614820800180c0004101854000e500100d11245e00c044000100c2e40d00450300070585110310654410452070b0302c06513100d10858210002c1c0d400c03500704650401c04c42d85004c401a280e481207646000c200b01e1036900207911000c90b00d10070040c10102614001c10701040f07260510f01240291400d50400c545001c001499610004031103c004044c4900114000d03000009149c0c4020140200102c0d0300800e5004000398042c949000010700d060b83c008103c3c1271402200000320798940101c4a156401000300590035a000141c03180790100d00700300b141e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 624860143 1250 624858893 624858907
    0x21206090406091403040303020705060406020312040809090f0601030b1f0309080f03011215020a14090f040f02180105070b1b07080705030319050f0103080a03090f0c060f23 76
    0xc0103081e000700003000d0255003130002401000010241040d03030300c26001ca8000c0c1c1c1e120000c12003540281e00c903510050384100041801240d80035034050b005071003238039520305211064000800b10442140e1800304641c1030f41c2000002d603810701403113404640684440d841014005e01164511301c510803110241b41d200d502c8a001c000710002243c0104210202c02a180d50f11514803203002114048252a5010203600a08100300c880c8200d40c41d101d9191503070721402d400001001c8990300540d04003584025000700c0d4001a880f00d0003481e1000860344401030355151140d481802d803210481809040104c10b00c032450000b404540034a0304100240300785c03001030351032112032070b004c0c800c24000800084000c20154200072002018500403900c00440702c0300c6003d02c0b9047d50850360115500b2030707101070b8400100046915040103210f19075451801052000098541100700a0b021808172805007880804000455000214460700d03025441d2070000003a00560761030010016130800302d00003000144c44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 624861393 1250 624860143 624860153
    0x22020901020f010608070e0907290405040c09050a06030c0c061805070f030c0905070c0b060f0604080f06010506030c0d1e0608010203180f070e1b0301080f0d030212060904 75
    0x9100d0042d0b910081c0300190300c40d08680d440d00724900c110700c00110030700c02081e6684404505001a12034180152031840034201c440609001462184ea08454007040080790b1130325a40100c1051b0783c3c4a0303c60020701440d00e01440304803e02640180105880c2c01001c90620340d01100034034000c1c0e0401004143c0c00020340f41d5810f250f4860000810030312590f2000a0200b495103810b1040707038003e880e5841c869941d11103800550b0303030484001000030381001020001940501002d50044c101800c1c0708641e014400104110764056040021a544070603c0240c600608200b6107016010a80301c0700d0030344c1400c9445640f04d00032081407540c05900e130f40300c200d071264900c0a0700750811a000010321603681c2d20040d1034003c1d8000da5040f00601010900445140b00005407082e40d04c9103100106049460605802d503558800360120b5011414444400ba041d124480030358013030038001024140e588945480b1b5460095031807581030a250050007028a038501154015600c1401a1b0303610030a951a4071300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 624862643 1250 624861393 624861403
    0x5160305062409100c03020d0801120305031e10030c090b010519020f01020307080901050702160b0a050d0e0609151b0901050909090607020c09102105010e0606010e2202090102 77
    0x1d401565100884904c10380c4100d02074150f90082e001d540c1d545a050074100c0d0a21024080d542aaa662600300400207104000450b0f000030700c3c04100402030034048203061000025103840c281c000301e02c43d0074800d01128120b210300034070034407104102111040340080c09600441418101c4000954180c10115000f030010400148043c0b000f1503403460030035005090040251070a580a61a02d4001045140005142c6a03003071030301c0301d10280352450858058220703400700040c1b508200080c45120810308a90054101c1c1c40e1904018003454640300140c00d1502d90b068820100c8041c02d04c041c041501074030461a1194000c0354035465aa000c5c03000107840c0c84c0b00d0300a000d604000580108074541d0390101d01075000d41003e500386c0703506180106c10494156000e4030020040706a01c502040384104c4413000311400d40744c0c03d0500b000180d0507212a801c440d0154140c02c9207030400c00c1007241c10340e409002881880320480724038100c410481c82c0c08400d010b0400d204010381e580000c00a000b0ba0080203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 624863893 1250 624862643 624862657
    0xc05090a050d140703061d010b130209041107050a0302250e10050d11030d140315030a08030f0f070c03080415061503020414010903120e0d0605070201051603050624 72
    0x2c132030380c00d50b482c58810010300030720551181000c02d07001d16800a041c18001d45004083c0103010510a10310008054003d501183d5000c0d0700580c2c484100001001c038a0160505900030009001010800c0c20b01a040981a840e40c14406c0d030f5034071801030703c00c0303c49407010142d6a038508010810794404103480108407803a007003507070b1091064a8100802160b0001e1100150007602a522040d00203e000d456680480c00026202042400054801240c0c03841c0f100014500404490861029864150726a401a590b1040000c054010130019284681039542c10413000d181c11803200c1110b8074014903180004e000101b0901c1c102040444144a60b00080c000c1c00107801079151040d2a04000b0b070080d40688034601c602c0c0c0030b0704203410240d070080c00040d0441c0c0d01b0455080d034039207880d28200c950100f0301402590108000e00c1000100c0c0d818401c00d48224410b070000130b0f440c200f02070308a40842d0482c000300b0405041500b000042e07100c034104140704130b2000d80c1e8140840a828094081030141203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 624865143 1250 624863893 624863933
    0x10f181407171609020412021203042c07080103020d03031a0406060504030309050607330207060b010e0d03120f140a0204031b080a02090606160b0105040c05090a050d 73
    0x10161481011020032443c0340e80010b10003040040d50b51300c804c2000d9016522503c100c00402141590260070720340a81551309103100152031a04d6150641c01041e050800251601e48460310001c0c00f51406030003885410bc0300e50304201001d90b1443e0300080c0d0003641c070304004003090b4031040301c100242c40f4041d0b20140294000e00a01104c0d45940780141103402034402600090f800b0900000c55061140072584150b800070a04080c580310410020328404c140c442d600c21091040c0c8085014202c0c600c0174007001c0f0310899001c41c010424500040c0203d40811182e1701c6242c25005c60b4001a030010070341354203003d4450700892195002d00005000303200751201e050380110110304001d504e108035802401a0b0b0310980100101c11004400c802c080400ba0140781d446030f02c40c00e0359601502d00b600107a1380c04480100a107186c2a42c0c0440f180891480074400c9907082d01d008014440c0f40390902a02121185030f00d8039034180760841c0c0c0026811102131180074011114140c03030074180710f0081e005a041181c21 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 624866393 1250 624865143 624865169
    0x11070c170604030f230c0106050a1d130b04050706030f0c09090e0705030703051c02030f0306130e0a060903030b06090d080a110d05030919020d0201110f0a050c03010f181407 76
    0x40e01e0128103036404210408601c7d483d00c2c5e07000c5042c1c50700c804440d003500e00b08410b6203c141810030f00c500c07036454054400420400b0700d0720b0410004d03414442d40d5108034415005040a02c1c50104040c041d2884003000318042401d00411980c4150f100c80c190702100c406084c08a400c000c981284c600b4240ca9030051500b502500304044180b02d00024492401141c10300000c814103140d502c00c03a00e038001c05000c059201402c001242c1540781054102405003140c0100040b070000c0000000c0c501911114111440d944884030181403541500c01c041c400c50042c0e42c0c10749043c00610014211010801c07004001107404600700102d1841882011000c058910032103412510b9000064000d8204642000e8184161642c028040a544580c41003c1e0703030160400341103103400e90042d140b10403c0110b006c1c0c2c5100302c46d001c4048003400c000c0400814090000b6000e4280860207150a4980d809000541281408944414010310300180000304e504511004040110036040604003010368bc40a8464048 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 624867643 1250 624866393 624866447
    0x170d0903030204050901060507033f0906050708060d0b04080d0626031318240e0604020408030702010807180e0105040c0e0303160c0911070c170604030f 67
    0x1d580100107a8104544501701c40e82d071184121058441e1100050018100c000c42d606210706441440c60100c4a00f000d032044030400c0180d1104002c412010384810549900c020001e00443d40308850f004038291421006500c1e100d408195240601d810050080b45404001818049414240c90500c100c0b00014052140d54600001c0800d050b0814284130f050500c04204424074004200c48842e00c19400382815030703207001c50903440044013020b100210b6444261030000b01c1a69451b960038040800100381d543c40c1454024096818000d1045004a204010034082c0000001c00e46070700c290f0901e0302151503554003034229440340340714450312084180390f1070200d4900242d0313022034161101600e08125003405600c0031a8141c2c0501c4069030580c008002003080d415254081172100c1e4003504803002c040c0c1e5580d98100840761500c5030000c2805002c07800c001000f845901d07030341c014090101d2440d9071f1201d0491040c2c82d140d01803c02410300c07105121a0043d6405446190240f03c0300341c9040c0c48a607a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 624868893 1250 624867643 624867647
    0x207061112130602120a0c030c08090a03030503012607120201051e18010314010515040f08030318030c03040e10030501050f09070f08100504051504030201091505070c170d0903 77
    0x40b00d0300034140503000d5030070404070200ba0381341520302010165035041c000704103c0d1000e884030915000f003658094001c00c18500c098948000400081d4031a54816540e50316210031202e204904000c0d0040e00801c088406400400c0080e078181030302d20390311128850303c0b580c0c40103a44a01c682500064800c2031003050078455041200034002e00000c00c009030039003003505c0c001101182c200300b42c209001400c0718018047c50814070501108924042d44841c98141c031010106c40d030043c150301c1100268000001c01107026054211005848040070045080c19500c0c141d070b42d280c0c0654012801407013070590000380a0900c0307d41c132100840e0401c00800035814490015400e1110840f00080030740b0900718000b416032013098500c02103c0820000d441d0061a00707640e5030151501804c03d581c0c3d48100901510380030713034181030240140d01c40d800000300c41805142801c0034005c9001421070140c682400c024482d03402c080c1000d812540443c01c0c00840e100211803440d070380541c02e40555170714640129542059 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 624870143 1250 624868893 624868927
    0x70f060804030f09241119050d11030a050702030304050d0807030e1f050711121c0305070912020d08040b0409050a091a0a0e030a031407080103030207061112 69
    0xe0180e41e501a41d490703800c1080c1e605501a02c10064030711184a413410f805c1204070600603a0b034005140050510030842e40341d926110302110720021510204005104205c07040014541c0b240c03045c107201c00e0b420520b00140d5107900a8030a0b260502c9000505007007195010300444000d024020490400010a810580c8031500002d108502288003410075215074030b8100d6002c584416194a44000b8400203401201d03035030001c040450781540301207507070600c40d9201c0e5101c81e009680f01d001050524110b03404c042640d21851020028540f428007440708081c3e22241e0241610340071400507040611510200c1c80b4540b003000b0150028501103400709070216220010170855040c15024083d0380c580d504150101c6513642c40044c8a1601c045641400f1003081407000e5100c0c0304602e000840b006204091400c50b40217900480000c2e40e50610701c84440000d500e074503040035051920303920380d60640c6e03070180d6112401e001e00e40610802007031030074405200b0031031403607000c4602062a40f03c12071030001103010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 624871393 1250 624870143 624870151
    0x80408120d1505060418020c01021809100f15180905090106080c030a061d0f0a061805250504061401030b181f08160e1b040902090102070f0608 63
    0x450070b10201c0826203100c0c030140002e5070401020b5626003850002c0700000544070b500c4403881d6940a00c0160340c1110f080c03001e0068095503504400304800b11404101d00c9440c01030110341d9808601030144421001c200000041d40e5840044030f0000410007029590b0041c60505540c10801340315011440c0d181641200d80a090030320005d0140d641c695a0035070b1220311284086806901010000003c111603402103d50340a0102c0c4c58083c20b5400f442c61030800174a000200c1c00d80c1e0012980d401000414840c3c004107400307080309884540704990301c8507196000000302e5994181c110250150402c54030450b400200300052003002205c3e96440714a51070040302c0102400319140c000004500c0c00c20710b8858100f42603202640e8120341d02c09030100d20b59413101010280b40c0e101e110010480860070050f022145500305484501145080700990903a01c0042801400840171901c1030111565501640e09540c042c030405610341c901c500040f4508002c40d8061003041c0b140c900006016908060100d000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 624872643 1250 624871393 624871417
    0xe01051209071e0e06150f0f03060a052b030e190801051b0d0c0504030f061a03030901390f05010513031e0917150609090a03080408040812 61
    0x2c102c541880c3c0044440ca144101c0d40100d03140c0780019218641075405044002c8440445414182c0c1680d0303060369500580102d506070800001800128071b8038a510030000c090858418007200d054610218108162071440b446030b4040c0020b48042500405a20000c0000944403003070049091481c80c01a0b5054030965182e03510300400308082c0703d80c209441003d05001d0071940d142c40b904c41d21920003400b0418161003000b005020201c00101165038200d10a8001c05002c60340c1c04100405507003080f84481c000c0e21070f130b204025154082c3d070001810a05103440e480001c00500a800c0c0f00002040c0b0030b0122044400040d0000080208034148014140c3c00781c402009169640c1007111000d00326070901a020514480f2100401982d50b1940c50510036a032070300c070040c156104c0140381224101c2110703d51a401c0505038816100401c1c2c18194003100c03c4805640c5030400700d1816440d085148405010020f03141c00140600c00d0100449000700034940c00c0390000018181003910940001c95407200c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 624873893 1250 624872643 624872669
    0x309071a0703020c12100c0f0e010201140a09061107060212070c02030606090c1603022401050604091517060708060d03120c0306050d0c06021e07060e0105120907 71
    0x541031900005840d6100e515800805000160f40f04001c66401c0c6205c0c110020b1050106c841c11881c00c40c0504d42c280f41d9181c60b031403040700e60540007404c6142c25580e020b04582c50003e090900300003010309590048bc417544001042e0341e0700d0030080c1c054451152600c46a60000665002b04641c0707030700902c011810113075815055200d2000442e060190140c02030350544c400c00120300c60f80341a00c84581c00c150b06420307a0380307041255200b000489209003002c1c3d001da00b00703601100c034460444140c1c1484142180c440e0f000c44d0b04180c0000c100c0e000c0ca001c0c071404966640102c840718034002e1082406440300500d0000340792000c2070040d0741c41e82c04440e40c00c00142c10b40c0200d850340c209038040744102503250300c030303c195200700080c4e02c0010718982d001c0104140c1c032001c0c0024586c882c400031001035070094020202181c2000c0000c1d2500403042c0030b402e4171203001d120700019242d0100b000030a44400e45007004c820507000c070040724503000b0340280f240040744000601ca103050000404108640301a180c0c42 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 624875143 1250 624873893 624873929
    0x705150f090a03050a033c06060e031207020a1a041805041112070b04030f1211151b1b0106050102030a020c0909030c060f0702060a0b0f091b030907 65
    0x41d00c0b0038480d54001c02040d000d210654269020790813486d841608501c00b1600003242c024840e040c40080302030801c10300d0409486d4507103c030380c5004240140200b03050490b1004024000f00c0e9036031220700c1c180300d61800f000c10640304545e60b0b050041300801c031034400c0d43d06181710810b0908181d80b15105101e101030020801d00c204174a24020039115039004008003402d030681000b48200d14200100500b414000d00d640483e00d2074480024001640c041d40d9188184485480c116900310301d0100d0401c10b0200c14010340c0f03901c0d8400607a4111100740b101801101b40c5804816001841c181d0551240c0442e001c1a21551456802da0004a405862000b4001039560b4030040e80c0740d20940c0700010058020140c8410b40b410304505440e0002ca10000300c0c0c2c034148140205034180b00e41600c203140b24440680a01c00c003580e040000e6034020307020b030304100722408030080002c1c1c40920aa108a00032040c00c0005148134101264200d10000c1c040e4a0607900d1800c000050b031500b9190040e48000c0301003071812 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 624876393 1250 624875143 624875161
    0x40b25050702190b0309100507090605070212100c020618060103230105040f052104091d010c0309170310171f020a1d0a030201030b06310506120a0509030705150f 71
    0x368011815504e50380810bd090120032034a650000e441aa0040c00c1784203104c0031200104080c6c002e031400e910000900703ca8688001381060300240000d103d43c0300030f030300031425400040358190440780d11440c48076030304481965000e540088891842104d510308401c00c400e000090101b0307140144200c00b0b6851146503111010102d0308100350348a148601400240b00c140d40c0d56121107240945200403140780505042c0c660b095400f043d46800c0040d480303800e14410040b040c000301038a88a042910f608514210301402c01c030190a200b0220341c1c40600c0281155002e040c003500e02002d00381d070702c103806e40d0343c008103408003039880380c0c001c4000900c0e000c82c81c000030000340e410311241010040510700e840b880d40d00110090181030840075808030301008510403805c1c80c259400d0002590700034080c0180c40200700d061420704298032140c050501000340118030900e882d036030b42e13000c8242c03071000548c0d45898200901d1400b480b84018400c2c0700788910200c9410300302c1591441a01d4142c1c2c1a14070f82e80785405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 624877643 1250 624876393 624876401
    0x71209030e100512061908060a0906140c0d090f080a020a17090f0d020105210601020c0402030f040303090309050310020c071a0a0f0c1208040b25050702190b030910 72
    0xc2c00a15a500400301d00246809501d042801131b0925405014075120070049081070800d591602020740e44001d0441040f140e80a041600d0904200c0c1940c4c2d0316040303101000c02d11036220b410003081e81e111040c10400000d014980c0d0110342040ba62a2203130f4803403101075583c03680d045080d901001c10038803900061034010101da58241000e8140300f07507080071400f8006049150f8000301e0601009021900b0702e1507004007020181c400620740840903041c00400039041c24480600c090085004004201040700290041600650f25240016440011303041c1154014400d4200725030500810300c24a41801141d006056510441d0041d81c80c600e590720447c02030100c681501412060b8140444240c076405205003a100000c1814030062514050740e61880b81d068454404000c02c9880c0284014089040625540714520f404415051f4680c24207020741200c44449440c10000000341840c21515002c4001c8845110441c040e058a0f44030191400ba64000301d40d0000c0302d10914050001240c12401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 624878893 1250 624877643 624877657
    0x20a11031b120f010e160602011a0f010e130624140c010b030d03020415032d0902030601030605060114070803010b0906090306160e0d0c0e071209030e1005 68
    0x8900d025210150781441a00c42d029402408240518010108509420700030003200c141260050950302031000c0c3d8618608440342c000c0e2046a240030000f0012400258504188074012505120014882d00048a560001810141d00009250444040707603c582d0000e509844e2049014170000b081c5c2c3c8a280c0c02ca01108510f0400104840c02e400030311400030006107202403404001182001c42907011a18010014400800007540040d04000b23801d010f07454030210b9241d503d804e00c59a4400300f80c01c0002101903888a155a00000c4c00800049480d03200c80c51003503014090713441940e940e0510707000500d022501e40740400d119410000c0d000c1c3c00300c012104c2c0c09501c60402c9055074240b114501070f9400941100c0e4215400700700110700f40c0e401b0844240f01b1010404010b0780003090900044c241c107922450340d8002c480380d1800000185c00c010b42c1c3e100366040d019440c1d00a503034240084072011102011100c015140c40c0e0060181030b40004078001035a0b081d500b0b486290311404084480b80b1850b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 624880143 1250 624878893 624878923
    0x50a180b04030c030221030708070c021e03070e0103080c070803070c03120507060203040c05030f070b09090a0b0616020102011107030c020d0201021e0703060f02040302030d030e12030403020a1103 86
    0xd000940080d01031101807510500920440d40ca84040c80408611008980405003803c1004030402034031607448200703180d01850310f14200c0f1040300c541c1c0c08140942102c6034402d14001801101c10781c507440400c002001000411110250717546d682c1444402c560100501305041d0003802c501181e900400005c1300d211640c00741152001d2499030303e0b180300f40425200c01d501000810484940070900d0f0f0b0000d140168001c1011a04040c038103010103240100e41c04180d81c058008030001c020305403005e07007554050b010940e0a0034842d51011403a400a00e003800c0c250350700c95404078000001a264401d10082c8070320170380003003000880b8090000614028070600900060b02540c161006007000d8240d05003091040c01180c20343d8400303450742a0314100c0d9001d00c0903540c0c852541003041c000e03903000307011941c5094a070841c50302c1c0c191b80101f51928103140601c000d05480c1c410042181404105402408090a81007501c07401e103458002c2d269015000141e80c05150751010f58001d10b808105000c642c623006c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 624881393 1250 624880143 624880163
    0x804091107060c080708072c03010204080106030506070e0d020a030305070f08160b010e310b13021e1e010509090c04150807142b050a18 60
    0x11598210142112058203000d604062040034002182c901034401903000d80d80b2203c00034900303c0b000400107500141032104202441d04081d005804c0d1246035840140c4e100221070709083c010000ca030291245600a000961034407400206011010070034601601041d40d4484107541403c04010380140281d40280d130040c1130304001c00010f4060001010214171840c0380c244000000d842c0c40070b440d041940f00b5403181e0b400542780390410100c2c01401d0f001d0030700c0c806034a449090900c00c01c0322850280950403000701d424142c8118040c042031281c0b410641c003040c07000b454505504100401302c80a0400c134051580c0c0f000c00401030401c200c00404494014000842c44041c0c803075092000e288809a150621104002018082d00d44214981c802d00c50441000c0c2d4803460084e1400d8002040c58848003006607210030b0103181580305480c460144400c0030b0040d200c1030408130428a20902c600364a04c0f51000e210000802821b581010f071155000715000c0082c410300c003039001c441c0d92030b200700101134000c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 624882643 1250 624881393 624881399
    0x5030d050c0114010902030108010c1103040e0c0705010606030605130b011d0607060906050f07110a081b0d020d0219020f090901060308040603020304120e030303040b4f0804 76
    0x4194054444507000400120b110001c107816640c980c03000381c00401000d60000b0061040c01b1003401104805482c0307191400d29012040400c90301c03400795000b03405c8612340b86070114505c0c58151007524a0141c004008201140d43e461001d8010714183c07140300c1c090b407540000c84080311200c0c81b8108401506840d009100381c2c45804a4100381c2c80005442d50000e0b00744284000718641d441002c540a114038000030709410522914903d50f180207115104110f4111a403000c542000303d0480c3d00d0f254800b051750307210401d8541e000300d4004803a5420790a07100752552141481d03800074054040788a5034003661a07201c12644020604844801c1c0650000320303604129026040407a48142d2000501c00001400341d1603030740c2c40c01140d10560040001940110600041c8480310291101700c0c80581040c00d509010f10000ca612400010005014842c2d1100019407aa04501c0750852002603070b0340c0b40c400d103582c00409101b040010381c00b0504801e400001c4007a074180540442c04501d4001003000e0600d0302d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 624883893 1250 624882643 624882647
    0x3081806070f022410090b0d15090614060f01032009060903160303080c0301030b070c020d06050705041a0301050904020d03090f06030608060702120d0b0a180c020f0705030d 76
    0x3540321000821845600820b2403139040100c0141c00c5410900a496003a0514407081c60052030290880300c0400d10b03081000c10143d86800301d040786203600c900c0d000070041c0c04407400300040c4000c040190455003040714002e00c00d00d07440c5681e80715060840d0312002c10303005480110102c954200b8804030b54420614034002440d01c5001400741024000e10340380c41e041ea200d002c46c0c206201001030030022680814140b04054004a000e94080300d00c040c41401c0d51b155444100052a0141804060254420a500c15922070540d070524064100105000a003000f9000404a40c014403c0001d4404d050f40b07040c0030352007000e0840b8129071005140e800503454980803c81c01c0207140c0b80c2102800b015100020340ea0b02981d0b24000104442c0d1800524a440c00c04040d040140080610007190090102424014410016200d4500400c0300002d1810340001c00f24454080c242c0101c0107100004040000400c05500b00346203800341c550980d400b44101c800e174240e9688540c0141130f0305410070040c0d14000c41c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 624885143 1250 624883893 624883907
    0xf2b091410110409090212030409050702120705100504030302090d0803160804170c160e0402040e0c03060a0e030c030c240c04060c0303020d0518010501060e0d02100e1c0308180607 79
    0x180018990108247c121071081d1850380281e220200d915101c00800c0030164060060814640001c0f243e286091103e6950580721002c1c98283c0074601c2e52500800c00b80761003035055940f004409042c0b900302e0600c60401016503042160b80407800a05171541d202020b10506049006550094014460381110314510030290482000d12949101782c13050460b903201e120442100928082e00000220708140c01800305a442c0e82c081c5004903441351504c00f006071000540300794070000c0140c0002c3c5d10310007400d11500714440e10001c90240e10000c00c254440072030100d0304400d0407030000c10760700d040d0000c6100303c14000021900030364050070a2204020840c040d5402d041101d20a140051504801c040d540080f40c9095801054090004600c031841d20302c01d10030280908800c2c01c02e400d0015001c3c0005800e461b60703100080c028011249109820b0340548002001904000c5c05041c0c4840540419108000104070950000b5444000719000c40c1800c40d10304590407500c1c0c0549559a0703280415a161 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 624886393 1250 624885143 624885161
    0x301050f010507020a0329071205220c17070506031503070f030f050706020c0a0302060c0304030534051806031e01020418020f2b091410110409 63
    0x220900f0001c28006940340306821026521404180203031120f105600942020000083c00d403130743d850002c1c0285a5006640004000699030b0081100d07500e00c0d0125041802903003260300303c19801801401080190300410060384e01e03140b07800300290350003100103648140921440e50005000c00102d555001050120101c851f03001c3c0071a4000d50340c03030b03c0344224461581e009560540050051008010062240d40014861840103004e007042580c00201041002d200080c803030140005d001400400038000d0b140115040070075180d02075902d1101c1081e002600f8101140c4500c0f01c41001e07501e16242c4030030f0302a180d010300541c4040036144001c00d03010601030105030b03261003950005a4040d006115019440100c0400940c0321407400c4800340506c60706400030003600340140f14800050603c0c42c180d506841003010f441e801d40304c110701c071140346094206074090081c0c00d159010081c0178a090011070300441820485082c00c011400c00c0c000c4a10010010a0341034003013000b0005070480e07030464089 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 624887643 1250 624886393 624886397
    0x5010f09050303030112021003050621120a09030312020a09140f13020a09140d020d08040b07030e0111030310090b04020f131e1a0f0910031a0d080301050f01 69
    0xc1a5140d0740041e1031a0000d900840c46070013103159a80445c20502d258071400620360405020a00701400050b40340c0801c401200e80080707840c000903919210400011016054503200f01e80d465603294001010041d140c041940441d5140c43d07032205400203842100e25103d401d035202c0160504000c52f42042482e000c042c0c0d1750207040411240210354840c046494826030081005981d0304d0010070140c450000c81d07100e8401e41550b80c004107503a4442220240105504a0b8942142c01041c43e02d40c0d000d004a820100080b00081640001c03d41c1084a40c24550384c00d0b207030102c410f0041e2048598a21013240c0503501e103965203d0800400500c0c1d0013140214500420160901d101c14004520380c1e0070100c0c80840d03200702c06030200648c400d410042ea40031701c80c1d078040c0c001040c1400d12141d10360580c80c8006117003203000141611074161000569849040040132004061105000180a00600045c00442d010120f420440391b00d0005080040590b0098109003140e180c1000c101040400d20031040c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 624888893 1250 624887643 624887657
    0x106050d1119080105040903270e0c0703140309100e03160309090b0103050601020307080a230703030c0306050a03031209080324100509040519110d180c05010f 70
    0x240c8514100c0908412070360b0701508040c4810604000b40f000d00306a0043d801903140c4600000426400501c040b0321a030402048840200140300f400c10f00003403503104501c001c03001c0003840090348041c40140040c034000d131768180c0001d503d51084d000c944030a40d8070070b0141d4002030520b241290290444084010f03590252414010110804140d031003003c001100001e0481e4014069601b4030312132a030142100f0700e0200710030316190002075601d01c6141e070007500452001c5072441000307102d040780c8003044040d441045100c4003040e03010700c042c0d0454502180440e0500d240001c84900c030b441090101d4800800c0541c02e01e00c1c6440075540d1581e03034031800312055180d00340031000c03e4245008500642052840e040c2c10b401c04a507410b030030900910818412409c4202c0d65041c19400403e5600c88074040300c00241684034240f05044041c0710030700b100805810840303c007102e807481c0b5014026001500e0828030422a4040f48583c5818000c0001000142178000500c03813544a40b80d40c801780e0b0711a0400030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 624890143 1250 624888893 624888911
    0x130b131a240a09021c0e0f190c030210030509010b030d0203030712060509090705150405130b01031d0f07060915050c0a06092006070507090e0c0402041706010b0a080106050d 76
    0xd000e907449100185116003846120210303030250352007010b40c1d0030b0440015140307800e800c7c51502e0f240c0148480c00ba20000806076010b0070310044010400040d13600504426600f09950f4001c0c02410040320484442d52820607050040d0801180d2228480c05580c09503203140d4412200b99501429001d03007040f442d0390f070074011605848048019020f00840300041c803407280380c002003241b5102c1020805804070400d04c010015901c45201100706a03403584004200d400117030340120020600145444135065400d01007002d8400b000c0750415100d481c22041d540c2c42500d40134103a40a02851003010035000f04042e1942d0240d105401038201444100c00380c65030160641c95a0064810600b000d917144104298105142032490b0340d0703040020400d803010380c1404250740310243c581e2590711940130503c0d111480900d203d1020302001000400003002191910f031110ba514038a03a07002d81800b40c05110f00000410602d584805070b0b0900c41d2161703208000b07a070a1000031580f41c0c2088100d080002e803206052 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 624891393 1250 624890143 624890159
    0x31407051f0507110604030c02010309050a030c020a060905091f05090f0f13080d1a130b030609010b1c170307030b010207062303130b131a240a 63
    0x220400c900840800c001d9401c03452a0203040b01c101030070344010f20444040c00c0f600600c2c0410034603440398242c200200042621b000690203030502c001c00400900868021000301900001d2840903a80240d80040c0301644400d01941e521138680a116406030700030307001504103024210503460382400055601625039580011070201141924040741e0b121103007040141c0b20511400b00d03a84094103039440c50401e440c1c1e4450041e80d200f000044480301d501c1d034001078118064189c145c1b02e0100081c2c001d9801450901c0c551006040c01c0c0390f480c0c46809450041034103040c0500813a0714850300185600303490004400251500034060000721540118005010141c01e00c0e100554824401600c001c18440114000242404565002001440203031b807420345012415501c50b41ea02101c080070955030380c50310040c01e1080004664000e1410b502d40d0b080010040c2040b803034554591064120381d440b8150018101c44e1001300301d034042c945081c4406484040d141000358110f10b00f4010b484001c0d9a500d031211 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 624892643 1250 624891393 624891403
    0x1908040504140f09060402060415030e190203070e04021c060e01050f01050424060f03020d0e0a0b0c04030213090311072c01030b0615040806010f230d03140705 70
    0x4840c00b884040c8041004550400d120581d01c000d26801419051405600240341402140206c00c2140e1580e000142e16502035441859080a0241215664603c0301440c0400d02440002280a40906000050945440d13190a0300030341c5d000348600381e48044980902081c03c0c0012040d0303565a02c807051900040c10a1041c90302900844242031401c1d03041c0707001d000c1a50310382582403103050b03c00e54034003080c0c40501900380159096807903d0796400034a124110083d0044028404650749400619038001100040040913180700d901d022350b0580e560301070203c040c0920b100c041d4004524200b80500f92417642c5c04545460300c207050000c01000641080c510f0715995410a030300180314450381c200d00c1a4102000c2440140c03181e02050f580d811030b61401070f007045c0a003800d40111500b180d298050505801640d024003501000c54102c2c0d82d584640001c2d128561007811070300c2c0c68400d160950190140c01d40c0c54001000b502e0101071403016034084898007400c800b020072503c82448403030002082404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 624893893 1250 624892643 624892661
    0x20d020310140d02040b031f0203100f12020603100e130308160207090e03041212080705070525080a08030105030c030c090c070602070c1e060801081908040504 70
    0x10016200d01e03020160314012103854010202c040385000d0051a03590f40e80b68081c0019506030b03004544840c600b004640b900204040c03070450342058000d841290b01d190303400307507200d000d2807074040400c0766880d0304203960005980681c0d18000c030b0050344c8001604200c0e000b5034001c44425040403426540c0e24004011038000d1b10303040c0d007810ba00d03000075092641c40461140c0005801034001b140142500d0301035910000c40c440c2155a030f8581c1403142d4040700c18000c0c2ca0051500214216100886152180d00c10241c040d140022071040c03008224000d00c0350f41070b5050303180c1c440c0081c00429801d18074500403418079820b00714107581d000e20210340c458003441445041c502c20741d40b240e01d9505000c105030421301008501c034040c3e802144c0c110011b0703039003e09058110203541403240d0b45038070b03030304289000c0d104650018040e41c41d0300c8000603103201400070528114050500303075012252a028120346a1000f0722800b04075a02620181c595131000164128001d4800c11080d85041e98950100d0240c522401c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 624895143 1250 624893893 624893917
    0x1602120a0201091202010507051c090f03020f25030308090709060b070302060105040b09040b1e27060f061c05010614090901020c1b06090307030b0a1a0f04020c1002 72
    0x3003544001c014a100301c20882c00c0740c6000030f12080c60288c10040403402100d14080d42c506c1403c0c2c1d8264099032a500a401d11900084040c075840c1080c20003a581b8114070304a001c0030b11030384a5075611240410078407124103084002c0e05900c2441c5407401c450303100000d42407800c180200d52000078a4401482064000c200621285407a04205c0c100a42000c10580c05180900d0030301051844981c2d543d1601e55016a02510b601c6030354486026120b00369131000018500b008400c0244103500f42042c2c0300040302d00c1c0c0462030500d11501403e00e9900e9a0f820380e4021039580c85d02c0003081040c80e010304040c120891106580c184200b4584603542510743c66070085060032800320810700349060040d0b0a80e1302007003d000a515200c08941e056680f00c0c0482d8020051992080010700355580e01001c80b500800010101c54a06071242002100c0e19002c0d200c00c0101032900380696900e254000050005038001081c1c151980d8418050102a6205d10507050712800703400101d044e00f00a40c80a048014010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 624896393 1250 624895143 624895151
    0x41e08070e153106050d0c030209040c09050a061a0c0703030e010210050103210512270a060b040e0c01080112050f06010806011a0309030306151b150f010b031602120a0201 75
    0x480030740d034100c444d66000107000324520449200420001070310902100e83c1910b20400c19612410700c41da03180415001110f4403800c1006128110740c0741d0300024151400602405c14a8035095a09070307407441100c140c03641d1034110000400201c0c1c00780f070801c24041d2041c010b4425451308a440e810844101342c01c212101e508103952105281c2003010600c1c0e40c0140b0f420b240b4501140d1110040b040d520040844182a40252a055040c2c01680c020b8140030702c0402195548490751500700090054104654080c51134082500900f07480040c20081081045e140c41e403490f400e011030040310242c03854080c0d4a5200c1e0040c1907242203410420f4030300800100014100ea541403e00070441c00e0008001044040030503c188032500801104132500810211040d4004070201401e04031540216100604c62450880102154600100d200e0403020300104410041d5078404044940b1801d003800707081900c00092000420603c0c2c20f0000542401940c01129092084501843e100f41e0041060744010b07511 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 624897643 1250 624896393 624896479
    0x27110c01020f07110105210601030b060c01050406051b1213050a0506010305060705040f09020c0709060605040e100f2304180320060c09060d02041e08070e15 69
    0x10041d081300200341d003441e0440c50a840d8858200350107250b006200c40c4818101c0c045281d0343e000740e112003c0352802500180e102d01a084d1428020700b800c80d801d0f40e40d40d003020001602200c0d10852840c6c03c107030048040742400d0031303145006046940141902d03400e820140600d400305004204040700340d4450300044c2000e60440ca007460604602805400502c04c01b404140800107030303040180d00b5640789d600c006071a12908c4400d03d1402d46113500000302186800004200d03258400002c1c0b00384c0d00e1410403080943c444c501001c0204180340b003050314140d4181e000b4025035801e81801c40400c00c00c0002c40744514515000102142c944031400311900d9405000101010b8000302200e888494142c851600e68007000fa09545030303900280440c2030110700082812407940d410054942501450408540301d030384900d500340d40407400203408850390880100000b152100050b6a8054492250701c806140e1100502002c031800c066020a40c061110125031030341c4640883c0c2600040b08100c0c0144951030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 624898893 1250 624897643 624897653
    0x2717060610050903100c2007210515071e09030b180c011101140108070906271107051507110d05040308030a0e070902070b0127110c01020f07 62
    0x1009480070061040a2007100c0c4070f540c01180d040403140d286000400c40c07080001e8201c580450039821100030005220985120f00d000180c03010039107c50340580105c1024201c0032003501c4aa02c42e004005a00214554042015152040b50003a07440d04005078012a0f418001d21445d14160400c40004c2200702c0400502c010601c0542d001207030841c070b02c04000044945191203500d619540e505102501d059804016000d41c4034580003200509140640d50f1140901901c40109228102441e414030f407003c200608919100074040c40c5040c0c6e41070302802560600000f81c00c4a202c1c4224141c0207100800110b58144441c1310308002c102c2c400c480700d18044002030031161481503481c140c2d610081c58551102d420204903802d880c0c00040c1c981e00c9540c1d400d0014090420b1a80721582d60061280000c2d917010140c000c4d1502d24480c501d01c69150b030b26000c501e1210344401a8400259081041c42c040040715944104100c841a410003454080302584460076603109181c42e001c88440020b03010305001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 624900143 1250 624898893 624898909
    0x409120c051005040807020d020f0301150302100908030d090516060206060103061e0605070f061107150c122013140607020603070f0c050715030507020d27170606 71
    0x41100c4010440c13802c02d0f0301c1319001c9003c3c2000c02030041c1002036141c400e658400c8420740c02c00300000d000b407081031000c900d20328469100c0e1000328000e5980404c2120441d0107015007100396500321006509100340e081c503000240150000075621405403103089105030300042c00040c0030b0074907a0010900c90500d14001422150694002669540382c003107414515118030314408100e520625000d620754010341007400b201800c07110001d000e070b4545865407045c200c50801800039180280002c0754400448030525003030b03403100b280b00d1000944200607201c04040b46c1d4480c01f0400d4241e825400c04040c0e4982e00d1009500c0b81d020ba003000c143c2444104040400c611180c511806d06454990030904964082210b501025002c40b0500c52066800001584514030a40d850b6802c071044600b003907510000d50714450500c400090020313060030002126a800010300342c0c4103407000d503203000da1070304811031031020703001652075448190145a1000803003000c0180d082c0c4d404900e140190006081c5002041601 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 624901393 1250 624900143 624900163
    0x30c06020307320a0c0606090603030c140a050a080c010f0f0506040605040603020d1e061e0501080604120f05160c08160b07022b0302010c02070b09030a110409120c05 73
    0x3007152202079084843d8040140c440d144881e0038803017044e0609242c400b01800302900800c15a520303001d0700000303042c0d02c540e10384060f601840e403801242d6080c480203600c4901c161805800c3d03900c00c1006100244022004003150b031001d0000054640d0181030660070354007028004405030b0348030b500780007c1d49098894400108801c45040064600e141d0200d801040b400c0310140c41c03108000d5540c41420030038024071280c40d03401a41080f03440c1100d03a01c0c45a50324410440d456082c640400841c145000060359805590071240d00c0c006080c001070704444000b001d00f060002c0041c28040103c1103c1c4001008a1161085004014190400d51a1032509007110b061500d0030347c2e8079808100c2c1c24041000c8a680c980c058400412030410f10f0224000070075850070742c2c0c16001601c5046000d055040d444080c0e07440aa6003511a46c0790b07100700702140384c02020f6105505820860b50b5000041d10f15601103289000074002155044281d2618400522040e0000c400328010b4401346003048018858109a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 624902643 1250 624901393 624901457
    0x1050a0303021002032a0d0b040513151b02061e01050a18110714060a020301080d030905010902060310151b0b040201020c130608010615050304020904030c06020307 72
    0x151858400965880c0911a846075484c0e0000c08182c2d46102c1000c0c061040021580f02c00c60745502420b43d82481d4480426520310034645080d035842460980074080c0207540b003421a20103911107846040c214144041d10010160f640c031031446004c0114010016403001580103491380d4030b008101403c1e4041a15100400c8900140060001da038640d0b03a41c1c416104800b80c00b46043c0e1100706020010302c00540c0c68005240082000e0307040080102d030000741c485400050b07400c140c81e54813007882a0b02080c0900c0406410840c5018807040c86035120980c0c40b40104004a02c2004680110340340da4810358103001d8511351064244030204036617120700000c40b5903103400c1108860444800000b06400c0b2001444082948045001c1da132080140b0800000c00030003900b4a07602c00d021080007000c0600c100340b625401c10740700040c00e88244030701c0081c034010394032610700d16030b981c3d82001980040140101c0c24004002410380c0814443d101130352041403a516180d0b440703e80080310070001c20403c100584 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 624903893 1250 624902643 624902659
    0x91b09050a0902011e0207080118031206030c091107080408151f0e0a0b0405070201150e010b03132105071406100e0c041a0306010e15032412150105 65
    0x20043c0d9001440ca000200c9051141d45c142203408412400e005455201901d59820602100c8880404600c5001c88500c29150960740d84101c5800300152551480040e00b0014106401c025081e0141c01c904091100e0040b418034002660340c0302c80c8150800e400800b081d40c080f00803200700542880c1c60350b810890b1403811110600c031600407494091030500504d1280b544481c086058182c1c6500007007084d41000b80140918500f160b0b0003030003801c141c1040c200070960302400241680810544506032100c880307969246550302c0103492541006034100712030340c801300400310880c00c011090681860b06a9521141e490299041a030851900c095803042203030403040c1840503042d0540e440c030044034492500e901041c4d461048038800c2c0d00446e4082101031850414000040740094011486048240c907650301041c4a101030000150401154a2050901b0400b04880c40c400c89030301c4c1214080b640301b49100004480100b41c4004486d0010030300c0b5404001116803011030741d00b00a001d004107594100d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 624905143 1250 624903893 624903911
    0x207050f0d081f050607080403050d08090d0f0207091515090305010c080f0703271b0b0301150c060204120605070215070507020f060909180f010903050307030b04091b09050a 76
    0x10a0342c0072604c00c1d0f6114620001c1d1032000c00c102c0034156002190084141c6018581500f80601000011100900c09000e40320004861500908816080322482d60040ca00c3c00d0500c16010010440303c20180d112156901c030005100700300c1c002c0c142175000380d59a200b9080f03265242481c02d43d008500201c0c10300c4540c3c0b04010701c0b000003940803680114980b801284803a44454803451402420501807000c880d607003074460521005512030555049050780701c3c40143c5d9900102803e502003809407803a2074800807e0303100c0c1e1601c20341903802c0741401120014039003907640345041d0510306180002c590301c42c0c80b0070030460955014040100d46c1243c00f0309446a52070045070040083c400d0002c000d00c91100301103070390401c1d10740318151200300700c01405c01300c1c41b8142650f5a207003180b280000c0c01e409100c1c440859800c4001170185031003540d8180c40d0242551105c1310244c0140c0803c0e03c0e00e6400594030348181012540b0351386420440c00351301300050302482c20180c1781015140020a84215a07040513206 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 624906393 1250 624905143 624905191
    0xa031b0f0605120f100306021602091303020a080a0302090d0c140a2420070e010b092b02032505090609070309021f02010c0e1206070e01030207050f0d08 67
    0x2842c0c0c07180000c030b5244c03035580da082c3e0b050310321020390b80010707150920200700d01088c0e005084a40303681d1802110088031540c0c3d0050194842181504002e005030841110000082d1920014102c524042d045c0503080841100104100e50400e03c01603a00640701c040800a1883c0311850040c03020003038500c1c7c2111410401c6054a0031a802031015140c1c201d62175948640d03200324a080c03a1003040e01d80380d140e803010381400c0b16510009401003c504400a00c000220303860310388100c0c1c13040d5801030512208600850b010310302200c0c12000080b40ca031008103811005903414001003691503401d0410404050184443d141c0d2407000d6045507001c0d010304c2086c4465a610a80d600380d0054075031401140d8001b00d131011558803003c40715048842c120443c510500c3d00d4040d0400a024001a9614212403804104100b580c4221042510742c07a08100041283c4610550030251804010704000d0326200b003d94850b840d280f11143d00c4400d9420500911f206540d108107880d4000c0c000e8240202c4440b00c041d40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 624907643 1250 624906393 624906427
    0xc020a3b0f010b0c012705161401081003081b0f0d0203090405040321050f060f0f0405091f05060a08070503070608060a1a0d05160c020f0a031b0f0605 66
    0x2440f83c0c8040103c0c1e080100542500885080c4021ba20714070a0b0901d040192400c081c043c1761300703e44a0048003081d4804011102551088a1400b02d04d4101a80c0450041d070755400c014000c645072491110012000c1030391103006051440d10100c907080042ca031000014180042041841c0540c1c00113003117011074580c00015144003a41c101c400191540b02c40ca000d0307816000c48074084d40302e60701030001c81840340c0700c55000b0381c400c24440c080c503c3e10356561810080c540c140c59038590f90110b55894482201d0505170320003503003c0c00d820102c0d1b203810005951040c0310340403400341402c40f07610b56081028504000094030001d05c20071000300200da080c400000e4581c4050301990003080070306000181d5503a2400c0c8513800900050210004007421600142c01d00e90154080e01030660070700b00410b010140b50a07054464409aa80e502e03124122a4204410311003484402d56015001020100104581c90308a0001e240f10542403a04107140c40020b8407030515651080d41804403e0101d03000860600c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 624908893 1250 624907643 624907649
    0x10110901120506130f022a0d0305060a0b091201050a0906060e07051c021608091c020a0605090f04021902210a0804030309150f0e120a0c020a3b0f01 65
    0x80c042450301249000c0e0000740134510709540080c405080c02c08025002e002e252440b03c0c090300503220013001340348c000c3c2c056070310544055821000704101000907900ca01c0292405403070040c11a5194031f00c4c3d050382401e48805840c042d90903981c4041f500b0070402a0b119500042c000e010442c1d071607203089100604980151955040365440c04444051440341d241e048600b1140ca20100c8103002100b13080c0320403103401401076035004240070101d94141c95007110000c0020f46c3c2c0100402034043c1000011189500100b51458021040c0003030340205981e82d0000c0d2007400c5802c011103c043d00d0803000241b81c5405001c07140f500405040e1105912490300c401c4414509160906031410b8840d807908500901c800300010309026400c0c4a69064201a9000200d190761401d001b07000f4219440c1165480346502c40035840f140e03008102c5128480d0103400b20f81002d5000030112040d03103071340f001c54012482c103604803d406440520700e0042c40095410b6803030144001198500800e18004a40b0201810180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 624910143 1250 624908893 624908929
    0xe011e0e03072c100305070e07030c11070603020c030f040308071101050a020613020a03140c040f0c08150d081c110301061b0501020d020f0403021813060504020310110901120506 78
    0xe000c4d40112004000469110b8101c42240d5601c3c03004000d00d800030346100b00080e05000c19461420300c03401034640c960004601510f125454040c0990003503011040d40c400c2808280404c055080103000504025805040c0040d501c0d8120310703000100c84504c0740d800741401002d0040b4001150300240c0c00758000f0a880c2d58015100710707400003a92110b240da200134402c8a0400311045602c00c080f6101d111094140c0b01402050200341c0c1c44030580d140000c079000010034140000f24250040d801070220340502a050b224130113015296885560300440c030440e009503120b00942000790311440f40d241e1021845108600b5541458002020051110320050b2198000c0d10410144802903045a0942d071141408650300c680c1111b4514640d0010720069105110752145006203450102c03e051003155499403035130744855a40c0c0e80303600a11001e80140d070148124610074469284611602c561040902019134837205914001070418101c004c2d00003626040100340109611b80d40c08031416050b441c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 624911393 1250 624910143 624910229
    0x10801020a0801211202010c030506030c0d030819150e010b04050a05010f0332100e010522020a0c02040b0d020102060a0b0f1905120601080304060e011e0e0307 70
    0x13041e25440ba00d044003400303403002100101d00f1035000c3e01503000c0726004071991401d000303d81e1524101070721950040741e02a00401240640d50000e44200681907012244000c04480843c541c00e4220494040802e0514000c103035480c2841400500840c080c01840703a080698900340c1000c002c00e4203400036100395070502600c124401c10ba5406a00308480e03480f590a03003000d068000b4842808410106691605203c610501060001001000b5641500c600c442c2d086116440c25080c401001c1c03440700d2180c0c03000710510422107925518001030400c0038069a500c10310414038010401112068100d0a00c5000c4201030880140d80104595521103540316001503840c800f040400c4e103aa80c4100c610b0361050170301c120080c841da5a040c40e002a1078041c2d5176092129100e24140b60f840380d007801351140c1903109000c1080420701c54102d0001d104018545212524111401c0d038071462003000521011507950361640030142401c01c0454014464507440c080d0b104622840320203001c40100e803010702e0141d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 624912643 1250 624911393 624911429
    0xc06040b09030a411b01090b0301030b0a0506061318060b0706091b0305070302090402060f030a05060f1909090503070f060e1618090501060b21010801020a0801 70
    0x20902410710b030aa003102d00d0014400c03046201505602c00e019002c02d801d13102581d0701c9600009405a04500a10100281180d06418480c0300140703c14000050401103100b001003240034805018500030f5100d500180414204a0b550806a40c001840030f03025401c03e02501e4268a0041200021501480d100c29441510307490110041d02c026045142508400109401048147d622000700c690040f070300f001d02815040c100c0e415031a0340b48006000340c5d010078020b1000d0315004d07402c1a04944010304141c078005607071042c0d0319a6002120004410b0356620100300c3c0f40c0c10140344907100110110785081c0d62080042203074480301810b026020a455a82c00f00c4130401c00e08000b02c80c5101d4014101288190311440c10714058036034060619081c0c09101c1659010001401c104019649012540c0303200c0e61500c402c0702c000302088401540c080d92200d80000d2080b20700b000a118010001480861149182e910b4501c0414103a2054107640e20410541d81e2095103c203c2a05680d41d01040700303003105c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 624913893 1250 624912643 624912649
    0x40812060f031f0b060705061605130303020d020f011b0804170304080406140307050319090c0b07140705061e0409020406031a010e280e07090f080c06040b09 69
    0x1c0d5000c407103030103109120081c2000340696a00c8120b90114080511280344110103001c400d02403c840101103521440c0440c01d445501c000014006455240c01c41c104090101100d494075820341c02038016800103c0d583d16002e41c140581611403010070000e00100007a40010080350f210340d0090403c210200002ca401c00c8030110074201c440000c1000a5101d003801c2c14200320581c80744c1314540100d01407010b46450241680182c80c810b000a46880e41103030341304049001000c80c100c0f1041002a40e0301a02ca000071844c0150380c000c0c04154103a207445211615000f4051110350600c080c4075488000c081200350340d5003007141c540003400350302220101150280150140165001004070718004a0003003521941544100c50504164010f100000030510054602e00f4844100640000c1410502c0c80e1403020035101c5102c01e8800e803816205160b40d038003c0070070000140c5113100020b8555000700010481c40106101508200c0080c04050302142c000602502ca50f120b220a1184040f5101450755 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 624915143 1250 624913893 624913909
    0x51810141612061512060605040303080c0c0a030e0f0607020a031113050a090606051215060a030f05010c11060c0a120f090c09061202010c081303050a060605031504081206 75
    0x14031a40003d01c00552203c964426603411301d40800001200700030355105616003401818211181511454901404e41c4c40460b05100002c041070a80c0f1010481c042401800f0080185124043d03510020f49286c0032041080015900000a00c902d405000e2280543d030381f41d5003241240d50281910000b00030101c0416080080d143c00500c0300c2c3c0c90081001701c841d03410f82043c80c5141c82610100b2005445038101f1035280b11200019101d544140c6a464102c041701000301d40180000304002401c0da5259284070b607526400c1401c03070301070351608800000d1641045881844450050203080c20b0324082c05508040d000f001881070400042000c15450b12003554801180c030348600c0c0302803052410a0601000d036000512800581c540751040c0042e20012005c181c008165050351004440d07100782d01c0780030064000a00c03883c02c520300c0e880c0005c0003907010007194609620500b4041440b902e08000c060506041d402d0603c00586d14404010000f03441c0c500700c626480d44044c4003403168036510301003a850 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 624916393 1250 624915143 624915167
    0x3060a1d0604260f0904050720010605150405030a03050a0e0a0e101e09020c0c04060303080f060906010519090e10140d030c020112020d0518101416 65
    0x5800760000340001e1001d42601d1800380c940d400c5080d942e1040b11000306440388140d051307408158109110300c1c21285003540083c0c2c0c0100d400d140002030741c07140250000c440004d818000009a64503a0b0800c05810302c0f0700038031f00100c1d0f400110303401c0c60314003400f0903101c01e4007140c001c080102c00103462503007030700800c0c0c045c07421140a00102039241c1c0703400042120540689000e66408050100080c40d203032507018030220700031403d0200d210249440500b04c00382d000740b48585c8403405513844074200d54aa82c0302e5580110301076a1080743c682000f0917807649c4000d0286c0190301801c95001003183c2a41c100b003c40b0210f0042d1406071402c070543c400100d0b0b82c040f039600400c2901c0310b2030040c0070300401410030344001c1e18001101a17955000307950030882452461840200030441c00305014001d0345c01071002d010146000d2402516000004c0c0140c000c1304d03000c0341c4109248480c50901480000108210610710190341820800c0ca5003001c1590b8034040d0040410070039103e0031006000c603522401c4600e4034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 624917643 1250 624916393 624916451
    0xa0609050106030f1a010912020103140c07020a090515090c0d090308070f170f090f032209020901080406020a02071d01170a0f080f04080321060d0203060a 68
    0x50340d611a1402000fa101000860034201d0501010030508080303035005600282e4140c4844600328a040e24102c0d4680d8003060503410f040d038406400c3c49030b88d012600c0ca84940e45400300c455455005204110303d00595410508426186c8810441ea900c0e50035000d81c0c5092046032002c28580c0d803d4600c10052280700704402d915420705c0100c404040d048150107000b03422715203d10000c1c4c41e807544202e440d4115040c1c1c0c212a80014008200c01e501316403076040d0042480402d440d0300300106480d0b5443c503401400c0074442c00c80c410001b0594450804080805811400030540c0351242c03031000240090006480500500c1d0f0014100784040d000f044441e00030680744e074400681c0f0002a0001040447c244101a035410200c3d0802c034500002260310f69100d6448440341c0d2200440e61500311003504006106500444100f1000c5118807040010303100d80095030034600e002440855442e22007007006420789000c1c400da50018401030b13501090b4643d110b041c078180040c88160706401040c0e0310500c41400c240d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 624918893 1250 624917643 624917651
    0x120818030d0b01030e010207020a03080c07030c080303040302070f08030307030b061c02030109050c03071403040f020d14100c14090301150806070e01020607050a030b12030a020f010b0f090f0a0609 86
    0x461050282c10281ca8040240c8040145041c0e80c01c0f040c0c241d2082d440001e6001d003c0700c0040c000180e94001601c04180c100045130403840e101d40e5070440001080d040481154404001c0100301981041030001034072a620320750850f03600c0c201020380c2c0d0b07010143c40c000503d03844041e600c14507100ca0b41940c2081002101e0600107180c000c6041009500078003c0d490054100000601611510f00450f40100150360385d0b8192484040410034407900050000c5504800c5204aa0007598401c540358491900400d070180500203505035280c90401d0b40c00c8420141c03400c0015007803100c0d8201c5c028011444041c0c02481d600d0300c03494006401045004811100343d0909100841c1c1004005486032242100780c85174140303100c200c80103907038500c02142c07010000748082102c00c0000c0c0c482d0300100010700b006032581c01044034681840d030035604464585401a441b14108081c400e40074094051144002d480344100c14001390081451600001e01c41011008001c0100d01d0303050040d40040002c1c03104040801c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 624920143 1250 624918893 624918907
    0x30a0c020f041b0c03031a030c0918030319051f2c010305030c0706080f0a020d14071d010507202b060b1c03361706010312081803 57
    0x741c40a50701132020f5000038581641018000c100122000c103180d801002020f1501c0c41804000c09880010704401c18010364401c1828210800c0010354000c085900300f680001c20441c40c50b07070855a005103142c9050480300000c1051205000e6640140e40e00c1c01c40020031016001d9411007848201c842c11543d18108500000c00d00c400400500b0141b54200e0984440d41c0d607411045940c083c050f5403c40c00c0300104c401180b140862503004100e00422401d02040715102e20303009000410081f101400131882c00f903402042441300841e090203200e800d003071090416500351100c1404000062121038424603c0500d07220a0b51042202400d80d0030355281c01403505c2c00e0003500021400c015008980345418048107221514015171145034410407114a0b0002c0145a201202c900b03865843c40400e401c00c03030f4518011070304c9150078000b042d46140c0600380060b242c507000c1400781e01c4000e0703044115000400140001400480304641850003441d242c43e01e42c075030740c0c4003030a03650240105212600c0002201 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 624921393 1250 624920143 624920147
    0x10b09041808041a0a0e0105070314031005040f090506060607050c10021606030207030c12091d04020f010302030601171f060206090708211b0102030f1503030a0c020f041b 75
    0x100280c4e180c0e500325908981070040d0a4140e805000300f054003040c3c0f12a10601154494406002d407540a1310b0110700b056022000086550300556118240c0e50320030405100c1802d040c018000c01070740c00f0f1010009030705103883c0c5c692035141c040c107800d2007401c00180c1b000620100f084908114500201401c000742e41c162006580c40040140c2d18480801c00e600008126000740300f603415503034041c0c4030803c5884841d5241015685001c800c0c0c81070004000d00410140009100c10310500c0c03075145820b2050600c0e00422030000c035038840f664100343c010010400143da0009071040c4c000b6820702c0100c00c0f612640c00000850005170044c2000c0784400ea000503400e940012050700808100054840da191921401031b12102e4030740207000e08a20203050b20340450b4030000100248069a1003445501c10354011031800da07403094401181d8404180c050160542c003148144010403012801189001c4054101400342c02441e00042d2103a40c1a205011094665800250a130390780340400070f107201c00c84100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 624922643 1250 624921393 624921397
    0x1a0c0c040e0609070f050d02011214070504180501060c021210090b1e04032705040f0623130e101d0f0f06011716150e18010b09041808 59
    0x162260f611950700001408011001d00380199000580340d9044484030360019241d0700c0082d041003a0311603540c900c0040300040100c002d1b004110b1562200e80e0b55150842041464561030a04c00b2500d10340f4004000180e00405c1e008c0409a06458070a40c2444c0da2902c58144184042207034800f5080c40c0720034007084440207003148500c103413640c06000b20991507007100c00100c080354000e0100d9a9082d1810484400c482d519141c800c60a044210107a2550040b5003624406100d10041b95203d00c02030101003841c0c1c0102d00785500702051181900c00d82000154032404841001c2c103282c1d914804021030620600407200920307080c8506002104a10f01c80b200300031440f404405090240f000100c180b07120101c2e20b1006440301e500204181d900b80310140444403200c12804001c0d00c1400e9407400d403040700213482001400b408055020104070354001600d0361080c48400c5100e0003641070b042200d015465429815110b03c0c1e02403649480008000c107009286454500c04440512074090b4200258400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 624923893 1250 624922643 624922651
    0xe0f01090f1709011215050a1e060507030c24150302030c0103020702030a2010050a0201050109020415080411180411041404122c0f010206011a0c0c040e06 68
    0x41d0982c2c0001e0b580703429031607015240d4018001959840c1c2502040031a400c0304003100030700441a440aa0799a00290f2102250313880040201d600310075030290200c1e0780e8200c5000f050507041c0603241075825980101038842004c0d0003000340e41c286100307000b80807038075006500610381d80c28200100c44820725403041400192108074401c3c801c0d03060001041d446802500c1c07416134064010030704c00840783c2d60080214110102120002215000d03901345030b0f108070050300114003e0b15181c1d81c5420310340c0005e0035203405030008802503004110810950001b90748102a0030b00d503140192003500c480c500159100c024882c0c0a84c846501c0000c000300403280121140500c0c89038000303a10501051080c04180c3e040a80b900c01d48004050004011882c465940d40395070781c140c54204820641c2440803855400180c04100e80c001005022040604041d09100d0510200340000c1c0307040d6140050500385006000717910340c0100c0380443c03150000d00040141202400300117100784522030000207074640c1c50b00100c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 624925143 1250 624923893 624923903
    0x30303020a051b0a14011e0209060c0a080c011407090314010f020d0b090a110412030e0406090b092a0913020d05040309170c01051b060408090a0e13060e0f01090f 71
    0x95172480058014802c103002e150904400040822002000c10000d40000e04400e4002c982005800c480e00c0091107460700841c4201121600c880c02c48080c982190660802007800c13444030414042100d4006a00c4011207500c1b05840c1c2810ac80340c40d481d0301400c8007902e09040745002141000d60140701e500040340c3c0700001e4400349a165100900360040e1603802c80d03807500400d410402444800301e003c200c02d43c00d40c0039007008190400d202c8042000c0324010341c8640b02d411740d22540d01c030992a00c10308694101c1c080d070b48100c1c0d5011014030260b26040000c1140b820020000039000301ca0740751000d000d070701c0c0d40e40301c2c8085403550300411154001d00381c11141100000e03007a20010a004040000300800d0300d02000c0200407d0912000544542c0c4c0540c919081d040e01c04086040162010440d81d03100d42e2150110a40741c00c0d0f10001c0c81040742c080e41081e10302f40d410504014a041d41c10740d10360600c60304440c0104100c4101d0525909023108108904201d50a2099480c140a01c4104115090b440360b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 624926393 1250 624925143 624925163
    0x20d0308070e030712020111070b1204061404020f040519140f0603070b0301140a1e090b0102073507080715090608150a090f0f050a0c09030303020a051b0a 68
    0x440805031541a68015000c0e2145041c17102009540309a403040e01c40f00b5001d013216140307500c0d80c6d042c0405401106601581d031b1007001c100700410000740160f4424008204c4450f9207824198002030a00344068400350281e41d42e80c0010f9440007800b1840f0100c4d011488041008401141400b00110411612000f200c6645400700313401303050016240007101c1c034950000382185d0034100101b01d440708002030181d002603007000119030f4811281c06400403a00c10503006102c546848804001d84103102403840c190b4001810802991641c0c0350b0f2840101c8498506503183e4041202480c2641078011003445d40e807085400108002400041c031009031422844040041c448203881140d00028902071180001e200f0400b1036600e001d090207145032079800a0811040603201c1e0018400c51f681140c0c503041e043d48804038009a250f0502c07460307030085180c1e10140129044c480000d00300c440284001420190300007544890144103e00307642a04c10f0100259034a078007222112581d40b603041c2c8044da03080c082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 624927643 1250 624926393 624926417
    0x2009040506060f03040b09010207021315050103110702120a05010c02070311030303070917010905060c07020a080c030307020904060212070905030d0306081c18270507020325020d030807 81
    0x301c0964a20f40d041040c624038540d140d0341c0d1615121800341100d40203640130302001d00180c2e142c0c1d0203403c0801081800040c0000c81c1d80c0860400c51072940068181890203051004a100540880d415582c040c0c07490741c1c1c41a076249005203003000d03040d07018295510f84041d07a051a0b50109000302228043c4c100c900006484208040c0c9905c42501da11011038054002000303424008019170500036906400021408102d44400b4105002102d2140c040b080000300712085140c80e50015015048030300c014041c444a84010139903070322031404082d01c100c45610014040102c2074046400c140d10344003251685041c00d41c2c000e401c54240c1d000d030a10a00405000c940010321034841c0100b10f4844c00010144809080304211454652034003035010480c0031801e9841c00f0196115110080910f00303a0003e40500d10710070800240107050340d4145a0741404248503005038000151400d407009091310041d200303041801d088e1642084080290410100260013090680008600e8030420750383c2c482e0707181048 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 624928893 1250 624927643 624927649
    0x30405150d020408060f01081f180605010b0910020a0206070f0f080a0507170a0c030f020106090509030409060b27120d020c03070602011e1a03030706020405101718012009040506 78
    0x3808419000c0f00440c0d1410001c9c13441c1b12a00500c107501c0c0000d6804003041016100d0100f9100d090b00450890040000d622400c0d04241e000d88a02e0b0300240301820320036075940c3c009040c0344a4031401403c4503030340421a40a0080d005d108a0b5000e078001c40c115681d1480d0b0070080d019420210040da60440b051a072444015210000c413040e1480a030b0300d070800ca82e0709580644401c8500c1203504115035945c0004100c1c02e03164416075000c0c1201a00a40c0c541c2c1c0340a000304250b80440c0c000201e6260144807a4400001c1c010740004040c0b410708003044400034020100301000e40c3c084038543d2500c02c9028484d0300a8002c00c80f046c0d803140030740c1aa0b140a0f180c070350907400e80e400b0000d180014040c0e1411501c405040d503000d0741814005400800084528400003869074108039800d491851303000170700b0480744c94940c280402080342401c00d111132102c40c9540040b40e0000401000700c0800800a0030108002035110707000208400039080c65114850f2a41c1103150403000e2810b001e41e15103004500740b85 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 624930143 1250 624928893 624928903
    0xc19060c030b0d03212d0e0d0c060209090109020703091e06141911240403050a020c060f040801111603180f030f06050f0603030405150d020408060f0108 67
    0x42405010028450f00e03559045880b20201e0360000b4589454814038200643d41d070103011002d2203803000300d480a0700400d01024540010700c030100f50b82891718100c50603a14000c0341900e00300826040c001e45c60785042c00e1800c0a0f1041060b45580b007410400003203540b40b4103502400300c0702e01a0303aa501c01c058480185028007078204010180000b0408020081248500c0010a01400000189041c50444a100440510601c226101094114010313041100c4100104280e003680326540500806d09158034550100c8040e10290802400003014241309000b008000d0305000c019101e240c2d41c0781e01203410201a0054059000c40b0750030040b904030701c007850750252400180416030490b03544415550030369510f948956200010440c29000240c0500a115088002c0d0b00170010400c4800c1245403000880c0d20003030803000f201c109441840f800340c4002040d50291002565900940c0d1400c05d500100c0c1c1c0503d1122004c2203000003400b042d0303980c01040c000e000340800002c03101541d88400da210788803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 624931393 1250 624930143 624930161
    0xf020c0d0c09020d0e03030108070509070507020907110a1a01060f0810120f08031303091d010315020904050c070224090904060b040507020a051c140f0c19060c03 71
    0x28500c0c990038030404803543e009150460010070300160031a813120030282140c000340e20102c5190017842040105007010f0040c0c40e40b200071860040e01d000c586a002850000004c0c1060b000c0102c1041200070701c03401081405072007a086560030f001003810200e1724031f03001c000340107420015404c0c48064403c40c2c0554a46401242c0707a00c82d419006042034100d0f001603c0e14281a10b1803500ca10407440407504040c025070041d047c00012204007485c0f03040c042d10002c4240e00c00307140801851503030280ca80f9940301460540b6484048c1c11112000258840082d000750700f0221750062030041030010051058008105181c42903a03d007400018400316201182c89117680b10b240540c040040180d140350030f910b6168854407640000900600100104003141c40071544100540c0c8410000d0050000c20800d04107200b10809a56016014201d0010042640d000f51030450080c08614120400303108400e4500e1704214404451504540504494545002607406e4566603d0f00d080d0005440c400c0c040e2003c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 624932643 1250 624931393 624931403
    0x52a0f0706021504020d14070f0b09030d18260d0e06041802040306020706090203010f0203071409270f0a02040302210a060515030709020304031707090b04060f020c0d 73
    0xa03d03102080e0f580d220380e6000f0012644410003103205000128680e9100983d00310100c01441080d0070100f147c0621543c5420040071020140301000071550000390100d401a1240b4201d50100d000c1c00906040d40034681001100e0609150654207410110b01c2c0d032040481d4070300488a01040c25130341510341403000c2c100700740c001c030041005011002d0000006c034003508000c280145425502e0301c6240c201d810800c411508180c940c0e52000c1580380901802c142103500c01411440c606180e040034000700c580156112110b900403803080200d555410000f0710540c9014118a08005003103903802c03400c1800c0f0391b09080e1825060100300d00e014a40700791400d50754084c0200105110034442a000c2004000003070030703140b18542c0c006001403214051980503000d510210340000841200300b6044c915550032030400c2e548148100b101085c1e0190380c011803102074058244594565000845042c07a464003c2c01100380c0c0058000369980d1f01024a0310184029807d5030401070440d0100600061010700c0501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 624933893 1250 624932643 624932653
    0xf0902031209030721080d061d0705040501030b12060703090210020609122a101a181e04050a02040b06070c210f060605040b09040b1501052a0f070602 66
    0x104001c001c008400550340660717051080001581c0d902c8010350b01000c16141140d80711003040040b5507440048031031144825001a015141c04130740100340d40130703510640d410103441313000b11410303a200e607150b50004280040c151780d040e10b05004003801622200b50201c0c0591803610300360008520114081d4001c01c41e00000c1c05c1080b158034061465500008500150003a03140c4543c01a4460014070b2004440c00c2005840d01307480002d038600854203c070707402d01d210014455000b400d681ea156404194182d8048000000340c441c81e02182414400d880802d4840300201c0c00d020600400254441c6050710803502030003841003103024060280102c0d078004007400c5006805000d250100440344001c401c0203007502c6000005a100e00307011091101007603840c0c0366a46428081424180250802c0d14026601030030141419a00c40e42800802488440d803d804816030f070030240e00c5803040390400701c02d90059041011040c014500c000b05c401c1d1081c8a5445031101500804e200401d035602120010b4020b40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 624935143 1250 624933893 624933899
    0x1305030706050a0e011b0915050906070f020d0b0f0c040503060a0507180914070903030f050c01060e010e0a06060f02031206031905150604060f05040c030f0f09020312090307 76
    0x22002e0714002e400000c41940f20329403070504120922410a8181c5003d2111486070141003005e0a1807060390009914084184100750072150048222410140c0070f648442d950000b9040001c508884204000d43c0480255808424040150000d038000c585003000c151194807144014082d5118a100305901508603400041c0002401d90107160300c41c00d2070400074000b0401c80c00744041d801254215003c2c1c540e5400c0581410205042115400521806d050810a0460310090080c10340e2a0f0340c1400c1250003d0490050f0000390000301c002c2c00300f200c110b541940c441110040001041340c075046103c1c548000055000d01ca400341080850841e00510303d40b0a029030309114142c0014100c030707054801c440350401101701080041103101d0160000d07100302d0041b42e078040010072010b01007903c02c3d41848010f210361818803038200d0441c0c07130032100062180a01036050380a8000030004402140c9400c6149011140c01d81017411418400c03015268500e449449110240c007610900c0d60300741d0305c4a8018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 624936393 1250 624935143 624935153
    0x2010e011b050721020d03050f130209040c0b0f190903080906090301091707120f3903020303161b08030711060933070806150403051513050307 63
    0x600b055400b4807140c10200900b0101c4146040e400040f0304e005074070840108000320361612403250444451030461540b420b001c020010140345010019201b240e0190101d0104115100404002c2284100b00f0f501c0e03144c07611274203d007500304400c142071108111940422035841018a0416070b54010a81d80c140540313001404100d401038002543c240d0f580e0f003040400304803680c2003815803a074450302146e5609aa80b400a000b0684a0244828007061814400f01250403031002480e4581c000641620407880310030039051403040301c01850403100445240c40625a01100441c450000f6071071010141442c60012a080900c0e1520725085912080c50100001e50590080d604a5510324146004980700300315203060203000e48136410564803441c220340c0d4042041c00e02c01d04801440300402d628003041ca001c0035400c40020b01b6102080f07500c0b00055040d0f47c0300d56100803100b01314410107848035140d28000b07549540034451501004800400210005203040000c1d640f182d21802960a000c2e880e982c3c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 624937643 1250 624936393 624936397
    0xc0f0709060b09130e0a0b0a15061719090f0308010312210209010c0803010f060e0108130b0720070f0f06231213032d050906070503040605070302010e011b05 69
    0x110140c41d0207440c54450102c7e040d094130f80d0280c0c24400000422416100303010607040b003241c0c003040501c40030381140000d2402e0180c0326540038040e299071100d00030240c4030080087c6400d41009003a58070303042404090603802043c06050304c0c442c5079000313824100450159052424048141441440da001c5100c08550a402400d0041010704103001000e480383e0fa104040d81098008031062010310200308100c1c2da1002d232504545a00382031070007280c1402e05101c0301618240c0703c003401070010b600102e8180d03489070f4011112550408101018243c0480400f501d03103055200c2c1030340e0341c44151004125800d544842d0411101d8079102e20000100c581e01d0fa00d45491140300e82242003d041c41140483e0744401030f81c6201c0c1c04280200182d9202615014000042540d00513032141401005000380e50b015600500b04004582404c945034800440024890700c82c0f00c000a059000100d0300007996500031340a0a4071512a800a1203035a00c0c110425080b00e0315120040c040c0c42c4840303030301004e550003900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 624938893 1250 624937643 624937661
    0xc0305010603330f1706060904020901030605040c0503030a09080f0607020d1805061b010c0914061806040305071502010207200402070c080601090e0307020d0212030c0f0709060b0913 80
    0xc20704540ca59500744d0b1001000031075200c05e220750310f410005a482c030828844561300c0b08003152000c03680d080c15000700e4a031980c1400010a429a21030104080c0302c030000a0304020710380241100d90b03441c0c0c61038000f81400414802d0210344d00c550010344442c1c1c1004584148104541c0c1e00800a0404010080340e07a5408040300c2405910024804201616000c1c0100880816030f107407000116203100c11542158500c49c6041e0421002c50818400140028070900210030b04031046620703032900c42580e010034410101e00c030303502c1900000d00004100001c2040002c407081d0191b0214041c40307850007a4240d101d100402081e402d4030400d1218140341c2032100f40b415200140005080450903900d40b01406c5d13460300720310b007280d12240040104074400c0c020140c40b1a0010051401c0900caa40421030011206400038854841c000c991007102c841002034800d2441140c0859500e0a40c0e030188507100e42c1d40b8003440c55891b0a005020031004542411540b00100207083d10f00107c1c004010b210050010b43c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 624940143 1250 624938893 624938981
    0x9151503040f0308130f05011e1505100905040501031203050705070309091104170f060106020a030c021003110d0203040203060f1314010e0d0315060c020618040f0504060c0305010603 80
    0x200010000c281510031b610540f51050000003022002024128581034100314110700d01424441c0825a8060301074015003141c0c0300340e81001340b401040c00c09072080c4600381c01503a0071524010001041c00960381401c05c0398030081e10100120340f41c042c02260b95105400000e00810b40c003640400000c0002d80c490400041e4180055007410b44455000110030010844403000343c0c410101e039845120280045401040c080c0001c00042c0202c0d03a002e0301423101c00c40d022307104240a18100d443c15001390000c19140180340b168a64481383c2e204210000d42044d50160300a02c150800280b0030402046418041d07100a41c03104a4040540c2e075841144041040401d0155241c00607104814010041201c02c0000c9440c0892050416103895036190150b5201c001040100500100541c54000403148140b8841a102c0c460400074001705018245814030850b2a82c9031404000500c40c05a212560001c1782d0f6405002503640c0c0e0b84102d094850030011448405d01007a0034070243c460300c44d07101080e40302071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 624941393 1250 624940143 624940171
    0xf0302010f0203090105040501060501052703010f020403290c030c031513060e13120f020304030804030f02090a0903140a2007030314120a020f0909151503040f0308 72
    0x1e800a026a081500d040b1050780d16482800304203c03081c040c3e80301820003031a2550910200b441c51f010208542c0d41c0c0d80b00021220076080200e52400e400c9810318801d0120b0a56a440e524909000d4480030740c00864001284100110f200c00b4001182c80e00461091540c14103544801010003550751000e440b00c001c0c903100280946e10382c0c544001100b29040c5542001a085203024601d40c01e0110003400fa1841e02040c00184d00028440c82204100640300d18005940c1c0c0040c2e0800da180d072142d60005464018081070020820910ba900500420301c240c0300f4200b00c2c2c03076040c1e880d000d9a001d420000c000c29552000c0146035030010300504000c40c000d15006185890701d021304514030b04450400c030a185c010540c14400d254000c583e040c2c203201c001d008a894000900080c142c81400035200101181d00040d00004040340d80003542c80401005051122605094a2a085001d01c4812690080d4000c01c80315100301a0b407400d0783e00c0750783c03c6406000170a000343d5045645c01030050042501001d0b03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 624942643 1250 624941393 624941411
    0xf010507020a09060609080c181b0403052b0804022701240908120d111201030201110f0606040b06070b040506041109040f0f060b03160311040c0503040f030201 70
    0x342d20541401440404000a1614140580140500101c0e0003000c403a07440b12100302805c1d2100c145102c000c0b22400240840e07501c94460704001c4003401c40101d248880003040c0030050010106618460850f81d2010020f03e0380c1080310118500d000c4440d050114843e04006405400c084c003040451040e5800c0e403d4101070003c5031160308080a800c580080700409503207550f4407450011202d060703035050400d00000e500d0a0105640e44000e4408800900c0011034003040d5003e246d040f007001d180038041c1107030300c1c0d2402402e041c4110500344400c1e03002610325050210036610110305031402070652009041d0b03c0e62200203000144c0300ca000415000310003000943d000c60088030b0458010361084004d000c50b424641403600803a00a809607920841200040c880012221318225041d942c1c0032268a0060410303040c01802070014410654140c01084010401c0510021000b42a24420b0000781b41c1440800144070442d91300e513034410b0104004001050118101d5581000341510902c00490a640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 624943893 1250 624942643 624942649
    0x14040b0a0e010b030f031e09100311070f1b0510050a030510050d0b04141504030309021801140102010f06052211040e1504110a110c0603040302031903051003020f01050702 75
    0x111001700446240c00108198403045030040008411803181441c440c10a02000001940804003509100070305588409404140045000340e614064001d00c00e00c2c6140114101401000203003100ba000418070300401007400d28080c200d4a6010b203641c1e4a9a04126280d06c086c3c000f0b10740944181040d41e00701d00002100d6480034006c1c038a41d4071915000003e42401e14010b5443c0e01e00b491000c03900d0b00312403a40c86c0b03050044400c13903030b1080d018540428210300a0000c520030341140b02500881401c03000c00403507003104220743c11703847c11001c0e4002c02820004800101c106d40e50380c0603943c1c0c27281809925a4141a000250410801e00316800080e50b40004e40441c0b0b40342e000342d00c01200350f800f60042241e4a4421070f0841083e031130654080c44141415a8040d0213803081030706000520950f8079800d44c0080c800c0001c1941c100000e41229642d04281c01c01030768940141c0641ca0b4944044c00044407080d10034002c05000f4488440c2e0b06110605541c20041441401c0d00010304005081c8050300140c0d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 624945143 1250 624943893 624943903
    0x1502070f060906021b060702040b01050903010c020106180b0306010b030702030f03240103020306090403110304080a05010504050123010501030f020d0920030a020d11040618020d14040b0a0e010b03 86
    0x44041d84840c060107140c4000030382040d4032042000101404800080b000c1d407516011524410340c109ea0006801041000582d40c03402043d800940543c03070041078900541c0c056200a065a00401502c1c603042520b110100031303111051521134040d081400100324982018010f141c100c0440d0054070f081082c0350002e032074160012034440e10000340d071000e0407410301d21801d0f49106c000d01c01c0c0313000d42ca107280250208401d2940500001d041184a03000303521603010504c19540071700303e100140ca0082c0000d0400c0c5020b403805540070b42d400c0d480d0a0200b015000301e000322101c100c218880c50b18640e860080194001d00c08510300503506902081902e58960441c42141d1100780714414a022100c0d141c240d5481200d040e50b09a40207a00c62203000001da80c03010004090141c4c8103040d4896410118081005031030181d0020300f01e229400c890181d0314040340c0240200b06040c44080054940d40740341c14025402c10765014202003940004617106610540006a1000751200040f48501294021910304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 624946393 1250 624945143 624945149
    0x9050a06050720061e0702060609060a0f08010203100b04061d03100e0a0b0c16060b06070c17010c08012601090b010f060306090b0105192c010e191502070f 68
    0x30b1307084581040303210b0007a00c0034004001043d0020008034607096801071b54031040907183d184107281000c001050ba035103140c41031001d0402c0c801007d40d80c2b503492803010301039001584c1180701780d40c0481c07001c1580b034142815241101d0060350707840c04150421a0170074030620701d9000c0c2a0140181407903507480045501448405000c0d01d4000c12140b03040e404c0070500b0200203403495024920810030f56001144030038583d44d03000e8000c00009841030080000403894800d41d280144006142b90b00028024500008034081ea2070141c024030201e031083c1c0084815200034040c0c9038141d486144403003a84056106043c0b601500040009018115074480701c2400c031099110020b03411400005100d810b500d4000c1c0c400070b240814040c40321411001c0080d1017801050070034a00550100211800c584c441c0d00e02a651b19083d03400d101c0b043c03450200300100c0c21568165540414680e0000080600381a40da4602071b6140184001d65907085c583c0d415850485260b2401c1103101d00304002c56002d000c96959402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 624947643 1250 624946393 624946457
    0xf0a120f2c040b010c0b07051c06080d021504020d0b0c09030a110a06080405030d0905160305030a030c0507030c060e0a1506030215040e16050c030c0703021309050a060507 75
    0x701c03100420001910903501c20541040701442d940d0002071502038580e6044141d5003001c1c0d44495110000c650861990810101d569080607400030f0312440100700d14000304540d500b0784481924400102e00c02d02003d440081d0000c01c0d24001d00085500c04402030b030003c000a141a2810100c280080e240c2244110143c0b1242150304035a10769203003e610301e100524890074881e800345031940750340e03440c0e002c1d6170b1040c40c1310b40d02d9460074402c10406104035403840c0c0b0034143c46e050158880c10304075900d402682c01c0e800841c2c5024030240196005034113654850780d150395090781c10a06599400081d01d0f41405800326403140e00c03020000181341c2c1c0c1c074215483c241d0502c005506451401040001040074102c203400c0e980802081c0110780e030101040383d10149049450082e4054038404071a10f00c9030034041007050002103040c04021130b010030380b1800c40340219000b0803041090700c419802c443d0401c80050003075105440a10000314035030070865100d4498181403007400c40500c1e4004002c00d0290314088 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 624948893 1250 624947643 624947717
    0xa05060604050d1121100c030b1f1701180902030c030d0315050f061602031513050709020309070905130b10170d0e0d02031218030f0a120f 61
    0x1a02d41030042c4600c0c1700c0e6004082d4485070f02c10000e070301621006110314031082951501d6003428490300a403c180001c02016003d001501101424084c0d0040a1000340000600d04107a0141440014140505a4440383d80603141420128400d200a10300020221b0705401461a800219a402c1c060355841c2450381d200810b529684240360034441085400c018859081501080c00ca41c0303442055855201c82d0920001000301b280c00040c0c0350004032906007150070320610402500780741040140708410300c81c0c01110308081c1c03030b44262400c3c3d01040350510560340c00a0410450200c2c55000a5004004801101c1100c0200c0e254521007440803110001d0705c20422400b00b100d140145007138840e0220780d4002d041c81c0c44403007a00a1484c148241134030301c40c90710020b54005540d01409003045c055496100d6542d5821540321055824100b46801d611030701031840038105944010500c0e00a40d40c1c0858282001d0150740000c2d945503000314140700400401144480c40e4110416901d802d00c01701c801522 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 624950143 1250 624948893 624948923
    0x11030a0605030f07030c0620010501031103191101050d0b15120903070308010b030402031e1b1801030b18010c183f0602131d010602060a05060604050d 66
    0x351411407802c0052403590300c130318000c00109820740380c00c406907016407070490f49042c141480d0700d0f021400c59100345040e510f008000810019960561a47c4e1030f8140c5c01d803450f50141004038444e00b42001d1002d4034003010024200c0582d8480d40003000d40b40c0d2414000a07a040201c0d01003080350b050b014084d10241000140c01c2e040d00423040d0207503444000000250700c0c00c486942c008011001c10f205207000080003001103003c550782840102e010200e079074040204d0040422200b544c0311202d001d010103c00052841d84100d044c1200790440302581d0007505001c80e46180e0340d0170300f14100100414100040489842c850b00400c0c01458240311300e42c0d480020410403110100c41d086c21b158419411070341c442459802c0c0a4000d82d03070500c51629510034600007122158a160402c10514008118500c00180001c40d4101c0308031a00a0740c0c40c0da005068618003502d20301440b20f20a024003005644100b0004100c00c545402c51940800050826810182c0d19004071b08031000c074202c1210407104220f00c1d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 624951393 1250 624950143 624950149
    0x209030a051c1106090a03051b010f150501022404061404050102030103060b0a150309061508011401060c1a07020c04050f070e01031e02070828030e01020414010f0311030a0605 77
    0x90400303603030010090600b601780003080e20341e22161200c000742400710100784041d003603c1301410200b82c01b2071034000b48000c201701c0b181c210080c03174030078030a100400400d8000301e1654400200c3c07407103d21341c180090201c015454095a030422004100311504da48400044401c80f25200d4528040d904c00c000258a950540c030709401a256050f0803540289108502006014000004aa04502141000150004641411400391203215071000039903e8030007000620550540c8200900180f05940101598803070008583e2a03001c100041c02c41104100c1184821841b40c4000d0f4001304a0b0048421140b00ca001080542d081101d0b07141020920b50b040202c0a50441d08150f141d14092078100400000d9400040c1c003d4140f540c40100580c0c0460340608000d54a01150341100440c81d002800100c007400e6140e105080c00d01e0030000a06000004000c400e050007590184c170200c001c800f2100c400c1c0d000440c0d610310000d16510400d61240c4444903c0410f410066015241c1082c02151550810041c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 624952643 1250 624951393 624951407
    0xa0e1803210901050c160302160b120a020f0405120708010f09060e0a080414010306030f0503040f120203030715020d0504140c06120a05072109200d02040209030a051c 73
    0xb07a1a616414841040364812142e4102c51900d1015980700450f8065030904034608001c812420180a40e10748011485003c8003000d072900c0d1001d80c110070304555586201200782d0240710300a400802c0180410f00940c5040141840b0300040b5004940c91295074100090a40d030046e200e0040e01c0350303900c0d0340d48103101580c003910040d00c1c2c014008000e0281c15650753f01c0180700340d00c5140240c920b41e40020803145c2c480d401400055070004101900b205079800c00365101e0f84980b140140351840e100c00081c96104003006c0c0d102e1950028051410641c4c16201d03107202d802c50701022103d0f00e81c01c02c00904c52100300d111300d40c01a8014180d100050400680741841d0021000200b480751406002c1035890724a10603c00d80c1c003910185000c29151100d460030b459143d0460301d001101d0303119800541254441f580003648460240c2c451804940720000030440c01503941e243c0f45d4001051580c608098180f58004008007000902100c040d00c40701c2d16000c1c100214800804d840c58821644420b44c2ca40c0084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 624953893 1250 624952643 624952651
    0xe06040c030e0604150e0304080609071703090103020702060f0304050708070605090d29040302030a02060c0a0e010f1101092a08060f060a1a0a090b090a0e180321 71
    0x101001074202c500011595118000c10081c400034011480d485950410740115042074069401c481d01d8030307129244c9a8494034110b40074000e9200b20301002030103401410311624000c45502c05980b400c100c40c0d004401a51050005a8216104100080950030a8001184103a001e50041e155050500007400d0800c50326500500410005100c00c0b80240e07900300051004551200c0c2d902d041e40504030081121300c02141c141c510b04248441000b00303140d0040000d0140c20490307801d840855840c00315240043c00307080ca0610001d088021245065402040d0b490040c3d455802d0400304407841c0b13880d8074203603440c0190480d04001c0c68906002812520814036141010a40441000c68103018049030f8849005184400c403e240001140c0e858a03a0402072010702866400054403540c0c85182c0c40007640b1802c02d80000440107500000c1d01d00c0f060007659590140240303103d140c68904514064460806001e11000840844e0345d510b502008100421074800120181141c120708482c069405004c010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 624955143 1250 624953893 624953897
    0x41a09010f0c030c1209020d050a0c030b10060f1805130204030302061e0408160c06270b0306040b030718140c0301030c2601050108211903240e06040c 66
    0x4c80444a040c0c011901d45002c070358220001170464101d000040f022000844068081d001c0d0881103002e01c04002800c105507406000144500d07102c10140544480113441480001441c1c0c02d0010141c9201e203901c13004065403011031140160311100069000c8a0f940030090103968001010400c164050000542c0f08021a00480035034100421801c0210340080008102400001c0c00c449a243c504903840308040d0007209000201c0c2d01c5031070181c02c0521091200e40036040e00b0002c030050342c201c800458203a908201015080d03898400a0001415012035403603890f014194010650f28080700360070004140503400030980014605003c0c210001c00f4040b0710300d8a0f410401480850910b410079070488081200d102000140c00c00040204402c0c0c201100d01542460000101d10b0800100d10380201c01c2540780b000c1082d403001d8228110700c10000002c61485403045188030090280c0d004000040c0a1082d4904604201074035400702a1550020001c2428040030f00084c0c0c1031600c00c62001100d58 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 624956393 1250 624955143 624955151
    0x3002010c030b1203160302120403050a03111c0311091f0f09030804031502040b0309060403030c09030b0105090c1903050a06210b091018050c0406120605041a09010f0c03 74
    0x12403070f407a01d9114211400780c42802012040c0d0415100300401d0544051081c02c00b519561a4900300b42c0b600d008041c02e40c00a0904c011000d00f1010208400c1e15070340d80c0f007103d0780d019440300c0c80603001b501c40400b41c8910f02c2d40900c5000d03001c1c0c4070340d4204002120010f00340f004401d42e10301c0107044100508d01c01000c100e08410184001080f52080f80d040d250001400c10840000c00004070182c41140c02c100f107007c4021040c09000710300064054002ca109440603c48102e4022084412040e80e11015100842141c0104120f02b82440c84940180d000e52a031842e003101380141c0c821400b05500907200007540c403010003c001a00d80304500c060300b01d9803250600c403170b1074000c025a40007600780050720013414100800e03282c0c42c00300040c0f03100c19030440041c00300025811303000b0700f800d141ea003007500e45020703101545079145007034450301040c0c2d80d15011580700d07244a600c0d80d00051070010012141b000034842417001402c0358a940e24450a00500041940c5000d03c0c0c2450a4a44955080b0709250030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 624957643 1250 624956393 624956419
    0xd110306090c0306030102070f050c150c070311030114130308070c080a0302160524100b03010e0405030d060314162301090e13022b3002010c030b 64
    0xc0c0800e05030800b1407010079070340303a0b21a40c00003070080c070500c0c2004103003a1042d00b40904015011030589042d80781241d10340402154001c0a25a6204007101030106810a82c802d20003c0d030182c507001c00c002406000050840302c1603c0c0b0071848541911114000b0100320005010144d0104007550700c20601e1800c483c5400b0142d95413251802032035500c0c2c00781034010910303082030f01e10b90700c05001c41504041142d0042c010000706207907000c10b045511401d8080d00c00064091407650404400b00d40414841c1c502e540e107002082d00d082500504115041d0100b00080c43c0d00110600078031010f14012035002e0f03200f40950900da07140c158042c0d9a4007124031620000c001d001d911008000d80000501d442d400c03001080d6004889044454200c0d05c03040e505d94050000000e0480180d5106501c281d5402911441c0441200540140c0020340c3c0c5d0450600c4020000241d80244101c0c28031701c00c1648003140c0c80c01070300c646074074406101c000e40c010b030342d50b102c140801e0340e150184150000703043d100403401a903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 624958893 1250 624957643 624957649
    0x12020c010f033201060f020307020a0306020702010918051e060f06030702030409020d09020f010504150c150f0504021c020a03080a0905030d02011b03062d08120d110306 74
    0x890181c4100707050b5a002d4010310407507040500400841078841118545665180400e44200c1c00e000d00c200041718520840e1491340000101c0d03d406400512207101645545c2d9120040d41c4403e40403810007481090006010790100f440c00c20440b003210f80454286451802c403540484505540c028503441c11007404015201c00040f0110860144c480599a9450350402d0f8550f200e940e1103803604500c0000d080b9000f02c12a440500d030700d842155204100070500c0011a11405640034000c2894502c404c1007456a00418501e80500d219015040c01900100c1d107080880b04c80d55400c1c441c0f141c685042004529010242c2050440102040c0345404020780204011001c075010041c502400060a000011302070100305008100050031034031510f0308500024041c10000c0b0004003036004c8422120f0816010b0300600007030720400c40d01c8509404c86c02100b582c10300a000514100c42c01c00400c04200d4441c02e100302c1c00401300454107030b0b41c0c8080400500307045075051048204400350900038016a99 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 624960143 1250 624958893 624958907
    0x606090d02040b0a0f0807092304060603170909180d0c02040e07030f0b0705180f0a1e0807080d08270303100602010c080103080901030e1f0912020c01 66
    0x180240c0e4000e810241600c081002000924541d55215011080000300390410340f44220a564507101519803032a52014003000b50b6030358000c00380c000e9041d50000c540310303209400b10035806400b03003101051055907038480d185007042c68080c50f000101c00068618042c01c050425541000d07030340350000c060403100c42d0303050b4407000c4285e20721081014015400e810f43d91590400d9001804120a40c0c00131a5286403914100c0d40001080740d443d0aa0f4000801090159080c0c408a082d04520250342a0b01c84040100303000610080b1548080861400b18000705840c0244061641315500e600481e401c0c602c0480c03410314258020032092b07120022910a45034000c00580c1c104008500390109801c02004041600000b807048031b8182c4404030030403a0301c2000d05445022a03403550000c1110301c8030000304031211034003400b020741008820003c40741c45510a80c481d0100100039410780da0a030041021100202c0c4071080020f140743c0d11100780c8030500005840e5941d42c948280008e0201c400c042d80081e00d50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 624961393 1250 624960143 624960157
    0x9051908030f210c2214060304020d060e0304060201180c05041d010e1509150408030903040e1003020907180311060d151a0f040b0903240f06090606 65
    0x1140c00841c003100000142805424a040f009403407010750f00c1c0c0880c03882840d800403a034040c48410b07000302010a10f014481120142c45c0303001105003a2185440c20b00c0081c0c1d00262080340c109a03151400da020400520032400b0240042d000303141c0e40d6140c000000c0c00d4031101c40c500d090132501c007500c40380002c0b25098072400f1034606490100d003030320000708403501501c1ca0000c400e1640d403d20745001e07181400851048100e44007654081d03201d85492051568485110001311090414070001c100442d04000156a20010b1030044904e4562152104000c1a4040d9811007021080080a000710b181101c10030354800b0003850060b004ca0046404085419440c1c030000d056228281a0200107480e50400c655900010220610649080c902c01801011080c81406d181e0f00d1102c1041c40c01076601002c95816544000c44a030801d13042071303208411a070200c850700780d05200342d40c80d00000c8041c0b1850800c0000e18003803031b2095481c05000040700844010206842502d100c800c2120503582d0b041501c50ba = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 624962643 1250 624961393 624961417
    0xc0a0f18060b04060f031a0d0f0206130e0604060803030f071404050a061d040b0d060506031603030c210c120c0204020d0e0111030c031f03120905190803 67
    0x4039100020190061040340c000109084000901140e0700e9003122140c1c52120680d41c040020242040c0441e041e0084d20004035400800442400c02140b1811091041039000a2000703117000041c1441e074640e682c4030b42c802c01c1c06044210800c01c6a1a041c803600008102020180d03146241884c0f411440a00042050b801c0c408180440c03415002100c0aa0300030700700c00b030841814117071142c5001d043d08001c2c03500d06c0c810151881c401079082c00c060103074402984019103054548200f41d903465000d482c00400301e036010300c205081880348941140c0594019400703611114a00c54840c1068205040001105264174683c921100020340d841802d0061094000060342100550440100c441d4160f08401960050010034406034050003a44540101440320008001140002c800201c590200b140c83d041d45100c140009074100da0900c7c03c416448003aa4119080300e038484d5601c00c100300a645500c40041c1c01414280b29a082051610f00d02002d61201900c11920304018542e8901ca1011402a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 624963893 1250 624962643 624962669
    0x120a0f0308070327060b0103090302060109090809130902010908070b09041e0c0f0e09040206122a0703082203140706060902181f0c030c080703030902030c0a0f 70
    0xc0b00610940c46203d003101000403a01800b050180301c4001d900c00d1110690b03e8034600440880e40d580a48900c0c503203540c1c0b6070040c0806a2034020914000e01038140f0503250910100022410369031148203246424042903400254030010380001040c0c101ca6400082d0290300070481800070f0101e80e01a514081c2e42254007041d082e440000d210342c200088031400442d24204034001da410303600420921200c4100f940c500c0e070150120020844d0082e401e0f01d010350021420051a2100807080c0301700b9a0100251014042c078451614400c2580d05840068420200010803010101940910f0040d0441c4012032403010718090172900c1007401045400090510201001d409040c48610096941c0190000e00c1005103a6071a131005019601c021888003001d40d0350540010b55113050346001d1000e90040e548282ea81c013049506031000602030800742c09001015161318001603203c0001c1c902d1030b110342d074003040001652051500e00321101900c58820b0b40c18a006101d080305800d4030b00100c0f42500d11440c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 624965143 1250 624963893 624963901
    0x15150f06050d0525080708090111030c09010c0f0b0906161b0203010b0d0b0406051006050406081906081506101b0c170609060c09010c06020a0e0907030b120a0f0308 72
    0x4000200004c40700040241001040c00c2441e001070805210701501d484413206643c3c0c0801c0c0d14200c4d00c5807100c602006006101040c07460380068017400f43d40c9810306042800b0000394694003030000c51034008880714140e03141000b800c80000d00c24140c11403035440c1c1200903180c1280f8050b01c08840000345650070010b0b540030805540d0250000b000145002d400f66905001604000d20074040031142035640c142040041100601c0e8000314108482c03840d69401d0905013000f20031601c940700030300b1000e004802d064030008a450300c1d210b03000081040c0b10080c40301000b00c085410f02d0b0f50005160610680c003807407025140a8015001415554402d4050608142c0d07a14040ea010180c0341c0101c4400900000624a800c90015416000b0082d52086802d1681d5036a0103804030303c1240c2c41d43e40025070340d10010002402c01d0700644030b88412400d00c1c8102000300c00104031401c00450300480001d480c7d92000c41c203800d00015030210400c82102502c04013100c3c1d2208019010501401010040c81800207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 624966393 1250 624965143 624965161
    0x10b010e010f030917030c0702010207081b060f1c0209030c09010f140105040305060411180402030d141903061a0c0c060c190b060f0102030307022815150f06050d05 72
    0x8081e200500001172902e80c104813441c0070558104100890151045d41d0380403030106400184c1e280410040035140d580000745006010480d0400c0c40320040d800000e01601c00200c01903101e40314070f0a00180016211048802010326040000d60140c1c092820a001407140ca4942110307102551880d0420315040010100100c4580c8140e510183c80d0b400f91100340400c010008103c5001c680017290b4800032100f00744004000428265002549a4001041c0c4204280561145440040a030006500749042c00740313001d090002c41c0c141140040d40d01c15091103844210b03140080c5d0340440312201800d148001801607520500c4500c014410382c1c0118103241402402c1050380402124000038075501142440d0100220a082d00c2d094802c407824130014841e0b520020a036882005a82e00410811035000c0307030002e4042085000180c0510344100b214049410b0310740ca00301003402000c00150f10350200328101006030998012814020b1410401c1100940c0070702511460100c01200090685903131101c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 624967643 1250 624966393 624966413
    0x40b160f08070e0109050d0821010e1501030603080a230901020327060d0204082b0809190503130518070503070e151c0213060c080408030318010b010e010f0309 70
    0x5607442400a900941000036030400741c0b20b0500b0096290520307001c4009e42c92001ca10034090240c2c021441d6000402c1e881c1d81d03452192151806040004059840f51a03a40035544041402400b0802001d242c003680b400890400c0d0001546030302c000d08010105000035180d20a140390540c003078948000107072244203440b86020303102000804040da2115210400380103500309109500c03090084403c40800581c0e1a045129503200c1c0e841d00c1040d00e4418601900c202130040c000d80002d00c00c0c0f00c00030a02c140e90101000d0364a008200a5440390000082c0c0c3c0003002c120b412003030160003006075000b040d40e1006482c41d000070f001d080c196107954032110111881c201611541d035201800100308601024400003c061311400002c402441821825406080e071240785c00c0f491081c0c10b5003400f086060300c0741c1400c4000600c100280c0b440c0503500c0c84010b01c2c0d6001561484004140600780b180c000809121b1090071a2080c00d0403414001c40c135001038101034a200e0004d0a16860750a9281040440c00d2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 624968893 1250 624967643 624967649
    0x20601051207260d090f05060702010c020d11030d0905030c0d0b070815040f020703031a1005070602091002151f060e011b052d0703020621040b160f08070e0109 70
    0x200300c07000d03940c2071340e0001d0100c52144100707034400a1502011410b0b00f0b001044034641038042c2c580440c415090303401d02c607600e46c44003c00d4035503550040c40200c03169003d110b254a208020368860303c02c10305200801d030619041001e5030344500b00a1444070b000541070303086164040310034248441c8a640d100340c0c140400c1b01c0c1d15a10356000d8504007200454071000d50241c4801030107950104844165444000e441c846030400f482c1d402640895a000070310301c40c2d00184003182c071621000d4100040c2101044201500001d04000f40e001070548400300580c100b507556220003030904040c0c40c4c1440a140341990032310b500941c820080500090601039000795080218400030065051001e481418920303151242055040e941e200c00018400c180d2880c400040c000d42a5500900011803450f802c100d42640040c0c05801203017101030308040f29940055100e445580544078000c0149428039042c000d041ea0a80b0a406001203400c1c11039081e03034014841d652107403903400c0c04c0f0800c0c441c000068825a000785c2c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 624970143 1250 624968893 624968969
    0x70e031203101701090c090b01090b0309010e01051e04063c0c0212041e08060112150507020606010e010306150c0c0509131106040b0307050307020601051207 69
    0x10074810004a000404030407900103402596400162441803401d1707030301c031082c0603040300f4441d401030128005a9006060110050400d80a115518080549580c1040f1a0102540d54402441010382c800b030058076807040d0f10745d840500006010105800c4440050030241030595a1403c9030791f114140318110300648c030b0828010b003040c800c84000c440412280c211416030b050400149040080c00014108190aa4041d06505013400d100046410301a00200d0140c1001e0f40c190000c3c0c1401c4c20b1128501030403a160000c02070100c0750800300e42419900301c0b100c0029152800b0412100c0d800708850b41c000c4000d2900d401420865801203000e049903400c1304814403041c1001d104826040000e003e4414480c80302070800c60b135110708110612408491940398545514401c1c800a00180e45081800000400d100d00f85034a51040b00040d4100312510400b01d017000051040c5690100042e50041200700c410034031150b1860005030308e0300c245208803907202c1c3e4081c0e03890702000750f1691001001c105034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 624971393 1250 624970143 624970147
    0x102090607060e0706090b120c07020a03082104020f0f010c06050108280809190807090518070f06050c01091b0315060501140703021f1506020304030506070e0312 71
    0x5400c085000304422100343e02c0c0e6208030000020814000d40c0c03500221858561070f00d0409214640b4100c03d14001000c07100e0050b4200b000000613031300c2098100245015100c496252130141c0740d0043c8030140550310043c0807212408010060f91130060740e00c0c841c00152140300000c00d07000010f845c40f2495010040000e8100f2002003003c03040000c01e8a10080c048261100e0041185080c05840e0000340010f000c00c8010402c0080394105600c00d1401c01e080d213101c280c44580e451500d28201601034107c144060f440e20180000081260100b0035094005000380074254500100c0c0d1141100912420080c41008036098009640a5200204880d0080404a654440113000f01030343d07051400708039000184001d034501c1c00062803040c8070a0326010384a0800c0c030040c03c2000c4c2010740020300304608511401d1005650f120b034407416441c0d00c24040310082070ba5001c00781c100d612841e80760031074000c550042c042000402c1c80000c60a80002c100d060001c410502c28002c40e003000402c03840c1c1100c0d9580 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 624972643 1250 624971393 624971407
    0xd11030d0f0b15091e01200c040f02091e01030f090b07200706052a0706021209060301030206030a09080c0a06060603091122060303020318030d050d090501020906 71
    0x10710781120703510440403607203001e015801c0340c0606007a004113034005403c2000c0288029070350314000c5003810301a105040010581c0031900c000e1a11300c209050300d613029008501020328a017018002c0c0c0b1280c2e18201e20550900e8072000216200224007414442440044143d041c0984d000354820880e2803010706080c0080c00e105e00300640c070543e0a132400c1c1c0014420a5080003004407404483d207070b2142501c09462550b141880c11201e135048100200503071020700d01c0780c1090940740980d14010250f6400508619480c040000c2e050540b01410401c42810800c00170700a9903442c000c4906490303048418075229119403060308010400c1707010050604c84000340b50607100e08001014407245100b0041401034076100e582c210151400d02d0001088000e20324105c0c11149012144c0e4880a4900280d12481d030003ca20211300303440135540140c003d6000007602c0d510300040400c12a50580065004203d5500003402c01001171003200814141c4566075141442004000e40444185030305c0240340d03d850b898 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 624973893 1250 624972643 624972671
    0x1821160b1506030103080301030602071b0e090606011809050919150f021327110a1409060703140f071a07031e09030201150e0106200d11030d 62
    0x261901c0d01541911034800c000c0d460600b007100d041c1c0307600508160460b442c41d80d92002075000104100c47d01c0300a408003525402d20007614000414040c09021101d062180d4401d003408009401e850410441c10b4601d070441412880183c200c485c4403000294070354540850a00b440c014250702d0400b51042e01c07801040c0310103040021402d8041510802141941d005940128410074110316803502c2034a01c100070f00488071032454000d00703158120310341300031001403040c040342c4088505007000d900108980c02c801da8031030701c00f010324041048483d00d42104140024564007500344010200a44429200180040e45041c0d48118640e00081c43d164025403408420030386060b030880031200152000140f4451183c044c981c40d00c200441900c00003200c80d0110400340c002800d05505641d05d840c0c0c035400e0126402256002001071058481440d4101400141140010301c01c0d9125100100801c005a6001041340100c003d06802c2948407401601c0c02c540c00c50141a00c0f00102c503182c00031695100d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 624975143 1250 624973893 624973913
    0x702070501021b01080a0506040b030111271c050304080f21120118090c080d0201060e0906060907120c031d072105010b030d05090405182116 62
    0x24009800f0380e19070f02e01c42c42d0b00010048560003520b000071420404100000402c1d40945e812042c060408911403082d10042402d540c4d1040540c400d841c0009452821f58585542c9525580540c9a860704c403c0c1c02e000c00110581c160440c03041880100910712400c0002c00c1085500a0a640d4152020081c44240480d12041c030002402d0043d08402050092400481308440001c540e840700e0b180187d00303110040c203d07030854211000b402540c0300400c0000c22503c060b030740e005241c0440100300d03954444c1d03002800e58150380d002c103101540a90911682c40b0001c11415407218040c0c9240c0c0c01c681e241501290b0810850b180301c45035a15001003840c50300e5044c0c126211030042c101072034442c6046001096a90021032207401005180744000c003400d1118a000c00f070079140188008542440071100003410440c14004000c00f00d68006003070090390400d03001d280e074007283c10340c49603504290125a81c1e440d0801110030400c40300e5120800da5004140e0300654040102d21002c05000d0509490300841c41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 624976393 1250 624975143 624975149
    0x20a050d09060e12190c0f0308131706040303050c130602100e030306060403030e0303090303040b070606060507080d0902182404050402061c0906050c030609061f180e070207 76
    0x1103042510480604190400c03199460550000f4101005170b01e00300c000706030000b8000c483e1686110000545903000c0b540c200f0141d40200c0300940c1d110324182403002c11100d658850b400e26001841280341241000c03030b615504c6900f41c203012071a9625002643c90381d00c241c40d1091503043c0004030100d0781660000380c2028060744240200170484600c50f0040d903e0101300ca079168401010802400020304c90112590b50a1020301140e0525441d0f200007406c640003600550130a0070042809400d008041c01060f000b131906044c100c2c50400c0984401060384504010100c1e5561141060001c548511200c0b4120800c1000b10100741c0c2001d40c943c0c01c0b111925100002920152044901907103054802e45014660003000203207800000e034403050300050402ca8032038007190f0b1a95600b002c00e000340181c1d88540740400c0c81d55035a1070810100099074401500300d17800b445684040d00081074003112006012035130f50800001c40041131225110209054218105411840040c4601f00741c00050060607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 624977643 1250 624976393 624976397
    0x11e030602040b03040b131e080c151e10061b06050c0a020c15030109050c040b0f120c120606091210060504110c0a03030209042403031409150a020a050d0906 69
    0x951100d8504d40c9840c0007c03100980044100941a001d480503200426080752141c0342180c10014080d90300742c00c082c4090a460341d40d403105800c121824165120b00c0c0040411181d982c5940e090001070500014840e010b402c00b0711050300c8400c1c034486004400e04c00c00d1540f224061210349403108105071150098087c10002d4070826030400901d00e0b003032560440300002482d50328103680c81c011160015000103003070302c40c0420081102049aa02c1080241101900148200d80e2030014402c2c006500b18003d02180e0800c038103102850b0402d924a5102d07800503822980710b038881040344001401c19030000b8451940d44560000c01b020000580c0020040b10400c82d001c024621101e9662103003445006c0310031000d90403c00040000038020742c06844034110207480025103090744248450400010940d40c00b0000c071580c2d0400030154025007842c010111460040d0409802c103010860300d643c00d00d050403d030180450b0103002e0cd1b00c02c00c0360200d81601b0200322402d90701c00c4040a0142000ba01810300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 624978893 1250 624977643 624977663
    0x702061602091b0304060f0e0601030f0b0708060616031110141510050a0201150b1201061d09090a0b340c120e220b03010e0303011e030602040b0304 65
    0x590403c1c00400030000720a402d070312526643e01e960b40c00c0000d00035100030940329607070381c910207800c5501003007000d0180d449140e01d001445807904104120181c018030290802024404008050b2581c03c01d542809001308059103aa26003441c1c103688c1d030300740580e20200d01c2c0309100380c0c400c40c645a41c0101035004881002411580c5503490f842006031030640c812a0080700c4030007502d601a00c144014400480705200010300500304100c0c17100500141d5104c42503000000c690300c4440810114624014541c7d030a0904034203484004280d02060910b054620071459480041c2248600303009284049501507881d54542c60941c0d4402031510701000f00390f507410655210481004080042c0c0703e000d03806611401e001392802c0d610342c0d0035803d09105000400041c0ba4083e5056240c00c0c0c89980041110420402400e034000111001c8a5141c0c1c101d51090307042c4050441c00210200480f8155000f850500c00041c17001c2c2d012107810300b81a0b20060030a84009800105121060042c5025078402e400c454 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 624980143 1250 624978893 624978901
    0x9270f0f01092a03020d0609150e1501080c0105070305040902030109290108060f012d030b0f13020a0207080706031a09090c09130506011410080c1e070206160209 71
    0x11184580724241e2086007010340c442440540750100304506d105116900120ba400c4081c0c1da80320810744c020308043c400d96203c8800700b039502d030300340400c504001ea45d2040010540c07400194590700c2d40340102440c14040001042403e1510403400c54010b81042c00c8255940c1d6940d241d841e0080c49200346500450f1b41c050b05040480d20a403141c445414816501c45003251500001c020300e508003905401d041c000350005a00341204030560726219520810740c00034910400f05405010703511942c1480e84114040340340d210703681d60fa540c24145c02da4a00e500c01078440040300010303031900d070f110703040300c6124410850000394923903258004410310100f490600c002100004207120b00080187c030b0141403a000040500b84034140482803030f0784100700464000001059444840c20440d080c1c04c590954040d5041d40001070400d000349551803113162a2210340c501e03242420413594044c507224800c1c10801c0d00e182460f00c18003142075941d2160001c140740d41c0c9420510346919200c0d4007407403c034010403a0390005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 624981393 1250 624980143 624980183
    0xf02070f110130021c05100f06091802090102070803030c1c02041206090305090604081b030c090f0402031005150102060a0b060f070f2102010b09270f0f0109 69
    0x11510492448600307140340c1c3c0403980441c040d40160654809203e080307194200c4070600d42c0203050003085003a00408032182008041c1819014981100e0240b02c0c41d0b1000304000340001d41014104800c40d000141c41e019400b0040b410159280d1000c03005100100512004100c01001800d8506d01c1401c00072942c1e01140805003a40243e2055000d096440c40c0107002040c1260015075905200349420b904c6e1007500d20010341b09404c03580050800c0d1f4040048441ca107000801c98043c1c01e0421802800c1d040d5a440014040900081c42142120420f01c0408d045403802c0014412498034040140800d00d8602004000e1078450082d0b18010300c920b0004c1078020351180310b008007110002d0704052900140c0c007007180e4140e00c0440b040340e00092041030a00410250201d9004c02070314006c4810701d40401c404000c0c290303900740700200d214203450014029040100d01a003004a501c000e5890300001458054a05180048100c1021400b90351074003031041c0410751041c041541300380c2c4142c0f8540b280002c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 624982643 1250 624981393 624981437
    0xf05070303050d05090a0c050405040c051c03080105240c0a0f0b060f0d030906050a12020d02070515010503030a140702030d030e0d09030803150d120c0c05030a050a060f02070f1101 79
    0x4050701410003a42c7c01d00c01c0d030030030760000b0707030701c540034105145460f0f40d240c0100d4408441c00d2071100003a42c031400b40c0010035600036850f030b0040004035a00c0500e2801324155035152070b4a040580e48800000038000340c40c560520607042080d40040071075142d40010308201c0c0c5a01d40440700544626034070401d200c0103107007400c20b240c90349070166030741070002c0d0602e0030503500c0b6440080c00b4400d0101d030109145103400e6500090408003a145009a101c15452505614015051102e00e032496420f60041c44140c80010607682c10704114544418109540910508e0724480c516001e9054017405200c0034209415400512144c0c5d160030072140c10250001044800c1c450a01005001003002c201140000d9000f00c0d02008800004021b44120402a6212014085018540700204036030450000c01d004540e08800001d11068000d0000004241e9032603864010310a4014210360341c400c142c451340c1d216603059500d201c0e44848005004601405c10610200003075007410f00203100e0203090114015200b603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 624983893 1250 624982643 624982663
    0xf0a0c05010504062316120902030304090603030905031b100e0d0b190207020d11010905120c090c070213050a151d0901020a20030f0a0518060c0c0105070f05070303050d0509 76
    0x403d03640c81001c6d81100312881104054860303202510f50b2801c0c40543d5040c40107000130640c0e4400000d9107865890302030301e80d0006620140c880d03040755203400110303034805102000b0004126100101451b144078142c46c8813410700c554a8010031680e55003800c00000e0764085019184220005003070f94a01c0064005900ca6044020342002a0429a00010f15102041c82142c0c0c014104140d00350388500120343c0052010011702100c3d40400e55001c84d5060904002d90480703442481d00f03140550540114075540719804040a616540f20001011002d10703510a41900407042c0d0a1501103507901c000040301c3c800e080c413540001e80c0203004503803c80300501c04c440044699440384106181c070542008002a960403a0143d2400304028450310019850020680c00505440b00c2e5200c86c440c008602500b0800703046540580f0301003050660780d80c4005000c26952409107440c071ba50700d0b01407621910713446c24010001c00c21303c1215404001c240d0070002505c1100e9416038104119515114181d03035880c0c046e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 624985143 1250 624983893 624983911
    0x10f180605150d380709050a032f221104081207051203040f0312050f0c070206120109060611030324041d060108010c140f0a0c050105040623 62
    0x51a01e00008051510005400144e0450701549082c1c3d100c0003010003000034031004001460703504000c203180e0440c040502409050300c0c1d4602c014199036618500c8035594034803ca0443c845090110840c1c0c50380d04003815584050241c01c107464001010041c0109542a01440c640c10008810303070350903c02e0f090781c040315069001011150108982584954000d0700c2c2500d0358040c0702c1b210319560072100700035805a4030544042c0c000d011130f400c0c01081c4601042d101da40f0603080c002030224810070b6030010340d000310300341100b10780da00350910000b82c49101d00c821816032080200000110980582e100c1d100b00c510399120490740c4c080000c9255281d01c01103e03002d140381c00010460303102728416009580d0000c009840040c400702c60f590252906a40c8036440c440c154041301c01488500020f00850309240300c142042d81c070181c501c0100000c90f002d2040c2c1d4801c1158045041d6000f40e00c1034084081082e0041c008000c00d05044c1011005014292070184a00310000400c504003050380303100c18030565010b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 624986393 1250 624985143 624985159
    0x1e010e011d120702010507060e0c0f060a0e0f06120c1305010c050304091116060e10060303020a080d0915051b0a1d0a05060406120c020106120311010f18060515 70
    0x103a000c90b900c0e401c508020b0781001414441340b00094485c0c0b103610608030101c4000c00b0600204820040e0340c07480452243c1c0200028040c014209401c003510591501c0b0803a110500c1c40c00c107001141d40c2d030060701130702e208070354942c0c05200c0680c1c1840002c001d4a10100c1d0f0380507009031030390019074034841448001001903204100410811306580d1010a040b24006002440d295030045403562a01d06010305a8600750750301ca420329140800c2001c00d01011050009106c160310b0741e00e01a4846181400241841100107416241003078190300c4400307225404960070915607107425400c1d00400d0b013100c040c070700c1425142e400c62203460218181c0e106058160b5640e4034402442c62803d02c2000002c0c0e40a801042c0030300c3c00704065503908081d1028080700e070f41d14004105030492030000d88059800190569251060500c21030108000101e641501410180135491405400c00d004241c0c081146030828600702043d002003405c984550040741c0600e4044c03020340c039280b40151200001c160b62503841014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 624987643 1250 624986393 624986413
    0x20708070e06010e04091b09051017010b06130f12150218100309060605090403020c15190905040c09080c0111150703050f0109051e091e010e011d 64
    0x1c8464960700c0001854000c0d01649482c000c84c06031900c0d40b10846520b00036103040b190411001012400608942c1c40602160503c500c10101c0c0785294058450055204550030803c100250081c0e01c4421001e000941d0301d496000c00300396051124040e1201c00f0401040000300050040309500c1c50320f4100b05031000c041101140b0780002d41c021881c031a940480400100581d581c2c0c0100e1036042030246d14049038501d114540b4904407816608024411601c580522000c01da0001b0481c14008050301c64070308000000742e0303240c074034000e20740c0b8540c4840c03811403854105548680ea4008075141980c06004040072400140c035440590b01035044203034000712451030301358070030032001c203903071100c2c4c4c055400c401c14115000f000c40d4030449442c2c010030740354001d000d600700541510b6401081066820402805c08a100d0041c1c03042c03501442458142c45808542945024003080039928413122200c0e01104040017524041d14a10f200d002c0294600103402e64294800500a0140404000074005040f8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 624988893 1250 624987643 624987659
    0x601061e021519140907060903050705092a09011b0201080c0307090e0f0402120303010303080c0711040f0b0405090d1b080f0309070911210403020c041a0a050102070807 74
    0x3000821450409420841101030303c10184a804540800c040d240702c80c91618580c00c502d0000103600103400c201203644104041000442c09000340c0d08120ba1180d015100d0b4640d00709894070080c002d0b000c000c0040b01802c40869000010402040c0c02e0720b03004181c203415820f600c581c4c045040d001c3d001c1112000007480b0031481e1002036905c4013103400c08400307182c2c840411040206086071820f4110341c44e84144400d524083c2510180c040e00c00c40190701e51f60541c1d40c0240f86800107440e40c584400081041c41c100001440c151402c001d0140c820407104c0011458030024240503040c0c2c2e4041c0e403805010480404d004a00a540702c0c007141c40d500d4003031607003502202e40107500b501c0581c1c0d144001d02201c00d400340904019030088444400900c41641403014203021140c413102d980d05526400c0060000004800c00d22400c2c0050041b0294000e03940d50809030705104001407070552052071314407a0300950820a204006400c800d50340d01c20080c3d02d0310010390fa60325550051040365800324401b0010301c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 624990143 1250 624988893 624988933
    0xd3e03040803070c170c0105090f0f1b010e0d0501091104020f0a051303020d052b0e040f1b03510803030a02190903031b050313080601061e02 62
    0x2074490710305c51001d803044800325000350300b240307501c07086c40c0c0d4483e0b051044810041003614102540790002d070020309020a5099500c1c0010342441903001110007682e00180e0007840c2410440c20050444c1100806078a0000c1c02030000ca070040f41d440c1c42d88204a01182000d05c00d9405000c0b0700302c5e1091500700040b070203540b40d0f081180000b92084441c00d004c401038907600185840307181b2800041c82c2c040450708030383d102203800c00785601120300141011404550b0214903038680f00d4080e200050f0344034190b40120080e200091000041402c24404004102e915500a42d07807070000040c001d07002e501c82404490800058001e010f2300e01c4d643d0b180804588041000000050380c0030100d002c840d036413880c1c0c490450700100e50006040c0d50118801c3c0300b10980c5aa41d1200c82214586072140c0c1c0e0855802074009041407038050034500f031507101542000010411218076014030143c41c0c0d01c81e03654035003941d500d003824041c1c5400070f01c555070703c01a00c50f040c8041601d040000d802030300010b11104032400c485 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 624991393 1250 624990143 624990167
    0xb0a061803050d05121e0c0c0f0d0509190b0315120604030e040b1207230a1514071e0602090402130e0601020d140d3e0304080307 57
    0x51804800000c0050010803410f440075107651112500c2d04001c000041001d00f000308210403030700001c00f441c50580c3d0968209640400d807600b84540341c14901400520f80701d0040b8001002d4802c0f003000441c4a900324001d00300b8544102c0e4072149020100e9a842c009110701d01c158510a0030602c0410000d10114030114120300000e88110801d040a4482d940b402500ba1019004114101c17102c0080e42000e00a2054408082c0d420402c64800d40300400d036181218854000702c03084400b24070016480c00903500c081503030002c0206a10703a03144d00080c101e10449400704c50104803c0582040900c1c074030821707990007541060305900d13603912020f0414920041d40c030044460130b070b007000610301c5660b0360700c040c0030200c02e10010750310701608220451039000405007006045d584400380e964846076018030b400003250410b804e45500d900100d041c010260013030303580703144910b00740c210000f100c40c10404a045074698515004503040d2922a8484443c0c401528080c128140420020704414001e00c10f040c02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 624992643 1250 624991393 624991427
    0x40e03090603010603270201050a200d21060b0d0b06130e06130203060622030215030f0f01241809021b010209030304060c050307020307150809010b0a06 67
    0x282100c65400a030700c03680700340c0259000c40c0da200351110300614164083c2daa50310441740328224540c099000078040d4000c0c4140402001602c1100100940c1440340c0040202031660846160032803120004e003090b40c00c4100600d8003085e030700990b0b004103518001c4604036412000c4492401d540100c1301000b803d80244520f41014007042000f5120195854400003400b449544000c18200901000740000d40c00d084556040d0045c0103001e016a924421902a40c80c41d82d5002030309d13814144403429040711507101961040c5d40403800319030361540d200214415521801a0031055681801510064a0078080d590186420409400348055603050307414400c86941040300181e1f1a1480b02143e02d015500324180440c0c020030304060202d02490040000300150b80254102031402022070398a010700c1c0718200070080001c180800303022080c003c403988d41c3d40150940b05d8241c0c03201002c08c14410320000270800200c00c400066030300d04040c231544641003c002d164000e020301e825800c8420000541060384 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 624993893 1250 624992643 624992647
    0xf14160f031b0903050c0a050a3b1015020709020a0e0d081903021c151d010302210a030503090f03160201090f08150408070812100f0e06040e03 63
    0x1802c1807040204030640e6802d580d051042d5041d40b44c62420102a9064140a548501c00602c040e0303440c0c210f8001502da2810040745000c072145451a55a43c1d00a4072210400301c001c1201a4070024214581c81080c2c61950000d00d02d983d0008241c5c15041c107500b51005800035841031181280507001002a00c00c140b0f04091610f07040000900300221114084801d00c000148480020000c000224080341041c2411420102004208031500c0710901545046580e50704c419504100e03560003860241c409003441c104010b20503104901030400c00c1c0400d030311484651482e0301d5803402007441d800702802e00b84050000045203a80a5505400c058481075040c01640c15140f00100d0800181107006c08900c40402c0d55180d600015000d000a0781107449949078000e81030090013400030f9406035013010011510442e51700c608111415001d1101c0c01020500002800079180c4204286107000d007881440c003030304581c1c0c0c0c0c3c0b0708458058002d202c0d007000e800c0301d400001d160703291681c0500c0f40b984941003900c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 624995143 1250 624993893 624993911
    0x301030f0c0e070f08010617041e050a061a1c0605040c1a040e0906060d0803040501090b0a0f0b1c0605060f040c0807020c03070b0f03190608010f14160f03 68
    0x191150742d080354a080043c0030b05508000480d03000c00110700600c400c3c117061800411200c92441c081000030400307003140c5d07050404450349100300a40c03a00d0380c41e0008292581e4801d5881d00c2d40142100c64004c0c0c60304101030f0714904031440d04030302e100c40380d0011554402818041d503403140c0c00b800009200365100c0340c03101e04c0050140c4510000c9401c400c188000c440c3c1d10b03410060002c0d0005070181c200209079000804011098448600954005400190041e00c1c0e517501d1820601500d07801d24020007000e06076086c4000e81c04290008603c800c039001091088000001c1803202808a40103c9696680c4440030380340401d806a00c626002040948101c1c484440840800e043d6000715400d44001000d1308100040c055043c4041100d441e070840c0a0030000d4a081c0c1c41041c1406412081100d40c880040494480405417500c0251a03500301828008681c1c1c400401c0e0003403c6c500c1c40c0170980ba081400350b0b41c4924880080034854a9090b100d0041020010411510080c14024190900d6903032340d0700c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 624996393 1250 624995143 624995159
    0xb10090204080a02130c090b1c020f0c10050f150103061208030f0c07081206011b080901020c01171303020a05060f100504020315010806030106050901030809011407080301030f0c 78
    0x7800034040ea01c0081811002c240305101c0240c1000d40142c2c15145030000401085510407020002c54004201064a800344607000b0a07440400716001055103100059408048070580060071000d50840107442c1c0d11020100b4050130384404130b4141c80c11f0100b08000134282120720100c80c00c0c14406140015409031144480300188071105026502c2e8900401000644110300d29141c1d80081c0301c04c111414203d09a442c00360900070070742640702010180c8001211640701d00700b04513000980360164400180282850a40d40d0700a002c118014042c40d032041d50f041d40140a007085401c4e68605607000b076550750241010303282000900310118021240140089030301044200c5c09600c1071840c169107400d0106508100301c2d41680510300640c01481003080c0010b403001a105001d0b02030074031451594503d00081e006007a1600b0032035000c4c10351800071040c0310524001d0500d188081e00d4482c13001400e881d14038920b025045008240136400c20050000825140d0f04514180c030440400b810701d0b80b98004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 624997643 1250 624996393 624996397
    0xb070806130e01140a020d0e0321061503040c091a0a0e0a18120f0c03121e090b0f060f1c08070804090507021b01090323030a0513060315030b100902 65
    0x81e0215600451480700c8039a0b1031051100c2382540000030762812600f1800a9200c90043d448200c40303041c03003800a0100d403103048022600c03840d80c9001075580e1801d8980070300c2d140214001d8014161a054607080780f48081c034000401240020001070b2028504102060031903c0104605641ca0300c6031049451401d040c0054004140310311a072403800e040078100140401c9910f0b0b900f1003040701000e10070000c290811440650051422030201c0d018407120382c00ea40560410400301441171802e4424414806042d060500a800c3d00c002c40b125521920304110300807101540c07655100c030b0310401c010034070503135035920744010b034031400c661401c001980d00c0b0760f01560090703801988501e40700c5081190141c0e051100030341005800c0e5448410100460000f008003a2a0100038110401d519410741ca4291080c16502070903c60021250783d0850380d080105140c01001d2400300060200b0004140507019004010103500410441e176600d40c41c40d150300071080009060415004800ea601151301606400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 624998893 1250 624997643 624997651
    0x702090411120d0f03090804050607051e010e16030b0f10053a110f03011b0e1207081b0f031605180c070209091009030c0b070806130e0114 61
    0x500141c03c41040c0113400034201c58102800c00d494100d040d0005003c810964065880a482880d140e0b051458001e15117160a018601240100c40324802c0300c1c801500203602d03044040701540c0325034101207000048244c050000402400c144000148040401240e15511481e100e110241007035651020405000308030f484036206074444440340501d20080e0381c0c02d90020685038030300300c40d103001603c500107030030b560341085489114481d038074140703599094000103044a9070341d0b90611403054801010b0100c0c550781e085580602c040c40d203440c00c5560045804401c550010380035041d512503c1d0400d1000701c81d201d0070309510803214488001e580c5c03403c020607416144000c20705404141030408004410010b00070780ca02e1866900c08015129003c8420780e40c0c1c544c0e05076484020380d00d0710b01c1e03642e041008445031a00c0c801c1c078004514040c554001d62503407605005000f09500d03910750dd0011500e1070001c5465030b811801d4441080501c42c51076100d402c586007040c00014910000d0107450701c6800c0190703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 625000000 1107 624998893 624998929
    0x9060513051801030501140705030402090612010203041101020111040b0f09120d080a050f070e19090c050705070801020301150302030903040b0403050a030e03120702090411 76
    0x15520100504801408600d4002e641c07007401d28040e00900c0103484035800d0410500720201d0f18000300d8081c0c8659541c4070b14560f00c0c1d40910104802c050421a041041d01c013296012140a1014500452050041c008084500e5000900f99442c0040e81c000e02c0c142040100800800b6204464910a440b4001c0c0e40f10300c40c150028608140409120107d401800e040e441090f61040c981c5221351518079040110340c03504585440092000c50b581400b040b403601c01c02e0746500e803600b000400c154008240c030600540f140300880648500582e4940450300c04a1001e04008007882403101500c0c101c00214103540c50080c00081c2c0d02ca0203841031051550000100d034001ca0180f0031207010784801074032076039616983d18001e0780c0d42130001c0e01030700000c005074035140b0070f4940481c07200c54484c0081545070505403940c0801203e000040c00c1201d05000782840c40206072581c51400400113100 = true := by decide +kernel

theorem cover : BRFrame.Cov 624820143 625000000 := by
  have h0 := BRFrame.cov_init 624820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 624820143 ≤ n) (h2 : n < 625000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
