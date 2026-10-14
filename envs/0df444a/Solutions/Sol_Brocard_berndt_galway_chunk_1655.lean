-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1655
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:04:33.727982+00:00
-- url     : https://prove2.me/submissions/466b862e-23b9-4be7-9808-3ef38400e2fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 297482014 ≤ n < 297661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 297483264 1250 297482014 297482083
    0x1009090e070302060d0506060919050f0109030506041121010b030f010c02030a030506030307150515100c03030b0f030d050d050c03221505010f031a1b03040302010e 72
    0x29520300140c03040301e20350342c0414043c1c0165036840501640f60400694192030314016515000c000805400c207080c400305c11101c819903503000c3c482c00b03403190910491081d40603055000031640d000000f0305a03541c51b078407030100052219980c580c2c4884c0a1002c00300312850502c0040105844000001300103180760205807500075404458a066410b200c1d541707140d160003106940d41c05101c2c5c20041482da0b2101d00003811445504c40c001c110751840c0a44030250705003030384160710886410102c0030700c002000b000c003d07031f0001c001c03c0000040c01c0e441e10000001d111b42c10040610502520910404845600107410710001c1d01d45800010380101d800744c02c1220314001d142c4c101d10000625461403d14042048000d83c201c0d40c0c0c250540307031500e030500c03c01203240540311507081203010800c203a5840326414440e0400910040c0c0310320940740d5072039030300410074148140600103001042a000c00850204806508010026820355580f1444069004070503c48100119190701a112206110072807840f0030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 297484514 1250 297483264 297483281
    0x20c0c0d0308070c0c08070e07020615060301180b030d050a02241b0c010f06060908030315120a0b01080a0605010e060904020402031008030f040627140a05100909 71
    0x9944500210404290016500c43d0090900c1c90000c410b60141e00744420b60b000b2a1b405135900e0310070000c3c005441c034491002c5070302802c8141d0030f4803015102e02c0c0d601c405050300b00c440140d0100c0c3c00c200401501d890401c104100780060980401c04214503000a07090880042c81400410400641610425030501c200c40200092419016822456038a104001000240102c0520003105400c501a850003016030744011081c400a01c490020481c0ca1009442280b1806010803000180401c8a440200580c1d02c66100f80390a40070642490007040552040040701e02014090390b5102000b1410b0507240310301a0011800905500940d85008400c488050748644403181c07016050040d2651850612900180c044501684a840d003101440d142d051551041013039110005075205d00d281c1d8003020b40101d440310741380c605903c060024850103081d98000052203400072404d0901641c0000c1590040010004e000c0c1424030b92030788003082205000c24121070104600c181d082000c0030483c02a1802d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 297485764 1250 297484514 297484519
    0x30e0f07080723130209120705010e240702010c050a03231603080411030f060a1a0102030a05070c0506030103150b011b08220608011712120a0618020c0c 67
    0x340100f020280c252280a440c0f40780c2c8540b5940c51040e1042e100754040d0741c600000100b40041051084400c140c3d1028144601c502103109510281454600810440030703144807d45840242082511180c03103e5001c4203040b418072110300d01c1803012480421590312118420384920544000c0c24001c5121540c4c3c04181c2143c1010805c40036003841d0000e908400b082e60315040c0300110703032242e00d000c0e9240c00c0d202218a8041c4a941000800c1841c000f41030750007044403c2d010401c081d40346090f4841201c01102d00d03800b5a10810107048800d104000600b0414002c120382c002441e21400090615442a13000f50391045810341714444846840c8980e0791080341c2402c20301030104180c00065070032000e9400140544801040115003c0f140500c1e0203000d0304880e200ca900c4e00d840e550040c20740380c1e007805000c00c002c003002c00902000100140d5420802e44030085c1d1420000012407045645c10000c0400c000c0c180ca40c20002140860b0305104980e5110408001d07845640112460f494400c4440c0c00710b1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 297487014 1250 297485764 297485789
    0x816090606050a1809020c031b030301080a02090709090f0504031b2616030203130e09030f030c1909060311120c09030f1606030606051e0a030e0f070807 67
    0x803964001c0101c03450f4200504141210260080d600a002005a401980d03a5400000c0340f01408030048010411a50709201104a403261030782d050380c0d40d00007401440900d90200ca440005860915040750b800075580c680400d03090b0701d60035403106941004800500b240d80b80c1c0f0520080503082003503000c950f040c01c0c95010190b80c0603100c2d018a07003901280035683d5859a50092801c80c4850100c0d000c4040d0000000d0350800682b03402075881d44820080480510000340104a01d18240b0700c40b80a0807000000b50f0a0204007860754040d5400a01310700203c0700200864194025944003120000d441c46d00c9104109207004005410746404681a111900040110303006101d448026150000d200303048490704c0c2d07081071011a01c1c0140551071139840f480b40242d84402140f1204100701640c40c40c0d50280500342c2c0c4c60200752128043d0084102d40e401100903c0ca48a0482030050300031b06801740f40109590f4074a24105092855500501281e0b800000c014020304404001a2004004601585 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 297488264 1250 297487014 297487019
    0x9050108040c0b030c0d060803071a070807141204030e03010f0209090412020f03030f150a0803091905102a020a0b1608031501032d050402130608160906 67
    0x140c01440c2c0d0701a500e1000c002002041070359a00707130295158580200c000f003260a450f03e80c815503076041070104a49451900341c07658803103415800b400e4041d00c0c03544c03507020041d200d2050594001201c000990b0300d208083c00003100c8064000c0c50745005070300a4480070004240702c0f041c142520028000414194010000020a9200c03440d07100d522907048a01040c2078038400710201d0400d10042101d098602c008424080c1a000c05400d05000d4148206070381d01404000c0103100d0460303c030384159815038009004002d10303070510081900704580101c1c1102081511200040c102c01d1801c00c403030000443d50100000d42c00f2074100341105c082138841c4240f020150941c0000e8805901e402002150b05c1c02140038001000e44050101c0440c1e480328817280c80f484c101c081011060302201c1028006410031607042441c21600800802c3d003005d0122909650481c4216039001e08030290080341c05c0000d100100300306003503620441019061070b00140401c00c81910300c03400d041e6281d800c0001d02c40d01d0603004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 297489514 1250 297488264 297488273
    0x2103140604061a0708130f080c03060402090f0402120d0203070303060e0c1b100f020d1811040c05070605100e1f210204110405010f17010501050c0a050a0b070905010804 74
    0x78107004035201541c0c556904c0652a2402082c000c803421440032607a80c1101044200c0c0143c8040e09545ca42c00840c0d40e0b921081c410166520f005540c003035084042c09006c607201c0504a0030541d030250010345000b600285440700c103031800c0700013060307000180c1022030302400b00740e4140030f0f4100030005040f2254541c03c0000e40e0310320b144504107041250034195481c1040c0c504050010f00a800c41c0c0d607100b00401d50700d480000c00139500c1075001402c1d40d0306e42210500283c031203c808040301c43d0440380389075240000b442804002d04a2240110611034148014400113a0700e00440d8410031442c90040e200501c1d09075070228140c0c0c05010803001d034410107070f20803540080c2c01021040701c1c0004700443e03246070f1840c0c0400000d802001d011790040c3c144041880595490f000404c103c48003a03031203c070040031903c800c61710300381c04244280f10711180e100100880d42c0b00d60080c02a0039000400e0310900d40346999000d24100030380c0300498050710180200b0422030307001415500106000e0828010b9803070103545 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 297490764 1250 297489514 297489539
    0xc030333050919020c0a0b01150305090d02210903010f09300c0f02060a0c0309050406080c040b0a0506030a09020306010e07051e040b0a1d01030213030807210314060406 74
    0xc103008660390215803170721048020040b458009800280404580d6180c0c0c100c1c080d000a030748140e10101c0d0a1001061125100203001008803080d9409010341c03e80814182590058070715480340078800a20610004d07a80a1040444951010b8000508029a4a09001c010451403c410042c0c0100000c0281c40d605c03001c2600c0e880c0580d032034000210521450512100010004003940000c004076002080d10b800241807e4402d020352201540503035148100020f9072914090000142c20045280650b402c1640142842010003404015603e0b00c960101e0455081200e50015064883d0f1141040d41001e020f810302620302250000c3d440c0c0713420712018049100da221042000140000340004001440302a24050b045124580c0e680e1501d049000701107007000c2e031039041d80544c0b690080440d50300074803c4880000f80c0042d42c41300d103886d6444622181e08135407015245074000e03040c011341c1e811040130100c071202d049440010380840c0310034080c90704200007810140103611707040080c00394501240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 297492014 1250 297490764 297490801
    0x9030203030c03060406170d0210050c0412060b06030405160f06051603090305120d0e060108070611120f0304060b0109030b0c0901030b0402040609080d050711010c0303330509 77
    0x1105a41c0d61384402010500800d0f10303034805100302410b040c1c0080040c0012504201c64142c55003100c13002249081c2d140101d070003d039107006452108000410140c0e40340031881030840c0c00b07001d000940e41c1003807010440d41d40c002c1f01c003110f10743c124504042d40d0130500c1040601401e250710607070421a0504101030540d20407000c003030004c0c0e8869181e42e01014410031444000d140e00c05d007900c5110184400d880c0e21074003c40c03c3c41685a061411010f02c648002400c24121030b8242d00410190340342107070a590901c100c1c0040301c058014112501c00181000c401810352110801e06607982c1e00c0c007424040e08582e845603921f81000307410700b0204045081e513640140c012040200c080e6407544940d00603030040c103000d01c00c25000350000c50300041d050340103101101101c80080035100561034440040b241441250f000401c59841a040c14803594131480c02c41803158031070304000950728429100c400c00e200074140505c16030049400c8082500d00080d00801c010601580c2d422864200100f040c40b00100b600b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 297493264 1250 297492014 297492031
    0x2c0601170714030c04150504060905151018030302030a030605010c050d030507030902090c07061113031b05040e1612030909020906040f09050601030b01050306100e04110c1e010903020303 82
    0x6014100c950b01840094082030b40204100030702280c2446c111003d8059114a911443c603100000842020074066540300704038150107070700d0200c1c564003088000e0555030b044004115400e40340c034160580d0700305c0b9440a14001e030001c6445080743d2000609448842e080541000f0f0700016000028000150420051105081c081010395903c60b0840050407950006507010501d437043c4646d101c21007000308800ea00030942404050381d01c10680803071b0300c0303046d0301c00030f4842c100c010400c04101e040c0c0c00080c034200078500b10b4603c80da94500150039201c1d420740e22942d98100070b02620200041c00000700091016007810b081036070080d2405401420344e07100c1e481078650002440380082d52514200e038050044d442108075100d0b141e40404e001440203e40203030100349001d0460b00ca541c000c405907886000020055051048240c00483d01602d10041064200c0e480350010006000e0041c06045050002070084c418150007000031017aa0081152815980c0d04d8481010040703036000c003c882d40080c4c40c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 297494514 1250 297493264 297493289
    0xf03060b211e100c0507120f080c0901090504050f071e020a1b03061b1407020d060e0a05061302010e0d0b1f030f0c170601050916032c06011707 63
    0x907040c04900300101070961483c2e180c902141d000c440c0c0e4110015202140c0114100c0c054000c454100340c450703458a11451011814a20020302c5640c103050061900c40c00616101140a684102040076144140e03038507084864404204110340d0f602c01c2006107600504070300c444140c000700354007135100c0e5407025000e00b41d90120000c401c0000a81c031040802158010b20402c00b014a072802e20034820400c000680024000040b00d030950f583d07003001d898020360000c00044202840da51404014001c02c15000b1950041c1c08202000c01c0c1c0034400c3c0c0c1c0c400c0100c81c0c902a801000c2d40f000400c070060403803046202d0282c1500300004102c55080c2d640c0e121000000b0103181040080f00030103500c1c51030744000e0502e840c8021100402c001003000000f25060301c20340040c174544030480f50740c80c4c4009000343e0303410481e000d0028200c880d280c22504502055800d0010f8900b841041d118201081c04210519100c212014066107207001c202207401004102c0150240c130600101d2661207074010301c102941e040700b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 297495764 1250 297494514 297494563
    0x103060e130f08030c072001020304090f090b010803040807091a0108060a0f0f050901051c2909030a080708090c060a0306090f330317040f03060b21 65
    0x11401c0002d0328a030300290150745a1170303c040d400c5503ea0103060122030380f109104940c2c54008103d00d012600c0001600510b044c2810a4460700040100c0303c620010152203548007004076442c2d0781920b01a11401c000303540c1d55820300051500d40100c03a404441c1c507500d489898040c54510041c0c0c07000130031007440c00401c41c0d100d41e400241014623342140180d010040400680c0c101e1440c940021a41d060380c0c0b00c80c181c0c0e0303100304201a805c0c0c01c0000c94010514040f840d000281c4082c0398581c0d0202000b00c8810705040420001c0111034220340158583e8000070308110010303041000c041d8440180d10303006d00c1c18a0415011500d400540070030398002c0101090045c40b45001c1d4000501034181c9020030050402e070310913540e0152410480145000c6810400c200d401d10010b0b0300c5e01104400e076415001080d18540e5420080e220018005403005000d20010a0802c8504840e10085019120102c1e0b540d001000b005030203002255405428820a1452402c5080205071007690b1207448180580310755 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 297497014 1250 297495764 297495773
    0x10081b010504120822081b030a03080a06080318091b0a050a030f0509060f01241407060507020303040308010b04030201120b0f040c1115221a0114040b0103060e13 71
    0xc2c410305a910317403280c0034030240c03403411142c90b02d02103a4a010445407034400600c51414207000300c00c98039401d90411500358000ca030140c504e4940084a00c00005842c0d9075610205085070002151082c1114080102040c4c500d030070b8241d540c115141c0100d010b21815034011001851213003050b8003090000100d1540c1d0114020342c003245401505030020310203031510030907007904d408046405490000c580800811301c82c1420a40314000c2010ba242803202840c00c0d03c003550000c0040380800200703013080058500291180c0034050082201c1d40096840381413515010700140c0d01600080030b03a100c240000c00161b07a2158807501410b0400302c00140c015001700c04695082204440d5680090800000140c041d500030001c0943e011368100380c4060f03050130011004c0e8141c094640d0b00c1840132004c0c3c0080307078010b90210303a200988115095101039000f40d411300f00c20342c801d9100348800f16039600f000880e400c0500440000e48424a01080f400e0708000c5503010105001d0641051101c92000d00800c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 297498264 1250 297497014 297497017
    0xa020a0f0f08071202100b1003090f1205270f0d0204020d1514030102040e0c09030f120d0b0d0203062a070605151507060504031710081b0105041208 65
    0x950021034150743c40800f03040c142102402c0c81c0d4500c00521441c0c00c030400340c2d515841400900d980062443c0711001883c44101c014021420041e01c0c1d822b45008004000b6039800110380050310302d512038a4a86040e000d0450303001400824186011070b00082d28016559036007240305000d0070071144021555440d0002c10028000e280d8806001454801e00031000008405030300704640d02d02c0401d100b01110007041c18280d0056104140c5d10070940c00200e0f1b10501c003000a0004070038003804407561010017a400c185410800a07965914040000b403454174680c1901500f03a1001c0d00751140c034007a10300c542c0825560f004c02405000b0780b490300002c10041c50200590303511840342e440314540c0c035a0498280300b4010507094034426001c445142040303c541c2405800802e444129005090521a040d19880080d182c001c00c21406c2203071014000058051118515008441d401907840440c1c0c01c0100302d138035142c000c00381030014100c040708401d140c2c1c3e0320038111416180181c610311031940c69442d000d02e26 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 297499514 1250 297498264 297498293
    0x6070504030605280506041a03060604020c2d0d0f051903060b07030302031008060108030f2812151206020d0609091a0709030f20090c0a030b060a020a0f 67
    0x100050030104940c0c1c2d1300d0f410060003120b0840c4c1c10060030100a50340300768114941009500354101c4000980d0030b02e450341c05404800d641d0370a40e44842801407011503001c0c2d0340107001d91a1905c0c80c0d40032458080c02c00045000c0840f40c20030a610240c0468080c0050269800140b01c000d07955118820461003600320314000c00031514110f84075450703071030050040e401c21244036404822160000500160004215040711200c03c0510324004060102c1a80f990200c020121240184104500380c061000e10388400304c091030b628002a01164141d5005076000e061032400341070342c400011301c100e01461031b0300e0f500c29622171001a503e250305865200608280d621018240d442d01d0000d030709012620006280c5a00c0c0f4014402c240c1d40d80c010705840d0710216000c05800d0810201b203820000702c005072500c0b007400d02c1404880006030031400081940c0001c4500d500d04a00100c3c04142d0701e0303094000d443d0720042c2100c040d402c0c04200c000095480400785000380000150070300110038442c241203404030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 297500764 1250 297499514 297499561
    0xc0911180d021f120b010807081308071202100903020c01050d0905062a04060507020103021b070303020c1206060d0222050106020a020906090402010c02210a0501050402011106070504030605 83
    0x150394011007a600000e60404010401003002600c1e4040c4c0c03442d0f58400d1039810340058490360744036111400c080302d00c140c00825040c07081c2c40314565000811001e00241200d1403044940ca1596200e000c002800e140c2c1b40205030b044107003003061110010790041a03a070410321003882c000351514808c80d000740180020000103400c501601050020902a01259184501c118880d10000341c80c8044041c041b4891846840001203040c002500158840d800504080003098002188c0f000b2000006062514641c01100541e01c5400c00840c81c1c200741001c0031303c20030b4500280c01c00d0700d8161301180d404840c44a0091149220011045481d214041901704069058100b00641e42c0c450350042d685142c5060140d2246441500003081c030b203040c54860340b19a5060352900041e007425400c0c0007200c800c0c8401d4241520000e8070780003002c0c104101d50640a40200300104a80c10302e400050260610301c3d00740c0d007558002c202005505600700301200c00301c0c2c0e4400c000040750741d104c410321200310125850280 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 297502014 1250 297500764 297500779
    0x110a0f1b080d141e0f010e01051c08031014040b011209050f0f0f0723010311040803071b0e040803040807020f090703090b06030d0210270804030c0911180d02 69
    0x1a140b08000b001c00f080607000c50740200245c40303529420300040f009224441001202900522650900d000828441c0c031780304c600d0422009441d03440c0356480c0c0017260219140e000038001044408260420005a40b40c00d0310200526061a000200107103203609004a905480d014000c0400c54200319140040c51800140d41c0d40407024a1a591641c2e030500c002d42452103082030125a1030074020804001201c00584e0380302240594006502500e0980c03107041c2619420300c000100031a092004000d01c0340b0402c02d503401258454080e090700c2810350000031116030a20704000014503000110780d00f003034104501d103031a003409200080325984600e0b802504013610b101400f10564040e003003010a00c0c0700741608441035948400307060ba075440b090102c0300141e00102400c03070340544a5100700750a002407091420081842d044220740d150390103108950700c100c009010018403841644a0000d0b0621607018004002d0b04000200540185405910350031403507441c244542d40c440390240e40305d640c090a84c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 297503264 1250 297502014 297502021
    0xf1f18050c0702311a0f03070905150316030c0b071b140f0f010e220207051509070302150c010219030213171c09030501110a0f1b080d14 60
    0x8010708800c504910b6400c1c4030940001c106a0f2402502c220003192445e40100ba1a10b50402c200da114a400705501401035540100b810005400389a1152003045035105500c50b2542c02c1c50f1600201c0380714500081c80b590424000204005030300030440c0d003070040c102d0703e9083d41d041400740b41040901f051082031500b01c00082c1c59034040344c40307490340c441100d00d105803086140070f200006040c1406240060481004110589011200390050303900b042c011051125030f20380e10904903803002c0001c1d251603010110400407994044001584443c0344c20140c0340c11491540850012407001c0d07006440326001040314081000d00b58190340003240380710720180c030785030038250060000d5100040c6440804061100030407071403011042d442010b80307250300500600c3c4850914500c5122081c011408004013a0701c00000708409000f201c0901c2ea089044d9562000103141c0078002c500c054081c4401d00c045001c940782034202c4082c0c07900c0800c2d007008000c3d5031200c3c41c0200c5c0000b0003071b10344c01c44070558800d41031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 297504514 1250 297503264 297503299
    0x6070f050c030d060501110c03060606030c091c17040b070f2909100c05090d0204090209070908070f0b0a080a0f02120f060603310b0f1f18050c0702 65
    0x2130300489130203880d801204059564510f4403100c203035011640550200c008036400b420800004e60340250000c125504000f074980001d1252222111920041c108207a014820b1003040c0c4180b888920654482618141c90025041c0d00c03406907040103440c80c004000d5403800d100c014840c6400c50040c00c502c0e18052142d80d10841c103141010b03180e58043e0320542000c03c995070128894189510300640ba801e0512540e5010048081d41c1450301b00e800540743c82e00d04c001601c0710b8518034028047d41c0c8500394040c1c100020140f8044142d4422040c11004c494100302c60711000c01241d100e00924a41100c1d03994840030501d0141004042481d134261000a40200d08000000b40c24090f1651b8030100300d01d600e501c0c080184900054800c0ca00d1045050b08801c030324800d00c0c840d0480700c680c54000401c100026119403003004c8080380e40c49001e414200070001e5068005660314440c0c0b0784007000b00e80150600e103840404c9524842c000580c2560341d07012440c0d8041d01000e640e94a9801081c402e2130050a204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 297505764 1250 297504514 297504521
    0x60403140f0d0311040509060d050f100f1a1003110a03090c0504050106050f160602120105010e030708030a0e011107090204050a1710090807020910080d020102070506070f050c030d 79
    0x1d424118000c405215041622074041d00d61401441d0082c43d042c1400c00741003090122026009945c4414010050303000a407050119000c2107050303001611480620f02410707002c0c0c64215a201200a1401c009010400318030a150350000713106840700400c2910140d01a0020036500c210340e491110040356205000c0d0f81038000300c0d1507030700c04c5016603d455601d0040c001170b00e00030700509020400501c05500192041c03400340000c0c03844094521048485501c621003241d2025143c044d40c0b0300401d00500803075030480030108009a0a40080400354900090942c032801078040007030030020000c61401c500e0307218038036003503910100c00241c4907826510200403001754130910995025080c000400a415a8903528480b804030040015141030031036400b00b00b005080701c0c94220350600042c409100541c80361207045100300786003200000c0072401c4c244198500014140c0c820f085a00400079000001e00105d04580c014405080903003103010129419030b824003401045400511010a84800e690784541 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 297507014 1250 297505764 297505783
    0x702090114010201060803030f04020105070302030715060f0b0a140a02151e070908030406030506040222060915090e06010903080705011e060b0a0806010e03160e0a02090d030e06040314 81
    0x800030172640360340320452038881c0401c903403c582c92007a0900050265000310000c0080d6031191069a01d080030325900c2620b907003c1200c0c801440f560345c1c04140050400c03034080201410102450030704041e011000105440c40002c103040400c040442c04c01d199600070000b0440d42d4022000314441458821903440341c8090340513421103000c8598010401540c09142c02d0416581ca41003e10710f41400c1a90a901400005d071605da00703d54200203107000851381d6101c094003000382502035201249861401410b04a190300000d840130040d41c00859440e400c00c102c0000c81d00880341c410341c2591360307800590b200d022552025000481c00200002003000642c0140600d1003440380c40d07503c4d0008014541c044641034021809100c100700b2505203058010881c00e42d10072414076028020062000100e8285010091700100d083c400e054248801c0c1801c000c0780d40d01008102086080a82280001b5105a580381c0d0103024005581522503407038584104890280d504020b031115540010007205981c0c25084 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 297508264 1250 297507014 297507017
    0xf09091b030201090e0907090c0203130501090b0412080412050a03142106040e07080a03090515030417070209070815150906090301140a05060a1202010f0311070209011401 75
    0x2092404000d58034110400740c0350181e4440000d0383c2050b944100c500806021141c2c0740c030030400b001400704824021610404a83ea000e16218902c0c080029100d8107590051030600040070024408116404240c40c126958013903034003044615070520003030380c1c0304540040c2219480a00301c5014800000f80a005641c030a0781c0710050f5626500050469020701da85109c42d070150516094031480300443c049030001c000030700005481600c004031502d0006541e01c803c1164210213102005c0c981c07c140b64600030141502d540400311070f880100302d0340d8480244001c00011490050000ca12804010f40300b519034003a0030740d8510304040d48094100d54080711000e112500c0040020030702d08181810204404d00959818200191101040344030b40040110b140c25643c0c5140c0c0152029240f6034407405403242c400c0005072410304d0800e200d40218690440c030310f4080c590041a005076400380c800d2002003540d14000810052804030408213101d0400007075030040c0d220001241840d40c056402401e02000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 297509514 1250 297508264 297508283
    0x10052803061508100b010c06020a1817010c0206040c120c03080403050109290105150c0109060b0f100807030921020619061d060604031a1b0906180a0f0909 68
    0x14510f130201a91143e90000c3e0000c1d814040c4000010000d80180c507580030242488080200f6054010011081546c0b210090a90713600d10541794403001c1c85096110319061002d020145020748612a01ea8014412502640604901203040c03000c04060103001d554011002c1350303103541d04e0600c58003802c0d850390261614414282d041085907480e030754407010901140507440c856840c24041081210000040c07010100041007400c0c9100000e103d08000144288000109510340d6018845c014280f40c4100d4081c1841000d0464940c1c0c008a007198414070300d01d400310340c0e100b03e4981075414242502048102c030b18a401ca01d080c060300404c210b40319141d80c405c0c0380410700307a0002207001e03511584203015603489829120190701d014048a1980038030f001d000d03030303151950300e545212216041d407a84945400c0041c0903c00c001819203403e00381100246001070500404600140040c4564140b011700c0c00c0b62840075111540b0b40f401d02400610058882e5056940c0c5c03404800058101101c1c1110041203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 297510764 1250 297509514 297509533
    0x30d02030c01050c3a2c07030201080a0b03010b04020406170c211f030f2108010b0325020c010e0a0602030a080702030c061e10052803061508 62
    0x4410703204e4644200c1c645550583c0703915a40c90a001004402c03500d40c10b01203142c0b0700e030461180561401111303003103660b031b080c0880310b118003001e40d052401001294004480400160b0790080f251030b08125520000100c1c5100400028018160801003542041c000704c0c0010301940c0100c6400c07403440c481c00041085607503040f4440114425401c0c8418071554805500c100340d04404510b590011034102035414109203080454243d1145601c110703191841d164180e010007203030201902c03102840c0503441002010200c0094101c8405015024230140c0c00310010354100b0a100c031420440320a00c510002c81561039500139160f40480c800140882c0031145040b07003500700090910110b40c0160b0142d8208040c06c07000710f4448501520340c1e0308600c81800b20403140c00013800154091080e041040020341c140100d0008580380040040b83c83d6407036500100825201d0540f03141d0b1481684e00c80086502048800c1286021503800c0030701254508000b134805456642800b03002d0301c44802c02c03600c0343d01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 297512014 1250 297510764 297510781
    0xc1903140c030304060c050a0206031f080c090103060b0f12010c1b0f0201050f04180204140916050a0c050f01150503060412031503210f02160308030c09030d02030c0105 74
    0x207a44003125415600400041254510400003160300034420000c0c0c0344c41820342c1e00020a2600140e4500c070b42900020b0601c4580138020300150010041000a401701c1c1d1104000078040d50014032016025a4403030b80c508840e6602c5002100d04000000c0c8900c5001c03141900e81c034001c021406640010a0f140400901ca98480200d2241c285900c1041040750404941c01101c290700000e540707114940741070001045101e40c40c01c000025440c207100050310b45140503140c080b2090903c1d4040e02450030380051007191108210000810310490134807030707aa0325405100f101c05480202c005440344c0201b0118441c900c5c03041d0000d0902d12400c0002007441c60301d0b4002c0507100c520940e4005c00c003c41c11212811540c0c025001206000607190302641c03240da40c2c0d112010342c05480c082e600b00000341f01e503490541c1034100c0c0c00900f1501940c4010a440f5091a01810351210a0700010f4018080440015040003202d0204c500101000c3c0550b15035091149002c0d50726006107880c03200d55424540001c6011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 297513264 1250 297512014 297512023
    0xc0f0a080906090f1c050f0a02100f09080a2f06010f090c02061f0f0303020c0a09020a050405040504060905010e030a02010615050a03020a1817070801050f0610020c190314 75
    0x4580001800482d04402d295800d0100602c2140e800c0c81300503c2000000141c9401521024907503402808458141c01001d00807564120305070510b0bc1d01c0d02d82c0642c0810000800d541c2581034a040c42c00000702031204203100d0429600c0b040c2c140703041f407907601072880002160b0241241c0f507005a0f501c1c003a8840c4070310000c0ea1941001d50006902c51000180c41c0b040e507040216072880e1010440041d26100c0c0c0304601483e00640064001d40c0c4012290243d9061140350940240314000003142000307a1000002c000d4441e81c0304661045440701e0124092241552103146c040ea4001c1c020002340c001c05816907100d1b0001800013000d5441e080340000c0d0100c00740c1c442d02c006501c0d50345a61030b00c0a01541030b070094009240d0310082000b9422400c20105094501c0c0b0042e2020301005180c424210500a10304001d98000700c00700c0c1d05150910062540e0043c1050304407208884411640303281450481c64015042585a8481d0b46064120810641c854041c01520701030381950080500d0711202e559107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 297514514 1250 297513264 297513283
    0xf0203070f1809021b060601020a031b060e030403060605031006060c0b0406091703010810110928060518030a02090a020c01150b0d050105010c0308010506030c0f0a08090609 76
    0x1c280400144504984500404210888048491a8002d88515903081207130010b400040c4071500d0b442c0503202c118410031406030b02110034401003440c42203507640240000f04d1000c1004242c0030701ca200c0d00400110760060300b04104048101d82c0c455940703040c210054070562050f58000d0050040d07940311102c0d5400348005440c0d0f5a101d401d011040c603518400a00070003402038603c142d50340c0c104000104010660f061011081c281c0540302c0d414a241181041031003489110a646007542114108215034141c40d01c4038811900382c0346240030000704041d42c0f81c03040c100c980c1c1c42c101d451000c80c0d1582c204000c0c0602010301003941d01c840a1070703000d00d44d448410141c0a9401100394000a50300c110b150000c28911601d1000070820f1310f860229045a4281ca0300000c25030f4201040c0d0300181000d622900f8010042441d18688450350794030050007040d8180a2140124000000140107061503401ca43c070111885081079603604403000003c12000d01641d0808140c0038010103d50090400207201c8078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 297515764 1250 297514514 297514517
    0x30f0510050c0301030b16050d050a0504030f030905060a021b030d060609050402090d02100509180108010c1724130b090c0a022a0901121103120403020103020a02012d0f020307 77
    0x1c803900e445011240311000c202e1031f481088001c1008080c0001d05000b07490151000280216240c141440c0c051b02489401108204052814151030003180b80002d00d9500040500c00051340da000c0f108034210301e0490390703040c804035220029103070200e48010f5010000f101e202e50303646000380f901c50041000380d1003810781056205d10b519460f5000351400c40641880e014031418030500d812407000100da40641c805e4480409803844a0040080300000c1c0915440010b141c60405040024101c1100501c0b001808241d0800d030394166a000e4030f8400e05e520940350100804030301101da41e071004040a081c5003503840e802458403e000c100c44082c0c14064590000c0c56802401c604015180f1f000c03040d0000404040821000c5501b0b80c406407940d042031406007018050301c44080c1c5d1142460511041c1d00e0301c2c62802544004407201260590006a42c140c3c3da0901e00542e4a0504850403400350007040c0031034085848080408440c143c0801258110028505090081142008121040b03000c100c40c40320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 297517014 1250 297515764 297515783
    0x3040e010627080307050c030a0507030308040c083405010818010212010305030901181d070e030106060e0315100e0415050f07110c0310020310030f0510050c030103 72
    0x218107030040450b9410300000b0004001d81071601c2504103007280b8240c0c4a102c0c1d60700001164030600c8018400054040e2064000700313910700a42d41c1e6181e42d206944806000c00c0390450100e001c0041031404040109814401c55030020004601c12050f604440060324800080d500720f09451003404510a0031a1016118400c0c65070318044012901f41403211040c4003554200012400c220090010714065402030000b1a295044030002400c00a03038505150707543c4141070382c100b08001c4080c45c43d0084088092500c0c0390343e1241201507420520011b4516819428407101103502588200d284840f404102e0171034000c0c44c890310b14002408819101110510b9070440c09028520b00101046e40161003210260f030f290615002d80030407a4402e840c100881100c0d8800d100c2034646c050421003c0444900190803104014030010742c0e00e4600610703085400381c01000050900055000800040d82c200c900104c84000b5890416220306448041644407441e160104035481d02c1c060035641640e503c030b81d000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 297518264 1250 297517014 297517019
    0x60206150f01020705130902040e031602010309140a0308060108010b04060909091b0e0108210d09061b080f2203030b190b030603060a0c090306050603070302060c0f0f03040e01 77
    0xa0014964074401d043d4481c2d030000003031a03144c0186804074a172121308000f420803501c2c810801078504030228040107a00034001010070258000c0c10301042942401d0000d1220001c0ca000100100702620001c058025140c13410107058100e8500340c4100401d80e5400e2107a038a80044070082c0c05640070306000a040e0140038440740c1c200d50b01041d03009005030030302c0c10f0251a424102d9400351480d00402040700c54440108803c010401a074803d02c21020740c0c7c500c50f4a56030304034a4041c000e01d80441c650f10744540c00082032101c250b10900c140003124003004006c0f1101d85018040210680b5540051b02d0041c0000c1c01003145190003504582244026001d00900c585089000d002c0b8a84c049502580341c416024041520807559070050014001c1300313880c1d1811074101802c1036402012400c1443c1081200c001c46a40f1580c18000e0703a0f0711010010f11030702c400700828075000a541000f5007180c80004e080c0300c402c07400a03039030035500d1030041198801d03508900d0458407402540b04a060850300680103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 297519514 1250 297518264 297518269
    0x51813080a02031e2b200703030e01050c1c0e0f01090218071e051201150e030105040c170307050607020604022107090507050d060312030b041803230309011506020615 73
    0xa1017143e00700c2c2c2000c20001140c03050760038509142c215581c40b0041c00a101c104164150041504401fa024001c102d94644014440395901c100302e400020700700c10200300c03400c42e003055101d02d00c0c4c081c1d1f0408032440108210305d054000c00840c582a4450b001e01d40c01d061200580100c0310788200629555005501d100a90340740c0d13001000d2000e4000c0c04000d0008100303684a141e6064000c260b003800d01c0c1d6400e0403040d0b0203804514031070071090099051104204c040b607005c040360811101d4081c2814040000010500d0850040b420300800c10301892003484003040e4002291401940202c8010590810140c41c8001340d180310f02491582d600400401c12800d400e65004543c800f1042c100540f03840c032640c954404030342c03040e0411102c50251400c40ca00c181d0f490b114910050728262401c10000d40700309a40c0801c5108480e00800b00b2440e8035616041c3c480070f8402950400b80401e00b152a4140001c00c80d018100e11082102941900d100000740f0302d10010320a40601c941481050180000c00103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 297520764 1250 297519514 297519577
    0x10b011d0f060928030b0c0c0a03050f0d021605070f08060f07090e09210906040509100314010b181311030c060703020c0a0f051813080a02031e 63
    0x203c6610000000c0e0b0000300d80b40c01e03102e6102c0d1007003210b81d10880c24194034041c0890400130f81801046038050003403a0030f40c2c4001a140c1e0703000b41c1500344982c46100000490541e849902d00c00503500780040340c01d91318010b074400300c8420300744907405a521660319610746001e030020301d12500780150300420120b042e56850410607504a8040e281411005031503e2a8401c00c103c181c0b880b80a581c0b00c5005441c00d60b1031200c420320414940c56040e46000b241c44002819405030340902d91080c81c0e204080741c41c001440260400865200c620f0203040400c088942d4028080560110701030082030b5108402201417990440c46105000f04030148880151501c160100b00ca0110b40e816110300c29402c403c0340e03039201c040e00b01580f09500809400700d2060034059130840542c018906071502c4c410074091907480b08403400c150210104010300c1c0d82d40d42d0038183d207c80340304000508070100010b0b0301c50240b6804002032006002e000d00382d544140c413101c0707440401e1040002c05213030a002c0307801c224070703c03800e440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 297522014 1250 297520764 297520777
    0xc0801090e070308180307061407141005190f0510030f0201031d010c0e06040e1603020904180b0f0408030a0e0a0203010f061a0301150f051902010b011d0f06 69
    0x1c22601c00d50f44a5840c00c83e1603016026029030030030207a0100c0b41a160030080d4601504c058600700346841c0000f0f1052201e4003901c00024075081010f09907840e07000d810002d0030130761001240c090201c2d0910340c1e6003810000403411031581450070302098110b1140309025441c00380080742c08900405241d601c0d00807076500c046504038101515455890440c0c1002c4000f18480500384000007041c0701004800750064084032443c03400341000b8041004881200f0a01e40da12000f603628804602041c484122b00034840d03154025807052030f09881100f81c091044d1820103491180c021008503486100c0c00640e0790504440c001e000d58030070400164088015000040107035405411104403a00c2c65000070b095130460705548209c256035090410070400481e0103084042e0b54181003030701d15410082c6440020850740240424812001d0000c2c0041f071080d01112650483e41807003d042500b0001d00030f010b00f0008070b00c10b00103804800c0c016025404485012900fa80090051000d01d103c02c041c44180d0700540d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 297523264 1250 297522014 297522041
    0xa050607060f05010f05040b1203090103021312080d0e01051311010201021c140c190f0507050609010e060a020406020304030b13050609210301031a040c181d010c080109 74
    0x3441e100c25800180e000f054060301c5841d61141c00c840c01c0000344801c44142c540c0442c07081081c0070400207544130100854942000a180c09a99400c2990048104c0c603400e0307200700076101ca00c00c4d0120078420341002070510087e8954040c007414507500700050030b1710003d441e00c0c003158221028400024920312200340261406000150400c00a00000c0c500c00c0300200001c11101c0c2c036413545000d071440c14031800364400d0344892040e04007000c0748007171544417040d010a5014860f811074000c1d1440d02440c140c61010340e000c0c00b110514903048190394041c0803c01c1c1e82500a114a4010800e4003605d4000d1300e055501542c002c41c1014030316101d000c0c4030100544200c1c0c80f406101c1020004c5541442030a108440c03040041c0940310140445030200720b03141c90850140c2c1428401480010300801c0340d02c00040c4400e5401076681c44a0902c41b020100b03552281e004882e0385007500c02459659000b500d01802d8034180000c0c4c7c849404109420786e00000801c0b00000c03015001030019059a40c8403d031001c600c13 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 297524514 1250 297523264 297523271
    0x303050703090b180f0109050f010c030c1407060609050a020903010501080c181b040605120f0105090414101508070f080d080c09040609050109050a2d0b030a1a01060203090a05060706 80
    0x340c4a400c2c3c00c647c201c01c420ba5858001c010800fa55003001d0160b00702d00409481c04000e5420050700081c58101d03115070040a1950000344e0b0014030603160000f60103000028010041c40c1424006200258800c0510038040d50a100c0001254040450070302c140940c0070700985120501d051464040d801c0007030020444544014460540b40170140150000e012192030301952403000c4c03031381c44801920040a130828403019000601c40768942184440e049030b845298013206043d0101424104815080c0b078060031460300900e001c1644ec464860b80450f0311250549000c41e45886003004882d4541c0100049035111409048016109142c09a0320180f07030701d10141800c0c2c12000103070039250140c0c00b81380300a441da001801001524410320723802280000e010083c03078650010350403200b0303007000e403241c40740c5482080340b498400d00ea040910551001015552071415038a00b1000404004800308107440c1140004645280004126460124000c10b085203440c600070030442c25500502040341c0343e81e01e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 297525764 1250 297524514 297524533
    0x12010905030403080a090e1b03090a1506051005031501080603120703030203100b1e0901180306060303030509060906060f04020d0c091a09090105040504170a05070303050703090b18 79
    0x405001400c043e40c402c1a4981d0354062071750005100d03202c5604103880c2c03c1800d60502c4030382102129030700b00c0702d41c40980f699141e40d40c20750030320305108101c600500b91081c01352403502c14000c0d65014406903882240c070302208910301c00e8110780e075020072100009180382c094140301e03a56026541d1f8990218009046411341c03c40c4030003015981c3c0145404401080e008000c0c070400c6074032140c01c000504441c0c1810303810458034202c007400c0c3c1e006c2c001c3d081e115980000740c03002c080e0740300e4000960152100880c156256603640740510040c400c51105a00007460712000c1800c2c4a400315405004d400c2e11801490962242e0040080c06503040c0c0009074030680c00c1040312214140303401011881c601c1903c90f405500d2400754911901d24180d510390705001401c000810882d942d820783daa0541d101905d001403155160715003041401801c00091003c4400890070000507076018008081e058802c0d9000e005548a1080603410b4402c507600c0100128801c030005109030030b03041d0140c0c001d6000c00b0126040c101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 297527014 1250 297525764 297525773
    0xf030f11041d060a1b08040b191103010513020304050304060f0c021c110103052404060801110304031806050904180606170f070506040302010c0303060305060c0c01140411120109 78
    0x40c8210b01e440681c0e0410740800102c2581885642024089050003024400341507800400301349004000070001450139010800b01c00220700750300301c0c0f040c80720000c100d1270a4007034042030607800910445108103032100c0040c0c245109802a2405503500c90f00650810381840300a0b00c400c0031006052042000111036000580d8404081c2028050b001c0140d0703884000340d0400c941c0d104401700e8183c0c1410700740420b024036010310740141e04a404a01e1070a40c504511400041c01801c181c0c0e0004c41c5560070a001d89030702003000d0300110701a0b032283e10b402030b00030905902401454241c2c418100070801c04e01c00704400c6d060980207039144c0c640c501d41185c01d0001a41d070f840206c0fa140c1d08050180b614030034551360141e400300060458a1420001008064684070014513580301c0d90000a04001d8203400d2a81054020303003041000e107902030700f1790703030307103240c0140c180000c2d07003012140158540c2080103c0328045030707210345035004c1e580200310385424080000c04c1c041c1a0b038214100811640d0b9072001c0c9004107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 297528264 1250 297527014 297527051
    0x7080f030a0f090803060117240f0a03060605031b0303030402060306040b040507200a211101020a0c030905010f201e060609101409190c02070504060f030f1104 70
    0xf10721a03c055030310382c1810800102220080c180c1c1002c826110001d009440e562161400b41c40c1c030140c480c40c02c0b01078111002c01c10802807440e010b500300c02029000700410105030010815280140d0803101008c05203e00880a01144c05600c1d4050300200089030250521400565005030003800102d0b03001d51003004202215030403110b05000950701c050301c0c2071820944050109040c1290300418440fa00743e1220340b403542904203104448039180744120364050240d059241c00310507982c021500c8803868040070302000c1010b10101e0005a54400c04a034540c00b8281c030105480d004d60365099005050008010410502621170500d44102d06503100010102103010998203a004c010701503a043c1101485403260010b80b85a1404c0e07420700003446949090200f28880040c04c03a15142c1c961a1507101503481c1e941c84800c1c504990a008592002c2d90b00001e01600b1624196001c20442c2d5640000c0c41c11071440d40001407080d900d404152021076510b5404405000000f88000707900d006420705c0c0c1e00344 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 297529514 1250 297528264 297528281
    0xc0f030305090d050c07050603071b030c0308010e07050d0525030b040605045402010f0305150411161a0702060411060304111c0c0503010207080f030a0f 67
    0x60744034410814201030a22210320300d0850360038070f01c5c200700000c1c0f0b18644820b598010140200700c08000202c01905c9014100d803a43c1000b0b0740c2c1060300b122420020180c0c1120780c030640100d052030b000000d55040300d403980c9100312075541d01c15042a40d0b0743e408201808000e08040d460401079111049001ea0084100a00c90740c0360300c0c0010441d040c03800780415a0000d920a0303201e145002d0280c058508206a2503d100e2224892001c60140b027404241240013004440340c3c411340c0346034440041c03441e06070300700100c103000341c84108017001420000c509564084540000200b1601c0101940b130030720350810108502400145814058203080040d800c60b035840d8280c1d08150380c030012004801d48804210341200103880a4485c43c90203461701228541c4c10030301103020f13020000000741806a00001c0c09800c1600401c401903046c0d603100f0940340210564010740d030042c01407a002a50785814804c03540c0056001c603600d4244140d8010b504407a420003003a035a8090b880c1c500700a0300302c03840d2059102e13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 297530764 1250 297529514 297529517
    0xb0301080115081929041406240d02131103010609060f020607140903010c0807020708011b081923151e06120f0103030e010903030801150c0f03 63
    0x594003180c080c1050400c41651007000da613006038414160204042c848101e00c03c0c0c101c03020a070501d081d21840002d0021020105071410042801d1004000c0c00101d110000603041d000c07603500e52940070303510035110103c642034550a00d54601803401420501e0040c8207060004150303016040c080c00c001c1003030300d0702c030b00b511540c502000006109807500012484041d190740d140c1000112814000a592214050300d80014060480c2c10115a0b5103110202d0f1003054020f0001d000040700d809018041c074809a500c0800350080c5000441c0b15003051080f14040c0c0c4115480c6401c45c50740c0c21081d40c00040250060030f44000181802900b04d0301c2e40100500014160718a444c58049201c60f11f8001c1400f4200b0450700c5440040c0500caa919880141c0030000709000400001c201800000e507240716181d5098030681c102d100f0401c01001c98030710103040300d000740c41d554404000c1c44011914443d143c0030090210300c0c0c0400500ca42208003201d402d5520890030101204241a210480780110b4110100c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 297532014 1250 297530764 297530771
    0x110312010807080d050f030a06050607030c0c12031704050c120c040f0b0f011107050d03030506040b04020c0d27090c021006140103020c030d150f0b030c120405070b03010801 76
    0x1148804000d0b5a00410460020b85100300c4094802400d03441003103c03204c1250740220101d201144154480801002d000700956035521300c5180c0507084030003207001a0b44003250036000040b034000031030b08008000c0e4999510040e56110070780b01c801c4004003420548562081c1e20024403a81c440f840c1000c075815540c002454070505400c00c10041c0c46180200310035842c100040742407180c440300000f0b4280310302402e01101c04000c0c3d0124500d0607041c0d03030210360b00c070301ca0ba500312003411340641c41640910b00c255402c0c04201810011710041c0d02c580c46014189511000b20b040c01d00c0d2054604a0500700c58842102c2c0c2c5402c81107001d9510301c1c0716000f41d108280c0d200040030320b5980402991500d050000030a2080a00c0d1010400424208000440c1070507000185190011020b001311131100c01c2c0144200030911a9111240203420240115440f591031709001007071403030a42d000d0368410013031800943d10f480701c0d21a10342014080640201d8551040d804080355680190b406540038107440d00000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 297533264 1250 297532014 297532019
    0x12030117010b01090e0405120a110c060f030103080f0c0604031d010f080a1521050f0c130209040e010519061410031d0d0c030f1805010f11031201 64
    0x11503440c0625600c1100c680c541510003855907040902c41c8112196514101ca0b65601c0781003050402158040c101002100003460308036454008908603544140e14040f503441030300240c28000603204520740d40340c0c011000d100401c00543c03090014211190a289141d04040780b0034540e9107809016141140445e60701c5480c0d0309105080402841c0c003000c24039040e030f100400e007840039117200005483c01e864161550010704580c000680d1180043c2a40302c030b0700f08400420307100201007021380c4100300d801c1d00842130000c01000c00000c1210406070014a85104902b405080000035403010400035001038441d0642c1d061802c003072080c54403801e0390f0b07041880003510310307a5a2003c64490380c000c0d03c0360940914a203402900e440340c1414002d00c242c10300003255034407224414540c3d9640021001c980c800ca1500325001c6030300c2201340010078460b0b282c0915407107402c03034203507004181d1294013050a00c80541c100000e6100c2e645041c13441f80c460a21908121003100700a08651264401d01407202001c0c004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 297534514 1250 297533264 297533279
    0x403020606091501120f0603020a080609060921090a091e0b03030f090f0a0e07050c0c0103020306010203120a11130302100f020a14031c0b01031116031b05120301 71
    0xa981e0703c848a6045a888410b0420010f0914076102c005c84020780e64070490099142042c0d48100c0207580c00410922000e80e59001d566511501114058858018540415004400000d00340d02d0329240401e03078801c40e603c0b42c00d000e100b508292901684650400400a031425040c4952020b2030348103128180e2a0101200d00f105171380148981c580258410403001440c0c0e00c0c0182514001482114808501d040c0c1d580000d00360b407416001141000d000b0010700091702d400200600460509000b13403804000c5000c0154200d02048440340e0160300304000110800f1501e510496025001c440009114400803040b41000e0304400c0e840e03100c11400c02014030651400c001407000b5501a8900000c030981c003980300a4850f01015401414640031408140000c08144140c3e6000b400251400281011810890000d0407c0615050200c0c8ca0072501c028880c8003001214103031400d06a01d0141b41c0c44943d4211422985411462001c28805081c0380000350244041200e02d5403d0f1501e036142c0d410000c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 297535764 1250 297534514 297534529
    0xd06060c0311030301140904080d0e0607090906030b040308071e0302070b060616240c120b0108070f120b190312031b11190309080f01050124170403020606 68
    0x10800b03101e610610041250b4400c0e80c3c0d50751810318041e50307000000d440b540380030000d83c0241c90f25034906601702255050078140c0050002d124902598618510035a03425001c411101140000f400c05003210000401082c001ca9055421080b1031411000d00c0c004408951040390303a45c98404000b030f8001914005110800d6440b0f50080d000f01d84940c071303280310260400c14406116400030441c52005d07201d100100d01a010344080c1000c02501031000307422500c0000d0441034082d031481c420701c0c60040400000c0d44200311103880f400c0c3c56150080015480d160989010010b24220020140c581250702c2007900c3d119010410320215003189103040781589880d44000c008001220100362402e00780c0125100c9844c880312a45901341092003000c1840e0101034117003810f88003e1079011005c0440d40080560103d4034500300e030f91002c19181c1c0b4003060b0b1002400e0300c0d020300c00c0d402c040e000440403811490502c4a00e0038812110306141c9100340004000b1185103408480c143c0c0913030054401c00c42142003805 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 297537014 1250 297535764 297535787
    0x1e0307140310090b1311031008010b0310051003020d0c030501050906190c05160f03030501060315090e16060f0f0e0603040f020118090605100c0c1701020d06060c03 72
    0x505903400c0d45040310a518014149100d8036141c2d58503282c5080d0f13542c4030410704d5005042001000d029400781d015003010158010b5031403c019803030382c0c98000364164061040c0072044100038058100303071030660554009003034050441602c1d4844ca4400100503034075412280c10040c0f150b00d466240b14074505042d421128000c2105041350010b404100c0341703040702e100e06003010305102c0e000500301424500850301c81c0500c15500c003846080300c1c507501c00d000703070860400003662207594284440e030b03203524049080d921070000040b5081c20310001440307030f00340a400001d0000401b008480c5001c0140c80e02d0781c10020140d020714080b5121150741c650b0194000890708140b0711742d06088103040d0000c030225210b44070080014103100084030700d407000c5a1280240720022840b64586000540e16054040001d102c2d40c031034107115000c0e030100c1941d45070059141100280e004586041c0591401508040310202480c400039655400c2041d08c0300451b161054201408590b601c0e41c4050210333140180540c8000e9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 297538264 1250 297537014 297537047
    0x114190206042307120503040f03200f0a0e2d01060f050406050a2001061401020610030c1211030102070b0106120515010c06180803040312062102061e0307 68
    0xd00508011420010b130b00c200315442c0b0504121901c032603042060450190380c202407a0004c103140000207120041120261304030044e19003000b03500507841004150700301041f5081d00000120020003031f400d05000059880007034003042416440151a601116900301510b0007840c1014100500405034803007a01c1d00e85507a141081441e140c10001c010700705005081040d0100080900d80b85c10348031b2064400700c00410030100901000b612911f03682a481e1451120600510904001a1070a448400c403001200d0b00704501003100c3d0304107024007807090807a0000361011500e8140078659a10240300a2010500a40000c4215410050b0092414820303110030184141400184482d605420810340c1f41e80c4000d0030406004181c520b0228054807040d2146101e01842c500c0001c20b00c012580118860382c402c0c0c4d0740c00c154141c03c080303007401c407107090007810141c0c0c8440f01c00c0c94200402000b02424140000e2403039003842070001e6500d000c18907401d12441003003004014840050b800282618110424 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 297539514 1250 297538264 297538313
    0x3031101271e03030207150e0312091903050c010c0c11010305060d0804090b04230a051317030106020105060a0e04020d1103010c1e02010209222304050d0e03030702011419020604 78
    0x2072385032107035480c0941149195488089404600f03d5081000f80c02d80c5541c5254003840000301324140030b40b1580103103103515469401c0c048100c20b4184034000b25041c1d01e80c4245015a05007480d00110020031004000d00c1d04100003c1e50907011070440c001a20081c1003988000c192000a20f0030300c803c2d03e10481c902d5201c01312804c40f10340030300869081c4a900540340e260000e00d075034545001501e0b4950810014007054042c90a141041c2c85480c025030507140150001d20541c0c071250103020340e580d00e038814020392140c035802150051030b1000036480124001d0700215440502240040d084550040c1104081a030220032181c00c03c01c10340960511600d140021401c01300100007240030508481034034511000f10b40c9680300000c2c0c40c0d604c00d44015104901d4000c02207840c0700e010004120590702920507115002040014510580d03a1003e501400b030083c6040801580c01074034100820711400e011808107001083c2e002d040b24008041000071513000302500d00706410103039911341d50f100007107159031134 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 297540764 1250 297539514 297539531
    0x313031b0c030215120402090a180804050405090c1e010c02060f0d05060a080d20150f01091b050c1f0204050a0b0f040b030405151003031101271e0303020715 69
    0x5081780d4180d019405503940241e6541e200c3c20080184040c402d88074116071030940c0517040c441010090300030f40d4001c0d1010401c40d124295250303034500b00035400c9503020b01d100d41441540012400119802c90060600840080c85580041c03215048000d440403200808565060810014041c003500000f0640d003043c91141405c01c40e54681c10203031a08000e101c48041c80c0406035001009841800704c40c10705072414030b4901500500b4a2405451a004940403d80003080e68071040c4110000c84043c4000b180c600e8541003400d60b003d800c8614880d44038000c5402c1b5221245005450088209011230016620303805c000800416603695004006910814450a05400740b0300381118140d501305900c580d00c80d43c0760701c0c0c03880c9000e034001102c0c910011103105001ca88203040007141c0503a031080c0c071140c807000c010704000303405c0700c1005690960401416941b1000c084003414105030190040e07580544100034142440c949050b00d140031070001e0703800101c003010f01541150008110f84c4401060001d20b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 297542014 1250 297540764 297540787
    0x2d030c0c25090c0210050f01031a07050301060c150903050c1b03030f031810270317070311040e0a1407021b120f0c040b03070b0313031b0c030215 64
    0x407400e0044404880d81c45040044003070007040b10610b04200400c0620083c45c144203a0103d03220280b00841d048030076840400081160781f403c4611500c0c0e2603503100c1c01c50f0310302071040b5100d0f14004410b039103a2278001654809142036020381400103001e501c4090340e541107404c0172442d00880d8002c0003209410314250010b507035000f008a0700707002c01d18441b0580303a07110383c1840010105803500040d22440340d200c9504455a064102d40f16440340303070300407078802c440708502c2c902d1280d0400e2004002492440c62003205491404001303800410f145000101404489a0301500e607001d5000b25203101c100b5801c101002d029802000300411841d441d4403e80d04144074060341c0d50100d5107040009a07103595844403e9115a03d603001d01608600c220b4900d04c03a20000242c0b54001c03426078034005c5082035207006160800040318021228900c0e105d901d1986c8840c8034915030103c10f1412030400c13000b05000a101c0301d000381c0c1480407500a00100841c0c902d14810080c0c003c0c494201000c25081c00d000520505 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 297543264 1250 297542014 297542083
    0xb0906011106010905090309100c030207060e0f0d11040204060201060e010602031905030601050f0d0212151011010b040603050d0315150e12010632062d030c0c 70
    0x100c004c2c40b0f010039a0b48812000e1030840c020002c18036002851054142c5650364840346a502a500035001e83e0a4192130718000c503001c2604843e0743da0000a4210300723000f64205481e00008981c001c9404105507102c140004090760b10036881200140e460307510500c0b19083c81c6141500524460000314680f44a04580c030402080c0b0100c140b080c03000c08000a10b1990080c81100c980740e09820880d0b542d640350301d64210003500003041075401c004202000402c81c003860130390080c984400928240415082e100119521004540d03a0a0301e5503c4804211041c1c88900076600550b11510281c0040c11307408a00500329204503907041090742ca0034400704101c0c3c40718003030f9502c42000c0f13240c010441020140800c04101c915005821a0340c41c0c0311000400c150f850050925032000c40303250704043c45819001c40340c600310003150075034404030801559800403080e261030075000311404521014112030f06411403040d003044681c00c9904500041a9815a27001e002ba0403910315840640752003802001d50f030f030b54003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 297544514 1250 297543264 297543269
    0x606090902090306011707080303010e0f070906140f0c0a05010506011d150706090c0b041703070218090a05101a09040c181104090606084203030304060b090601110601 73
    0x101d55404800191b0820702100740900b00700012680d888d41d6401520240080441d0365171030280003500400e500910034400041114155034807035107400750081c803031505031344008a0814a00c0040040440e50202403100d46c1105007d80f00000385850000005003c604090304c692046c4010324005244070f41d11001c02090b07811014625a13207980e91440d0a4004001500015144201100000464051600041050324103d015a10346c00007084501075407030054404c025409a400c403010701c0c810820381d455651144000c02100d011910355111107080041062803000072507201d18154036046000e001c0b8410f228410344d0300701034500e0151144c0190800303c0c012180e501413818452130142d01c440d04100d4051482c5640300369150381c1c580723505000f00580c0c0701c1e04010a041e40b001861341d0300921400c1c00300903003000781c02946a44001c0340e400d5032240740c802c2500d007080641d0b07002c090f51010006903100c0e611078040000d1489085081044002008105c641003000c0700301c0c80c040100300468070504 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 297545764 1250 297544514 297544529
    0x617010305030703080406090b100807060c08030c0d060308070b0708060f03060f04020625021e01021c020a06090b06031e0c0f030c060712080901050c04140a090f060609090209030601 80
    0x5c1034071245403640180000c2000545001c0064040c018030440c070b95400c1c011070340b8080444c0c84452365204182c401d902e00d00b0300903300607800d00c000b0740c28845c004010f01c41c2c83b540103c0000c80e251240e48201e1a9001010152103400a5030b0070132542c2d54000e03030416040082101e52a0100f07400c640043d9680500400c802c5806560713101007411500c0d81c00c10b6855201e4040e8604003402c040c0000700c120404081c4090703204901c2c0e0143d07940608030720b84040303010a0040c1c1c090f01188801c45401501d1b000c01c00416421071090080c0718002c00c0c2244070f0009080d106020324441c07400c003481050718200201c0d80ba4211120001d050b043c031a00d00082c5d02c2000c3d04182c070302200201e40380f4000390429040f400c40720b80008c0c0015500b000c00142d80c908d0702c1300d41401d45a12001d5280c81143e0703401c0300c0301180d80d055120800c010600410085000365540c610b0010840103146481c0c1c0c0b115016191047e1091030556142c0341c3c14000f150304610b07400702500040f20b0860500d0090740010707590b198103114140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 297547014 1250 297545764 297545777
    0x105010f1502071206180b07030902031c080105010507030909050c030a0c09080c0f060d0204030302060702160501090611030c07030c06030b0607080405090403020f0102070807020a06050c0a061d10060617010305030703 95
    0x220a40d20f91003104a882c0c0c0144c1d10031131f80d19120402402038190048104c5c0b09010310f444c110742001141000d03a1105a5503610b2040d1030b0309103c010340d040e0744411400d809020b40c1c400000b45c5445980192441062522095920303802e01c410314500b51100c8121034010f00500644c140050b01c000280c404150f4403c5070a801180c80300300200c1c210b4800d00024021540c0006404800d141d00003030400d010360410b82c200c450300507804200e5103100555000d054009508450300700301040c440c241014120b039204040d13a00e09010811954541502680101c4071031200703042c2004219003502c5140c0c0044025140c103403030b125003a0343d036240038412402210b203c1e410b00e802003428503100b0413440c0a03030b41c0700b00000c42d0381d801c42c1e0820310940d0704443d100700e00c41c2c0c4050700c01107200c0340f03c1c005540903020040010305403000c40703a641d4009400c50b010031850300000508284054802004150350300910384500103146420f10400414810800d2204d050349285000104002030b000011501220703018580304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 297548264 1250 297547014 297547031
    0x301091d0a171b060405160806100902030c040e07020d020f0f03090607050a0f11210606010c020f150d140915100512061501110a060510080105010f1502071206 70
    0x1030303140d0f043c01001e40d28180709000411042000000301301200c40340d0205005801035440c40314075503034841242c401000d9038624004001c405010340203990400c01e11418607040545860f01c00b000040104c40d58001a4410a00740d40040c0d01409901a0740d450030001c0d0080c030301410f19243c1d49210310f1160743e00070300d00000c8030418040240402007090f503020201d0a8021454201400c00c590100c04862103003a11065210351152800d840e8400c4544104c0030b81650343d101d81c0151f07802a031908099070000040d450404d0b00d035550003450140c42e2803100d4207036125200c0c1c00400c130403120306004c142010644502804030040d000981d542024400d9050305200fa030b11070284d808a03070f80079030029800c019501d42c900c030341c90b80c08100c940c45900c0c010407051180d9100401110100b200041000b003d0300038000305404a613854001b00e0b03001515071059265a5903039142c490840e6407d900100c080405040140314420381c0c0c00e1840e01040c0c41d0310007040c0803401c001000314a00010840240000d030317074a200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 297549514 1250 297548264 297548287
    0x2010305182d0f1b0402040e04030c0c0504050106120b0a03020102121b0105010303030204031104062301032027060d020a0c020301060e06010201060b03091c02120301091d0a17 77
    0x402c07800d07a00d2103040c0d8510742c00040341c6950715040e0f00300154101d10191444007503401c01388203136411649200c00241b8030751900c2d1400d8503560300420301580c0f22802c0305400309598503140200ca00801c055614100e0516070301c03e2041c100d034a01008648903054180d000c10151380c1c009174817007030340c0402c005140d603072203000c80d081d1100f109200c40c84015500382000002030582503806001140e0050039a080c08004400410044400502901001d07080326061040240701c00410141c3c80c010605001484141c900035800b4440000d07010711800000010302d80310003c0300c0e000880503101003c4403c203044900c0a000480600540902c041d21580c041a624102e52041c4074002da000e40240c020041141c44040c9080869003c035101c03805982040000038141c0c2000c03044074031074500f100141c1981c0031001e5a0340e030103052414040c0c08610a01c07011407000c40386070000354003c10a201d0005126810300080c2e0f40c030f0f0040c1080ac200340e43c01c40b030310300c5c00419401e4800c045001741c40b00f141a079500d07a8410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 297550764 1250 297549514 297549583
    0x301050c1b0f010606050417010203070c0305090f030303010f090e06040f06050703061d1015090b030a0212090a0c21030818010e03121609060c0206041505070201030518 74
    0x158030b41c403036007400000102150400c0085c4160358070b001520300b40c105808940342c00c4c0e10043c0d41d64800506a440c0329800309210740043d20303012038002c1003047c041c914440000c1c55a002a04144000f0742c900c6400c200d50703070041c40784c802e54a5002010303001610382a11002c4c0c6074040e00102510160700c0720000340c1d817070303110368400006822402c50a00200e0541c010b004885034044590b01d113010005031000c1000b998600340c10441c01280c0d50b079001282d09040d40350205400c085d0008007400d4091001a82e01c10400c071015202d0316149c0c0083c02c000300c05052460000040c0d5001d40788600b121004071900d9840125142c00c42900b508150426403145051201200b040f24044003080d441c000403c85c03028804030050455516940d00c2101e552103a4624043c0440b010350079002103282e0034402c00100d8061180b265189000400c100e041640d904840e140c620600410b8030001480007400c0800c40d81c00d482410303007000560329002e408000b186280f035990340b109039100152010a04481e240c0400300309 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 297552014 1250 297550764 297550783
    0x7060b0405070c0b090106050631120303200d090f061503020103060806061f0201090507030b0f0a0b0a05040f0b04020a0903230606010f050706091b050301050c1b 71
    0x500402042c82c10400080a035481102c048a2900f1110701086160f0814003540007a180700038141851708402c090840703c20030b8907502640c0040e0001900c518540e0341c20a25000030851042c00040501c8580b4004007144d0000c10111490341854034008040b01210302a1f0380d91000c0202d0028070300d01c1c10304199040c0f54019000030315040c00c2202441d10f0000040000003128400e880034403125850307801d059244c013000c89803240c21000c1600b800c018404481819000300d1100c1c000000c800b0001e0302c940e070814809800a584480020f01801000708198280903800f2000b035200300603075011800051080312092292610130341c0c40d2400100b441806500c4a041002d005008540d2131070b1400026105074464441950444003010050f00c030310144001640040c20404090582035540d2401503c0b6003ea08914204000c824880d08000a0040c8a8040110b000d038080c822800c0c6200308070b240c1c400d025003105000c0d90400091000300d40350350f42619003000524000e00b0700403c0c2206403624010129 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 297553264 1250 297552014 297552019
    0xf11010f0204050a06090b070303051e0103050a1703130215130e0106110307030f1404080307060b1c020a03110d0203060a0b0306060d0b060f0105041701050618060108010b07060b 78
    0x1885010a1038031a90042085403000d6442000d40c40d950344080e911544940320b4100e03440002c100d00c00009110358495a071100014128a01c0c2d49034821242c1a0354000740c02c01c844603032107907000200703200c00d042d0700f07800b24400e100381e40b45149088182501d41e0b080c0506c0c000c1c0109102c03440318940300c04180c107540311071a42e04028401c0f1982c40904000c218020312410002c50312007107402101503004000c40c0d60044d01500c0301584c1c41e1120308220365511949da0720465640f018080030585440c28401409024046d00021075810369030780421010a244501103404071001c03c10780c5005031240400501142d0f0803603800980e1002240c0800e802c04080c40000307601d4003c403800c009185945900c0310004041c1602180c1260b034940042c0604c0031000c2e6400780000c0000e80000e001c42c50b00e15000018020185051410642c7e10b00c10508000407007d0308500c2d0741d4443c4100080e6051020640c15040e800c00701c44813050415200183c646141030040303580281c0c0005105050048a820080c10036401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 297554514 1250 297553264 297553271
    0x15020c210f0703110103090f080a0e091e010e070903080904271502030c030604020304210903030210270c0e040b010501031b021c030b0301090302071e0e06010f1101 72
    0x1c08240c140c449406020032140001c00c0048100294802d00c656910720ba48400c420900a04540750f42c101c4d50001c540400400080d0703400980d403a01c401001c0ea01035a500d1154091110031040345512580b8141c08c00c403c0303c00d56208010100d980408044100c94000191950b82c500a0340401d000d0700707120441c07201e00202d048102e2203001d006400803a086010740381140c907000c500f0740003a0580c4025220a111404d052012038503034600340d8011504948a62660551024416071254103e903880a40e0808545003842c01c2044c9501031041c0103e40c810040d00b04080c4618140490301130101e810040c05000750700b0f1414007003003102041900035084141856890740b4080c98003140503d0240101c2d400203007001021582c081d04074501c00e80810050700a8000d07440a40d110002200d103d10700707902010380f619800d403a40d413428841c1300600c50090740900260342c286000310140c0d8840c0c80300c0c68004804284108601c0410b818042e0700401c091030f0000389a15403581c1102c04900140740c41c0d055519 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 297555764 1250 297554514 297554533
    0x61806062e09080d0804051b0d020d080d1103040203060a05070504030f050c1005090315130209010b19080103120f050706050f0a0c020d0c111807081015020c21 70
    0x10003006420848003a182164003410401500716484034041e500101280d1000d1000c4203005c5203238804c0010f5900160080c942c004a6400180640945440c241e808000001e40d48242c2c02860045000318038208070220b14600b0664003295a03900c008003a03a500a030342e0000710303e05620410494004507004100d80051040500f820303a00c521303074520220f10459001c0c0c01074001074041d1040d2503040030001e0141c418000041809408240b00900c4100491039280c00c840c01681c841d106c1d14060036060458039124404980744945544850f03c0c00742c2801202001000014824082410501d00b103151110040b003581e05d0550742030080b480001c002c40d05083c200017002514980d002d102d515503038001d0008441d90308003a03886900354040b130b20025426014410205e949400c00f050b0049002d04017554004140c2c01c0f04403542d07400d5994900003100c2e1030600410f4080d17041c0715009002e00c14100f18140301c0c4000080c2da200c40d1502c565001d2a0f80c800034040072120b1110f000c080e1038000d01074070040d04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 297557014 1250 297555764 297555767
    0x15020903150a021206090f0a0f15030f0203010f110403060c0507120804050d1d0405100f0b0301090509070501050405010f0309120c0209010801050f0621100905061806062e 75
    0x4020b194070409031003c22000603020b15002020701e02448408505c44c3d0242c60342300303d80c0003602d82e004842c40c07034030b8692810700d8503a40488696030040d40504201d202d40850340c8101801d4030142c1c1c00707402d0341030300700292112a6810402224101c9a01800018400035214800c2c1c8150040050260444281d0340c41000415000b0050900c85c07407148082d248248601e11742a500030743c3c3c00300c0b02c1c425545040100d01c0c07281400da00c200d0b0800c4800d00390309402550340824031602c0c0e089400c1034100c494003000410650b011401015048500c001c0641720090400d03000070014061803141c00d0410402425842c1828000d600c10303120f045e000071580140001169014080c405d01103070813401000720400028200c0818850720f8021840b1011804150311000c00b0080c401447c40c054100002c98542c3e000782c10081049040c9800603814008264501c09040c1705d400c20900500c02c0001e0750043c50000c5c40140701103400782c4c0c40700c2c04880c156080c180301440f0741b4081e60a0243d0b03160b000040301c84910901d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 297558264 1250 297557014 297557017
    0x10051303030e0a0503041a0d051f0b04080303071b0210020c13060807031403040b041e08030307080612010603020409110a050a060215150409060e010b030a15020903150a02 75
    0x54041d40702440b0861803200b5141c0d0700e100010002d0200e4109100c20302580c100782501070b11003c2c440f03a005090104056a84040300c006075546109401d01d002c070341c072410780e0303000c40d038401001071500c09403c0c540342c00c654035128400204030314100139024526921407048111010945a0050031000810210240c065503805400200502c0358901c1070324652401020b0140d60103450761840903000c0c1c10b283d542d40082c44050898481142d010602012a900c41031601074001010006140c21b1211940460201406480d8000d201c5c030360010400c100141d45c014821980101d0203442440540c45030381603481c010300803904029070003410143c05505124400e9005091054110b401324a925655410010003090b18402e06001d03812080060880132802d110342944010807042d11510036a10800003000c9658800085846940d602420b00300e65109200c2c1c4e45c0c804906a0081003c02600d8860306281c038a4810840301040e00000c040301c054509020341940344031041d91904050800707c0001000c1e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 297559514 1250 297558264 297558301
    0x1801090b06040b0d050309090a02090306070207051938040801090b010e1b070c15020d02100e210f030408030f0603070614030709050303130611010501060e0d051005 72
    0x140d0810340e81101d81d2a03c1c070590204541e0040043d498941c01c1c0c014412309010040c0107840c81c80d800c0c4007003901914140455441115030703a01408000f41000704001481c00c41c09030780b11030641440f206000d4044c0c807000070100c0c40603440c900c1a911311100c0655038003101b550703c0c0c104481d070041000159100150405e0140c0c0b40304d4042d00700503a80b01c10b002c0d680c40340c040b00e5528010248410103100b240c540d10007000c14600901030922100d03111241041c01481000000d00142d00c850030200110b0b6043c0300c2c03440d020380407400c10300c42080e880c40300399a82c100107100c19108021810001d0b8185544504541001e0402c82c64161a8505403d21030b03401d80044401c0b544112103580028041e1501040110540300b95840e8541000c40e6042034030003a800043c882824480c4401c400b084039070f4104040c00105141101c07104c2d456041c01001400308621032036139600b42c0c0c10100144606a00300711811246007003175400003120640f43c1026480c1505003101107580d0761034007051105004100f0050406e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 297560764 1250 297559514 297559519
    0xc0310020c071e03290705030402091e0105010f180e0403021006031208150406030803090d0c02090c070c1707030209162708010218030706080c070b1801090b06 70
    0x94039561108440c0c560b0788000094003c080740d078502400054002c620010b030f0003112080141e010405150481c0d10890140d6054001c02c00c08802c220441c83c21102d8260b000304010203071814040d04a940d20028038060180506210710007411032003d0344552060440210360443c10b1400f40d5513402d134122141c80503103003540140a60009584e402c98140604c90440c0d500286840041040031012282e240c0c2c05403085025284845001e07913182d8860141c8000b450048498035601c3c1400c0704a0b500d4030145260150a001c4080306400c00340c1e6800d103003e5880003100042c0b50303441116107403180c0030030340c1c0b600860341c00c0c1e401004604201c6800507014050780c0c0b0070b4070500140e8641c0c000c1e440d84030180c42e9410000940640001100600503492403410142c560b40e0301d201c1035100c0c52500d0a90b0040c1c442d08a10051301000e002e140d10b000c10000005060754242000542485070164445114500000c0c010f24120b5000c00e403d041c440c00003c03005000200200204ca01c50f00d4044400c41003610324a2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 297562014 1250 297560764 297560773
    0xe06150a06020303010e06010e0117091005011203090504090309030b090a0b0a050112060902040b030102040b0c2e092d030e0910030b0603100615090905040809120c0310020c 76
    0x7a850700000403203041c1d4140400442c00c40d584d850044403a00e0000d1034642c1084522500200e01000f0301808a0040c101540a050780c080020005811108142e100c0c0d1805080e441a14010980040200d000c0da0026500481c3c0303084075060940e4508203690004210021403020002c07060300110316030407814411441481c0039111030b480f4000390b510a000c0c80eaa840c4070482c000000a099502410b0164030180010542e12080300020382203030403603030142c9040038001034804800030043c4417403648251001400403100940d10309008800388882c80c01c20321680d6444c0f94a06210034004041c5800740c40d81e1a28030200200e5480c40469080e0307003000c43c0452082c12008120780b4100744014800c0501056000341c8502d13788802c0d401150142074160035014903c0803114000440c00783d80d01a00300408072240d00e020001c8020001c1c1030980c400007410b032070b03c1c05110001d0703243c07800c8818400c0304403000305940c507500345e04904001200316240d034540704464041004401c16005041c0342806502582d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 297563264 1250 297562014 297562019
    0x8030a0e010c0c0608090f060c04030203190b0c0304080d0c0f020607030c020303130303110c1f0b06180f13051e1915030c0303050409051e04030e040e06150a 69
    0x5551101c00110002c1c003ca2034000240440c500c604501d60f4092000022520310820300c880039030030030b9002c3d5104808085c0c000340c24400d606040080c40c00408040c60a00d03480341ea02e442e030866408014003800c0d0f100c240000450300f848120000d581664028510401c0396200820010340340d03000b00c04029000d4003a083c005030401d402031240703050300a180d03006986035540b21070407201c4000000f41e0480606580e251f869141700c448001400c21800000024961000c484020456103c1c0203090388401e0340c1000421411901c0d1102552400c1c141e0406040c51030380343c400010880300d881d0340000d4225502c81a800b05124854000e079000350102d0812046c05414100c900f60541c400312010418591070550b045040c4101c0e034000c254248200d07a9641d00e5a40769655580b0061305a03006800103140442c0600018407148a5143c010007030f610744000720409464031541d1b0b000c00510207814000c00c0040701e4040d4603260000c0050f0740c0c4050540b0043d144c5040310b14220410f09140500850201001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 297564514 1250 297563264 297563267
    0x706030c11010209150a02030c0f07050a3602160b06190311060711100903030e06180d0507170f0606010c0507090905030706020d0507030b0103060501050a030f020c0708030a0e01 78
    0x21949a00e001905c24603550550840340052031b03000c4141401144020031031118a400e0900c412024044c0c4640944011480c1900300304245040381c106c40c00b40c0c1e07280d204c100b50812403c900d481d40d100c180041c040c4070040da0340000c0c00900640011034401c4c80c500d400c2104100101303a2140c82003a085900d2000c5403001041004541c00c180802032000110301140c108a2501d20060481c1038803500140340101c0c5c80d200131441c006051400e0740c0c08500824800e004040d0410a2251074020a80e002810014000b400c0d48440840d118640d0207005201340c0700e41801814030071840a019004803c0b00c603081c0c00341c600c3da55a400d005603031002e030203282c011952541c843c0650312000f9400c00001d00300541031038900300003004944401c6400f0f101c10000040025a9800a0642604440c000003020310b40b884020741070301d1072840340904052400a0501c480d030b03001003ea80702e000d40ea240003c1c0b1003075002c035540005d11074504020b80038481c05c1e00005000380004020f00c0071404030fa81e801ca039015042d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 297565764 1250 297564514 297564517
    0x50309010606090810113001080613150e07081b0607111c121706090402030d0315080a0807030216180f0209090a0510050603041e080c0706030c110102 66
    0x740ca0301034002c170141030102e03052900041c00e40c2d0700c2074000d01c1c038003d600c102e90b807803403920a10a0302c0b0b58a10826040400947d403440d01e4018160040982000c1c9010b00d0b2510488400d00070091407000380300c50104080a00b640011000c0d84500101c46245803a840079950b9480c01514203480342224409041d12410700c4c10541d01401e500c4015004070441001c100184480c020a40a0f00e0040100c0c090011644044180401304180d80b11403120030340c407144520101500901e00c50148000e0014400140c0300000d01c46c0d40251207250016045985c1041d105220111390b10011081c810b03410f06c0018090400e00030700c10a48650200e0340103190300030800782c40c0034a074420a2910140c445002980080356049900b50680840c2c0040c0380c84a443c00140301c101060b5041c410389a41d52081002181c0001c040d20054581124042e00314a403c0d0b5416034008541d8009607498000300740018100400402500e0740c05410f40c0c250b030405501c5810090041480d065000009010342000c0c101c526010310 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 297567014 1250 297565764 297565769
    0x608010b091501050706110310080109230f03030109060f0e07050702151b011407020a0203250b030702030d200313020f0301020d020903250e0415050705030901060609 73
    0x2051044035075110082e1041e8240459a03070340c148001040408001002c0d40308900000d40300c41c546644a092a41100500344000c0d00100c640ba07251000d4000400c030001c451400e0140001d03414445068220f00d41ca0415114a441000c0e0340310210001c105114990481000c0d0b690390750310000131641e100b805250700741003540c0c0c04021860400000c009420015500307120f40b1074800304940780c03192203008408542c2c0401c3c884044d50f59219042c0c001a403125031090b4011215200030022140d0540000351a0704041004da00c8480b0246a001012282100d442000780288450207407203150811000e0744a61210b46040110b620340805005200d44032941200d10307420300c1c40401e05554031180003002640008d0020780c0d000820161201c502e82c2e0900040008900201c8050303110424075050601d010341c000a1043c0783c0d100721001507144101c0c2c0345180d003141c003444821000ea40340e508059140c0f110380300b0a039480c1070421003045202c54210005600407003004001301700641d40d44c2011501c407140350 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 297568264 1250 297567014 297567019
    0xb04180c210213180e0105010b21040632010e0f01061128060501090516200114060f0d03120207050c09091f05060d080d0f1109040608010b 61
    0x321440c41200442d4080c00c44540386901404980da00c6113030211002c1d1460034402a0141c5600d404a003104c3c080c080d207801007030301d01c180500b40b40c04403440342d00045202c8a51074030000e009000505100564100020b0b004440d0364425140c0c030032080d8401c03840744000c1030a203d00d040400014100d14603041d0b503071084a5200a013580c81c1d0034068211426807228145100a1040d552005a00903042294070030b2201e00c2c252440c1040280c0ca021025150143c0c4610900d514010802003c2d8a103119003604c0c0e40107a00d05082d5209002614000421003800150440c2d8608025885d0310302000030030900410040f11400d40b04c008000400117400d45240c0d00030009020701186800c0052160007901c0a584130b24190b501c5800d5480204500d072004581e1010785d640000840b00070090501261401c02d00c814405001d03d04c1c2403030101d50704000402d07004000b040001a6001b0000056015800704a41000103220414070b42d0b51b001c0e0b0541180e4a0b40d1b21891070500c0004403104144601710103803002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 297569514 1250 297568264 297568307
    0xf02150717030403032a030c090311060c160306140612071502150a050106031d030703180801090b0117160b030a060314031c0507020a060e03040b04180c 67
    0x365032200100b074001500480c2490340b95051110030002c8840d11060240d1750710961150800f0041d4014207454800350701e1000d00046520a1002c0b49244010718088070043d140c103580c81d0b08145649140854018107011002807554012007007052640020011040c5552a080c5503241c550804c51144060342d031840d05544601020800d0505203041d0114025150040d1111468144030403507440f00100d529070026991440144900c41d0540b2400740684054462032070428816107803681c4e00e100b504005001d2201d96110f68141000c14409140030389500b00080c4549840b500d04154115401e0049141c50f00c890011890410000a280c3c100c18000c130040320348042c645807000d10580c1c005000b400400d51141004004110300c0b500d010060084c0d400295a40c000e99a001700c0c2d03000b011007100c0349440c00c0405004400350300043d0b040c1d80503004400050b81e92807030b2142e02e20710300c035940c000c2d02d8101d00400e00050845041c0030a4400c554503003030900c221038080300200e40c030722021301c40703101a80380 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 297570764 1250 297569514 297569543
    0xe15090c0a0c110a180609150b0f0306130903020d0e01140403020906060d0603030801030506060a030b0c031009240b03060a0e090c09040f060f140109020717070f021507 74
    0x7010f121500140009010301801c15180c1601040341210b80c884544042c0c0c0f1402c0810252140780b0403550701c0d0200210440307459041280c21280c41c8a0003042b214040804408695195a2000d4114507a10798110400002d5698600a516000704400311400305100c0d1080d488103500641405401750030000d0460314260955007004129503002c0d0040d608010188a540031043c854441c1501440c00781d1650210340d891403501390705c3c02800a0549015800c080c41c200005406907202c030b500324850084650301d82d0b0310448141481c1401d170348010030f46800d08951020000070402041000168040080341c05910b03000301d4002407009850464000f10701a00c00c01c80901d2281d9281e4000c200901683c48142c0e4030340008280c620142d40a80e104401070415804101c0c462141030041a44090180070940e5801031049520341c2c14890b20406540000b10311703007000500c1c2e096107004a40940285d80710465403d06071018250700d201203000b60a0642e248155a4240c01501c890603800310304568130b8103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 297572014 1250 297570764 297570773
    0x160912060e0615010f0c240902030f0f03031b07051b03010c05070c26070803212503021b01060306060509010b07060207111305060f0103110d05100e15090c0a0c 70
    0x1b003071204141d80902c1c18092002d0600304101d04034a000140050104076580c03907004140c01c020f000303001c11261b81e005038a00300340500b001c402d40b03502880300d0356002103900c050460105c0d0340c42401d00c02001405020704d10030500ca1040c8a04903206403d500810510750490825183e510030480d0103003c4150f0880208048420040c81050342c1ca61442d00206c04008440660329010140c2c1118a0300d410120f096049001c0704001c1d45e850030b82881d420781c41810504c0d1007a5104c250140050441c02d0305080c1c1202e124000c0c0c04a41c41c42600c900c18000c0b118800b80401d000b0300c410b0004a0b01c807402d0100004840ca08030072410306a1380081021841c041180c0d544800940c400f0b601110070311700703401020805564600e0000140742c505803021807240b9140041041100d18540c101c0d05042c503007044c803640c400381c1c81c081e106004410f903800615a10f40c1c4212702c540207101d600004980100c0001c00411084030110642401c0050b2002d540da0345420042d00414001c0c54800030010303451100301008107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 297573264 1250 297572014 297572027
    0x3051618031104060305070b07050d0c02060313030203090d14070b0703122c030912030f0403081303051608060a020a051804060b0310080c0612160912060e0615010f 72
    0xb5500200001416540da90b0703602e080840c1c0d81d022402c10000410b402c024000c0a1014180008840c94502d04000d03080d03000030310a0001401e8001141e10b80b10603074003094003c004442e68407400401820070441145404040c0040889070150b640c003400304000b072042c9135481aa00001d0b4940c4512000080300d95010009080300c00c5141c0c040c00803d540c000c9151960200c115111074207401460303450801b98140460000098212815680204245182e1192040a0320b05032940180580e903619044d0050010300081900090240d000344068051420b01d08101d0380100c03031041e01514625500d20011208134000c17840c40b80c001c100304000741c003981c02c000a1607040c003481c01840000c4282e119000441c16030001c031264081d54154003000e12332404e0420840c0000941101c1c105c0c07070400190f100482500015000d003180c03003402e10400c3c4050740100344820261007162107080c400c62003814004043c09003107064004500400000c5000c1d201c81410700c245003d81a1a0460001c044020442c1c80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 297574514 1250 297573264 297573293
    0x80f07151704030f11070f060516060f0212090a030801152601290d021e0705241303050309010608031903050f041e0201120c0305161803 60
    0x10010145000c800407008014900c0c00356000390348131101d1450340c000c00303061001000b038183c00c4c80d44040c1040200310429020035041d1009490301688564881483c854102d80c0e501c0028131090130b2411040300f0300300715400380c0b004018090210005440b8600445c0d12068003080c050300051086005101074215403541301c0100c0e4803864401070010300840e4051034403c8541060000314203100041085541c21261400d803886504107441441d000c0300c1e40c07902188940c030103641404d80c0104400c0d060b043c0781c10409440c884d6101007540e49003042d260054840900f901c601491040c40750310014414007610340c2c51f11651203c2641c0300e03041c0260b1001d440d150001400c1415a41d215800031031913081c18000b5118840380705d46000b001c07200c03141001c0d055650040c011065446c400c410080840c0c00080003004840740c2d42c44409441060340012103c5a6a105400680c3c60030410220400355055000d0307071182c880340c6507247c0d500c018600308652010000b580345201906000c42400441c80341e0704150307207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 297575764 1250 297574514 297574517
    0x50d0c0501080402150304050a02010807030e030d0e0109140604030822031d0315180c060f0a1707050306100807020a0623040302101407140705010605041104050307080f0715 76
    0x10345000e141030074401b130380112400c545542100141c2411960484000352b01b2421606060000344c3e84003c040d5940c0c01083c0500074056200c04200302940029440200102e07040881d45000c110010741c400c1d920b04040e81d0031000034603031038001600e05001408103004140071411004050b0042d407400c951001c0c4002884261400c003151281e0183c0d800c0246461401401140303103060b1400403c2040c01441e40301c0c54013083d0b001441ea0b81d20320359aa03403c581c00317400c0125009850b000310403821108000102a1900d5102e00032090000043d04500914400c48003120101f502c0311400390103c607104420307144e040c0075034450481d90002820681041d0441d42c008200b200d20070704484601d5030202000e41d82680507070001008000c00801d18001c40e030300442410b0001c012130400680c02898083c640c0582c410b5440f021500004100c0d0a4000d0720003094000c00500080140b510503a00d41d038428440c181c031901c640e80e80019074600c04101c9250700440c160142811520307054410f510f41c4154503c071300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 297577014 1250 297575764 297575779
    0x403030c020a08011b080901140103080a0504080d0e042322050a230106080303060603091006091a030a020603160512070f03050f060d1202071d0907050d0c0501080402 73
    0x3c035a81c00344205c202e0b071400340d00c1600c650581e0320070103031804c50003030100051307641850500707885075541d00c0710141180c0e0300021595540140080464540c007171a000480c2c503004510301405215440407012200342e808035007c10418010b134907001400140d810b00c1c01944046180010907450300b20b441113180b150040700490700c62545540751402c05005240c101c41c1120510004a0640d04603039225072032100c020001c01400342000f490a0790b03400020825803280c0000400515030403800d02408660329010001440038540700d500c85000f501042d141903098610010080c0b0b104e0bd0001921a14103402500040c556250103503030381041caa0251981003800000c2005c0e8100c620039000c000e03c180256030710003c070840381103402000d03180050072032089100240b00707000c4696070310408200003d40c4204d5800c038005224100780c2c1801c1c09075001c04a140c821003075a15072068103915a5102d201d254080d030300c196844400b002080c000401000e0300240701c648080c00a540914002908507000801c00d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 297578264 1250 297577014 297577019
    0x70903050109260f03060603060f040c020c030d02070b04090b0307050d030903060507050c10050a110c0a0b01060c0503120a09080c010b0a09051905040c0504090b0f1302060403030c020a 81
    0x98203490365440b00702c031000d080c4056514280c8180008186040c01004001e183c502001a051a0f5000c0640310a120710f0000020039078580d0340625403141c002010b0014088042c41983c043e4464010024450290285002c0c0001c0d09201103080401d85910140e51800d0606003c0c9007001841030b540c0044d05032050560100380c40d5207100c0300341c034403a11903650070094038210f01d481400e03114041c04190074490140031344501d014001c40d17140c190700300b02c00c0e00055541d0340704402c2c006401d81400b08080d040e4009960040d0000201c1c4110311070707020740d111150710390b6035032011244011070303e4010f02241c206003c4079102c0903044155513000702070740741d01240403d07407500e500c1010750004035101c00d56951a80410744a0502038a03a800400d0908801c120b140307003180e0b5640703440703401e0b900c2e21121942d00c1000904204001c15a417000c0c040103042004038031000e180c0008226000d980005801e044400020860060b020f80d03180d03035035805820b0b00d003441c0c81c0d55420741f035204548004036402111048003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 297579514 1250 297578264 297578273
    0x60d030c05030c1c0306060203160201030e011401061101051b030f04050106080d030f1a2b0605040b0106090f03080a0837060608100e071103031005280608070903 71
    0x1d640a51038604810303200c0d5440c48080c044403001e610035004c2d900140540c2b00007089240564020680a09010030941c0807004d00a004051240b507080501150314000f0030f0107a4041d04d0a0902041c2030001c0006460740051041441458064040076420410001d03029442004485030043e00c20400829240c1d118903056041809008071140041c0e600d140c0003207200361318051a00e1014a516030040c4102e03c80f80400c01042d900d001079002d035011801d044683c06c00301d5110030022900580c2c200007600b0186800240d0341004e201d110b000541d06c0304046600c800001d42c400440e80e1200c42940340584100781680c14034001442e0312070510004508020780c00100b10101040000d0185021807410700101607800c607402500041d00f0080003000b000540300391044d415041c4c800118513142e545e03403086800ca6010b03281d0784140da0140004414000740c01e842003111026a5001c40720a000010803082d040c0340407101d2000c50000300071504041101c0c50142d00310b540c0004480c5085a0307029265140c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 297580764 1250 297579514 297579523
    0xf03060c0909230717010b180901240f051204020a0302030312040606080106080c1201061d040302120313030e03030d11120703020403120302090a0302100f0f0503060d030c05030c 78
    0xf062005104034100c2c0c0324100500420300d0b40b101090501466808101450580208050107041c01e4035800003000842c141070301c100d072026405c0040000d0030740c0d030b120031002c0c0d551250308e80c0c0346201c0f541d881d413610031560290018104540d6a03588450600701c010307111002d1100003a0050360400b0301c110002c40035032000c0c03004025034041c4000c05803ca04042c0341c4030701140d509030f0004086900d030650900c002a0f010441040d660310444411011071180e41034140140300560201d01d240e100c0c000d41900d43c03030848000501c124000d80a1324591030610100309003a2108868030120000c2c000030a2000034000d075014650301002404481c00c00304242600000c4410001e90020300700404504040141652003c590780900140b40960403d80340d42d0b18161111200c01d070743c40a1613008100045c031a00d82150200040d034009240302c00c2811540009012481040030030320004001c0c00b480c10300d2a018100326401260082c00b241c0c00c1c1609030b20100e800c5640c1800803682408108002006140100b1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 297582014 1250 297580764 297580781
    0x7020913030207080705060a201c0e060703050702060a11010c0504030506090a02030a08031302060d0b010305060117181204060f08010e2211040e0102041805010f03060c0909 76
    0x4660140103603040c200640340001caa4056040c42d4420201030110340c5514050300c00c13000b00d41c1003808105001c0d1041031000d0450351407c0d8031034410401c40070300803049142d0408000c01c894030703808095252503080c01450721801c0000307400314600b08114401424418000d040f009002d24046640300400442182903c0003000b041d0b00290b40401d00344140035081c81401d42080303106004080300d498980c04070740c84012130070700035010450210005202d00d942c0c89a4144840e4010602503a42c0300307242200004204405036540003902e810000703007555010b07206d00b0492213901c40d00d1560990701c144d00e8980300c00100c07500a102c1d008001c6a40700070724001c0c000c0c00c05410b040e19000612404400b0060080c0d005a00440e82c00741500300348503143d5103c1050610440d240c581002c2030a00c1030074080700130640c5103c0c55400a251081ca8103010324103501420584100314610142d0081c4400d040f41074030400c1c040d83d8041d54100c00b00300000350320b9500055485d070460400c4641c85985000700b5088850b0300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 297583264 1250 297582014 297582031
    0x150b100818010e0a060b0a03053705120a020106030212030912151b07021305060f042904110a0305010306110426122701021c030f02070209 61
    0x8506001c00290101204504444800020030119580385900340e9541070740d040280c40c880e910682541c0e26128a4407500c05190494110b80b000650401504115040b0807492442c03103401007031846282040680f82509103030081e00800104203a0020314000ea4441d4840200355940c0340d90002c01038560048656040c000e030700145889a136a0700500902c1891603003015040c0d040014915076994002c2501d58004503401981e20945a0100b25050a41300e200006903012503001980b0011494a800c00da01c102c4066504464085104040c0010340f8005a003d40205141401c8030344011400300801c400888010400724134044040c0030b411481d40400e04600c0002c0c2c4640052007480801c3c0101c0c200c0c14800e810710751510f49012501c50f40078070b05c4400342c0c0c8502403243c1d2034045c00b82d04110007903d0000c40d5900c2d039594011000d40c0390309001c0e1000c010103c2c0700d007030713902e01030640c00401c0801c10703000c1c0500c107501d41b50b0889804400910a605407600055424010301026848006149100d81d284 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 297584514 1250 297583264 297583277
    0x30f0b040e0a0203100b090103060c020a1505160e0a06121b050304030e010801030c050405060d02190302031006210602040b040f1707080d0c0206070b04050a12020d0903150b10 77
    0x380141400c1210780c0b6041a911760802c0310030616901d031202c1302d034112030308010001001880248101d00304015401c01405071890010035012141c0103501036801060303031150070003086103581c4040c0c81c0109204011030384940c0c1041c0c100031503030040c40c001c4603146545400044540c1d0b40d441c5000044543c141c101d00061002c0100020140c014400706414902428000203d6245998100c28048a4024540a581c03140e0114840351259181c283c0038550040414082008010700720005590704d200591103407084001e1601044494231501003540c04a62503d4540c038001c1b21342140c03d801c4505c046501c6a800c20002840140d01406030000d010840071040103a80703010305221071080b10521b110301300c0d00304500810554100165214003401c50341464407140400340005400c5004540c40680540c00005c1003104100340459440d07441440303010039210610030080105e940d0400b040d103000225000c081d0500200f0541c61410000801411010135442203020108402d074460860802c04160b9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 297585764 1250 297584514 297584533
    0x319030804050d0c0f240e030309010f150e090708010207080301060906030216060b010504082b02031603181706090c0d03050702041d0316051506060901030f0b040e 72
    0x5001d00c3c440f00b071080c40e0401101e07400d03846440716030040100043c03810380d80e203040e0f07000040e013000002c0703449605135010416014021140c980307030340c01142c9040762075182c91844070f400c0300c807849076040c0440400820038905042842442a00001500c019028481c07003d0009003028240000d0071092302c0b801207180c40b5458964090a0030800d170300700406142c01844482c88040f4180c0b210841c01c0e80010000c1100101e00c0b0050b1000d1041d50018807190150640a000d06004103021170107406ca400d44003036488900c0801281c0741c2c0075a8464144202000e0640804203201e440181380599403031a601088a03550061601701e09078041c1101d601d80c00030703400c02600c2c00007408280341e00942651005c3e000d007480e9030002c00d00c1c810b1600080c0310b595100c1c0780340d40c008107290307141c0142800d40003101d543c0c40c4d4000160000d42d0b61a0700c212414441c1c001d00c0c03200d642e04004c0082c000c03c0e000c1c10580c2032140300da00540180c03600c010f21041c1c02d550381100362500d030350354010801414a01e1014007103000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 297587014 1250 297585764 297585773
    0x703060305030309010606301e0c02070806010f0b040e070201021908040c0902030c0417120301030c0e1608010b0702010e09100305010623060a090902070602030108100b011b020319030804 82
    0xd00784024401e48886810345405048105100714403036a0005400048107070b0800000c81c90302c480321035604802e503e0b04200d00c074ac20303800161a10540703044008445d402c0ea84e03a100b8000c101c00b180900240c410b4240410000d00c1c03002e08803590008054000942810169968481c0d68900c40d0103040020342c004007130106000e0008000301c003400c1c41500a614501d41501200380e90701ca01d11400e92038141c004405040d580301409981046000218120380c0d030750303403810a0390040d0301038001e0f091002092004140f00135101c80c083c000c1d01c3c10710b469501e00d5078a0034004004941000c401030b4188420402070203083c1d541d002c4003e1080340484c164445641c01c600b049802c44503e07800c24941d0649642c080f50021095040843c40340d0300844541355103000c0b12200701c908040c2075100d140640e0003c170b5200c0c100105a000b4606913280002100c181081c0311990100361914204568049600e0440c000e40c101003000203000300c140080e04036403104100400341c038005005c100f42540000c401c0000e02c400c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 297588264 1250 297587014 297587027
    0xe0a020a0e030c0603070c1e0305030f010603060617070c06050403020102190509181f08030a1101050402090429010b03060103061d01091d0a0c0314120f030703060305030309010606 79
    0xc00307094004125810741d09021031010b02c000391690092200c0e00e00450104041807104803846040409480e03417490340c62802420680003035401740302d440c0c1300c00c0001c034415200c6c0c8601002c9401d85c0c0d65100001000b42c500351407115001d07042d4000c100a064003800860310500809001d9480303a0700040e6181911401040c1d0b01d038940c1d0030f0908004080040d044079503039000d00c40280b0a503d140550b4241c80b07442820362a004070130b50403c105514444002a002c6000c0f018003143e060544903034020781c0b000f540031402c880c0100c0d0003d621400f000f020a0102c1d11200e11021400d0301d4008a040d9a103001c0813080d2034440036409040d40110000030040256418081c07003004003010000560425070b01c0d89410b0b07944405000702042c50343d4555001845c40f5500b42c1d02016903141205030703000c01c0001d081250303402c1e030140410345c0e10070211513403a4944a00003507450106130400080ca8280b6400070984031241e800945003000300343c0c5500e03003c00802c40600046026a03039840001562601e4240b001c2e00c10f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 297589514 1250 297588264 297588287
    0x50d0e01122f1602100e0d06060501090512101a03070e0a06080102090d0303050c04030c0816081204050103110c12041404020a0525080412060608030c07050108100e0a020a 75
    0x30031081c02003d09052021a07507070f1500703904880d50503130a400c02c1422602254031b0000c0030b41c000114a19034040c40015446202500e6003030b0b07102d1105a0b100ea0910044004c20f4004a1a583c08801400000900d0ba8411070131034810000d00705000601e40006464090684c01403001180e03910244801100c1c0342c0701d100300a0040d40025414011440000740b40e0800102c0301030203140d02e8800107200e00104100f03d130f02450b401942d9140260300d4070a05a5143d80c111144684c4100d000404034201ca000601d070607440b0046c00c059442c0c1070420780110050310f0941690303501084240a1501d6000b02440315282a000c0b0340010f070f807075a01e80401512010101e41a203401030344100030955140b680041211201c0f01d440c02612502d9003078012010800c0d00000b00070b000c041002c103001c11402c00e030a001c0c019650240000340710607910791800320b44901c6403981100c425449103404200300e50282d07219940c44602c210460183da5030b03491144a490900b210a011059400564802e0b80754002680099 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 297590764 1250 297589514 297589601
    0x1308041401031b0509090403050d090c0e060f1005090a08100c0f030b06070605150306040303050a14060303040302010c05030d151d0f0a05090a082113050d0e0112 71
    0x620403410703001e03240d841103991080c0111140c070006008e2502071001c56080d07c1e50320500f00310160481c00c010414210320b0151034005120314020403581d1500000c40030490b88002d00c0303003502c00c0e10310000342e401d03900c4188041e81041d180ba000056460b4140540704821003c840c2c041080c1c581240020840d038420404d03d014589013a0310220a500d48000361581d0705e501c428006950b0311221620002849070344400740e070503c2900108001c0684c160481402080d010500b07102440c124004a04e40d403074119661034050384203120410141d0b104400d10503403180620240d0f454400002c000d02c041c1c80c0d07003e16110005404030000c01c0044160842d0155200070b01e8030301c60040c2400744c0101140b10028003110300964680c404074001d07040901a040c0e40662119249070f07586c00947c01003d0b01c110349602101108103d400040f00c0403c003001804185600102034151b1010003c0165082d6918828483c104406071020785e01d17103d124403c5125480c5810403c80039002c045012408050010030b032400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 297592014 1250 297590764 297590801
    0x1a06010c0b0c0a1103131806030305030c03061f02030c1c0c1103030f18150a0819061511060108010e03121902160521090108130804140103 61
    0x80105140c19480c0d40c0101403656115907803002100215041525400484c0c1c0b140030004011840401000103002200d444080030071f9491900b0710413900711080383c84050003040b02000001c42e051a8a0000d55210a004100d448101c001d070740443c00c80645214140701503403001601d80010038040190408100c2c0c189100814076001901c02441a4a01c3c0b1006042001a58042007035039070500589812825a1170200e484d20405418a0300000703141d00701501495100c600c00c0041c240d800c040360940500343d2904185510307102074107042540c41884005440359100c40c041084500c4c104c40c840e035510361360350740c4440024645101e8105601a070161626a2416241c0142c400010080d100803449803664203416a864000f8588401700b07401500d810284006400072950100b0600109198042d60403550051048407070039901082d80081c084c40543c00380241781566100d8502d155001d10190940c0c0f0442842d691398182c1904507801403070b141d140080c055a500e503458032440e2100012042400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 297593264 1250 297592014 297592037
    0xb09070c0b07020f01110702012012130506180910060210200703170108010504020d060f0902040e01020901022b080702160305100b010c050718090209041a0601 70
    0x5030140d040036000078426a0640c000a115070300a01c00b41d115141ca100c02840811409480741c0395540c4506d0040380400c0c07003010280081d0007082001100c00b01030000400011400d102071841582020245100017280180d01040e2500c4034405010618207203040030750000c3c800710801040c00c1e00142032110610301603004101e4640d0015211080049000c0e000442d0801c292105c00758805114500a40c8000002c5580c10075912454000038020181005201645c07504200341c2038aa081d03d02a40c0400120300b044085103d550110640380c001c6600003490703290a80c082000d842c030f40840381e0322696000c00e0705580741d40c06100d40c0a41e1000b03042d1801071a1100702d9060100c0114070146406c01060800050580c0d0081003501040782c61500310141840e560300c2c00070340d5202c90900c0c00c1021070030705001c2c982c80c0d4000c42c094101c90ba40b00024016040c2013003036620300400510003015040341c4400300311003d81c6841c1021401036010b9486039080703942d446217000000e000600054100f1903140d004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 297594514 1250 297593264 297593267
    0x316291005191503060e0129040e19090203101407020c03060c16080408010f15051305070e06070c080c120a0b040f12050d0c2a0f080705060108010b0907 67
    0x88400e40f5070fa50440e600042d040e40c0101e00030710b281c0d000314004490b500008a001039100d00e0140200c03818070404d0011280840078036000780610b100318051010000082028001d1152842490754001c0000084420668000034a0100f920f80c0000d1500d0b81c901c9680036103ca68007016078820301b42d000174004400c02e040460390b0703044020710404010b4008607034046840340c20002100e41642094405840b20b403180d104a009182c100c064009081c40c1c0100080c80d81d248842c2d900132103100030582003d18801803164130260000030310241c04c11071748441c1c200640d50b408024140d0b40c2c1c018180e02e4000c0b070404d52103c0c035100b90741c10034520951411240400501002a42c05000c0c2d500414089072078a0341d14010207100b804110080c0412035200c406a4095403000c09403e0030180c5075800d01a0614a040070f68540307c0d011103d040c0e5003a0400050b0b03040e2104a08000c4c61440703001313000020b04094860702e009800c00d800444542d0030035070041121140900482d10816021242c1002c9810003620 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 297595764 1250 297594514 297594559
    0x3e15040501050d0b15040303051206190302100314090307031d0604050618060d2309101107050d030c0206250809010b0d030e0a170316291005 62
    0xc04101d44c9441038091a03454014250054554118403183c41c0c42d2a850050019044070101480402d1424005165440c101480610514a294004c800385017150203003e41c500342c00440794103154030342200542980c01921118802d211031009142c84290903d80100041c6141c0c2e001c40c10036400200b051842d80d100780c101c0d4211181100e002c1c0d81c82da010441c50900203007201c2c1c420781c803070700102e0807650300c29854211003020105034002a50482034181400e8109000360369580803513021610707100101030b0303075403011007003d003c100d40c6410103038103541d403625080c0a14402400683c5400b6a031b942d064040001d150403004200900c0913102029039205040500e040c564020041e01c60041200400e0039031200301c0d00340c000340074500d801c00d16040280c200a00ca001c01c0b0f01900010f540040d681007001944032064112801443c076144140080300d80580c20a071007956001a51101d44401d0104541e80b45c00307a40810b5030a5074140791032154000d10341490740c00240074101102001107141e02c80075 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 297597014 1250 297595764 297595777
    0x90602060c0d150803040306050a050919060b04060f120c0510020c01030c09180b0109140f04050403020c03030705071a120f0709050a030b09060601020114043e1504050105 75
    0x40004140f080c4900700303542403059038000758060000041c0841800180d81216203d40e101c004240060b4a5002074242d490032910a5481c0c1450003140301000908560044a4085c90040010403001d454043c10061030500390310100c0701e040b18004800420034406207071801840116000c500e510f0348208040c1d150014444120304240e038610a901090340600000700103086c0e05c5100f081150003c01c20030700107041003031400e404511250b4001919140004000724451405012035200c003010a05010190070064001c406500402c01e020110343c41c100041c0260341d008030000c00c034072882c1c0300440c80c0481c010788802038008410002650318040010403907800030421070b5416540d907205441198204400d40102c1c4d17002c1800007000040c00b2482008a001e00501d41c1038500a48501006a088418480580180d52600c10029010480c0780368540110302981100620000c44812145184008064128181140424804150305101c666040820030301900c2500d0541043c001924074040d04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 297598264 1250 297597014 297597037
    0xe0310020706020412030309030e030318060315180a06061403040311010f0e032215140d05011203020c01020a0809100c020d0302010506090906061f030b0a15090602060c 74
    0x401c6800c01141da411600100345007011900d44909601d0010082c3c42090300550000d184694107004625011080301c0807203104d02140c00000013110280305003500020f010204030300c00c4030861200c0da21080546101c1254002405240c0d181202080044404542004080000c500303081038a02541e02c088a400c2500360070000000600d44800302c1c00350240d11045496542000ca10050700b42000000c3c014281e030158080c030900061094401800e5010b20600c81d60308030070b01108180074001c542050450300108000d500d0302c004141c0e0802aa04280c0c00604078007202c002807000d1660503c0b08030303041042403000d05101c1a440d02c3d021407600810303002521408502090681c0d40d8002c21550220030b41c013030003900300c03c8410b0401034001c003c1181c245009404180c0098460032003c1603952050800070452520003101100322904c003401d244494080c59580c00c8161440e1fa2462002c600800c20102d80140c28101d0620042458071164490801d42d8420b406000041005400b40c4a021108 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 297599514 1250 297598264 297598267
    0xa05011809111b0601180e190819051602060304170c0703150209031b0d060e15011a07060209040b060d0501030210031401030f021f02010203091605010203121510021c0e031002 77
    0x1f007042c40307030034110280701d09090024855485420000d070702d00036020b030010f0103182902c07204402e40e050b251407085000745030303508a483c100d0800500d4080d02035500b050040c500245075001141a66005a002200f90038640d801a4010401c00001400d401e000703110455041d07003024100000b1036a502d60b41c250b03100704200d02d011680c1160b00e4202000788103c0d0000010b00540c0c1800c00b14a880d014422400012803100c2030001c01e1072041c4401246000008e54000ca01d05020347d228503000f5007189062560068072000020010f40c0d03040040d00900120150009007545588104122281006500c00a0505040c1c0b10f410491130a00080d045a410211002c4500b071144001500c944c89124806d500000003209e9000c0c02d6070542c0518403c109503011505e090a0804007500f040c2024800c45005910803c81c0c440542200c0c2400c0340c00c12500c180091080204c03200141440442d140908016841248294500e034441e0941c0c0c111038a90f0708000c20b00c003841d100420b4848144001642030540c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 297600764 1250 297599514 297599531
    0xa0503130f0b090d02150a0c12080702030307050a091205060604050f130204020f0706230105040915090311012f04030308060108150915120c0a05011809111b060118 72
    0x3150220306c40c040711070011044d591450700f03401401400049405a03505040f040038941041d00980803240140c0441e0011070a44d075a5007401c83e0300c0e81c00045410308124941c600090303200301200e1041c01d0f0230300ca140a805546082d00c144012a100203000c1c0c00000e0010041c00198900441c62100e21385d011340d80580e6565070107240051901c5640740c010040c4e842c2c00855113000e401a03450b281072138001858400140d03a507508204c01c0c0c4001c5180070b4a20000b10300c0d40c0e08820450743c40b000c01a8800c1c03d01c1c104c00604440d0712404c603a200e107070028072000000701c81e003c1242007420179980408010941d0341401c1c215140241404130003400c9074140034601000c2100310301090740320308090100508030245440d000002c0980c280d514421580035407603c115146252001040c5500c401da4050540116140b0344070044445005640401d0104044004042910300e0603018405075250070809860703135880303040801403044840c42c0800791103404c000018411882020000100a040a10040380010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 297602014 1250 297600764 297600769
    0x9050d02031f020c0d030b0117070e030d050d06050604030507060c0305040306090302030a030f090b0c0d02070c0f0f0509040c03060b060405031c080901062103110a0503130f0b090d02 80
    0x1455031180092203010600b40e0308030701c440d038009002210740d50040c1c40d00c0201d03002c0300343e081d1079888100b94007080c2e08004081c100407520588590103030301458240d28040214022034102506c0d0710140f0b00140d000a41800703000d04500070080105011340d400c070b1a15185440d0b131526080d5a005000421600c03083d10390505100e0401d0b40c0103190486801c000030500c520300070b1b540c1d41c8525030ba6030200f41400c2e5200041103440c0310b0080001d070080303007815141c2da40b94064032056102c1c141c06200c107a42408100081607004040710b0140c03864200c00a049801c2000e0b4100e110103682c0118411000a81000005625601e600307040320761001000c12075580d040c0020358907001c0c540046405100d82012403c41e000000e0b440480010b480d210111280c866040050903130381d1034011000e0f030008103940390300d09a0016012805082c00f134034003005800b41948000d800e000b50705e0b100307440360351001ca00c1a207286001c18888000f45078081034400b0710703450300c2c852034114044c1d4610b03640714240c207504040a64 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 297603264 1250 297602014 297602023
    0x3280905030706030603020906040203131713090506090f0108150c0d0908092d0111100603081909050a0504021803010f06081c0503041b051801081c09050d0203 70
    0xa240007020349801545403900240102501d100c01c3e4890100c042c04540c89050910840e400340c0c240d00040340c3d80681396281c3c3d505c90b950f5004140f40e01001080f078009500060040030014254405c000700711418403004101c0e0345072010300200b40704400c040040040c05000515810b0480442d280d2880654501c0c40034002030145480e0f07040e400782008919010030134a18001d240c00e000842c1c04010164001c40b40a0201d4584400305c0d1001400c001400031542c0a0400c000060103010216041115400e4282d400d86040c0d610840380180080f409482565820491a03c11011884d10b070042d94580000039042460342d1207084d0181d9400121003c02d43c110911500320500054028410300c044000040014401c902c035601c12405100700d000b902e2010445076490108050b5211030440d206e6450342c03500345800c0b400c0d500300b002d00b02100051580ba4403100c030b042000c120b0402c00d103030340c5001c00c07060030852165804110088100c8511040c00d030404075102c02d03601e040e1510b03c644403003480403a160 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 297604514 1250 297603264 297603269
    0x7060f05040905040605070305150f010e04020c100209030609010b09130f0c14041a060306011b06060e070f03200c0f03030108010b0307120312200703021e032809 71
    0x1000d00f45400c000502c50700360030032801114140d41c208501d5880504414907603050b9007110b43c0c40408141841c0d26980305a40c18400c10200600040c600011741d40741915000003c840c40c007625402003100c1e500c1e07242c180029a4040300c1900203000041404000801840d801004100030410880d031440600900e070440b03c00680e802610508025240c3c4901d064130200410040e10a80c18411114110310000100c076902100141c80d023070540c0c90701c10056079031061180d81c165031510b007200ca24001c0354060142c01d009080d441804035603810503890003011855200e4800c1c00741800c1c551078000c4070440520403031505201c580040c4c0c0390700e0101074060074641071100307151907440080000300d0501010340c000341c003140e812400c07226265640d4007941c0d800c0c1c0b104880a07001c607040a107400104a240c0d00f0801d03400000048200b21810026142c0003190050345c03007900103034480c0e03411800d1707658081241c0c1c6605000c038009500b00340203000110f48403560140c12a409800a00000140c035004082c00c030003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 297605764 1250 297604514 297604529
    0xc0601030b040f02091e0703020f091c1a04030e0901080616050405040c050408010c0305010f090e0c0a17150105101b0228090501050d081809090708010f020a0207060f0504 75
    0x17080d04250051350a0a20000450b41400a149000c155030318013910803501c3c0003040c48142c0b403c04550780104207002c0c0d50019200c110300400030070940050500e00650003040da464618551504150500510300501c001e0303d81c2c040e6000e6401031110000020b801a800743d005080804200400b56088035a800780d544000e4200e0300345281c003000250002c024001f5240030000030020b00c014008103c0c06d4400a12801c208101d070750300c0600085101e50000d1041c072202800322255a204c100200314003e840394446102c600e4824030020381000c0500114940c1090480e414882d94185000562405209403944082c0050540301d4032482d007140120000c0326030001c00e1500c41c26880c0220201160001940d070300b400100c15400311341c001c0d187c1f10319810f032100600000c2000341e45540320001c6910041603491a03000c2894019407075500d032a13580d8840c0114001504240b0f152075481c609440212021030380d0720740103101c03509079240d0000d00801110a01d1401221800001c0c0301a2107612640e042500f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 297607014 1250 297605764 297605779
    0x918080a0201020a030b030105070e090912040e160306260a0b15101110021c0f0605030c150906032d15030f0d0305060a09020409060f0501050c0601030b040f02 70
    0x8419607019400750410a07803a490500030481d544040500726042154a10007240320000c440c0d0b26070500312080d0381c1c0a07403406c08580e00305080c400011425042035110303c07810110300381008189030f5800b551541b8140ea50030305110a030b003403500300d81c4205001403800c0765011380c40c40080b0ba0108104802c004681c0c100e12404040d0410640025204200000c1240100001310300c0e110400d100b018102c01502c1041d0142c102641c01155910203544032100200702410030f0340c44421f00d005c89210707664002c0681003000403254601803e15042c0000340788800d11810988003d5884154600101c40d0b04a42c200d6803165039554411030354070400325441c64510010710b01310038025007601107142d00b13000700070200c0c0d4901450316040405070f0f540b41100340c05c002508240310459140380680c10168001400030011501192558003440481e00aa07001c2144103441e01420440c12000c643c400026240a1803e14a40080d44100a030b0b600d40603c40200204002000038050041117060f0600544c0e0080080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 297608264 1250 297607014 297607027
    0xf12020d06092301050a08030901030b04022a07380c03070606081203190f06080d17010503030a0507030f0c0204050103060504020a1710050c09060310090c05070b01091808 75
    0x80314048060403c2c903410070000c004070303d91500e55840e40032a50054011864071b014400110060072041800c1c9411640038040320280044104848001840c1690480300b4140244102c0749002000c0d440303003039030821222000407240a14583c0910200c00303a4400154245007059040e007521401103038209500020400c07408102c2240c00c000c0c02c84844030704480c0007020b01f0403504400d100035104a0100201050071420000f0300342c0103030f008a0140c120000c0c010b90380710f82c0c407030070040ca285900e40069500080302141c0c80146080d103015120a0b4011402c1c044689005007a030b01c54210003500b3305c00d00d01c8001c1c81841c41102a0126240c8c043d0044c49596500d01e0510060705013590101e03caa20540320224001002d0481003104c0502d07500242182c10030004908000c0c14080c1442e11480320400c1034841c0e80d210140214000c18490a85202c4245481d4016040310003110944081280400c4030101044600e2032040c103407142e2007400140800d010841c001d83d00c500d030500a08144010407074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 297609514 1250 297608264 297608291
    0x506091c0302030114091f06020322031703092109100c031b0809060705061e16031d070303081b03040b15120f0703120f12020d0609 58
    0x4400901608190200c25104450040e0143d020134054109619a03042c1719120900d4000500c68010030802c2002c000404903080c86941d1380b41c1608030a0150b071001848044080505051846e04015010504070b010b00f10f96400c122103000c2c4401840d078801c04004107540007428003440c42121644044c240f0f442055068001d0340b500061300d02c621582c003d803400c0f9001400345411980c8268541d541d0041401c1d45950401c90f07104507501619800301c03e022442041d1109801010094000d8004082c0c61500341500c038640c8020a0300c0300c9a60040c81c00340485e034400fa041101c0000c450703060120300d80c2c0400c03e08080c188142c580f90802480b64000000c00e01d80c00005060050140c00c0c4e003a81084104030a1410510055400801440e8058002182160240744940380100d00400f0311100000c3e601c2042c1c5011507072401c01c05203410090042042110100725082952103a003030070488500c00e44000380080c02d81c02140c2282e40d0f00007503c1c510810071684070001900307170584204890f5104500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 297610764 1250 297609514 297609523
    0x1011040e010303090924180b030102040f091107080703030f2c0d09080c0d03020307020d0503040e0f040206070204150b04080303010f090e070b09010c0812071805010c020609030307050609 82
    0x107040c07803140b901c011030500306d0400c44100e640801c00b031100b119092030003081d01405810340303803841c1d076140c0e0707a41c032205c89681c081c00203000405140c1d000d1241c19044c41103140440743c1c4100250a4100200141030014402d00d0940d4240c64042c140060704451112078480074184444682644510040040140b01030f0f408440c00012a880112241c1d0303e003841c42982c0d990b102e4000c2c400c89a1110800003480d2529101d5401103d1192068a09000b034550104003d140c031030034120340360381000c10188070282e40a1403241c4c5c800300302c000c2646541829008074201c1d101d0300380b0181c000c0c2e4498011520f03d49103040d40c1002000c0601d0300640ea80d40d504121074980d082802040b006098142c0001441c40442c021506e40c141042d02600300189000c1d10702c0d40e1680020344540c144591480518003169511018000702c42c541010688107140c142c42c010050103042008002c0c414103020248210b03603205d40c40c80981681911903564481d03204002900d5402000300040c29882001c0c1000201800840d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 297612014 1250 297610764 297610769
    0x71715010e06060409020f04350102040b12040606260c120d0f0e041a1809030a0507030302070b011205071a03060402030a0902031204060e0405091011040e01030309 72
    0x684000040c0d0321011108200a01551540da108109020078014a10503600811805408001c00c03480c1c13136940c001c180810f1201c90400d07a012003541001002143e41400c18078115083c1c034008501e81404c1540c05040343c0070305e40b50700c01c42e084548001420400c00798810405081c07100e00325000c0c2c1c10341b600d01d51582031203118100742034094201207203018100010071085034180d0001030074050311501ca003203a07070807031803e5940c00300560b407034100d03069854030f03c06ea030118940a900c1c2c12280759078909001d4074500044a0220660705071040110350034012003555400040e5191050390380c0d04609049006e030045d80400380183c6034010001410300f0001a640d0983c0d40300d401aa01030a82d11058440e00c02210b22410a00b01000c0001440a141c56030080d6400302c1c5900d03001900b42000d8000ca850040d40b0b450384048240006401d220164020b41c005860b070400712030502040c5047d590340c640328070b50500742e01a45500c400c481d0f1011103052060b00c02518408100809a69403810018040103051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 297613264 1250 297612014 297612043
    0x317160b15030a0506070503070207030f0c150807120c0507060218150a0e1012050403080702060a0e070b07030306170a12050405010f0c0c08030c0f01150e070e030717 73
    0x441c40c4419500b40400c51807000d58020000e80703155501c425054078294401001e44045001e46000840000c085401a200b1680502c0c60340328130f1401d00880c0142008056070304010702003800200700460f03900002d03020701c40c00ca20300081a07030b9480740816144e0780a0050010100d82c0040b0390f4a807140080408000f140703200722a40b42c2e50859519160359140719000c520400188200d060340e046013000b0003c0e0040030312514024203201401203074281100c00c160303811000a4046c02c1840300d808e83c100482c80c2c110814510400c00601102152540c03190b9500c15403420280200c0c01704c0926010398004e030001d1108401c030504031109100b2098407000032080c1110118180d4840102e6680b1a6003641d0030340b4410b03112150384a40184050700c4912271580115a02c507030460b0081a007020510280c5002d0340110003d010f50070803040311500303449001460300101403184101300090034140e100c0035040501400c04203010040640070905050054114590010f4402d41c41005e03110300003051040344014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 297614514 1250 297613264 297613291
    0x6080102070f0507050603010f0b0901090513050f07110a03080c1b07030314040e0612010b040f0c09170d050a021c0c060b0906240403120504030506150105040317160b 73
    0x64004104850100313028010404005580034054649020300500bd41e07401410281c08465480d40020b40b0007015101001c2050307182c505001040b016030300e61302d400ca0018200a0f021011030741e00d09a40d1548407002800300915800450000b046010490f802089014071605d0b502d01c01041040d562082d500c022800240044408040300300da90302541c082e149200c4242541d912082b003001048092105090b01c15540d52118240d2991548a40180640c0320500030a14000500d00500301072065030000c1c0d00c01c00c000d0510749400d01c001c14100b5503034140d8140305480d0400308404a190105008600c5d8205181855800c14182c10542081d641c6100300c00602c495001441407008190055411a0300102030300340700032641d1082d141201c1c444282040403410720340d9036110154043c140b0308400020030310006080c4140b04040c01a568810341003800c6201654a201c0001d24511031440082d16148081a88119101d046005c40e0441480c2c210b503400a080319007440410604140e07401d0352031508 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 297615764 1250 297614514 297614519
    0x30c150c030402060702062104060c0e01051c09051e1515101211030a0608060c04140603040c0b0315010e01020106080a14010908070506040501050f090613030306080102070f0507 78
    0x20003084910031a030241c405030408440d40e00380302c401e40145c4144c8012014008070303914090340486000788175038051000440e00360540704024003000701c0180d90381c1c1007000800c40c0350700c0e11090031402807108040d114001607043c0d150401714148020201c0c10519040000002100310744005084800d02032000351a0f101c544401c0320071000741648846198102800001400c5000d000c1c5a405400b40a1440c01003842541030a0351420740d48111404018a507841c4003e104070300381000841d034040c003180129440c090410440e803458216080032248142800400101003001c40c070780c80c400a01501000c240c50b03013404a0700c603000c840341c1041d5500061700c6080c1d030941907205005040840302500301503d01440180c64000e03140d1240318803010150b49504003d40000c1507403004006c0c0c3e13030040001d0003142c10309142030760075140d0181003500350580c0642400b500640100d61035812419201c561030400245140540240c41c407580310a50300d5101054050520415060987c4000d04c03400c10380c1c00303154 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 297617014 1250 297615764 297615781
    0x512060a05010807030e07080a080309161809061103010e090c19180e0f060a15050108060d03020106030b1501090b040e010b070809100c050c030c0f130e030c15 70
    0xc0d5600c505400501001c002c40c8041c3e001c1d5004004138004881907039000f541340c2d007030035207841c898600c12205424000204881c2d400244405c042004610520800c600d141c00010715400003220b83c0d01318525a01c1e1501c03010030081d540710360306a0f0000c055403500e969440029440441703049886640782d0048005440f502c0c6005505103601d01d04d03940744c05034a2808c0c9149484000b040110402d0956600c0031400c00c26a4100452000c10240c01c004145610b4420701e1813080e0344001001c0d528500b0341107002e00c80f80e0f030460300480d401107040e500160702d0741741410100c0c00340c4032070342c0050320107a080014050f2040b11034180090f1001c081c0c85902c80c4940d1107040002a10607440340b040d4041c8084014424074843d5001010f040e40030300e032100e04050b20003000900d070030908910000400e10456124003002410700c4100c4080004402500403090760750003243c1000982e160061080e94071144e40100c1e1612030b407200b40352030188011203499042c0c0c07154141d902e11012140c104201c504100203003103032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 297618264 1250 297617014 297617029
    0xb210c04091e020f0d12090618060c0206130b0415020c0f0d0f050d03020a1205070e090a0207050106080f010b03060912030403120c1d191e03080703051206 68
    0x2560301028011540d240c18042e441e46005034034049901000e0690b15210503900c2e541c04481c494010100b2804903d100580580442c1860b4010000d00081451445ea00b500c030480b45001c0720150700344001404014800618684101788500e209c0390001c1c0303004100c0c400c040e4080c00c19103450301c02c81040e203062002d00b40e070f40e500812807c075030010681044500f03d0402c1040c00c0c802e903201d02c004146070b407003d5945074106542c4001910000741e01090080700c040e4001480c1060394002c2d20200800e040079200108a0b00c80381c100c40d402011003401113140491168102c1c0c2d5815040303002041060340712003440b40c0b01c050f140d40a036460b42c20100b0148203860041121030050070400000c000c0c80070044070038003007504000c02c10b400f404140000005090b03050300800313003c0041035440c05654444102410900412110042c0c00b030941c00b9424402c0c0548440d12806551111822102c1040f840d2200304010500d41c00c0217041601c0801d030302041640000182ca41c42180d600ca81801c3e0340c0d107a0510621 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 297619514 1250 297618264 297618281
    0x9050102070f0b0d0c1403010e0f01060306080d030509070b0708030118020310030f050a1a07020f011a010e030a120810091109062a030d05090313030b0a0b210c04 71
    0x10f45600304018645222250b01c504d40d042184d080070040030b901140c2e0881c0a0308240c0c462404903a40008110102c031800111300c0c00750810381001c10920381010469552812101e04250a040d521404100c0842042044d54000c181d981c00d07143d41c5805910342260340c0e03002841209109041650070041580050090381e105040101401c0111460b540340c0c1592071003018000d072035502400c42218049001c001150307800c070000181242680c140828006e1070b024002501540c40d0745440d0b40c4000c182c0164131845141c40342480c00320408510440003030306110707001f8001402c84520742c580b204410b0b00054001e125103a0111a1001907960300c1d00f880c19075080d400381040e01c0b40104480140d5150a602801d951304c200030074420f107440700100e20a40d03900d90117000380700f070350021a402c0d2101d0414010340c1d0b44094018091403c00482007000701700a015404001c00c80341e0342000007450b040ca5a4001444034078010700e0440c801c250a00c844a1480c0c1100c1600e499004585a00c0010304150164400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 297620764 1250 297619514 297619529
    0x150303020a021905090a0e061e0c091201050108010b12060103030903031b0501110903010f0b0604090c02030c06150126040209090a05100e15040c09050a0f020a09050102070f 76
    0x62039080c1d42000600c180410504400368000c03c3d003c90140c031542c409178841e40100500103001101c0007a910b103046802040d018807101e01d6101800200120881160055864642d0340d468000d41c500181c94041d80c04043c040703561038140000340d03c4e20150440d0828034000d4a500000100e5001c49988580d001d000183c0411087c040404c0041d21138180320482070128540540301103240e54889003980c50444070000d00f4103001c034114000386400c0c403800902c0f081010040003031701090000304507140620312684c0aa540d540441041450090044441916018099503028030300341d080035001031030003c445800110301160b00d82d110039a40702407801d0f000554030304000d5940c5580c20021038501c010b140b40801e014424031000000c0c070070881081c0c00302158001003001c7d8400701007580f0340000b8404c6c0c0f4500c0a080b2041c080410b04008492065a002c2e420114882d90f5031143d80001c0c000d44000701030101d10001c0e08001031740c0d0145030401a58401d81c29650035a0b03460b81c600b16100d009008004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 297622014 1250 297620764 297620773
    0xf020a0f050d08011715180303190b10021507020708060f0a0c03020307020c041d0703030e0f030c1c022103030f01081c180f0b07030801120803010e090c10110115030302 74
    0x10280111b107070050350f201d4180202c0c5915410754488003801d540080d0b4288020a0310901d901084801c41d000305010300c103090b2215256041c003880004e540e24082152a8803d10150005c2a0700c244240030100c060080c13142100e045003000d64220403800d800316000144189082d0440c0e4a1078840d0085900580316036000300b118468010401c4001c0920348401c40c1d841e540c80040101c0082c081c0002d500030350107038440b1482c1000c8401030081c41d11164008611a400c41054aca40c40d5488203000c412149440e400f00c04040d00740d01c00714a411a0305c10701c084684415044d610408038002005600c98054900280e926990307132070f035055681c0100c0082d1010a6022006104031900c50500300c8410b14205040402e0f0300d544441c1c00c1403c04241c0c01000c80c2d58000628103003810340249500e030042c068818a401c16403200e07103e000d0305000600415581c24000e0020948903141000b0421008500409020365400c3c0004081c000c0790b2403402075413580d401c10040219456000c101d000c112600740d0080c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 297623264 1250 297622014 297622033
    0x503030412021b09181b0f06090919060b0313020102160302151c05150907020604030519050d0c020106090b030c0d03030506120d02100b040902030d0f020a0f050d080117 74
    0x10b240c0310040450300103030f03a24810a00105c0302003164607032410b86a111a0245802038043c40707224542161241d00802c000c0080704c1260300c0354a01385601029100100c42c0728000210040003810b0b0552185410407070100604c64020032000304c500149100360229003240c0c1002040444012942c48003961121248502003420007480e070040070003942c0d43d64002042d091560300c00d022914240c9a15a60a0b5205d65003c69810314210060f0850100d0000745443d1506540c0180a4407910040e44c0c0c00c1030b440c031190515103000ba030960300004003002e0705200020310740000030b00920b004e104542c80366042080348500750070702003404904140007502e045942e00c041d481c1500030748006043d241d003085d8035108101d107003c1c0c141b04400058040e50702410500062242d80c1d42540d0344458554441c0d86050845001650700003165100368040d03043c010400005820700b40d05005000347c0c0038095840b0800d040c0b0800c400810080042041c548403600ca80e62036a640b6440d04001c483c420409502c0103003032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 297624514 1250 297623264 297623269
    0x90a050f0f150306090c010f210f1820010f05090f19060f080106030b060d090512070f0b1f09090206040506040b09040c050c1f15030503030412021b 65
    0x342d448451488912034140700300003c02d00d0036030b045420007000d400180f040c0d4890343c0e02068101e1031803000e00e40518408101c0c01e000c01d00043e207001000d0301c0380d618420311400104a07080300e1920080c02d074802410403018280010300c0300418ae01d8984203c2980100c500644c0604819403200b5082d5840c03070705010910381400703d00b0f031b1941030035a40901d0006040c1c0c9403004221188021f41081e0365003032260f1443c00c0002c0c290002c10b801c80700c241420020140c100c7d132906404e8a403040380c0d025010400f10710908000d400c0082c100544013549100142d01c0c014000c4c0c82c07003940c51052040c0d0f41150035a69203040c00c0c03c4903800b5000c03601030815450302001802400d0300418181400104001e14040d80c07200080e45a600c035901c02031108002140e2400c90745000e00c1050b46030046030900b01d01c1c0000c045085ca80783c00489a02903074900040c4201c022143c0154401001c154000d0110828262681400c07a502d0300125421151003c24024590145202040d4124024010f00e000c0412034145801c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 297625764 1250 297624514 297624541
    0xc0d020702040914150f0c0d0504030311041e05030111030c0315030312010501030b0108040302070b180d060e06150d030804020303191d0301060e01060309050304091406090a050f 78
    0x20903a4800e07200c07128940440e0080803403030100b0561000401c04e000113035003000c0170301c0380041608070000f080c00d0410041d01c416104403541900d107020300003142e588900e401d40042800b0f100c1d50b2125640864003060050300301c65900d000c082030b08075103540c00e682c81d0105170a891022542b5820f0315024400714501683c60005590044000100380000a00c00d03000b0138034640104a048e48000c20040040010b540c0611482800100030b207007040c0030f850940c40c040d40c0c0d500c0501c00d17000c0c0380c0d90000c0c1b403241001d030303100c1c1c05842031100600c05203604005082060140442e903c0c0f02ca540d000342d2001c81c20034250340c9080d00d4500c03405051404e03405566203064070354400007041a82c01d404100301c0c0a0282800c1100b03004181281d813641400b600c000740a44c0c4c1078140c00500f0078001c0e898004140054140c8503526030440c2c07418903010030403885600d040c9040d4040e6034424951981000b100c407010301b41c4901001d01c1400d0985240b41290f40b441c0b440005d81d807054641d0a80c264601002c03440e1340258a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 297627014 1250 297625764 297625777
    0x150a0b0c031602011e0c060606080721090b0a09030f09080712030903020405042001030216120509060d050109180201050702010e28090b09070f0e01031b02010c0212030c0d02 76
    0x1080181341c5003400841c1c149a0301154504001b614a10300030007080458402e01d400382c4070304d2901920a141805e00545021000240d550300951040684091440c00b03801107041e640d4000705602c034a0400301c403807001801c01c102048004c9507a0039001c1100e24490750482d42240e0b5032500911040d498101305110000300c12406504210f4290700100158490b80106402144188102c68900100400c80200031024a80803070415004209100c0c40c42c03800b02d6070b0103c482c3c0013407100b0b01d00d02907028144c0d8144036080e1144d41100300815107803020340d42c603480b05040f6800e1000500404080e0402100703003000c00080280820014400d8a0241d482642c92a8101d680600065121352070941c41c0780000c800c2002d4617a92049024060000056a0058410582043e1200700d050b0905000180112180f04d03904410004a042d8161060384250400c1401101c1c2c0002d090f04807000c0310000b4081c21110b04040c000d841211100039400d03021101b141d12034804803480900300700c211860400603500c0714 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 297628264 1250 297627014 297627017
    0x60a0e0403051308150702030a121a030a0b0708250e03120c0c0109050d050303011a0d06090c08102301020c09012c01060c021017150a0b0c03160201 65
    0x9100048400f070303403200d0380c0c009030a000c00200200c02c410710115403a0f242c01840c10046400a0103890521508100700c1804903014450118000b95280b45a0061030083d500403540f40c400d400e00c143c280100841103500070503c0303945840c1a5526188103003a20240f287d000c607030320140798104500c01841800d000780440002025620341400740d51410034030390041c51019115811290400031950b80011101f0000c14040d2001d61412086032034a80c0c50f4041445400151140d86038035029501a40040380c400d1030400d00e080040b1a1594006c030300800c1d09005410202c1c42120114210703402c0082100c0c111004003881e0840e03200561450120088903842c907070306510641c5000c108540c2c801c0c050b94044c241d81000210006e650000d880c044e00131411056034200c4028005000c0366130f100303018a400a40603a20f24146800c40e0104482c4040c44c003041c031860148070418404254103244030300004440450700c1c6480c1c240c0700c01d20a112071042101c00442a4006c00030007641c540183d03640d00c483c9005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 297629514 1250 297628264 297628267
    0x903051b0a0f080406090603090213020a050f0c031308010506090109180b01030b06091f06030207020f0409030f020c121e030f0307020106050301140708240301090503120f060a0e040305 81
    0x710781d2034007050140107900b1201c3d0310000c2024010305600c054001c00910441c41c1c180042c1c51160085440038271044960303c4144d80002d00294818001c60890701041042040341d81da0350441040c140d10390301700c0340040346031004031940094a0581402405d015a070020000344180e4031700b19200b0024030b9268102c00b1010000782c001da010074503824845000f580aa0101c4c16a8904074003002040d0314014000e1042c0e00d6400307803644c442484000d0404c15103140b400c00680d0b03401d140c0002146070a480500c4e5500c14100b80c0c0d2981015070000c901e020341c030016003c55a4003803490041008000703c4204d1340303105910940690650308007640d04150f800c1c06281c26245072031040c4000700d440341d00071211500035039151441000a82000d114011421007200c04111540c1449031001300454805416100800303030034540b408a46410404400200000400030001c03002d15203059512a0825007010000d080d112002030380920480e034004c1e12600c030003030826a01078281101300b40d0f00302c400b034170640c10001c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 297630764 1250 297629514 297629533
    0x1509040321021908040503071419050c030d1b150905030a02060103050f1b04050403090902040f09140705090d060f18023c01020f1002040305060a0903051b 68
    0x20001041a0388941d01c00c0540d0711840d059200f5030300c03140c241c1c03c801002000010000840e00100503183d500b43e10080b5058001034000301c2e203142064860030313418521444d41820041040001e00700d035a02034150300b07403440c0c04501c1c0400e0300d00000c3c110150450a200500007000112030304000c951183c200032000481400e540c94540c80e5421210101000d80d000d40c0050041c01010000d9030292100d14004150b1110f0098440c01d5108414030300a005940b0390020804140c0900c80102c003400c4101c1085480760383d0781c4050350202925107d804032103483c100784c00104003541e21a00b0303c100c411341c49203450b109401042c00140c1080140603180c0c40c0d80c074402c2a11800c035601a01c102c064a00d40c0d82d004441490040040f14100689401da0f4490b0003c5119134603c404025036403a014001f81450401c64905d0040c0c1c180a800070031440207004800c10120450002d41c007502c1664040c50441d01260f98144a1008030f50303a01c50042c011410038440e40030100030020b02e12042d49006000d55030420f5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 297632014 1250 297630764 297630797
    0x30c031401031211060c070b06012007051c052805010e011406090603070612020d0e0304091d0a021516050c030c010315150207050a0b09100815090403 66
    0x1500380c200326101400f214541d074880da4081c1a080d03040702c031540a80710034240075403024040d11421500400210720803001900e241c1c016415002450b0002c41161a20108500034545a003030502840d4881c2e07881c4051065051043e03e0721034030342036000c00141108200141110a103c1c46130a220042d20848492580000d03028055440d60601d131100209407483d045410311101000240100c0c001c010110400c8600d07640000c4107002c82c1c4076420304070143d03002551000082e10680c4d41d4036481c43c2c2014003030000313800000002c00031070b038070820f0800200c1140301d115400ac40031401181c5041d80072801d040054642004070529492103405090301e0003c01a02c1991809401c882c00c5d1020340248001d50b07040c0c03d044c40801000741c400d00c1d003040b038610101c01c410569141406034422440b005000161200d008100c140b000d04401000742000c0743e5502d808910303950203180010700401c41403200c4501240a04001c6015905c0324061031102d070301000901c071001000800640800002052160546 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 297633264 1250 297632014 297632051
    0x7032003030c011b08041203050a1b0801150203122806060c030314060d0602090402040509040c1514180d240509030406020c010807030e030412030e100f030c03 70
    0x8070b00344000300307004a64180050381e140300040c5550520481e03008010015042040d640300c03c48413420001f500c0e4603003444a078000d04502000303101500300304070201c0c005600301e8481e504a9a824403554068080074a00701e031203000d05400505120845c10101d5443c800d21180d00d00708540e01100c560a680030140c010b002d4490b070354817241c04240000740788014907515000f603521102042810007007070b06040d00400c044000b184005002a81d012481c0d90b5a9075071031301107400801000304245580e082c40c2c148044e0010080c81511440b846107030f0210b6409010b0795030014110031000e007450500f10940b8183d0349000c1c9120f62254801c0005100c40006180c901e10007000c40703111079003024009501820f034401c9410107408070030380b54824401041044d43c0007820320003d603801e00e091800b980340c00304150701a14500891481a000110700428412000c20120003024000d0341c0d0071454035906c8043c0103051f0340d131070b4140b00050540031042d00d08600a40007502e030781d1000e00d40069243e44c408442c4081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 297634514 1250 297633264 297633277
    0x201110a0b040c090506040c0e0402090109080706270f0b031305060702010509150c090d0c090903050904060611060a270f020f1e130608060f04030801060203040501020703200303 78
    0xc0402403818012000c0a2151030b40c0186c040e03030704000420824030098180c3c1c01c0466002d10481c0c0004044a090f41b20b560040300803e60358080b54900f98540030054204c80320041000070200040d200e02106402c6001241b04441a40003185c216508040500741d00303501c02081e0180c07003c100a8140c0006408000c1c02d4807803461503000240390304180c81d038582071a00c1a500110086000d809001c02907000001300d5103080070803224a00214140d25115054070425405110401d150901d08001e0582000c000c22540d007044808003c0d071a16444244da04800c0b05088a0580d40a0000101c5406445e0f1107030034401d10280c8500700c0f400320541d01c41c512141c800c00031209540c07808011411414800c0b154240c080c2c0499030007188007000412f84000c600303401149442400700c6002e9a090052982c000405484803009884041c681407090200c0100d00380c03012800a40180300002e94a44040107590507108164041c00c110742c919200c29001a00b510f043c030036441004041c2c200c02e0369040004044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 297635764 1250 297634514 297634523
    0x60f070b060108060a03051b03190302011e0908070308090c0a0b09101403130804051819051501030504060621030813020d03050c1213050901050301180201110a0b04 72
    0x280d00c1d054000520701c040180100b80500c82c01041480010300214600b81c10f103900038902a01e00d01c11000191500601c2d02098a816521441c0781042c10f40c190082d6414003010040b28200300b075400c000e001180c2c0c20b0440507000c1c036403e00c08900020b11802c0156001010300c03046400603002200010303202e03400c80e400030918540c00103c1502d00d04002c3c0070400c150760300342001c07029100c2c004205849480020924006400c111030208100850369090382c002c0c0001410a4803c40342111034841580401e44541b210320741526441c0e01030485600480344500f8104031120a88020b440054002e0000a44122410b588548022500e40940d000810300da81150322200705003902410050f06200c000361070548502d1080c48840056120200c0a262140e81450404daa0305500c1500504001d002003164034846400119845511030050302d09064841c129416190ba0741e8900400d400c1300c10300541c2005100b4031b02c2c0c05001543c05039a0390b40032407001d442900c10380e9100d61303180020345104450484 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 297637014 1250 297635764 297635783
    0x406060f2705010e011a04090c0c060f0605060a0c020621040309170319050904050c0a020d051c1107150903033812070b070b07140d0b060f07 62
    0x104803050071500c0e10549207881e802000254140b0091525050741402071075061003001c10503480b0440c50004070b600a1001c40000c200203003c4001c010072101c615070054900030304081c8140400340385031140504480006000d50316114041d40705030344e20075440c0401e170b030322640900001e840c5a800d40c402d031002441107a104421481d291130003400b40315007a003164505141100c038402c1d403ca000412a0108140407100045010001c40e0031109031244070106a0081e05000501035406003002c00741c0514201c5800742e8090742d000ca5000c445034012030144592040750b101003142000b01da41d0007200355040f02081d107440c01e0502e480e00c201100e10803014028039503843c61030313405142c0d0600c202c8400c0c0c5034041c186002607003500c0c5810300303842540c03d107080c240600701c0811545a403040d1101035108881c1094a840d507503030b45810360164000c2c010589020301d414000460389403140d6580103904102100740c60400c000c00c9402002851507108190b0005000c00c000442d1074510f102620501c1d11414282 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 297638264 1250 297637014 297637049
    0x150a17130c14180702030301090207060603020301140123010203090d030509030a0803100e16082205011509020a0c0803060d0f0809010e010201051515040b0a0f0801140f090406060f 79
    0x2c464041c1e00e001c80300c0b450f0015010f018520398088116811100300d04009a190000c0b81404001854550300095056207480031100d1110100385149040310b4500168441c1181d0b011006e01030513000d40159401a00f081241c0b80b1149030070100c10158900a24000d410032600c0d0b00804d28215800d1230680c3d04040110401044050801002c80a000443c544a600c1d040c5070003441d403089000c1101c4001c0c06505400a20485140a40c051800d6800c0212035100406070415074020401c000300684800c08203e408100402140201d408110f1a075507050101c1163340c5400b80d5942015201c0b0b68000707991045480810042030104210600400407a5600c070f100388009410030490345040703419a4100b03020040c284200070009814040140c0c0c0300403609584820b002403034451904584a04100071841c01801648007140c000c1e8140940c8602c00d00fa41c8861105a88e107142e07240381c95110400b2001c1d02740c2800c24400c0960064420b1380c1c04074030562150035020b203252180e001000d00c3c4001d011803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 297639514 1250 297638264 297638269
    0x606040c0f05030c042d1a0d09210509010801080715050a022506031808091309020312030f09070e071d0a08010b030c040905060c2109010506150a17130c14 68
    0x300009002102c0e0400200031134440c1c110032070040d80c0120100230762780c409042c14040780e130744200c16401d0f0302202c2803544039035108003800507045600c0c841d001504460011070118030018803403090710846041c0301c610b100450802c80d120351003100c1150460003070140c50001c80d604120014280302d00c0c66846118141092401012100415405140e2400a21410303003c1600c80f0b0480e9410326090340c0015080e002c1c441020301400c804d9a000350140302d10800f1040d00c00d400f0340075502804524654842680350a500295500100d00590306001207000106600e06d00401040c0702c100031800340602c40b04071420000300704007001d07801510340d651550072043c5a45000e22460b070003004111410030032a16943c1390141d90300c000030603403644810002140c1d641d000180701c61650320803101c0510b10807450f15149150103003005a50f218026503400919242a042e0603040e03501411083d950040700c081d4501111508080c040c0400101c0f00c04040a880030070303c1c00c205100940046201e005544441105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 297640764 1250 297639514 297639599
    0xa020712030c021528030212010f090605060c0d0302090f03030d0e2e0b030a0219050108181b0f0a0305010209030606040b010804030c0309050a15020606040c0f05030c04 74
    0xe0061107000104103030541d2803005e400c0785031303550b40580060301e619112000c150000d1041407040710740880344000010349400100c00c00780c19a07410640502906a8032414402c1a003d01491052a90045118014000d10079409040858002000501c20a0742c100100341158402903c803051280c03038150410800604001104030040301d030259640364030584034074464564210f048101825118180289256020040400e201d900100528005140c907405203400485034814030740854003500001d140b51080a01004947c204400034003054100101e01030001444042c0e40d9500542c02d1000ea14030fa21004520805503102d00c0c00103076118141d200b014503200b0001c0c50144110304282104503688d0b4408220758200780e06042c1043c0152040c17034180c48200141e003103250400b545c0d900c0001c000d07080700e000080107082a000d0300e41d0b0352030b00c10030b100545011981c494082612031040c464824072441c02140d001d10503640a9080c03645072041d80b9000c0318903444c8001c807111800e1107650b50108404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 297642014 1250 297640764 297640789
    0x6090903022506080903040f080f160605040e07030e160504050105092701020c1b190305070512120c1f150506090103020c0109031206080a0b010b0a020712030c02 71
    0x1a121054003085894050100e0183c0a0350f03040007000c0001c103082103420001e481c01303010b01d080144052a00c42106070b0742e940350f00d00010407500c110341407103d280890000e200240c440341c3d40c0d0741d850035050800207003810340f02808400030142c0c0e82ca207002c00c001042c00300c030321000c00c600381042459262a04100030b440068000074810b20880e02403044801c001c1c004585080e03564060500e103020380343c18660080c020044106a54003680e120f13103c0c1c490b207090302c01100e4941160b40091f240364509500d5288420743c0001082540005828065407402091840000f400e078000c41e00c801240d650440c0c2160002241d80d00359503c41494032060300c05c50390121010f0009481c04000200307201c071900726850329078403545014101c001014030f500d911039012260740d101b0404c000e00500f41b541c070340240066440d0206c001030518224001c04d08807408501c0d448015007200350f080c01c690800c65843c000d135001401103025440703046400184400c0c04c3c0c0c800c2016500a45464002c00300500511000f4944032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 297643264 1250 297642014 297642043
    0xc16090e011107022e08010306180c030204050a060b04080c0102010c020a0f020d210e03010e030a08010509070e0d0602040302090c0c15070210060e1f21020301020d0609090302 77
    0xa00030008209122041e166440d4041700d01d460303281500400100702c103900c60084100c02003202c002c00035a54200f60101d0480e8441c1c10208001401610510b141d80d6035030300010080c0c0944102000949055080f082d00b250304940006940c84d80ca0119440b00c0e409640107813503903000035480414a41e02803040c030b40d0180c40c60000d0115000d84c0e070b4440001d03c3e03040d80000d10804114030741d041400b41c20303180224007101d440703060f0144e01482c0710060702c00c8040400300c6100390b0a0024036000c0300c0012040c1c0703420000036258070303a60341d082104000e02074100421400c20480307c03245066403683d4111001c0600d40c010280182e03034604500610400e501d00915450120004008003541a1000502100c40858140e0504a1900c40290403030501c10400300f4400c9140c00d03c40c0108990003031107070440c041e00c0c800c55800010a504644244802041e105009501c4c2442030743c000004248011911120704c001c00051610540d02d1100c0101e40300c5820000340949d8072070200381015010400100001c511 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 297644514 1250 297643264 297643271
    0x50706030207020901090f0f0e0a0b010621020d021e0414010302040308250605160e0a0308030f040311120913110409151a07030f17011202060c16090e01 67
    0xd4000c00ea481006102d400986640d901100d46015100e600000920f007807610103010700295600540d540d400d00c68012faa21590b40c400001d0051b004040802e0700855404140c0f0180c0c40e000170031002500401c2001c003040c1c0d003c0144080040080581c0b1550746004204103032285d040058055051004d9541c01d07060510400061010503603036025100300050301001c000c4a240c403840304100150118a004020604040c1441070410f0310111542120b40300759203140d0b240c0c1120040017810034803440090208036007003000c0b400c002544c0203455030084c06424462001c6500d40780c41881c0c1043e00c1080d842c0083c1c04648080c180c54200407005000300c0c0c07100107100400c3c0920000c0b4481c8907a2050303401060b03550000704800e082d1155410020000910600c02403500b4206950340359126002c02c500040d200300d00c89035458010130880c1c0801c43c0c1440d4898840e8200030194490504c01c3c0390a03031f4402420300450b07a9171441002104000b003c0e8004450045150082c000159103a02e41c4603d8031303904 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 297645764 1250 297644514 297644527
    0x708070b03250c1e02040e210906120c0408061e0105040c090b160206040806011a0703080402010e0103060b190f0908032a03030c07020a0f0806060d030e030102160507060302 76
    0x6103c0c00f19114550016280c0c8424040f6030441c4070120006200250800d0400d4811280da22003c244c07512082d41c0807641c440b04c4444885501c00c144100412280d1188060102c51807083c2d6040741d49600840b030b5003100d46410b4075010f45524218007200d420740303898032540c1e051860b036000c0d240350f034010700e0159020702020140400107000c0500c140907070101101c0c0410394803c80050500580400e640190510b03a40e0b540701c03211245c59120034041c0884800f501e0010701e00015082d000c03110030580580d900d51b2071391159801110700303410702d411460402d61543d20101d4041c07603400040c003940a8a66900303003140b124400c007829003c0d100d0305003824801c02980820592001004686008800e07031560b208035000c1c074400101c081c4c041000d800e11440040f0030480b8405405000b0405140201e608400c030320ba652005018032082030041e8519900002c000c1411070901107085602544203080a51840d4031081c003007800ca8008508003916051080c50740c406111060090b440500310782c3c40c083d0300c3c018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 297647014 1250 297645764 297645767
    0x5090606031602011104090501050301050601170c030c07200108070809030a0503100b040315060b1305010e0f1237080a05041503020409050702070303080601110708070b0325 76
    0x1c01441031026003000240550440c1c800c1d40704908500f40b103000c4540f16502c4049407001010309010301d601940c0f84c44040344081d0701850a206080680d000c034803031240c0d64030000c192140c1025200c1e00841380184405000035100300701100754101e4180100381c0149500b4001801c822010f041e0b8414003042c841800f480c1c40307021003116900d060310b0900c00d03601c3c0c403224100340c2070320186d038080300d000340c008140401000183c06000d03405806000e002d0200d42d07241c0740d02a200d072040001ca41c804170a0b242c001c200550160941c04e481c014001c2c00c080c01c0c86c50040100e110690310900010309900908004c2c5400d4643c101c00b4541502803011030340c806403410741440d40c544030418002c0d043e4407000c0340400c0c840384a0000c403401b5042040e0a104100031100014000c1d400901841c0e240c10304210000700da440c03001900c0000c5036010396414115440d254010b40b00c3c0c03440180e40712003d00030032102044809041002c40001d00898807107660328a0010500b140403040cac4599580c2d512884080040940d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 297648264 1250 297647014 297647017
    0x705030a180c080102040501091401020705010305270d020d0203071e02190b09100305090a031107270501060c080403060515090901060f050105120109020d0b060c0f010605090606 78
    0x110900c0000400c10140d00c03a20046122028004118003a440404500a441034000d80220385082c0c03101d007540b5840c0e004056801c451041c42500503400f41d90308110a601c02e800c01c1e900040341c007612a40c101d41b80c0070400380c01200e25900441592007004000d600582c104517001d40207000348080c5041c40d1055450000d4020340ca104559042d01d8600c030803042d5034800f4211118428411401e4007d255103030810b01e1250869420188108412a07d01080500a010b0544950b030304101070320035880d82d40c1c4d007a541c808048a501c4441c0c4079880c0042900c004626004035202520541808810140f40450096650582240301082480c00c8100c000541c03000598041c0c0358801004103007603454460a01c121184650035552150000c0b0070720509c03c40c10f500c90030a41d45c090003681c0d20307261a1001502c25102d4002c0d2007040103407800042000c03520a50207010b040f041500003281408840300050f0258114583e02101500910110100091b0903c1080014035098170980e00c0c610b40080000c80e02d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 297649514 1250 297648264 297648271
    0x105010921060504140d080910020705150c0904060b04050418050d141e0c0d0807270e07080a0506040603120f09081c1409060901050a2303041208070503 67
    0x60382e480f800810100582e031084481c5801c4103104030b621510841c50300400301003090391a11298060310b034001c602804140203c4940c150084014854402824080c6040b188010841c02c65910180a01042580c490095400410016400540721810481000102e0b5002d49503098800721103410800004c0004c41da402d03094905084c0101100c110f0100d5291600c91045004480c8680075400c4410403405005000c40443e10011510784184102c42030f40c1d50b440580b0050701241900006142c4081c0d44c48810706e90380c0c2d2a080c07000220303558486040c043c0009941040125034080100310074070510f03200b0682d008000700d8040c85031a103591035401d4812010300688040118516a60660b117019030303414401031250208442c41600f580c0d89403041c4d020440140b800140040c0c0c00c40300d455400900b5038103a18801850149044a240e00648455000b8034000c8103002c404507944520225400e00001a90064540301e5500e2a141c5807405e882400002000b0a11204070140411158000d003502d52 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 297650764 1250 297649514 297649523
    0x10e0a0b06011d1f020c121b1207080a021503040305040603020d1b0e030d0815040207170703020a060e0d080a0e1e030c0705030303011a0901030b040e060105010921 72
    0x8114244504409004078000f00c0f504a000340c880e8201800d80d80308900c10b01490740e425641c409444904220b05071070795000c02c4000d40d007e54038042c0030100688107820f2429006005449035070401c4c42e07050505006601405160308032040f29419802c051a44e42020b6403241005403661420f1303600a04030b4003d60181000f0181d002c00c030103180d50407940c000983c6140d208040600b0300881d1034010203c00070490051f02078080d1046960045020302910703801111180d4141441c92402c1d4103200013074215107001d890320104d004003594880c2e0520000e01125010307601400d031142c80d42c00e056060345d0100c606e501c42a40b00b20407403a0000e92114500707400000800c40801e00f20301d22522249040c4403800d002c401e8145848501081a00c000003c001000707441d4191505c05a841c0100340d10b0380801d2091040c42821031150250f07445064009108070901410005803030010301c004903044982c0d500500752580d2107940140030395030b0480c000d2001440301118004034600c1075a50100d0362600b1480090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 297652014 1250 297650764 297650777
    0x31b1c031706010c0f0506060a0503030a05040306091a010b07021f1b050c1c120203090607030f03200304030e040209012001140f0403090b070206070b041a07030e010e0a0b0601 77
    0x2c549038810030043c0c01c1582c1004080d140301500e0f041064668038251041ca21402440e240014141004400d4464007500780e10b400e1306013031a50b10b6200140624203400c60306a140604980404c00d8070900f0315001e05911541c9a4580e40e451046c00505000c00d0350041e1060405030748110b0040c1c1c0f2044544280f00c98030f01404081c0d40e28540503103008100b81c034066102050150040c00c00d00159440d4040c0d500403a000c06119040a03401da1307e9110707444195412135000c05c20640428060030440400404929001681c0503240c00f110500002400d180c0c2e50104c4004284818168082c070350103400c9204136011440c242401c1c001920300d400d100124030400c08100821590001d082d40f01a14040a055440d1801d103002188081300d020304039400c50101d1701401c00469569180401d54449a0340034122502d002c0e45a1603801802000810894140c450b90000c81e00f403486035040301d40220340c103440c0481d02d0004c3c940124203450320600400c0300356000780c066101041c81c3e02d025940290f400e09040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 297653264 1250 297652014 297652021
    0x10b07050106030c06020120030f041b0e0c0307020f010b2d040203070c0b0a0c0507140f0109050609150f0109050619030c0306061d04030806040b031b1c0317 69
    0x50740540030952000e0700e28219000b001420365010f4020864250042814180003502c0100381e40c22400300b81e03030b2000703132040110004000030188101c3e00503000c2e44c21900c54140381d0702c0e10310018140044509500d06075021091260442d0108686c00f59011500300070301201d0710348008200c00d08003403120410002c0d4600c000e0340011141a03c0b40842c580e0203042035503607240158000c0e120020510084550300c40c0710000a2490096201e503000d101d00740e41c0d482d483d00c1d01944400d4403c01e10310040320100e001307104400361492024420800e03100d11590140890b4540094050b0030104588010802d03040c3c40400c1081c901c500c0180c0c01d041d03401c0340d400001c1c9038407180040703881c2d010f07143c1c500c07050703c0b103524004014401c114402800300d9224030300130f10250340ca07030361107043c4502d28500f242500da4000001c10002400b40740107591010020f44005604000e450000345000c00d20002820075041a000441a0381044560911511116450b011042c0c1465400034500703200030108103000008600807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 297654514 1250 297653264 297653273
    0x100911030405250302150c0d0503010b0702040f14041104050901060602060a05130209040c080d0e0f0103050601021002040330020706030504021c080d150f0501030b040e0102070f030e0612010b07 85
    0x81c2e070113542c01411200c0080d507502524400f50303100c400d19000a200e0310a4203146907201d04e003101d040c1c030740d0103002d50b0a03c0210b600b404040c1100c00904040103850303541d030052038a480d01c001e5218602400303e83c1e088142e2139003880101d85000d0684d03142c990501c003042c408603400003030740e58000d0040840000e07942d403006140844201c2420009600001c0c40c818003007444203444a80082d503640b0025140c00168054060307482541d604c00058000000c0c110302e550540c043d0340b0139948660180140c4104510381e1003200100c2e0b0054104071000c040c03150610a144041082c001410104846e5094080c1c542c4040a583d880b040c0c800c080c2055221000642191991202e030b0111403442081c45494100324540801c01c0e4100341c400e074460728a03080d001007048607540c515a00301d4202c22101068641010700440203800b0144000ba0032a4444140c8217403600c091004160940c0114555207025040d464010000c0024501d00f61182e1820310402ca0800340c6022582d0448042c04540d80e602c0d010b5151 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 297655764 1250 297654514 297654583
    0x1b0e040b030a051c020d2c03030a030c120603020f1512040305030402120604020604170a0c0303020705030d05040302130902010c1a2d0c0a05040b03100911030405 71
    0x4050381601442c94080d0070014001499020f9807818200a10019800748040baa5401c040c15400300090020152446803510500c03011150441c04110320380c2c0c07000708004a807450f0311240700180002d40d1144104191907015080880380c0070600c1080c00000d2460f00044c038421180c0380410303c43e942c030201405c0c41c00921001c94555180d101405441d528050401400350b400c2240c0a0b4002c00039815600c2c0030b42c0000c130712a403040e81d00800450810b8146030b90078008000f000215203242c803418000c000400d4085030094000c0d4030a900505541d810072080c035060520700f40e1400140002071100f807005a46012245000c003060311000a4003410500049480e0814460b016141c00190750034200f40503007112180f403050042e641110380d1a40c40012400c071080c06d0b280941c1210001c040401c40c0c120341c05004040c6c00000d1310b040c504241d291003018119601c183c407507105203200041c080203441e01901070060500e500c1044682586402d0301c2c0c10f601d40300c1a80700e180f400382541c215407458100450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 297657014 1250 297655764 297655781
    0xd0e01050d050a140105030a151a150c071a0702060f0d0509070905160210150e010b040f060c0308041101090801060b12151f0915030506040b041b0e04 66
    0x100705109a00340722040c0e000400d095080d44c00d400c42c1640000c91603040020b00b0001465102c2000524000290880001440c85844020901400c0050007056658402480c601c501454440750b54a01540d80004d2900342d56a01a0b0403800391400c40300a0b580e00c41e000e407a2266010b4500c00d81d28141e80542814070311817540d600052600d80000d01800b810001060700c2521000001080907482d1038003550081c11080010a005a10a080100d04c04005803c46280e04801c442240411a101d8140c5030510100b60070208101e207003c9030401246249015041c014500303400c010398072110a403002407002100401c00717803510114a03010591070344501202c1000300100300003049800c0d114a001585540103070550003a03d2440d802146094041032a00d1118240c0100b0f1618820b94140d40d01c0302100703102a00601340803100d100000d01a4611560500b004043d035000545880c00300200000c0f6084901014012850307d8840c1704800d05000100000000f942460b040c01d202e0240001c01501510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 297658264 1250 297657014 297657037
    0x506060f1810110c031906151508040c060504030b0c13030606080307051204260c1e010f03050907060c0213231303090506030411150c1e0d0e0105 64
    0x142146182c10340c0c4003074800d0030207078803c2c20b0f12400040c0c0010555194540d800007182070145901410006032035600c01d132420005a048558465582d17504040a0b006980b408408030301030408002c02c00c04203920070000b41c038403420500c2c1051300b16219000180e900900b0528413400c00583c0790025408203030b182000b181c0c802804c0c4105a1901ca01c140c03a80c00c022000c0300d041c45500e1214001c0700005003a5000d944004000419007841d41c4000d01c919109220000e0090190312035000d80ba0b190072618403004201c0129820b12901800d0004058421301980e50080620740414401121404a54034046824500e04074140300d0150000907981007001c8810301502c0c0c80c00310b06241c103d038000590304c00027601c0511526250b54101100a003000800c034003c00003000314400340210300d0107001850b0000e020f111b41740303925000308000c07035410b214400c80c03200f84440c08100024a528200224004a15040740030b000103400411220307a134820900743c2005200803210035400a0344117009071104004070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 297659514 1250 297658264 297658279
    0x6120807050c0307170c0604050f04050c120108010b12030a2c0307031109090a0f060510080d0804050c0a061e02120313050c0d030c02090a060b070819030506060f18 72
    0x1500d517113070409004207030194018003400c00521030303600d011710544003100d0002c2c180760401580501008004c000080034400100000e0101030410b080060015010f84030a000004900306000200100c9094520607880b80e9481000014852540308070280340c98060700c01030f0504c0f000b108030350072140310304440d8881c3c041c4a003030800000e0061000320180030312026252122142c40321007026448100c0008080c02e9040c80480c1c01000801e1a40700c9030340702144403002d0100e00d460700344080c240f10035103046000248080f818001880400e001c1d480d04448112004d07800203107001c2c0098418682181c2c0c405041c101580c4039000d250080c0211012810810450b40d0b03030346400c4001100d1741503001004d443c01c1c0316441c4d072182a03040c440c0742e940c0c0041d0140c8035004c42300420750030050bd00e00700a00e4460202c0e04c4407000605540208050710384144a50b21140d11400110b1500100302d80750210b4104141c2010103112480c0c444000300e03070442000c92000c0790307585400089102105140c102e1941c00c07070310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 297660764 1250 297659514 297659519
    0x18110f12150112020904030f050d06090c033602120106080d020f010501060503012309100e090714061620041a13020a020106032a080106120807050c0307 67
    0x1c504540c01400034441c846540e6260410401542a840c0b070080d0895042804580428000d1b54007094003807042c50708500d052400300342c2c001956465440741508685410215040e60f800d40a212140d02e200650b8034444070014255103241400890300c003826008407505981591164914903210808a6000344075041d40c07003480c0c1c0d9440c1c000d021058018000c02580100c1000c060003898100e4201da51441d0842c0d09103800011504a01c00107480d00820811104906440c1c0400c124425611414800201071800004c41c00505c0f00030480b445a401c042402e00c61000011044420440151405034032440c641e0601004001d40742c8010f0302150808000700b40c02d06959510032444002074809001107009098198440141c0710346003035024a100b01d14885c00000c96003e4440e412807840041011582c0c1e444420002220580c0c6030822821904080d0340c1401c290107490003480510001c00525250041c0c02010855158005090b440c0000d030b00b006216080100f20704000e4020140c8908a6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 297661870 1106 297660764 297660799
    0x31b0a0302100b130510060e0319031803060212040201030c08090d080c040306021605012003130809060c060609010603140a0903031104090c030b0418110f 68
    0x80d024400c01d00d8030b80131809010b004807030b502d01e4800c94500b0030070700400c9040d40f400014040e074130588907825001c0c0302d180c0441200e0340615281003c0b40d4050182c0e2801c44542d40041d1400d8000b0540a206800390002140150710076201000340d6050a0b101f90b07001407049031100029000400941030746405512043e42c090200d243c841d186c603881b03a942800702e030050711030004100e15220f10f4200300882441848445e50041030f2035040c0380050390b20034200e032100407e58100409582c0300356041003090011b4810041c0e0007000c00d91586950004c0c5039503428120750b424420604040000358040c0a8410116502010b903213900d42070b0380f540490700180091385021020140c0d20b0b880c10050600200141001d04010500403c0c440c0c08010b00405444610514600c6a1b00e800b40c510702d6039000000b001c2515901140c0c0d4035200480c0000a1810252110056048941e0700040e020b030701c = true := by decide +kernel

theorem cover : BRFrame.Cov 297482014 297661870 := by
  have h0 := BRFrame.cov_init 297482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 297482014 ≤ n) (h2 : n < 297661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
