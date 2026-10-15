-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4039
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:55.363982+00:00
-- url     : https://prove2.me/submissions/dc40a792-4fdc-45b5-ba2a-814f7f5b5ca3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 726258992 ≤ n < 726438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 726260242 1250 726258992 726259007
    0xf08060f040905030c1e0705091009090311060c0f0409050405070317040602061501080106140c070906031b0f05060d0b040c0816090602070501030c17071817151f06 72
    0x440d241d40100ca001b020040c4d90b80d11000524100d8400602ea020314001c14401c030218081c0c0380500102c0c40010110f060105406111040740c441e590f103142c00b8003099460f5041c44000b83c03031604442d0081020301401c5298409440c02c2d42e03040800081c0746c2d102e03841d005180c81101d5000604c503040b4848460301202c0004003038422100740d502510450359442030902840c07605521500d01080d01000140710143c400c2401c1c4c0348202e094203600d8a0059043c08083c90030b02951721090601e9240d01c010710030401301c8a0100c01e280d4140514506041c100300810881c41514000c0602038800410701d803a500c821030f0030078039680c80301401c00c00220560200080c03001208079003003001c11020305a241c025512680c030300012540164042c0030421704010046010f40344401f02201000420381c0b01030350035548148801c0c00751340701b0307240e9600c0000d1414014545030000d6100d8504810064400c000641c80400c9503010703d50f00f03240000c86a500d4516885a14203950419000d041444030049480c6811602 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 726261492 1250 726260242 726260257
    0x1b020301240501170a090507030c1206060605032703091201050124090302150c060f0109150308120a060807121a01061d0619081f060f08060f04090503 66
    0x901c005440d1140019103000c03003442e8072107010b0032119001508040c0107034051421a48220141c5090903641d450340090030707003180c10000b034940200a240d0100a00da100c3d44004101d46d060807802c500c0d1181007481c0e13032007a1041d059222a1840c07142c402c408000d0046502d40b00d00140b50200c1481071401c01c0d80201401d0180540c1c60b0006100d0b6240d99104800c0310017541070715034a24070b60318195802d00414501c015000f800b041000c0c001200c017504188503080c8644a40710710142c9a6140c140183c050b1201e0f10820401d85040c01d1007803010400c0401207400c80c440070502d040b610f446142c902402410103502600b1a40035481002c074002d40920742d0110a180112b0b00a00020f000c0700a001180c4420b110780404240c000c01ba549100b01d82c9209900f922800910007402e00950000903180d0250305204040015213590030000c01d80030f0200b1034040325000a510003a4682402c401400d410035400e048020f100345a000140656661145ca241e4a10040d00500100589160080c2d60760080c26 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 726262742 1250 726261492 726261551
    0x605040e010b04470a0201110405030a1113020f07060b04050f220c17120307050a21090c05010809010b0306060d14071d01140604061b020301 62
    0x203000044085424050314203580401000c200b02601e07584200c00c803c40408102228031001300c414143c941441007009041e010350482096852010b030750024211841810100c0c8000402c0c00203100940700060100d011503400361040641310b242c003001032030300454180400c048500008401d071140b648800a004140c1c4580024805514170304200400da5500b1124031009444110010b80046001d0a40400c0c4006009071403c444100b5101c15031045503d8000c49640022011034100400080000b00701d80440c0b00403c3c2d003942032002000780a8464460800b0402400180c0441c03000c01504810780850300c0400d003003145129502d03003010081c2080c450f40e40855800000510400c506000c0c0345114913000700904101e0391540e04100b00782d480503100343e81040c8206402d0b11035580030002e0b0302c003030042c070500441514244a0a1900c1c0c281c1600a40c40c002c01802070704c9032680b5610700780d400380d03403050600500348264501e1100107840640c101a50641c01c084003800c54907025090b445c400c50720075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 726263992 1250 726262742 726262769
    0x20f07032901150c083708190506212d061f05060c1506190303080703090503180f0d0309031e1a0f0604180b0903040f060504 55
    0x42801c620340c8001d12401c244142e502c0c00c56a00c0e01d10641c2e40c0443c0b103120b404510b00303004500440604840840880100603031403040c80a91160f41100c0103100761a680c54800800d00c1c00360390201d40900303c0c40c8403601061322417000c6043d941d43c2810800e856484003081c0b200a00388405030319911045001049400301072a80348801e4a850244000e01c641e400000400f01c54644c0c10b1141580c41604075402c03005000c1840100301560740c4e2005195030594503008101c0400d00d2002441c1d0194041c0c041481010340b200d1300041e0300b4080403548212501402c02040550351000306a000c0d160191000303142c3c0c0400100f00032800c0800d840e800c180b03003090f01d0a4840f01c1c0b0182c20b0141e40f050140020b4003054142004000140f0100c1e49042003503405090012500c4241d962814400f00d0641c3d0402c3c00d4400798104050071098042860f40a0001c4500b8096090020340a0324100c1c024800070b000e0700c24070300004d41206401c1081350014214200c0028100b96101c00081c0300c0c2d04a4003901101d207200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 726265242 1250 726263992 726264053
    0x1c050a02150406350a200d060501090e0c0a050708161112031b0a0813060e150a030f06030215040302040501091a01180506032e03120f020f0703 63
    0x4401c05009240c0c00c40d50041c4144c8842c61180b07030b070400001c2c00641e64603110010300c92100c0445a000905805a841d001d894252038143d2105440c1541c10003410011801800c010720301c101841c080d007051119a140340ea4552403802112280b2400e500035042103000192030000042c44041c50600c60301880b00c1ca403484c20500100000d41c00c40e10540e1826600c00c1c0048041108a00a1190b20a40c0641200d03000f2050342e0351201c551300480900000003400203000c00c103840d04002104a022001c860303250100204c100600c00900410901008040c3d40d1000018a120260710034000b079a002800308800c2816901000d8255000c1d020890045080100008000d0014001c600c44545913880c81c00c90902c82200464000c441161088604d0b6800344000510742c54040c002d50090351740c906078251b280111140c0300b24181c0741d070301c0c030350f99101e0001c2c1e04001058001c0b2036403c6d84004c0b440c290701a81a51281280707000c20158070261103004a100000030440c1c0610308000c800c1100c020440d00700074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 726266492 1250 726265242 726265277
    0x3070912110429040c0203090a03120801080d091203032901181a03040c09020f19020d0e04020d0204080616020106080a08030601140d0f0603110d021c050a02150406 72
    0x18488040800c3c80b50328403000d000d00d042c1d04100c602d030a10f8411682022200000030710080920b9106a602c4100c011800e00d116500c0f40941d4003400c03402d00144282040707903c00030011b844500c521020300c0b5600040c1d4003054825002084002402c54244440f05c40a8140892241d0011480340c0400d800c070900341e04140a00540c44112100c14488141d101100d08040c011036000034011200060409008100c04d0a00c1c40988240c54048106c941ca82210380e1000500d101c0010b104c1e01954015205005035a40c000300e42d044400c0d05440140e107803103c0f01110f00103405150440145405a00d04000300010418510308007059071307600078010183d5841005440d4281d480c405841d04c00200006405940690b00c6000b0300d0403c0c8002d07910380440340c02c040080710f04000758044c0031903c8a000b0002d2281c1000354150018041350108142100d660000d00080f0240c0f89080003140c090105030144003042c0700d00c1c0c3c450390b00689011003205a4448445d5154028011880800e6201c030300d1120a00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 726267742 1250 726266492 726266531
    0x7141210270509010e030301080d0e0a0b0901031e0f0203040b180a1205040e0108030702040509030309070302191214070603021801080901060b0a0504031421030709121104 75
    0x40c40a201c525452401d000580098a8000c00048440d9259410f524011004000950080c0310071405454400c60704213008004c82d80c00c1c603a180c0725802607101417000e40141c4081f50300f488800d003800240c0003a210036000c10703200000f00626140b0310f00481c610110301700c1c0e001184998403551420407030b66940c031031000c043e84188401e004594811504000010b45070748041590900500f001400c041e503624103040002e00c260040d20b0a40c0020820008509060007915017207805900514110714000c2030040c0c0d00c5003240f03c0a0300c641c0c84801e00c0d41c42e21b40c40000e01d90152200c4402007103101c1c91313410143c134004041c071412a40c41c418a840001c14034402c0c030a0754072100b0000c00109101f0502001190b01d1103028240e0b4085540c0c82c1c40c0018221001802006120381c00d4a60300d44079480c1d41414500c0b082100c0803071403140c0048203243e11400881c1a03482e90b0310010704249499441c4c3e00030031a503007036040e00074000c1c3e401060101010300c030b0403245211028408403414000846070f42a03850304013 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 726268992 1250 726267742 726267779
    0x15010e0d0503031b0903060a06150801080d14040b030a06030317060306060906130603150b01170711030f0307022803090306020a030209221b0504060807141210 70
    0x1e40040c0046200f890061004108001030303148881d0400240d42d000078105201510b10ba00109d84d00c500c1000152500641001c1103881400d000e40c007503141160f1142c41d24901101c40082144182c11520b200e0a02c07025078010340198030f2942c2d00ca160a00450f00280300500094011a540c0043c4400c08200d0010b5203208d403501401a220b00d40b00c54082c0900c00502820741c0740d0040d070301510b603008051244103140040d0300801c1300088441404107100103d800841509040210711520301c20f800c080014110b0f04001c0b0361400072800740360382420360b00b540560400d08803207030000001c0c4204141d000821800007100841d01d446001c0954201440e224400c00004001c9019003008101051240d406005c2030142420b002d1300c0e140c90000021a8035040b07020308405400541d000302940c407154410440700c0e080142e00842e00192410020f400c0f800b5504c03400c0108105d1900107000c4a05c228080564039a5010509859000360030074012503440031078500c00034100102c4005207044442c210501c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 726270242 1250 726268992 726269003
    0xd050108070825090b01110a050705040510030b06060a030216051c0306081f15180b090105150703030902131b09150c0501180f06050c0a080601081b0315010e0d 70
    0x280d40c07078036007004064540d1795200360500c07443d900920101e040510658070840e00c520b0107048010308020402c03048030005032440b5904640c90000b40001800c2c20001034001c641202c1c03031130b01c805188004401920030300140c0310a461919561004001000864180d8000e03880140a591030200d00c085046800601c40c408450740480700c0b80d602800c81c45c1d605c60000c9004000401c00264180700c0b004980c40c15400b1034912002d01015051400f244e00c18215429000c0b44c1c0011194508000125138405075610144407402c0010358030100341c029401000c10703e0b03000e0320143c10307101c0340d0340076500501039050700d590203440054422458502c1a0102010390f501941070750a40a5034040c1120340c1d1212078400c550130b650300c110b40c2c00140700100030019544c0c811500d1000410701071030002c00740c840c0541910740051041c86030015858204223240d6200a0a20300102c0c15038a00b07101e0015159032441451002800009022a0500070403c07180b1881007a02c40d030441c84c2d0b03003200740800f1a5000d080a040f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 726271492 1250 726270242 726270313
    0x30309010c0210030e0f0d030b0a03020a05062d07050c090709260f030a090605070b0105060a020a0210050c0f070e0106080619120c090b0d030509060d0501080708 71
    0x10301e42100b420307110f01d0941c030f0005480f90155511514142a0600c48030056100c61038001c40035616000b00b4175807a000781d500318086440c5a0214044d440b4901849105070707008580e058024544400c10044401ca00c051111920341040703c0c2e0102e40e00c40a005c0c1c649006005d50110142003140c0040d0003031351281d0752100c901e07190851203041442c03856501041101c0c56101c030850004200080051211114081c0d0f83c0c41502c0035018020000e540c0c0b00c1804c0c01801c2c458500071030068260307141100d005450061761010b0700300040b400c0c10080040254850300340f11004810030342c008007615102207440d04581d00c41c03c0fa9056503555145900c22001c802400e080140700080c030030102142c014078040c1040040303529000005060807100d40180300762032102c401940500942c808440020304100e041040488a0b0b1000b062041e0b20390040942032200007d0000d181b5142e81d400c49810329090101006256150b400003900c644031880380018600c200d03020a89249030348812a418415096030610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 726272742 1250 726271492 726271517
    0x10504020d03080a0209190501090e190b0406090507030509010b010212071104111210050105040b0d050933070509030601030b0705210702010e030c030a08150a0308071103030901 78
    0x9800c2200103004403059038007800006e0040d150f4a24184445550038040540030341050001020b9594a622a1b41c1c82018070041c000c40085620028402d6201c008010800751002d00204d000b81c00958050310010b803501c020011f069a165015034000c0c030f046002481082803c1c0b0049940307407010310710208284410040480000e85100303400311044400f801c082654000c0100c40c0490381c1100d503102800b42108030401500d038113a6549413014210900b0140d0425003800c00141d110f015007001809100d90321004503013410fa00308400000d4501420340c0e00710140e1050400c007031942103410150140411040882c0003107020305d0955a14403006801022113a18588901402040103858441400010400c481091040c01081c145004404156a4240c04d14503c02801c44503680951400d98000748102c058003170001c0210b901d401e1240c50041c03440e407a08440d200c80c001c00600b01d00d900040c5440000200075414014011003030150000b0394120201009141e1684124480c0f030780000c6002e481103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 726273992 1250 726272742 726272747
    0x2030706031e0e0a0f3504050d050f0d031e020f030609070e060d14071e1101060f080f0d0503010509040221010e0c0a0603110301060302030714070b010e0108010504020d03 75
    0x402070922000803948131a0aa444211041101c01d20503141d14041003540f200441c8010912001806a040200601c4810400e00c02003030040e07000c1c4511a1002c500da11045c030604001c18a80900c000c0705945150030101d80180007080d02c2d804a0001d2044112141486611351003996980c0d040d07008070a1a580d1024204685804020005403c0c0700e03070b030b0140f10040d403600300140a0018041d0380c001000072605032691800d00e00140410300300720788511b200001171884001c1528501c1c0c0e9040c086010340541e240980500f10b16005810741d0358601c24000b8a0050000704a41040080e800766491410b40321004c44461100f40180e580145a50000c42c3c01400d012400044400218002211f0740224202003401e43d080131000c081c0a03403141d4240b2220b03180c506442c01c010282c0c0d04040046001c4a514144580814820707002859804000901190302400840d600b0301e0307039030349030a036101d41e40c0c5030044041c0e07000e0040e00039000007600045201c441c148604d5002e143c000b44080d01000c1280c1c0d04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 726275242 1250 726273992 726274001
    0x5030c07110109091107061b0c0b151f031103071704021302030a1415130b011808100506100503040f02060c0d0c110402031003030c0812010e0402030706031e 69
    0x70a04101c070110340000d40d0050380c03082180c104918108690b603515030b070401c68103444c61802c1e8000d0600c0740d401c0010107640c10148402d02254090608011a52100410440007524401003030304160a40080c1002560203941d82e0545c21140e1810854402d03c0550380c591804121045004110014541c5854039002c2da400c0b80c1c054801042c28444680c1452044140d13042030721a0314825403a1610320003003021141c815940000008144034851b14084000740001402040c040b055541e078808480c404e03485000d170380000302c1c03180c40705514a5680d100301d40d41c0e424215070310f030030180e2a09021610f140313804641298600441d0740c50300e0030f58455448203152840202000c03a03101c04200a4156000d200b4480048a00c84540f11490103090034142181c1c070701c408070041c520442c410800c01018151040f42c00d025290135241c86009009540342076400c500c20190a403030010401000000e66840007200d8034850351099066508841d918502134080c5c0b00410361030061402c80461030307514031000350300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 726276492 1250 726275242 726275273
    0x507091103070309151109030609190b1515180f150c0a02040f0e010b0604030f0b090f19260a11070906030305040614090a061b050f0d090605030c07 65
    0x11041d0360b0342034480c042d003181d846c006001e6030b1110115aa185514060004a5020810354050161070000c0003885004880f5008001c1032a00002c000c50b49200c3c01c0545100a608054041e01e080b1900c0210690940c100440102003c18400005e14182c100a10041a00000a0105112164016600f2805401c0340b06c50320424400c01d0100405a540c502803581c004c00c4404000801301030034001e903829030315103880107400303080f08000400005040044103443c4a400104e078807120b49419509a050400c50350b5007035261311441e096000c031030349030300600f100007031241c2000d01c40007000c030401c0001c40f20351400480030b4902c2401241203250213800760f6400d09240340f0941e0141a00c801d16030017190f1081c2c2050780010400314040c0074464128144400540c1001041ea0610989000081415100380140010070003030089072040900c200d526040401e40c4441a030704500740700180c0300c0d907585445000034001603204900103800b90080e0700300d0313021700c08980566140070b00360740b94010700f00c03092030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 726277742 1250 726276492 726276503
    0x14070302390f0d050f0c210d110403080d0b150c0105070f020d0e040518030c0705040c170a0b120105070201050601030c0905010c080a0215010b0705280f08130905040507091103070309 80
    0x1502031400020081c11041002c0482800395100c48d0030780082c0c401c56241800c50110712108000600210b9418010381d211414903550118a1204902c0420100780c8145401c1444c07020105260303080200642000b4407c1107284c1c3e4002080301c1d1800c04aa8500030b20503031314046003241e20030010300d01307186d00300980c80001c61110744030554290690520b103501541c12004250080340050010b440d09000c0d0011a034030501c0d040f841200c0d80701d0b540303082d141c1c0580000d202c3c81c0c1d540000c0005440c0c60720300040c0050350030001c00c500c1c908000084d001c4e110403184180040d00c0c000756500e00302d002c0c00c400000e444041c1e494416582c45507403110016403021601d0700c1944210b07031301a550601c030005210b002e0030102801d15195003581c80d05900e0b0070ba4103041c0307021000c000401100c011040080c01303004031390000383c1c3c21000e5143d820206424855442c6d1600d0074034400a000c2500011508160300962245044911441d40d0b80111401c8888481d081c111204040011840c640c0c82508002a1103002700c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 726278992 1250 726277742 726277753
    0x11209020307080a0c21150c09030c090b04050109020c1002092e091212230406031a0d0b070c0813032414070302390f0d050f0c 56
    0x14403a813480d00c541607804540c1040004014481602e020b0003a4078100c07134512014181c940150707907140a000d0342e4886207001642c3d60070081806486003004070011074000f0313040340029440d82c46840242054401f8503010780e0400f00006030000481c402c40305408010006094481240400d1a0295000066041d8000c2942d020080f014802884c00039002c0080081803046a0b080c00e4080c2c03400c0c145278845446002507040c0100401c80d9003a02001c094445d1512000d414040680880402000002945508404100887c26642650001d10714035030442c021003c200d4030604001c085039409100505500887c800304401d90301802c0118000c034442c1100e282040701d402d0103c40011b800364415560180c04020b801401c0420a040003e4600d10003428040c0c060080d18807000c0d003070040c00540406600041c06030380061442c6e85402c2c4911410842c00014011340402030060440f2215800507005201e0140003041d0b002429104942003601ea507800c140807140d500095400034506040c250003103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 726280242 1250 726278992 726278999
    0x7050f0f090a0213060c03051b150709140607050307020603060d0503130e06012d050c0f0304080706020313031b03050a0b27060610030212090705040f0605011209020307 74
    0x1c18107098480e00304407000589a1000669a095607082075100c0010b10058403810303c080b9910600311018000600c00300c81040c5866078a4520b040910340100b19800d812a0a004802da40045a50122610442c200c050030b06140f082010a01c102c4000034110303441081540014188a40515403110340186500c4404103140c0f58030341140e00c0b0360102c0c1c0c00710a1650b000d101659a24500d40c0d0800c40a1800c0c0c101c40b80310010150001c008000e50901924a904005040300d102c2c104480e1220114415200104480784260b07969400c54056203015004200005c81c8183c400070030789412816000741c009500d4038580b11401038604622903120400d100c204080082802000050391035485021040031618203000400000012003901c403039460a981c000c2ca0b8910030000300c0b9038100700222408076414941c1c90041e0000c1c401e8140c40740c4400700010030800c507445c0101e50b550403128103131800d100303203410b018000046449c00d026071030100f03010344c0415403100900c0d0b1203201c52502c05030844903107584 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 726281492 1250 726280242 726280249
    0xc020a09020901020607170402010309020301021902010b030613080a23041e0906050d03110a051f0c09050a2706091d0d1e020a02060301030f060c080907050f0f 70
    0x810303801500400750002407201e09940d0410070558045068900362820921b02c4140001100000d040a810503858103c50429540d080d0b04841406002c0c8a00041010703203a41c01070701030104420168480e006d400005072900c40c1500600103180d0740466154603203038500e0b40c1a01d00c84001c201031140c5070b1071241c220030f2002c902c400a0014004c2038500c41050b80c1440001c04042c1c0040e044255103d0030003004111903155021003024280d03050800d0311423840c0c45403e241c60300d00c0700400545540304800c01d03202900074121080c85d1018010109000c3e808a0203000e880042c001e1207250381000300c85104000e466446a2071011034510b10820380c040c0000c0b80c08007400c4d280320340c000610781561800c4200c052420011f1902a910400003d80710440b0328500180c00964101807645104410340a1410018070074000081540ea00500694407544c50b8100300148400e80f01040312480c1c9840340d041d0080d0300800c100d0b84584104401440c050381001c0602c0b0808044170704c0c0c2608048560a01100b595 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 726282742 1250 726281492 726281509
    0xc0d05100c0e040f0605060f07020d0209040f0b1e04080901031407050c0106091e0518010903020c18060306011502011503260403110d0c09180201030c050f04030b070c02 74
    0x1001c2d03598085060080402c001c202c64000016044591030309500300050749404081d10f40c0c44c900352221039120100c0340007003507003152955030081d84407104008010402052111143d440c0d401000b901c030042d5140d02c070b11001041580801d85004075101c001a0000e0800401400c8500c0d040c0f5000c2a2a000b980d030600c1c105c0c00a513504008a40081445201004244584001001a0001803040039503241100c0041c1c13100355400c030701554581d0006016040001c00d40601c40344035400810180e00c450400a440b400200320301c51103015945521040741801035580e60250320024003420850b460004000400058024901c0540d525020312031031010f9407000c1724000358095400d2941051400d840030625a072241032441347c001c01403009002080d4540b2141c001a101541e40b030480480909000d6522040d980c4903440e45130910403152900f00043d0880145e452003030300e007401014450710064545002d50f0600d0051039205100800c0410f2f2021070301e83c0c2041003420520000702143d000b181800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 726283992 1250 726282742 726282761
    0x11106090c010e03030a0e04050403140c03040f1d06040e0f071701060609060c120c0206030c0d05010b030705180a0b162a031227051509030c0d0510 65
    0x1904041e4248450b560011411804080e045000c1e510b4054902d00150085446520f050701543da00c000107410940a60040300c0e040d00503003019a11a4092a03800703a0b00d41c0300f4000c204080101000010380a4a24858540001c08010042c680c0e995a1404d000050401d400d48000a20aa4990480340310381801050b0207096454030140003005841507076070035125950700c10002c102c4d080d00c040007103542c0505014000b83c1d004014006403410a03c00325138850000c54040c3d4008000018480100401c5005000e15003160000340200e03a640d203500701c0345000407291040800c008001e40e01004595a101e0344018000810f0481415100c245008a46c0c10032050051400450000c80c2c0c14050505c40c410f4003045d0141411580000008110119a030180b100030852000080c824807030b40c0c0500c2020713a0700030618003c600c0403141c5c00e08031700340d0002c94401c1078020052010594445a54941201c9101c00040c009141c1500610b003440429035085009a0706070007801c200f9414261980900003d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 726285242 1250 726283992 726284011
    0x60a0e011826060f070f0f051306050a030b0a050307051c1a0f100305031c0e01110a0e030a08030610021207080702091608010b0a05040f0e0f130c030809011106 70
    0x42c0214585415405480354030000240c40411080641c44240c42c65090324070325002d0104501c8072006d8600e402982140b821001c1e10180208100d540500a8650071800d994140489584141440140035982c080c2c0c58164000d41000e0045003030012000e0071800d40381001418042150300e80c3c41601582d10001b01c0001d400d030040c083e40320000003000d9013003042000200000e51950f40e546d5036a100301000010b601c1302c88000e210411405030700451855450b20b00900c02078510515100d4940d02050800c0049149900850018200065601034460344611200d1540d140c4404102500d1040301f43c85085115a84ac03001c0070f4258072020306485031181c036415448100d00c0c4108184008003c00c4003207d20141e5540b056119800301000341160800074000f69907100000085410748520f411141425a84a4000500b41b10103103401d8420400807492051a44403020142200403043d4809448900c0040c002c1c4040381c59500185036520f03050414225501e004e034011400c003d401c4815030b80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 726286492 1250 726285242 726285299
    0x3140718080a1203050c1c0914010e1509010b011b14030706051006030506031509010b06070c0e0a0e12031512010f060e060a030f020607020316080705060a0e0118 71
    0x102c654040c09001d80100c9801d51035400c1a09400b42103007601100247d05030301980700c080b2282401400d050006403c800704e0001c2c82504400703900035a5503586401d900e10b01c40c210b02c001400868040c4213607002c0000503511880c0012480b414108100b404990a172040c0301040c038505840441003004045140c4210008240c0745410a0150183c3c0c103a60710010a141c140300800009541c082000b180c1c41c049800e103401c650b160300a005004210090038560454000507422080c4460b02c440407080343d960340c450791200d83d5400ca00405490300c0c00c544213000c0e4004181041d0301948403014580c04030121003130078104218000000d002804582185609966800301c00d034480c842c5001c0e290142c51101c90010403803c01c000440d0300b0707500030310024200355544040503045546840844113b250018221620000c410f46510b00040c801d200c1c0070014800c1c4c420000c0c032402e0800c1600c0c111242a140d011211484400645081c21100b64442c6144811000411008421010400201d114032540203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 726287742 1250 726286492 726286523
    0x20c060a180b010605070609050712200a30060903030f0b06160503220501110c090c180409110a060c15020a0203070510091203140718080a 61
    0x1241c001c5080088801d114400356000b00d400003000d40d04540c0207113000c50342c0f1010790500320008c041c20b0314001c115000e4060300040070000104c46c0c2d8409801540302007141105540c3c04080052040c52442d04444003e00820101e1030718001244610b08603a540350000c42c1a542910341c1001649045070304650341c1003000c2c2450f5052161014412940d03004000c40c118050006401c1d000750280100c50712038140c1603004000d028002e03602406900c0d030312030349940407080c01440c6007222030150500050000301c170103074218400035030340040001c06030104400380c0301c0303502005043d4811a004901080c4606030b100c02512284146a80c03180140040340b0000b4041c03080140e181c0082c0e11030010005038687c4032003c00d800b00d1598400d1030b0000d000580d034048001040e8194003510f14080c0103406041000402c01141d81c2100e00414810086c4404c0c00038503440c1541141e40038848a000c00c0303841000141141d01421040001258940f440180b03a03035034005061808800c0c3d00119416042162110b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 726288992 1250 726287742 726287761
    0x90c1e0c0b010803030f190b13060305060c120a1517100b040e031b160f050a1d0f090f030f0c0c0409021e010909020a020c0f1f11010f020c06 62
    0x14058403d2802540c40c0d4105180c0904824201400034200d20000f002c80324214991944011540c40d80030f80088081902c0d102403030000c000e6480241d0300d070b00600000814103140b6800726051148030b125030014584845012400404d00c20041100301d400c00c01c0b01042d40c403020084840c184100c80c000340b85080c80c1c0324600c4107998040e51614012030820140610540e40881a100900501c280640740700f05a10002c5280800c100d170545104103406401150442054500300f0503680150780007501140d5079600c55148510705000811000c2141c1c02155009200c00d0745503410030030b803804a2340c4080704907003c0c0f03045038001c07244da441c0000000f03000b580210092080d61800c01003240d0400c0032078aa50080341c03c0303803c003203911505000c20209009050703014000840c05448200c0c011500c6030703c0b061000e0346d10128500389034824126007911441ea4a4008034150b0191041902c0050010708003c0560340f0603c1d104c0b8260b2107540ba200880c0c40e851041c805080f4040315003004103c03500340b01898 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 726290242 1250 726288992 726289013
    0x1b0905040c090b06040909060231080a08030604050403020a05010f09050715090b0a02070f0303030e010b0d11010c030302070602070b04120c0c0b0c0f010c05130803070c090c1e0c 78
    0x402050806140f04003079a1080151800ca071074140004c550004c242c6802c00c000e10800a0100100440e40010040808100000c1c3d8804000310501d003401901c54a20741c2d5240c00e059001400c14a08000240c4542400d402c010f8000307110380101ea04a0360035a59481c2034680c5502100031481e940c015074001d0200400600c001015403c5580441c1d41c40c80380300920140c0e607400b900400784000500313540d44600c00c01c0640d000705001001400b0050322031030010003401c035400c004a115070a1415035030452030400c0c3c0080e003069100700040003d40502c1c1c01580c00c1703a08000281c0505500b4001d00700490020300051510502c40c06000c8070302e04d094900640e1501c1c0310014103040054021044000862190803441900c0b5807401041d02c3d03c5401c0074951602403425032400007942042461b52040d07400c100a000d241d52042203c880458490f400e0560700e001d03850001c0c103d004e000200f0808481164464460402589480c0c6102c0750403642404002e07a44806060000c3e904120442c1840402d640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 726291492 1250 726290242 726290249
    0x4081c0605090f0711030a080a0501061e08070318080a020609031606110d020c0609010e0307030e0907090e01060903120c03080414032101230105161b0905040c 70
    0x90030069142080003107900040c004102c0700951204402154405014141c0c454000c5210421030740c0c1c503443c418004000207010b681403040f05040000120311140900f101280c000e04404407110700c9408a042181e0342d62001e4442c60078965200911411800c5a520280c50326000f5500542c0d00c90311404009e02d401001032591005070002d0080c0c25044400412450116400c0400410341d0000301c000ca03041031007132000c1e48407030324800101c5010121012500314403a00c0c2410007086404d00c401c0d0010703160f101c1c1500090000706400e1018003a403510000c590342014083c5094445c054503049840700000c003e80140700494200c2c4810020828000001442e10515180c0300e203124100390380c007034402d80300580010b0181344034900700c806007441003050755009051300e540c458aa2201c40300e0030802c08001c0c041e80c1040705031900b180c0360080340a5508600114180c0d5045c0c5044c0344050b441846102c07902c001ca0758003000701d00e6489a000b110750040044c00418100041070308143c42c007103100e15026030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 726292742 1250 726291492 726291547
    0x6080a1518060605100e090109020702010e041407030e06070c03051602060c0303010906050a12021c022718120c030702040207060b0906040e0303010b0d02040f06020d020f061611150408 81
    0x3041b201079842c3e43c022541110121100507848400f2480142c580e209110290f940140c5072019501100ea000b0741514094281ca031410000d102070101d02d5a210303102120201e0110b01c240000000181c480c034004c10f41c1503030181c038188000300139078000383c03055101500c070480950021006000c41290341c450940100300c200c43d050300d002d103070802a000c01c421212003e8415401050705071910074107046000c40c640c0e4000c00c04100c0c1d104110042c0070790045140c0720750301403001c1e400041100d41020985000c0440210081c002c544003003004d00341550001808400341d010901c05500141c0713940c000f0300403880c45801c2c0801c000f00200c05000a2040007403116100b5814120301008802000c0b0440b4103603100c8100496589580d4103264029116030341c0401788982c0c0c0c0f80070005649a0103d18035802104641c00e450000000c2043c06554810030b855070032a50241002800c00c643c0140750700d409404841058031545c02d5000e41c14114480100c5007074401e100000340301c0c0d00491242000782d69401c4801c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 726293992 1250 726292742 726292757
    0x160f0602010b01020705130207170a0207060302130512100507020309040e031201031101110f010b091006080c1e0a02010c090902180d110a0612050105010306080a151806060510 77
    0x100001e580d01c905d446840d000d051502154a400e038020f4049580c0786400c4014a80c100c00c000c40c000030150300418000d001030107070318004203205209008440f88540c0b04c1301410483ca045c130040010324a0303900d00c81101881020544480010f0b82d015070307403041d91641c0103181c540d0640024441034601c1120500c1c219003040003201d040c01000c0c052941541d4100b12100c0b02d220260f00140c400e21000d4a858440d80315020800740c021605400c48170100005542c4590540c442c0d8442451f044028025080400d01c0000001e0a80708050060004010105a83d080b82c0454070700d001415171000303000d140142d46030300c2d02800107504060303000c009010000d821403520944081000c2901d1600f041d091052a400f401c403001d01c4007202c1d81121800b0010200030000360b8603400540046403448200000d01d0403c0b000042543c003a201e09421146010050004501141c0e199142640781001c00e0661540c0c070480b488a5091602c6122800f9214200010700746080c18200190880c02202c03480410500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 726295242 1250 726293992 726294011
    0x80d1106180d080612030f09100306261c1106181506241b0105071d0d0605191401050105190306120c03140604020609010c0c0305160f060201 62
    0x11910b1890318145000115510b4050000f9054400300180c11010303c40030510941a000100c020b02c0400c504481140300d05804000947c2540d043d0301c0b650401c004844202c0981900745024282056401010f603103d400c0c0b081560416051118020f000040c41c0100c40303041d440040100541044805071009202c0300391311601170f604e002482805094400280100e1a940c542c03084801580d4601400010705c041c2d0b002d804070040c1c00c20002e0b00414510080c00c041440c9041c419140030362043e03601c4428031225000101d0704202c01da00c000790401140d500040c04500c452003500c1c000c601e01603d464149540ca5103c0303007980d40c9078800c94403106008004200ba682c000d0100c0d001c0001001d480c2480ca0713518501900201025440105001c02c00f40c1c0780000c00c0000081d14003980e103c2d890042c111811001220740c0c61604450007504000104040c985544c094001e80d10383c988214071841016849a032020300303113042200d2001400c01c50600510400d0500020840500707a40e20003003015514 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 726296492 1250 726295242 726295291
    0x6020d0510062c0d020307090501091515090b0702060904050702030309010b06090a030308090a12231905031302030106090c0320070204022113060b03160504020a0207080d1106 77
    0x222101151151452050132011902d080c8101e2004002c421000c112660390740d4600703405010f03c0b0342100380074048264041120358074241030100e4000f0954036201c0c0e141c1000c07000000c40c1e1000308181d038004d900b802021844e507180c0c001c484c81100c0c11382c0074507100c0c1440785015003991048282c80744a001d043c0601189500c0f18041c0104880d0585040e12440c0c0396200e680d400c021440070003078445040d406940c040d542c1c101e10808070020b1001001c1084064404028426020304094280e04d24105240c6944003403061001e11b4120200040401200400703500107400c44256a02100c500e94480d034a0080450301486400e8a842244a01490648258a18000c903128502e4001d1149030b0210b1640c0840c80301d00e400f10072510956030341804509007111070b060f40365805081203480e64140400820107080c042048032881c3d00084c0160003a6003000708200c060f40000307030500c00318480d100c0c000513903200810908424003442d840b20780400d04051401420090001c0010030081000300b404805540f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 726297742 1250 726296492 726296567
    0x50a0e011505031e030d110c0604050615060307120902010905100c0c0e01050306070318020913060507090f140616030c1403030c0d021e030702100506030a020f0d06020d051006 77
    0xc50001e0002802004840788600c2401184500f108c030388600b02c100020000000380d081d009420104041100c10a00b0f400c002880c48126410b10001d9180740b031072030504000780c00c0b40040d1031050408a80c141d80b00c0c0e0215960040d0054034500150307510b408042031101201114000d0140c0b00654980c56061601003079440310f02801ca001015034130b0039040c110811060700f5001c0780764010a07407042810554900c0da00d10b004001d084c1d940c1e0b40303090045400710340903100050440d1180c00e40d20055920748a6000140d081c20141c035900315104000040d000da04030100002c0b0a4400d0721441a016003e0030444541004034a0141c0c15600810601c80010000e000395818284141805130761541d2000c401075a4000b10a00b803400f158002c41070144081d0080b680c0c041c01030a040b41048190b44500405584e035500f418040c1d08161040e03e0341c040f0382410111905894001c000c05850102142510300442c1c000301e88142c55041d064606008080c2e21034854100c000c460083c1806042c500c10802e603480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 726298992 1250 726297742 726297757
    0x3030909070908011104060f020f1e01021e1908010303090306090206070c080d120603082a030a0e010306140109140a0801020c0a060c05030415050a0e011505031e03 72
    0x14406100081c1d1128801e44108003c0c00401c03009000d155001900030142c2d1308030340a4103001c0303000c1500081a103403001818650303050b1803200070141c0254003401002060702035940b4247c0ca5400700035001d003403034600c40306900c8807040c01301c0150b58204640208901a11800b4518104481c520040001c664003441440542c1c0d089a40002c2c0041c0d50b2000030118444e603c0d00900c0c07590030210020380d101d800b151000c0300318800c0c0c6861100550340d107882403c481282c000100000b0060000a00c0c0c5495000c01000e00110945030300ca6003d140700c0c0151941e00031420003030005400008491382d55925010300402030008941d1000210803443c000b8005403040e0041011030410025644d0903940e07842e200d1001410104003c560720007140c83c0c410b84030240090180c80c040e003000d192114213442038003100e06c5031fa00804803003410a4a1045180a400d01415000d001a100c001410600000307101e645140340810b08203040040c41c100c241420021840d00100e002684072090301542a008011551003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 726300242 1250 726298992 726298999
    0x90a031d332107050c10060f08030f040e06011b0f0302011521050c040c1d0901060804120e18091006060509010c2a0806062704021f0e0405010f05030309 67
    0xc2d983c1c0c2ea10111628001e03011104000c1c401c0c04100507180341168000070540b01c50000c015103854444142c6696841030003000000000d042108000700255908901d030000414504941d414050909012088847c43c40c242e8440e00e0200d1010105030f024460040c0e0400c410101b1081c46190400010102c80b020f043d01c0c2c60420801a02c4040001c01d1084440c0d440c0300400c00c2200124103203004040801290b0075041c00324540010b40c1d498a8850030041c101c074440e40d80e840e100d03610b65a8820784007401c503051006005914514490316030b41e020280500b5000364907c20308d2031400c00d00f640c0c604111604c25140b040c1c5001c0d03083c8072155010007102c944030001e0034501140704192410000d00074071019551002040c444c000c5030741038008038884c02103403406030848016444403010484800f0364900fa010010391004c038200c0c4600407100314941d0090004068180700543e05103032040400e6100d03c02e400046401a444046280c64861240980b49007540c80d207480b424180400c0d070340d108050f00d0911 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 726301492 1250 726300242 726300307
    0x50f1303090306020a020c011101060302032d0a12031404050705010f050904050703061806050d0f230c03070f18020f1e0a0e09090a031d33 61
    0x605000d142000700a65205a045603030f6102d03040025154900508224005000720248007800b10050003042c0549400030042c0c8501c0c0d02400c2403401a810b4000418185c1000301d000b103071015014496509564011140504a0481e03804000d086404601e0001803030182c52041c40080ba0740090810b050f01c0007802d11034610341d10030005031403500403060b11582c8241060b042000705685600140b0407503070390100d01040842d81e2070100003601e1080c060241c200898001e06004140b45101184855004c0c1c84015292401c1c20544148015080d04a80150313110303101c0c1c29082e04082100304000c1072000e4010200e01e040c5504c0380a9261303290f403100401038000c28250402040310040300d640251b5002c0c28030340c41c0115917410804ea0460240c09000c5650f410056a40d4140103016600c10031901703014100321252a80d041c0c6614903911214100401c07200d40f83c14940d01c90944000c03504801043d0009401070400140008040c1103880000303075030061265074404482400d45401c1030030030068402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 726302742 1250 726301492 726301531
    0x903031e090c09010b072d08130b0706091e030804060906060b030108010515040b130903050f0c030903010509010b010c121403040b0628050402030c07060501060206090c04050f 77
    0x14904281101050fa0042d08500001241d4402e4401130115074840c0c2044100c0c01074661740055040e10703113016a00c11014002d2001d00140a220082c84521480087d4180181e20b480e0301980035005103000702c88699a4002134801e010201000100f01e20303112107000800b15040d54000c21a28001d0300041800d912518810200141c0340c00240151030443d01c2c1c80d84960f95010602d01801042e1090503500c0c0141c0612007040c1400c0c05141d6a20f8005082c4125888442c5416001401881c200b642004000c2c031004450ba0741100060103a0240f01000350b84a800c024101800c541000d00510820380c5000d59803034550b608040e20001c0581c02c0081e903842d22401c0c00003520040141304080f0b41e000f60010400c400c2040203242c6034050142612a142075010352403012803094000108411202200901000103103000d400075680b0190300c1c1149400e1005c20f03660f05040d642c080c0c01400c0541c01c1386c1d0800041c06030800212410b90821902030002d42400c220f4401c0350203002e840014132054904506 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 726303992 1250 726302742 726302761
    0x20312061804030807030c020a02010504030807031101020301090c08010e06010c0b04060621051605310207080301030302250e13050a03020706020c01090e0c072a0e0903031e 76
    0x1045503400480740c00e545001e14004045107030441e00c2902007450210a04036072440040c003000d8680c0d068503881e2a00741552030304202604144d4084003000f01110700042941000e0010f14001c0c0384007200480d000c80c00100103070000c50140c01c00000c200500081060980c0d12046550340b82d500b0441249094072a03040c010040c05003600316400108400401c5015060745480381451103000d44252007240c40e04075021040c8401d24441d10342d01c105050700b0119024440910650001101003c0070f010b40c5056100707509903001040142c80c022400300040040c55010311510304c11400d44a4803418507148000415102f03c80c038050b240b0101d80c00e04c0054028141c110098162a405c84100c841c40511842d0080d0303141013501840303006001e800341c4447c06500032110401501e0400c60040319580e68901c410300150032101050340e102c030390310014046406005c8142c00707541070324410300180581480300d10403c0742c60240c90102c0039807007001000031035003d0b03143c000070446000c01a40110744480815 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 726305242 1250 726303992 726304009
    0xf030109091b030807020a080d02151305190c05030f0a0b070e0603101401111b01091a04060e0a14010810051306091103010324140a0207020a090501050102031206 71
    0x1066148011420220600c05500301900710705c3e208035110205141c13a0b00743d150b1681001313905100076910117140c0044a074544995140c5c050115251b030103208005407901482d2101c040c1004143c4c00b241c0c00d0034414081192005006000142c0040c082910032074421907031542080c2001e85580500000318403003c1c441c00801a5030403008005d6a103078140704e061568810002d03c5403600c400c4040521040c15409644046459041e0001800c010355544846030141c0701341d02c044504100540402003074400400a0040f0b044001c1c201c1c040c0c860b400d040004d4180c42d110480d4602ca404900d00411808858440702ea0b182d410a01c0e101d500c98980b4220740a5194103070b000035500030342d10700360403058080c282d124800f10f0b0b201c0c01c1c0a00002444994040c1684820b00000e80289004a1213900c0500d10100c1d01480d00d581d210300003489020200d0a00458206903403d0711290313000208441545002d591400c00350042400400042d45401c001039640e105004801c14001700c1c40d000200756545116a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 726306492 1250 726305242 726305273
    0xf0601031b0e15180105010507110a05090f040b01080a080403030e131b08010e1303050a0c0501060e0603060601110601170109050105070e09090312010509221410020f03010909 77
    0x3122455090403c0f150301100700e50003045000d4000c1c0340c0c0c0d0034150a00d5168250482e041a110540781000d503460300c00000c007070b1200c5990000344004000a045d00ca1700035070761003000c0c00c1c40041c5090038a07240c110320301136040c0d100c03e00382d500540d54030340859001c0b8110380841c0e030f250400c440c80c00c1c07041c0003113041030310600790b4510700c13500c1c009052258034850170401080c242550359403c0301307030380b121000c541c942011380e8a40d03881c2c00d1a002910000b4061002895016036a0500c2d0158411590354542914803d401c0601d200c4064030030720109050402101e070f00000d0900b040381c02d010304c0b400c1a0784c0d01e000520520040200700f2640e414005000e6001c0e0805907000f1000344094074017514041d0180d4000c98005000d50100b0b4006007807020040240c945910400c45200c845901e40401c01810401c00703000c6c450132003c5043c420201c000b030600400500b034030071154010f09040b0480c205080c08004000d030b81c852401001200c1404480c1b004482c10340300342c0d14001440c5509414044a25400b100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 726307742 1250 726306492 726306509
    0x9040905061009140c0a050f04030b09010605040b040b09070e0d08030a06050307050a06090905060a080d120b010c0c050d062034030c0204181b0501020f0601031b 71
    0x4090040801c5800b40340c1041c0e80d41e1850520a41d4810842511610002c440c5a450301005008600c0c0c1c5c00e10980c01001c045520b101c03207605294403903d0710411800c1c291500140c170b030340d83c090400123400c05000b03403c4c4401040307030200b101c4001440464447c2400030108801c00010f14200400f076610761081c083e0554002c0c400755181d10b441450407000307001c00c0c000d0724440e101d02200024540350241141c4281c1d4081c4d51a541002d1420443d0005064060302007580051202e00c0403400440c01c0000c903580ea006075944a0400303a1490484089074985410305042262030004440401d041c1000d602c01c445054804c1c0386e10282030709000004018444d81c10030012111846a03002c40d5045010f8150b00d04011800000203205e20108482070a20504030002c00408003511000700b8041c00b107804005001410104121440d00c441d140143c0c0c2c20102211000b000021910003090820118005414203000410644c034004800d140d039424144401002aa2240c0c052107604000c00c3e203c400500d01c0c7c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 726308992 1250 726307742 726307753
    0x50304330209150c100c0933031109061806031e070215070c060f0501090f060e070c020d060213240f2106081e15010b09040209040905 59
    0xd1030308002035448822024402c0700c0580364100080788000882e412203001c013000b40490380601d8500300c06888004d142400740315850704c0000d11180c070160301d9404a11800390050032416801a601410055000b08004151a0445111420110104881d20480100c0700c00b9160302040d0000340441d415100101d41241d0040240800c081e10703031b8071180101d0359140d1340e004160b43d00201265a110380406054580c40c084c4013080c010b5010b103d080c203149001d25000700d48800d903090500190b803401e9110244269852070140c104494074807414010f002c40600c60610741c2000000188690304400002c0d109000712140902042500d1381100c981e1042007288109180e5114a0313504680961b22000b0070000c3c0d445000714085105042c5040340c071a4540780e00d9012005440010498600800e042421690320b46010404400030015110381da00c80442c10402002401d0503142081ca00c09202d541c4102800010301884881c0c5003510b01065054030011b85608012002401400d0380c80009130490199 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 726310242 1250 726308992 726309083
    0x602040902120105030706020607080106140c010510060212120601141201080102030402010806030a120809100e16050108070f03020d0912080f01050109050a1a040506031e100501050304 81
    0x702c4049040340c0c0201d09449403259214000e90700c5001c01c413804000144044014441c5038080c01d50004449911080c803404d0140d101c0b5801e084032000d85126107155000c1d0360070459541c1c100440004420300300a014144500c0002992060300d001d04a24144007000740348604100300c00c41941c5052405a144107442e5075511540c0e4000d62098405900080803100003411030f00340014a81d420039480b0b0b456240a44a204080700e180c4000750421000b07001e11440c1280091a900480f018209040c0107005281161280e0b08840c903920790210741800101010881026004100008904001d0502583c0c80760380d150f00c0b40c014843c03018020030443c1300440f51150690300111461050107400d00680351030740c8540c01501e08400c0c2e03204045d4495005141030140d1104440b0401c25003885481d910304003070300c070b00000340150421100c1c540d401d00042140005000071401850300b00d51902c000610705410807000a0143c03100600280c120700b81011014614140c072050040e425000c2ca00042c6c480f40ca = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 726311492 1250 726310242 726310267
    0x120307030309050d030b0609010815040c1701051005030c090301020f030712060b0f070f021c1a22060b13050106030902030f1c260703050403030f0501031205070602040902 75
    0x740041034505100302c800c0c007144240281b0800248a20040459080018100c01100c40c0280284201c00c04d50b44180004240d0b111030194000e00d8400c3e89909882c002c14a481b050b2403030050388028400c10400400001c0307680c01c50112501b2041c507514480da554031100200b80a4840d040e40c0044107500041040030b1a03910600354404107e00ca0f0081c06517903544c0088441c40d00607001d0382c480045041009000040c2402412041c491014040d00703840c5c91074000f0000d503100d4200d815034000341004194815080c003040f101e6800350110700c0100042c555501d05103070078000790000401c2035a0720b40d003003c0c4a64507001842c1c803044400340c0c207000030f607140e040c010054000844200d0091045c035252078900350000c00ca06003024514201810881d4803500200c034210f0a0b0740c15207814032050800043e62070306505070207114009e0303a20007082a00300303882c0041c1240c0384864a84103031361a04e0014030000760301c1c010020200c055498016120010303030401c600240f045521240c40301740300094100070314030b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 726312742 1250 726311492 726311501
    0x6010308030a051e1909081206031504030c0210031b090611010207170304150c1706030f0a141f090b060108070e04020a090509090a3e1203070303 64
    0x40118400d0045458441c00c403c8141e08900c01300880701040700c001500100b0408003c170088201d0130780480d08075004d40f29080107510911400c0d0111100b40c00308078040c01c04100c0c01001d850300200329080781c605030701c0040000a18041c001d2061551010354840648a42c004004120049009069803014840c0151122100c2c2c030901010580c28200071380700c01e40c1031080e51111900008030300720380b01c026190941960710040040712000c002d4201c0a012891707030711400c65028507907154000c14411403110781c080100d00800444c460740c020b610320340f868900802ca03080ca0944c803c10281008145a000c24284510a00c0015800705150340c1202422880e8000807881400b85c1c28210b40d03500e5140044445250454240020a0958a512030507080c158002e06c41c01c0c1552500100d07080c0c848000410045040e1f401c000c06510084451003400300c900352240558001c2414502941008914181c3d64550180621042c001c10f03040e40c09552568001c7c04140070300700055a07913410142c9009001007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 726313992 1250 726312742 726312751
    0x30307020705011b15020f0708070804030b01050d03050904112b1407211103040f150c0c02061b06010b1c060506040e060d0213021c112a0601030803 65
    0xe440c01100d003141414813a0010b80203500a0310441c1110101121407019603c40642400100e0040280e030010500fa00b01405480d44a80c10940c0d407a40340d4101202c4480c0c061300424419419000c5000000743c12608403200d400d0281c03404580003a40c40c031400310500403400054a400703841006903240c070445d0030701c12540c82110b500800920034200442075140e1011540c00003c540920b0f40c482100184160800c03454241d05408686001e010750190090740003030b80d0403501e825800300d000c401c100705000072502e000390f0450100407141c29540000c10b00038141c070380a8041d03c0001400d1014901e030074100800440d80104999455a40302c90600540c1d2008007010070b0300c03000580354400300c1a60b0081608581c0c00401d03d074100340c20010b0340302d50441d000e0b081a078044017030f0604400580f51000c0803c80c0c0d5080480060b103800302901c1030004842c00a1002d08020301c1c180708107003001c446005a40d009911110310408241000c1c1c01541c1248039104940f04601c40c40000004024485005500c01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 726315242 1250 726313992 726313997
    0xc0503030c040e0f04021011070305030f03010303110105040b13022e0809160303081f15031116080705031c0203010311190b0d180501060501023306011103030702070501 74
    0x4139907400b1200d1a0340c0c2020703207009502003489041611100e1180e00700e82c0801c0041010345400d240d8941c2c0742461079200c511020001d84004c0010000c1c150010409865991441d000b80030900d01903642c011980001400d40d443c403400d840e017020654841c005c0300e4510305555562040c82c040110003a5164000800c22400012980d100141e080b80300850104050800340d84e90819050031581c040c5d5140500903e845103a2401a884909000c8200c48850041031420341d401c0d1151003024000b41503071701000c08084010000c10a180950301c4074000d18906541001d4081d850351554a00301e400d5102d004036030030320b2000c0002d000080514940c01141207130311030f034a0059500300190a22070344000030000d44810086100e010070003074450000620618210f0301c80082e110145202064a4210600f4140c0710303a1355850007032256507010420440111079a141d044035000d5400d0441084000300000b0149070032942d030119140344d0052180000b001c10210603030b500e9150450300250345a00f1442500d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 726316492 1250 726315242 726315269
    0xc0f12070615120b22150507091a071a0f060a23240721020c03280c0e07090b030c1b070509100614040b0405100c0503030c04 55
    0x10ba40d41002c40d1408840311041002400380c02d035241d902d204a001018940307882c060b0f01c2c0c0b080300064581d400103d10380c0b10701c0324210b0402e10410310b0400c4400c001d10a90074001d0a250034000c05c0642c1d03c682e00020b2140104541e51001440d10a001241e001e250191000d600e04c01d01a00b0008600d0b000d101d0380040c0c85854007a596030589401c0e900e400e400b10281d25401010444460800b12201d009110951400342e1282d0a00c9100410300e5010300c0c000e5a42881c1503a50f1903490307031a404200344400341840100040040140041d071101d0400020030384006040c01455800308103e54a003868503080700725100400d94540405a48038004c0314801c001072035004000c99020901030a890050700020354190600001201d0641103034005a03880340e040c4250840026280e0b01e400d0f00b14400c04074014041d141604d003110145c1340044452003904600e50521052001d209070340d040d5070031038808031100c000d040e41c3c0340d40a5901c54190200a4030601000042200f8001400c0045c0100d543c0c5d5001c001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 726317742 1250 726316492 726316511
    0x70e330c10151a07061b02010f0b0d080406111009030509010f020607080a0e0703050111120906070c1e0f06051f080304030201050a1809090b060d170c0f120706 70
    0xba0b500c2d81402260140040c0c03848100c0b00c00282000742c848140303d440d0010b0b900010000302c0b8146425480c2c1100140e46443ea00724500401d4083c1c401c0041056450b400074980c65502c512003401203000d0072080012040c1c41c15118441040040c10100a0382c0c410000c1c4146030400521a600c40c0d4200c6011800c0740440d820302e50320000c0c00c01e00c204403076507600e0450785800c00400c014204805042d10640715054020001c607001303108000708030301001c54440e80c4401140c12488409002005501e140d08100d040010040c3c00c401e841c0d000a03400308a10038203040c0006e1001c900040d261001c1c050541410800c410816154001806441c2c0244800d00000d0a4644401c801241d40109080c50f082880200015401080602100c0c580c40c2003041010b03000c014488044965980321141e00c5440e6000c0c0e03014000d4800c40b850300000e0a45100304102c43d0350b25020407035008000040b00f4a080007440600348481072005816060034941600d0300800107101c4a03940d80c01c4108141c546501c0c105110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 726318992 1250 726317742 726317771
    0x60e10140d06020d0609020f0d0b0105030106020c090709081606090b09030a0b090309060c0120090306070c0302070512010f050702010b0d060c03200a020105070e330c10 74
    0x2400c28005080c00c104040d503984240103900401c150100d55622000046880030f0f5900286c20045100c00f41c00ba220078174400d2107815660521500750500404000601400b035001c503442111000c160f41030032540d10344072400c561500a0360f0210096001d22003107200c56844c0f070441c0310211601c507594603545a84a140200071341c0b18103a44d0650540c4425120b10020307090010780c40d030000d15542503a04120355a008110035600c1480b602200d03956500c03001c504061544003c0c0c50b5040c1c0b2864030740c2001400404a40c0d65400a420a028840c81c094011b0406201b00880d0001d0003001c2c18403220450901001c5001c0c0140500e80d5440c0360030a40014122441481090600b40009041c8040070403030b47c03504001000e043d07103010f0800d03031980c688034205c005103030303003213610b1207110111541e54041400d000f0300f1100e000d020282081445050314600f55586403800c2400b4100050a424030840f004225401003800940341c0024140400e070b1094a023404500c006c01030f01100e00920403999039903c2d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 726320242 1250 726318992 726319019
    0xf07030810080d090e190204030516060507080d05190e0106090e0609030f0a020f0712060b0904021e040b090a0b0109060807090b0c01090204050928050307020f060409060e10 76
    0x300000201d5840e42001501c85c0a20110340000c901130b48004104118981c040580c1c0c8642c0041d1266440390b0003400d0581010708120008101038034010381400c40e65034880c0d019214a06043d01c525441d1008a1100300c4240c0d286c0c00b181a000b0f8041240d4480059034901a0480c0d00c100d0351942d2410400b05003c1101044841c414008078016601d0103611204403040c541108010760210b2041310142c000900f001c00203213000d49141c020f070800310402807400b5030542e070900080c03502561800c02404010b031910b40d0b440000003c2c0c00c4d5010a81000d290108000346946080c1c280d1040d40507041c8096960710764808414100c082e61521030b01c58a0f44003e680d54001642c2c40c1d0001141405e0030084003d071342c4050b025141428002007a010783e1500000c0c01d1341c00c20748146c401504104440c0908250244e41101102c95142c00d44101e0441034580c07a4590151100207405815110803808159035030408490240418981c100001c2e80c8443d16842c4440c811200704510410441000ca03840118561 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 726321492 1250 726320242 726320263
    0x20f3001020306181012030314090a050a11030307080d020405032506080c071a060f040618020723010605040513020f010e0402041d04060605010e03030a03020f0f0703081008 76
    0x1030400204e06403158040800006002d168450303084c1d0404207121a444500940040c003955021542030010054051200400b0b094805a580001c0d100c03400103001081c1603404681010880e0500f2500030082821072242c00001041142e00068030178820302c942d4003500c15180d0130b40440d040301120880001d0100e00419131070381e41e81c040301c0c000c00c00c0a00c80d080c0c003a03101d000010840c0c04d09069075100030003a4a4041350b00e4030101c5240c204802820520034409a00c00d0860301880241c6c1f41812a0f02005c1e40411510074181d00002c029091184030041071010350800003582c8441c14007101a1390081050380a820f1090b4282004a507001034900300144100340c004040c00d03100f5007200019550340340f6140c140c40c5c04c242c09200000d8841d501402c1084042070f0320980010610b450b10b000811960b00e5041107060011080f071040e280d8a000050715190800d50070300683d20541040504900d019200c5040452940080c0305020903034007a070446c1c05404516440305416444440b1141c07a01d00046 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 726322742 1250 726321492 726321499
    0x3040801020c160f121419120f081306020c1e070f091a011d10020c09090a171809131a07020d1b0b0108150a15050607020f3001020306 59
    0x24071902c0406d01000d80b46c44403014901c00c03210080b40b5075028612241c403d00003601d40d801a1801440f0454122031403c40d459046c1c9011085407404400c5049004807850000e411281e01140f110903101e070421400c0d400510760200800340051103c5030f03a0b914603450207032001403035200400042a60042c080c00c41200c60300b003100710000c4440001100c81010300022211a2480c403811304c0720319242c07018221303d048403036800b030300d0201000020f004000d28054800341099014140100100c2c2d0401c080d05000c5802100b0b0135926035804ea0352400c030300d0704011103e903ca020b81061281e82c1c54602c040384425445900b400c044800d0a0740c06003090380741100c000c009a001031000c20790840c450001c40c20304420903000000c008207641c84004440c0e409030070400843d4010f00c0d20301c9840300880b0f0201c0c2e02064080c400c0c80020244c280c240c01901c09485010302650011820304210359601c21514003d0300d001c0c041c2201113504405400d60003d010002e045c44001040d00441b00c4801070007164402c42002d0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 726323992 1250 726322742 726322769
    0x160605130621062414030a15030b0702060121050d0f05040e190e030406090506070309030b0a0f0f02040b0315180106020c1c11040c0203040801020c160f 67
    0x6006940c00d01140c0002d580101d04421540510701c403a00c80c040143ca50580303002d60311103d0010700002c400d00b5492440038080e0b80080520a580c0020440b5407000340b181d00818520381240703105610b012150002407081001104211086600181881c1200c0e00b5808110318144155040306540c03005003005482a000398005041d21402985601e8200711641b8100b86450754030704801079170850599407011135600d05644040c3e502e8460058840e1080d200b40954942460000083d1030301942c0d22400e4090140482e8400501d40690941c0300117642014410342c19140900520b401046e031100043c803601e00d040d0801554415074400c0d00c0c2961300102d1210314540322603440d0300102c03010840035907028525011400080c152400014001d00044c2c005003011151041003080c10010803100c548888114400c0202150b190048900620810b40b000517141134032135012406c6202e6600003c07000d60000445405007000050301c000c01c0303c0031420008070680c41e1b0f00141e242200600c5035031034400e10b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 726325242 1250 726323992 726323999
    0xc0702010203181c030909050c03060d06050a110c2b0905041a10080103030e0414010b0901032c1e0a03110304030b1302040e060f07180b0c16060513 65
    0x111680c0e003420303d000600d065003540d0311507400c46131074022075011000500100d80800000c0005d01441b504007200d105a0340c15841c2800100701c000b03440036030141c502d81e00c8070003050007040d140e44454446080c030400d0756030b949001c22015a513107180c02c580e14610004205103401030244130720402c1e0500c03403650f0391090040c9842c0801020b0401c800040d03000c1050030010300056501c5070340301000424543c03901c642c55131541c1009003000340240d150714012030a201410b440c80042251060640b048205140d4840900c00d004800504400b00800410605500c0c144803d0003000c140218910340c7c07008450b819150f51a415104507000040b00c030725544990038080019004c0c200240780b81104804503824035540b03494810a03288142d458070100c01500c450f15056003401d01032015817031500002407960341405e2950340c03402d01000b4011410442e030341d60500552001480e0200060a620480d5511205403146507500c54500f404000a070f0140c60400040d16401081960315201e041c003080902c441c070b0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 726326492 1250 726325242 726325267
    0xd09230a080412031209030206060a08010204081903030b09010e150102030702030606101707050310230909210a080105030a0c061d09041109060a0e010315091509020102060c0702010203 81
    0xc800d10100d06010f03580c10000345e840520b1084050260003940109100d040107000d11850008540003080030764010001400844400900e1070320100c1c00c20442150410745040407001810113510456000039401c00006e0f0110607902c00703074000c00700000030001c10070761400160703942c0c031481200030342503005007001401924161155615545070360810f4203426444e024010103080b8122000804030b034012091040c017510000e614009403890b100200420940280c441c1c0c02c40d80700ca0342c014460811000020f0051f82c2c180644491400545407900d0b510984d85a1807c1c50340010b6910000140300e80000281840c000801d0202c0c5508188503c2c0c01508281044403182050f40191341c0b0341072880401d000503261201c0b41803296002d1810a40e801c500881040b20006015201c2d80c8504003001d8140300d009410344c03041d0704480d404503a0076001480061070034042d140c410006000b5400f054451200d00040ea00312000e0a8400d901350344039a5940c0c141c840319401940350181c0142d10074024810000c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 726327742 1250 726326492 726326519
    0x8010f090b01050d1e050604030206010f0e1f080d020318090105091f0302151903110922021318020a0c0209060a18020d050a0603030e06030c0d09230a0804 68
    0x707000740601485c0090000442064401c200c104030f41c203500c0082088181541804030a01600082089880840c0341221401405034050000407c0e21300c1c00e280c054800d980c2421850051280c0e0040e5540c43c0c0841e94080d449030000b2031040350820f10b840521110b450310f807450030305030350001f0190b07465038545403c1c910340060140036209003141100300220160352641013a040703403418142e60320f50383d03410303070a04810442c482c40da85001e05040107071603460841035200707494008009031195840b4040609540c00c0f4000741d0b0044071242c51001850700b02c44a040c3d1540c50a46110740c9080710546244e2122408034400c45603443c0000e041a80c2850051804405207504480e00420301540319440c5c400c07055401403e40c03443c6001a90000d032106000c1d645014055000b01c0c0544108100c52841d10b025018020702c00b00305110b102c0000020780c1401c410010356000c401d80c1f000800c030401061030300b110070b080481c0c3c19029203058942103c051420018140b0b40d42940300d84071600705440d0500c42940103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 726328992 1250 726327742 726327769
    0x3280203070f0f02030303190c02010b01140a05190302030402011b020a0b180a08010203071107030506070819020c0106061b111002030f16020405090a120822050708010f090b0105 78
    0x1581d00f0601030250b6000c10103940950350b41c83c01c0da0351201840a07080211020001d080c4190790411019071f01a81c2c1106038003c2140d003c0b074040f6990f4500340c504a42e188140581e803040c0b019080408900300354160701540c461031003a290068004841801c15010808000f0700948c03003da426030034405220f00c1c00c05050b48045082c686041c1601c8140045ea00700c03c9604252640da501008102520b41e0001c0d148880b156203d018080b13150468035816150080102050144180c0c4804901001d84c5038a03400c140b2021080215241d000080340706019180600c500310000e0001c810b10f02040c2c1ca25420503002d5640311514a0035041180280500d44003001c05200540c0001e02120456500110081c0010410004601e955104600c10401140c2c00a040004554031a00840e40051074104081105000341e0800003010b40d207030044200c0d002c2d2035034296164603100034441010482c1c00034940301950700c010001c1c0511022810880f0485040b40f1010700001c0c3e10400401072803c0508400360807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 726330242 1250 726328992 726329003
    0xa08030a1109031903030609090302070527190609060b0315010509060f1903060302060a0e0a0f090212070513050f031015060806041401060305060d05010e03280203070f 74
    0x3880b400000103400c0c1034002c000c3c1001c5200c614007120825603d4441c2c4009080103440400c520000e43d200250398103250300480c0c1c041d58001c2141c400f42e40c0d044490640014240d680b40185203070a0b80301942d80d02c070603594580c0c0c050410601040d10754040c0a04010b40300d0344104542036548405110040481c80004d1350f0600804010751841c50b10307020b00408005010004e070940d0742009000292100344440c4011041600d000000d00c0182c0d0b0382422200d2041a030302c1e0948840c00070030002080d0500302e40c0210402156003c000420410a401501d12740144400ca003405664a110031703030301446810609230705488a442d080c404c61400ea144144203072809021143c0c141851860001220500344035420702580000d0b04105080e41b02a50380d51000056400340300803031100000185403c818003900082c0341e1200000b03240c680310302e610860390f107070403200911850442c9036402d612580600400d014000a00c0c10700c10070b000403000381c11700d03a00f002c2d4000d41c9400e2007520303009026907498400f10366 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 726331492 1250 726330242 726330247
    0x9060412181e03020f0909060f100b03040f03021006030203251707050306240d02030a0f060203100e01030510201c0f20030601020a0c03140601080a08030a11 69
    0x340807100301a60603604411000c0b5000381811801000141ca031800f0f4242e1207441c015003084814140418110380198a51001241645035225241400412600420ba10f51004030400040c8111825001c6281d4001d80a44200140484111050382c002d40030194142d07210001c5840384010440b584582c49000002488980f500c4845881c0c4003641c0d4580c0c1c0b170040d40304440510507440c00340120b9401c12040c0c0014034044404034002040c1200c130268840c496040c0c215820b0943d1001e101040c4283d0b4050305a007030b100d80c0303458004001d4200b41d510310a500b000c203402240710101c8541c0241601d03000401031000c41c91004400015002141e900b615000b0903628030700ea58010403000c2c1440c2480d8100c1c40b8044600c440f0350400711000b60340c0c0c8038800e6003890b6514481181d4041c0080080c007040700119501c0c0d44000050b4030302103079408010a41c60600700000140518452030500424101c1c0989102e0b9070b23500b204c070f940c4446000c0d010303110314001c00120b14400140ea0141d406842030b54070050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 726332742 1250 726331492 726331499
    0x30703021e0c070806130303020a141219091104020702010309120f0e062106040b0a030b0109050601050a0906031814010506130216150b0301061d0906041218 69
    0x3544816403000c18100301c0c0821888580300040c40448003400408000b0302d45854031800d01911b03402c0c1040081d0030b140d030010741e03000f009208501d54112a42a029a2030b038a0003080030031003035641c0c1160207021011a12040080e042d078503008095440750440507000d900284542040001d40c01030f08106e042c5951000c540d0300141c01d8541d401c4254480c0c1d01e03608a061030220300030344a400002c4c0982d20441080250621035040850502c501ca114000702c0c51440e5940400315005000f00c412151344070307203a62000400c0150300504541600c42400f0705210988035040155001d000780d5010002081000005000e0395110f6806070010698041e940242040c0c40d4440c241c010110154810059454100b00486411b02c6d441c90207141e4603080c0114908494191401c0440b0b040035401840e0b10b10184c41c0c044d40c840103810850b08200300400800080d95180000100d50810f000342e001000302643c0040e0b040c81c0c010440c14444c0750008402007400042c0301c0d04031181003415001280b680301d20003011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 726333992 1250 726332742 726332767
    0x9120310090c0816090b0304060903090803030c0c010b030312010e0c070f03051809040206030703020f04090e0604150213123e04062301021002030a0b0a12110603070302 74
    0x50b0402203544a0108904250140840f2650550b40380c4041c0503400004205822a9800316988560841d4001a040845150886d40c240840e0320000641c4804028458540c9081c8020608954600000c021101110b4181070716400390030602e0100c0c1c2110030040041c2c01005000a81c4060503c108a02c1c0c03880c565180011151002d2042e4000340d4042428900b0300560044010b03139084c00c440c030300c886180c0390780010301c10312004010908254010500c84004281c83c016a809001880c2d01400300b203030140c07041a5140001c803025a005101a0b420140755900c2e03108850f11103450b0429644c240f810b140750f00d2a20010b52a04658a803414014241c02a20202900f00b254088000c40d001107001d0040003c182000d4241c1140301e1858010200500f41c000c0954000b03411610000840102d03c040060382003003184c0d48c2940e400c0b80004200180344000d40e0004260b01d004944510746940c07182640075521b1200c203401072910300b060045201c0d5244c01006140d200b40a4a0090316140d48500d9a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 726335242 1250 726333992 726334001
    0x110313020a150806130e121312050d020606091b03040c030f0501060501081806010302041104180605130c120b060c01110903011d071403031b031c02030912031009 71
    0xb040000344455003449007914040030344c11010403420794103009080081d51810f071900d840d11203601d0070041c0082c9000300c0c041000d044000405049400c40031030b4505080581d00e4a03c0a001e1700c006000e030300c00080385482d244003440c0c000c800601e401d165003082600010034a60014000307580c1000c1c80500080011031040020307203094419000441d040e450480003405000f4090800209110300744942640f2100c002501c41c1129011203000c17401c4810412480c40d03911444e08072007400040f0b0500c110280c042900058115170b42a101d40c0b0007410104085d42c1103d4100003000300150080082007440c0e10300f0741010214003001465146008546100e840c01c444000002035140c0d040454822131a1030284501180310140c1c0444090081c2107e042c280c0300c0c03565000e680c0134801000c6581255071010420b45084985100a4186402800300c0e000d90701e400a031281122103554600380c102c80007541c001d0324010f1441c00020160809004040c224680000741582c040700100c1400103031002d064000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 726336492 1250 726335242 726335279
    0x807140c0a051005011404020d060e0c130b0f0403080309010b0319020307120c03080a0e06030403200109050c040209060c060c07170c060a020d1b1809110313020a 71
    0x60001d000c403440d2160901040400502c249454040104406000c400c15043e841b1011200180e8481c54280300074010325503034101c11100400401000711030f220074001001615034005048804669811486641d0304c180e6494802e00315090000700001425140919080080a030001c06d0052821020034500315001600325500c1e202036140d00c00754102801650040d040c02c0906070040740c185d480340101e0605600c030051400360300084015489104031418051680014411070b070f2070915041c010600c0040c1c104014080310382e0902c0c1142c00b48148280c40c1450b034010003810682d150f8404020094000010040d0000010005036492083c107010503481100c0c100b000e5911030300642400940c3c00c40320350502a0607801000318004504001580300d9118560100150f5078031160b00b00400a8140c0c444403176501c4091f254113201103500302002035005141110150041550360280c60241c401306100c080190744100084ac3e01c0030b015560100001d0300203084c2c0210704d0b59400103d0200d021001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 726337742 1250 726336492 726336517
    0xa06050402032b2d050a020703060e011514011e09030203010501080d11030a0206130c03051e1009020f0d0201170a0207020f0906060306010c061e05100f0305060403080714 75
    0x8900801080d0402030301c8100d500183c449800d9150950740348030000031907644c0802800004030b45114481c0c42089100003865003e04248541090140000d001c1c000082808904501c8004041240001e10b0040140038005035114447c0da03030100c107005940b42c007400f0010100024200d003c40540c400340506402410b0480c0103000a00c00020024450b00352220040709541040120441182e8009911713038001c1c5080c03080d07140300b500c1445c203c2c0e03190550380e00007000d6020320808441341b80720017a240140896001d003030750351441c07050150204440400034001c0d4059104030481030141800c1d0780180c0040d1042c144402d2aa000d20001c8040c0c07902198a4003940e50001040300850030000701c42120024103031034190041c100078000902c14040102050b04010011011006200280d004000c80200090805480c440c400c500c98001c0c0c40200c50041ca102c1300010001005e005c1c1c02403002c12650410301a0400c2d03215070360f086a41e8a409840001008031840da101462210b18004050020468 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 726338992 1250 726337742 726337813
    0xf0c150e01140103020301060b040b040b090109050a140405070305010f060c0503070507030c06170403050d2c010f1802010203040621060e010e090114061c050102030c09090a05090a0605040203 84
    0x1841051f0030764003550040b0a10010501042054140300026103060301c00c040c0c0150b1725a400000101c508a8566106507404502208000b8803990783c042815101041550700b0301c865030310a4010750580e87d0078400c00322f040e080350404001d414890a83c00304414031a2041e47c2c5080d210fa00d8540c601141c5400550b03400c0e4003c072080180d88c4d0400508800c8440480c442c4030a46090385014006006d020070000f041078541040d1080840108054140d210003560000c00d9144011003041c001c02002074512906480d221400c0d0b100c1401051071001c003a41640250306d02030134818100c6250100400d035018402000406e54250380c854007402016100c1c0001007002585064982e0040c07405c00380c041c90080e494040b440c4010312000b00699400b5205455003c1c0c1c44000040e208190440000090000d502c044180720407400354000409401a0455501600e5240c8494400032500c058030b0020300d070f6102015900024a09800940e0720500080c1510a0009007650b0500c0d200b01c140351040008280 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 726340242 1250 726338992 726338999
    0x90e0f060a0e0715020307050a141612020402160503071a18060423060906010914090c090402060c1005070f02010e031b010b10030207020f010f0c150e011401 69
    0x10040a584101040010310942e2808030000f030319106140503626003618080300300521140200100c903090b950101c22180c942c2842d040241e4065540e8403281d00e103004208030412540e075514011f00641c1c18942c02d908215940380d08100c0298804000440070800d085280c8021540c244050602e1130f0150081500d4010b5540018128000040802100915226040701e9000001030050b911a51100f0b40031042445240400385600144c0d0400030745d4415181001000703070700450603504071070b0301c41d00600441e01103607851a091a021075030081d0a07400b42c2c0101425282c0030428640141c009091249010442c1c0c0d600307400e081c0d42d03100800c60306454005200480d64001c00c1c00c504e007c078500c020400c00251120705a120701c290301411300b1105400c400c072541404290711100c80020014015045011200300c060003035000070f04240e10032300c09062041100d50142488056118055030b4a0100b6246a44c074258500c04c02c10801104030307940c10100000000034032807400408480390710803d09624 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 726341492 1250 726340242 726340273
    0x301180515010b2104060f0207030e030d0923211605030606010203120c090306040b011701060b0d020714060c0c1002192316110f030c0415090e 63
    0x141070340301001c0f43c0410062410082e480041543c000100689007006a40380e074204070002d4100301e045d44607403034400180e8204054001c41e009082c0c0c002502580c5910310040d030203952000a6210324001442d84592f04281241c0304440d81250a100806d0402d800603001070300b10444000e0b05002c00e95520031400c0103240f200d24128440200400c60040182d8601000002e44070300510310000075003031a4001042034118031400351214940d02808482c06450315007051040a4020b1103800104485142c110b10000e0040c01110165003104814034a044e6100813824001d44c0511030a480708620300031440c90001c01880b07020b02518840e12b0507510340c01041d0107941400000e507480c0c1042ca10401003840082850b0401200390001c0781450000c14410130b42c1141e194402002c101d0000c0400520100c0203c1c00001444140f40030b0422900024034410a0040380900d12880d194141e00620303d0b1f8185250a800c00c1040b1900b844040001590314640e21065411100019500c0e40005114039404403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 726342742 1250 726341492 726341533
    0x50c2a0706030b04050907081b04092112021603050f0706060b0408070f030c050f0303130303082502060a050a1107050a0203060916030b100e04060605010905100203030a050603011805 80
    0x101102c3c040c01f1014a0305440517a110080826900c0c0c040f80055540c25581e01c1e5409035201d5904801c50800300e1411110121101d5001c0074001e0202e0401b20011140041c18401e80d240300415008101c4401061f0720155080d401004001c010800c1c100200000a01c0c0340c014080200174085402e6215800c1001441c1441c02d070380c02c0212070300e40ca4807007000450072202c10f80f000c0303400c15590f441000021101107401e511411031303003054800c0c404d036002080503030224515100d04100143c91008540c24903098080008006481006a000c040070400e00c90843c0d00c00394100d4408100001c000d00354520000c440d8120700025200d0b900001d1100041d401c0a10007103502c41c0680003e031858069103103442150324420702020702142180c0340083c54030b500881840c0050f000300d0340010340c40c0c03030b1500d8040042d1010b8082c1500042c8000000501c0381006c0c06010b4886816401560855554024a10044c48000c0ca540c0e4103640351003042c4403026109402c0c0325181d008002402c5003018103502820844c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 726343992 1250 726342742 726342751
    0xa020901080111090f030a1407061e0e0f01031b09080105010b0c100902040908040b07061a030d0503041a100e010e0402060a030e01060b030c07020109050301050c2a0706030b0405 78
    0xe0341016103046030380e0805004c462000104030340703085080001a020a26000c0c074180010048082d9003080c540010001907181c0885150fa035604051205035a04070b00c1c1c1030800400540400c14400c10004c41e840c00308c41d01501002c040c903001070018110001b004804a1048403100822040030080c0804c503001e0282c0c901400d40348850500e4504c0a4031550390307c0107105144041c0136a180f044008654980e041003214a8004070400d85840d103074989134900c0d90100c0300407070341da40c5040300030202c0e42e14454501000100c01000740129010443c015502580001c0048440d00807100321044911052005180140810a020b003501c40c2001501414408180c0111241000034402c000046c1e45a500302d449414280c5808603030822400c914601601d0701c1c1d00004941c00c004000c0080c182c000601074043c0a00036078510010580d03c100340741c01c0728070070754443c00b415008010002c40443c0352001c41c0f2a001404c594580c03206c984201241c20111303503801200010f512182400c850340f4242c0a80d5400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 726345242 1250 726343992 726344009
    0x142a2a0d032307081b010f0603050304181d030a081b0306062a010b01030f02030103020d080313050609010f0b0108061809070b070f021005030f07120207060e0a020901 73
    0x2904554401078041248000c0300da1030100c1404030080c2c499400010707a00201e912072800d1303840302d8038001a07203410014400300301d07207030b6181030441c22500d0180c5c0140e0003107a401002451902e400c1c031102c9041d201600c0200400b41d0340b1003001119044003100c40b40620380100021390781b62604060010041c0c14040d001c0220341d415811056003484429045030b801080480c0c030240e5a04003140845822602c0c0410711000b07840b1985800c4038074106401c55180381c0d209980403c01b44004201c100100e00080c080690040100134480c000135a01c14001e40c2c0091103801c40a8049140e03a54142c030340b040c11144c08205035100c0000c8480d100d158001c40384a80b07400d0034400c800d4940040030a41d500e0403400c00c1520003c03c4404100004030502c460f50240c000720000541d20341e940e0500c90242102060100e0080090a541002c0706100340c1c00d4038014545104050f206407030b2414202d81b5400310b05084942c0076400c00c5143d00044442c803c50500e0b000c15806040e1010642c0104162480140d000005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 726346492 1250 726345242 726345259
    0xc050304121a1026160503011d06041203020c060414060604050f1609260f120f03090c0a030b04051b21030712020f010c142a2a 56
    0x7644070150400c1010b0300c0d28098080c8409a1080007662070035004d0280c05000d0044503076034800903030076445c0030b001d9400941c000d00c031480361410406d0407030002840189113a0090030104001480e034045103100c1071050303d405810146040001c1e418090180c50459100340300300c0f85440031003c1403003c80e07403007881160208001e1170b09044041001c04010403036a4100507581901c810140181a54400340c039000d4614072110141d42141c0129201c6654800054030a1000740402c2090000b40300312104007a42c4201d00703000200c200d80318030b0b400c003419000c26802450443c40c0c41d40c90f44403230300008500512155483e41001c0c02d10340d04041303a20303541110f508989403181441c1c0c1c44401120303900d040007031840c4650141d0340e14110300354000d0b084001e00700256409510102c90b40001c1c0d0901500d8910001c0100f0a81010203036100d82c9060206105c40e0014003204450180b0034200140399401c01418000c0342400794a02070a10b4411000114100e140240c20368140d044202840c003410002d0b540c0b02c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 726347742 1250 726346492 726346501
    0x10090312020706140901290a0506070312020d0f14310203010e03070b0106090302030d0e060c0d090612050f0c160f110f010329010c050304121a 63
    0x100300d8880c9486800e0600e0300001d4000c01c000d241d50007042d181c90008112441e5051290364240a48216552680610b2107007450310300d941d590111052191400421010304c03503141405100c00f6400aa400740c040c044080001c1e86486c031240024040f26081500016070088022240803c8a5040c000c014014260808001861038000c40e0200c4c260707810801d0401002c0015000903c0e01002d41e030083d090350800a42464807140040a009007a2142c1d1002000d6070301e89004a41d0051544000b0754168407c41c22081c0440c0103440741d018030300d0013070034261038206a50b0600e4682010612000005074440000308141a441404c0900b00c0111034414000f90418503599022034101400c1c4041040001034100000316204412000141c0e2095400100911900703000c480380500d003081e54050044150707646555842071045509102c46507000f402031090307110078281900c491b2083d07641840451303502d0001095081010340018040c202c04030010300014036240410700c00c98200e400010030b5074000e00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 726348992 1250 726347742 726347747
    0x60602010c0c170715090c0509090a021c0206070c0807050409053d02030106120507050a08041b0323030c1209040605040515030c0a080d2106060f02100903 68
    0x4a0b010b40c1140080d031089403070b00409555445100b400520328810200d222100395415008a01424002c0d4401b607025a540c0d010b0100701c0384201c90380101c07038000f441260f006107040b020030030002811000d2003201e0f00940e40803503443e500048080d109500c07011402c100c103007020000311000c0c02c4159028410744c00d86546241e954040d000b440b166100c50080340c0d4184a4030300c119034500110034001040704540301c0d0b50300d800030b60081c0102d60005203800744038030210b600d6005103030040d03540c0e60b61580b034138040510841d000302020f00103c450704800302c007940920641e00c05800c00303140a150801800c5840d5241c0f240e0780d80001198030f0f944d80040c41540940c04011030b00740100c00c042d5003101d44d0707110079400181c01440150041076000e45004144000380c00340840070750013400182c007180d031007024803004c0200f5400a40709900503a4815225444101e1041800d4124070755a40050100c03100c0006000041c0d980301d40144001807035000b05511840d42c1009000480c1c4c8192508002d28000758900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 726350242 1250 726348992 726349007
    0x7050901080f2506110325060606020a02060702060912100c110a03020703080c0a020a030605010602101b050708090a0e100902070804061d0306010801051e0108030304062a0909060602010c 82
    0x2408188648420040c03007041c130510458640520840447c0305040e0000004810300d0800d000948007140b40c038101090540c00050010409034000b016103040020300d42c20070080740c6c80850104e0300308402030300c030030380ca194100110345060454148c040b4141c00c5140c001481c029504d44079440c0d40d88080804004030341c0115140060b07079001034010356070301c450404083c40c01114004c000c1d048a9020000014401d00b5403080d4140d0751070303900340c6040a00c1003842ca001e84503c0d4600c401c500c4078a00c806240309000d04010300b02c851040001c9828456000b00142d2548801d52041704180c0400c0100a0b8000f080003481002c0c1910610860601400b601e071121140240d0003468107010305014003000c0380401447c0760741d00103001070489103990384440c2094043c00041e140729002518000ca084850460408118140c513071850040d070442c3c0d1f490f200e05010300b030340b03807100f0109911801100d4404501c60160100800503500e54400051404407004101d07040340d8400411a403500001c4551380798400c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 726351492 1250 726350242 726350249
    0x1602060f070c050f030f190503061003020306040603140102090a0611060403030c05040806240f01080a0b06070f03030204150e09132d050f030906030f0907050901080f25 74
    0x10095446480e6140c06032030192841301c88500f5100204066490424001c0145400400d06400c0a01d90011b20010349150000381d442d00d40c00700544403000461032081d40613542c8004c0040002c10400c1e600d480300009080784c640249201d0b500022000384600388240780c500103145070700d00768503541c2e40c1131070680d100c89020700300030b0030180c80300b18180116200701c0546001e041c41e1425240b144c140031014285074403101c804080243c400c0c12105401d803a0041c0c4010f003450040e1149081c5649040c0d0041c01003102c040d0300c44e03101c42e0a00c2048040340502c850304840920a40b401603440d4102500c524480e00c690001d2800c10110100d02c41c0c103601c89880c51130f0080d0400040c00d0007005140741584d1906003288841700e2039400503045803004051a045141814040d40c182c0b41c640c24a030307a08070745038416002c02a8100303804101107200407000012a551160a2405907808141c4410014805190aa20280c3e8542c06003d00325911001408003503010300c0f070303146030b55003d441e040005100b00a1074031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 726352742 1250 726351492 726351497
    0x60803121b0f1602100c0501050114030d12060f0e1e060d080304060f022d0a0215100807030c210c0512010e0726010b0f13020d141602060f07 62
    0x103a010708940c02c074240c0f1400280e0082c0444c0c40303ea10071000400c6070040309800e035030f41c0d030800d00001590605004500810400039015046140302c00d0000c3d1955034500800c60305441c0d036800c0000382d036046045c0340c2014110f140f0a00c60103003400f501c02a030808411441d4415900124103001d403603501c00000d408078507400003070300c0c0e1240d82d682071440040c007106c1c0c2c0b4120710074000109003d41d8440e03103a003c0c100c0301c00c004800c1d8070034011a103800f0460143c410503002503070008581543d070a41d12441682d0041001c0c000301e80003610b4200d1103050a8180d4030413102c0e4a54110107000721012520355280c2d41080030895134112400351960807500700c003031080714000c4500300540481e512081d0050300e410a03040d411121318680d200c15001750104c80131003080d81094220382204160030113000700d10072603100924421a88108001b0490038140c2200d16440d0942e00300915154a00103002da00c201c920669003a01d098a0040100006154000710f20011500301c0020054189080201550048040d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 726353992 1250 726352742 726352747
    0x2070608071205150a180c050304150509100212010603050105061305010e1206090d0810030c050108180105090f07080d051804110408010c0e010906080f0415060803121b0f 75
    0xb10200d0114012a09219400058904010a10200d03030109044141b070b001204011114209004840300d004c2960001e01962503401e08070118407460b01f007140c0002800d0b06451300b003000c1c8115481244d120220100441c01c621004002c1c01d07405114041c01000103076450b43c507180c0d81030f003140841620350041d00d041c080700c0901025291101000000303000c09140c111120f60030029845607946880754030f59030014500d1070010340394000a43c400c3c403c9951002d451302c51141003400541d00008000d082c4640348008010401e041c0a00340900790094a24801410301070701c5045015043c80195080030340e09a0001c0c29100b0703890780c0042143c01841241000c070300912001800100900380f62203d55024000110700801c0307480065221100c900c42589520f86145501c03001034602e49a12b220b40004500d4000c002188050f20441090b03002d482080803092500302c0c550803108880707450b00410540d40c00450070f4003072030b68851000b98100741080b40041305100c085110b03030350500c10201401c0c00c94801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 726355242 1250 726353992 726354001
    0x3050a20121902120411010e31021909171e010207080c03031807050d020d061b18080105250c02060d0e010f0e0c101e030204030302070608071205 64
    0x2000c00380028106988400d540d01d120904c140c0000c28801d03181641c0250042414180725030080034401c0c400b0701c0c0600340d207809012a01d8002e0078a90000d60302e10301c951030810005d04444aa2009145030f503c004c005842003107449400a008041580260054101d404444414181c001424031400c0341307660b082c43d10580d0200f602a0190003842c0008205540c0428420078407040480950f1041940c00068890080740e400c0c100daa03410316206103500101c0b0040d180d8094205020501e007218010038000c904203190354440311403c2500c0c54920002041c02c010580d0181074510346030001d1215070002d22060610441d03103072108601d039902014119403540c00d00c4102c0c4c0286001e07003202e0b03001040991511280845007001d09003110b50207082d94078054030408070038441d10490414810300c0d4005c1410301c9a9209004400d501007800c00107112030140501903458000c1101390408040d56070160b162442c518000c1e1414a072030300000140610023040100242d8060603004121010603030110fa640c44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 726356492 1250 726355242 726355261
    0x60409050c090c091c2019060e0112060e160c0c080a11041a0f060405130f1808120a0b10030c1103040605040b0304050c03030a03050a2012 61
    0x200c580100350020b01007010401c0340c1d19424083c20201e1410f41c2d1034020850b0418246214174030144c030090064015001d128901005107004010103140030b010705154100800c2c0e10a41030782c0b070358401c82c0001c482440c118655684040d030040c60034001c100a12801d420000e1403070420100811a140740c500c081c10b40000c551064407440900c03030b00904250f910f039031903082481c0c40c4c100d940401e68940c1562a6000b40c90704041c402c0f00a26000342d400e140e21200c021080108a5007142e00d041c0d44080705000c042510f5403a50710b0070300d0300c9030700322800226820801120310035640381d00c046002c07890440d06800c1c00304903940200d51410814030656009581c2d007c61400c0104003c1d418560803071162540ca40c41c058040d40584000c411580b40d45503e16403485510b82d4a01c124011100001d2051004125550804c0c002c3c542107032142d000d84102910510110385141c10198401340000e44403030500414545510907058110127a050300c01808001c0c90080d00b0a104560b0b00140000c19200040c05010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 726357742 1250 726356492 726356503
    0x302070f0f021809011506050a0f03050403180801090b1f031205040f03080903060a05070c0215190c060c05070f030e040b03030a020a030e0303071205070302011107060501290306040905 81
    0x3d103503d426401c00c1c205042d20500900600841100c01c0a50360400305e06180030340255204000240c0e24a610445c0107803089010741009030045050006090041c1c40c030302410b4070808050603120000140365909414800c1e40300380e01401504144c59601701108903050a41c100d01d090740c0d000040610540c21002d0704845a01c142d41c03081004051a61010082181210050004980c1201161220345690a0302c2e801c560703054030b41c4008204c84c4c01202d001030609401300224a5880301003207040210300c907089603c030b010040c040000510001981820052240705401c202245481c0650801d000c81e0348000403034005100c098207000d000600e81480d90b960750800240d060740070f001da98031080400800b82d43c9201045041b13001c1501c03013400210364207000003521202500801891240c0342040d400b41c41550250b2016811035486000740d20b01d0200f003038020050203100300d400061310740c50300469040004a10108940c01b074a86018541450f03800000d4071341000044900186501440c40d00e41d00d040e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 726358992 1250 726357742 726357769
    0x280b1201030b040f170c0615031f0e03040f081005191d010615021e100203090709020c0309091e010512030d05180601060c03020a030e1c210302070f0f02 67
    0x5810700c84818544c4220707001900384100c6c0c24040380c201d40c80c0e000659811050304410140c06074010f880c549078200f404050095034562000300010701007000d03041241141d0268015602107110020204031001c4100800b51344294884410400c5083c09017440000d03000030301029018640f50003403904c500080c20050070043c80c5038002004510303136480c09120708135552011000903015202411006a400d00c0a07044107000050262080d280030075240030003904040c0c4110303450720801c400490400c0041c0300800000324180c3c02141c55002c00382c208603a540c2c004202510141c8005006080703000301041940c1961002c17602c1c044420000b1018510b14002c1c1c0007039600c0a41082c081c064a90b0321101c803000100c082070103880c030136130b254103041c2d88c203900b10741c002001031b400394403103001083c03203600d0444090800804007d68071010385134841c130003091403c050300e8203006d0182d01800402d90804480300b600440c2402d500341400c60300c0e00c4aa50452140281490240340340b024210360b92540083d424 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 726360242 1250 726358992 726359003
    0x61e0906040219081b0c0303060909031213210e15190306031202030a050a050a170403050318070803040e0415020c0601032603010320280b1201030b040f 67
    0x2080500d60000d0001800380d8500800b0900138807054405c80451040301d0024030711a00561554070740d14180542900014000032107400203000a00c03140700304412071406001c0c401c0e0314a900c41d01a04086031008a9000d500760050354410358902c03480c2c0c218114584070b05049480d0510b048800103400c0c0103224610603000c4504dc2c000340e2001e4035030140d100006030380c000c0031090440c000400040c0c0e5a84a1040c0c02004a041400f401000740c2c458001420040c4080ca40b49000f81c10301e150340c1d0450102a101200491804410010849042620b044884801f81d005182962401403135030744038840e40c0101ca581c0454a0005403c1c0089051040520100040110f580b540b41c041c069031075a0003800101c43c540c41e24506415142c038030598003a40d00c202d4606d41d0740b450b465070344c0d00c48035210f60625a1800c0d5422001c080c409569400444c0740c0016012401c4050191800580000da02079400042c1c041c50140070340c82d039064810020034196948448078a0391601c40d810b01d202087c1c45140000c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 726361492 1250 726360242 726360277
    0x61d1003050d0f030609152702030c090102100501060f12181101090e0618190f0f140115140408030a091a0304020f09180102180108061e09060402 64
    0x1c642d640a4080c0440c000070f990300700310450b2210101001d4450440204104c103200341c2c800e0104c501e40f02005216400300c1e90b500306140c0c8811a03d903003a40c004840038001e003940868400344550f011f00c072507065529404070802c140d40c14608003a155220704903040c4200140224000007003a015400110230490340041d1204900d65844d2451204404019850000307411000001c0c07400c86075103055000ba44000c1065043c0e501000500f02c00603402400107500c4e5800340703a95400d40c400c9108000088040103008104140000d10324030998082c0b2003c50100d0342907400410076594002e00a5084079042e24250078035070140c1e600b0f203440d401a0340100b6801d0000050800d100d035040340150701262128071100c4000300e49c920241560780011100a074018103400c80e0f034002c80c81c1c02008103074081c4070a03124840b01c4100c2c003891401c81e006941c140114120308008003138190381007001194855011555095059101000c007208080c084014601428130030021404070395030340d0144c1d2070401002600c20b9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 726362742 1250 726361492 726361513
    0x705040e03040603141b0702010c02090f0a181505070e03060c03090114190e01021e091201020304021c020a180c0818121803030f030118061d100305 65
    0x507140da0161103450046440c00300744200c3d000881d80100d10818402540e404010b00d032450100311036110b40c030101d040080d0340c202000160b03031318000d00303003d81c3c010340c1c0101503890103070713601c3c0d04461042055800c0803032030340d00d12400503900c4246070b850440c0d100804902900e8000d4140d80300d0b20915541035050042604100b5506420300196102d44d81b0784000740602106119803201a0805070303514492004020390100c1c041003960420718030316281000041c90710110b2000c44114043c4102030140c1c00c00c0004680c00c3c1d41ca460102071a000032110021440d50506038001645034018214000240190382c5844066507a11403580006204540d02001c5010340451070700020f00150b85040007062403800460902512003a001d880110400c1c002d00546c1210500e891150700710400224100025030000100c544050000c4d1441031196010541ca0794181483c00d98201e44941d0006a03143c0390820070405034056617007055031012056945460382c0c44248004504102903000580700384140940d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 726363992 1250 726362742 726362771
    0x31303141009051b040b0112050711100b0114030121030219030305070206090c0a17010b0a03141b030312070201240807050a030c050402031f291c0b03070504 69
    0x48040c500d5400b040c40140c034013001c001c1269a0305100038005400c05800361000740c2c90b13502690300600719081655103c00100c1000c0d1400c0307185410190855200d0108040300d503084514040540030400740c0c1c606542c14032401d8042404980440040b042841141d002814005e20880c800380d80c0c0c1481102200d1814107014010341015a40a0018410600014100000441c481c20401c0d00180041861031808146c00585580d030081c902d810f560350992021981c0d80c10140a004501c501000c107004503190b81098207041540c07101901d00780f01d25669a00c2640e001c17040303883c0152000b140c2c1949494a40c4200d004188484040060508100703200c000a0508001e26044610002c1100c0c0004d4035003042c46209081031100401500b44a4802e010503e41a000713035511414114000c030000c00c41c0984010035290070fa00a120812110404803800d039090503900352100c1c05c8001c1c0d0382c90120106503148802c040039402821550703079050b11105582d81441400c0003080300078018014600040c4a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 726365242 1250 726363992 726364003
    0x1202011b0b010905220308060420030a0c090806090705092205150108011119050f22050607050613060609140a3e130b1b03130314100905 60
    0x800020b2580c4d0960440002000403e40091b9059a81032080d49420303051102030420316050340c0c602c45158420001c0160740102441c410303004a80b0100312104100c5000c4c1c41018035401022450b00300300c040080b59140000d1100441e8010349401c105580c40c1000124540c3c1400d20b0060803817984c140d400b05200700003030350440351580210a010b45903a650390788c82c22a002201460b200303240c10f00c80100000d90f00000c5401020340b0b400d0036842c040c40c1000f004442e070310518115408140940300f0341c444405400940d4090801910030034900403194031181c0e038884006042e403048041456500c0100304c100c2d000040100741c0600b081c021098082000c3c50704d154212520031015250440c81424108010074042070b10001a400101e041c000c840c1e0024080c640c90203007096601d0030015050014498021840108800110591954138000100341e030104410700c803d4850f030051052641c01d0307030754054020441c1c4c1c1c4004912100b1a10303560b941e0610740c826810054003441e00f0360010070300801203071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 726366492 1250 726365242 726365251
    0x506070f0501061e14060702030303070521370c0e03060a05132d031e0801060503011203180e010303180605090f03010b0d05030a030e071202011b0b010905 68
    0x340191504c8841000c0c14000c040524159078440300001c02c1841e52024020b60f56880c00303001540741002c04e0300400d2441d03005a0313901000540000340f10420a04101c0c03c0740d180c0b845240d01500301c0c01c2200e02c800b007082041054041d00c14849007115208104a120200d000c400818140322131170b4901e00c040c140c01e003240c2070b481c000e0040c074002501600892203164403a40b051103400c2d580205689900e175004170351500c6620f2040d190b045000c0b1a0380c907684076480d214402d58840030041c0400b40a8001304a00802c910306005034840140b000325004000d49040d10b950b2201c03044041c540e4101140c55140b589000344194800e1000424281080d10819040e03e020392a807001a941040a10341018980e20402c400500203104c41c0304c00d40340184149412090040022a010069000080301c1d02250300d411212913000259008142e6014003520384100c000c80040c08801d0b1910030845216008640d000381004444001c082c602c040703280b4201c002c075410610500143da120700e020801044283c2c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 726367742 1250 726366492 726366503
    0xf15080105180304082e060305011d0c0d1101020a0614092406040218030f0105010503010b0d0c03080f2206021e0309210a0503090901050109030c15020102040506070f 73
    0x1c030740c801c40d10b00010445046890311001092420400e400c0c142c41030021074102c480044004400c001452050302814001d180240000180c91f03480d0030403481e107641d03440090b120706d803c12000e030159039032038400e48045190051094464188403c004034103004481100a220510b0080500040b07075021541e01d1160551004903040d8000302402c0e0211107140700e02010404004400040041c01c0c190003070008000024103500030340c8400d40000e0b050034548260b66003139a5499004100360301c0c0034011030070142d0701a00c144c4890191750701d0350081361040d8007001d8403c2f500010084106007c0c2c1c4215181c87c10701c000510700e85030194050401c9251070f8801c1c1c00040c421112500300c086103206105134090301000081d86081200c90a01543c40c003d00c1c241083c00141d944440d180c404180542d4a1300780c460720103155142c1c000d03400c00c1000403060300030030b040120106007800014424540c240c2511080d50044e90b0700c3d2000070003280a48115000350b500301002141c00fa0400200c102e100702500c2c80386 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 726368992 1250 726367742 726367771
    0xd171e0d0c2f100609090b0c090a0303030504050c030d0c141605040507020c0307060c0309090c0507080c1c0c050f0105092505090129030105060a030f15080105 70
    0x300040303409041800b000601c182040400b050380700800100401804088010b4442010241400004541c0c5681c0401081034030395a11904010750070441d164803051090045042c0781c0c00d00d0202e906256103000003414141c1e0f079000b24007407103402c0000c035102950040c03c9985013a80c60381c2c000d1400c881040b00b00c030303150011038980680e014081a1110030002c611252080c5900e454100009810064400c8007903000c0c1c17044426072900d05000b807001601e000c0d2107416004009107001800c402056000c0c200c0c10b0f14103000d5110307641d03114044584240e0008501912025010951030800c251900040c9010b8108008180d9958011301b003001c51031b01600a881c101001d01112500760742c800c641c424110307006150304d010100400e80001c0040c0001e8180d04000f01c0d1601c0c007042000c0800e8204011401014105031000d054102e410700661a005100c0c83c155450000814058040c1045a00a154540200507002c0d10b1035481100b01e8078a4442032041c071541c80c01030314002c106c169220111010103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 726370242 1250 726368992 726369011
    0x130308160b010e09060402010e130603030504050a0504090803040b1902070308072006071101061a130503121c140a0b1f080a05090f0d050918060d171e0d 67
    0x785055244120703d804040d0171166555401155040122032140d40d201c40c00c0700002403028402d109000245201392030306562142410308009901410703501030b0317204504110780c10b40000e5040055a4000e9030144201c17440383c95880c0098488502c10310b040300d1300751020508005140d032142c1d0050060100351101d101c800ca001041c04e06c2c000c80038500d202c20f58420030114180610903540484404212000014030640794200c4120866013516a4543c0e52804107044844106007090306c0b0081900303c00605207541560051503c600498509000b00903168600c40e03040c0c0c003150400c3d218948075545194881c0b500e842404001c115040d0f07054042c000b188101850070000031039088040c01c2c1345c1c9840c007007940c55000c1040a40002000b40c0d4081c040c0f4050710300010810440c003580001e8a8454a0304d9421000c00d00109448030140d45485103e06024880a522a040d40314000b54101c092130501d94400c5202c110240300c7d01c5c00121444004031184002014100701400345a01e2840e018404d0040d0f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 726371492 1250 726370242 726370259
    0xa0519080103050c09060411070323040f0e040519030f090506030105011704050106090603080a03241401020703150b0301051e0c031506130e0a150605130308160b01 72
    0x1024000140164404e040d003092510307041884940c0154020700c049051071464800c0350090b0051a011408103444560a20140c0d00c45085192a200b241440d6802c251804000346030350044da1181d0460001c115000c2070601509101340d00c2c01550469015a40c0d0310107203402400c054908000341d00090200502050916140086a040792016500d20b494400c50702924803003480007a004403111366841000144600407801480300940c021500180c40b90740010000d019901c040d648800350801c1c401c0c8a4510200c83e49c220015078000c1921402441c0e01400182d103040600c0e04054003040d04034084140c2c070381c01c54200903a03180003a8024002d944400011006180e0113101c500c0c0e180752481c000640884403840510781c0010384104000080c09003c01103200b42d84007006104a003031072060180507134040715014640010404404100c908000982d0301e141c0b803402d00550301080000600f101070000800c1600c40516005940141d550030742c2925441c04a05c00102210074904541c000030b481790 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 726372742 1250 726371492 726371507
    0x31b01080a0b01140f09030f01050403110715120e2e050c030604110d09120906020613120311040f030b0121062a1d06090a09050603120a0519 62
    0x48041c2c4482d0b40c410b0a00f0b207110320541000800745a0b440040c01b1004256400700484102c0040c910000502d0741001d00b00108125144602020796034050841049100c580d80000002c020252403c0b0305088074030000c16019024002d00486c59100f604544150605607a50700a018003010640d50707061400d820f040c8040d900110b484000040c0203200048490034960401041c41e180403550b281742840f1804100c0c2124140324007564038450b040701c20480f4581140440000d490140005c04e414588480c2440e504481001c3c010103000e40207007031520041c040c3d00030b545492030389005581c985440c2d600d0342d610001d0511080e65104082c000004a01c0000d0018070102075a0010180081c140c0381c803450013505160440003211500040849180e125141344500c024116550300c0454541d0408920b400c0c48000e80e12500c00c03074017004144603603550650b100e82140c1d850400490b0682ea0400060f051900503480c1d040c0c8010300040c0c501c1003d80c403000030b10a01e400c00c4007200440e2400300c03040714200f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 726373992 1250 726372742 726372761
    0x250b01141002030306040507110604030c0312050105030a110102070503011119140a03020903100903050912030f0901110106050a0303081009060f03020906190803090a080f0c100e031b01080a 83
    0x143c00820109806051580001c0d81c0710300b680c100b40b10f5495204503958a4400300f204c0940000c1e201502c604100f65004080ba00c4812082c0d01c00d03c5954104400030340c03100700038070005007400300306451054164002d01c0b4800040c600100204201c802403424032030070b41c0c016202040d030800034a517404c060078001c0c0038040070300d20314041507800d007141c0d41016002940002040c075418030483d1501d080c8841280203600e5403900ca682c07032507110240746051200b0120003035911450b540051020b13820b4004000103440c81e1030004d00e8607a0824464400c954010306e425002117070000c064090100606800007860b60088074030740729011040b0342d00c407022822a40346024084a4081340c010410151800580301c94100c07100404000329010b124403030180c149103030b600640c416040842c4803407880c070702802420014285200a40100b03a4041c03010740e251300000070081e100300c1045100c0d9401511980300c1c8450300b1409421284000e000d400c040d40c003040d850000c1030004c1c0455001844500281c0a42c5d40c45 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 726375242 1250 726373992 726373997
    0x20705030c0303121f0305120403021c082b09050307020a06020d2001020d0f150801090b160507060f090c0503210903030d1803140408030f250b011410 66
    0x1103444010740030f07080e92041c4580102001c17034080c0c040f000c28030034000a508400766140242e03840303146106200d02660780d525401c000c0106408644c01082d41c450464000058410958106080903111410343c000d41a060101072460400340740100100040107040d43e60084500b2804143d0721101203907035404900c103020006000b84480c0018501120740401207400800002d810110480510340440300040740c4d030358030140c07904000e08650144005140242c03071002c0080c02156010740743c1e0151810041c0050304400001884100c00901c1281680c11960740410188030705060402a0030180c507a5072000d0303c5045d40d2100000c2c19280001c1d030840c03060405241500d0074103c18035003030b90581201030b5040e010700082000803441c054a1280100110801d142007500b80703114100103010301064101c2d1184440204000c2c0a000e03400000d03a034000340c00c03109180d07980c445040121031080d0a150000c22a1002a8000f010000898002030580d01255169400c080000f8100210f403004030004501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 726376492 1250 726375242 726375277
    0x1603030e121c05040305010c020d030507020d1d0607150218042a030b0a0e09060601090501120507200f0c0103150509090f060117010e120406050a0311030106020705030c0303 76
    0x20148400d080c8091042c0e030415a003441d41daa260300e4250790700c1422203030042e04548047c245858061141603009079444c401001c3c0d160104038003800c5040c0540d0016600701c06c0b078075084820340d03450044031f60584e8810001c030340c500d107036402e0312020b50000000b8010021410b00b0740e00840c00d10f841101c0d004034070040740c5c00940b080400000c0c0c020554020746001c05848501071107080c2c503140000303001004a80e0f03071120706103000d0001500740003000c0d1400b810048107200270001681d01024144a128540720000361365140d044040e9002100f0098900001c0700b26410098544804901001d01c180003005603640101342e4001101116414510501501c0d841e0000744254144051034a41c0b0400440484088012486000e41381c00004d070b001300e00301d9242100303d860182080c0100b941c2c11581c00002c4c00d4800214410242c24090303800344500304940420030641e140e119800c041d0700c2601443c0c91960b02c2d61144d0000352a10034038003416010703100d11035851149090000c216038406150304130354038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 726377742 1250 726376492 726376513
    0x170606090904060f05090a03020601090606020d0f09211b0302210a0b0903041d010e0705030c090a08030406031808030114030a0b010602011407020a150c09081603030e12 74
    0x45500c03800b07007003540c12541e1000c03105a911320720320a01c1d00800340e460060540c402549030091800c1d10580200d1102810804100b014a800040f0010725282c107003802e502c00001c010040754459a43d81c07264000400b0740c45104007001c0103410141195005440c980c401288980d02540c20107032070300c0004d4100c1e0303080f907000c60017034400c14180815503614400e5030440903650721007418001003a100703030800d0b80000404011000b075205025521204d50b902c000c030150b160481b526884407004100000703001300080015500400c1c078088810100000340722135422038503500e61540d60b812074001d480101c3d1618003400380e50311003200b45882c0c403984524414916800c2c1545040c0804c81c803008241c243c42215200c01c0013403074201d09176018102c66400001c0001c041e28441064050151440c0190f400c2106400b010842c080040e007039a0b0390012012984c031041910407100c040459100700800e000f01c00c801011101002d0810084030b010341c3c5d4850021b00c0c0c2c2c00030000541d000050000c89a44281e030603d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 726378992 1250 726377742 726377749
    0x31205030f1b2b1b021c0c020d031d1e040e0c060d0504020406060813061a04020a090503070918110619020c09160c0f0804090e03070317060609 63
    0xd4100207000700315042072400a00d00c02200384420541c4684401c5103204103c4000350300c1580e041c1425041e102980c046002c501035124105090900d100200b24a14011403601805142d105c550340500350940150040c24020080c41507000301303000e40310760103075074650618020701001c00310079119030094422490401040010700560049042d14001c180080000d0350307805000d48a414041d04010640f45070031310400c82141d5141d00034205011520090010410114811280341503104600141410003c98101024941803d9032984140000390701540c10ba0f016080d04100d036000d8003203a0410342c0312142c2c0705c256540e02c0114040040d03200e40b4400805c402c60ba4000c417902e0301402c9130345840c0c0d00c0388208a802610400a901507840307020020102d05051031600c1d40000c03000c0ea01c400c0c121040500800c04580000b0180003620a01e0200040c000d40c00c0894009003a03c503410010313400c4000f105a101d4202840540101d0700d121844803641d140700c5900b070300c901002001e5901e802c001c1c900700b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 726380242 1250 726378992 726379021
    0x203090415151d040507090b1e16020901120f170904021215120705010e0f0402130821090112090210030614040b0a03030503040f0f0804031205030f 65
    0x1812034000703081e00040d040400105021a101c0e07a64500c410310b0106044100754548400c038550199180000b00a0a44c0d8051469030656040c411050741d180e0650300405141c800801c2500800d11000520b614508040401400002d10a40e1001f425070b03038919210500c0154500042c02035030b0102c18000c0001d00c0f1350311080e1f0350842400c0c60b0b810403140070041030407608600450102040c3c040300740502c400c0b100d4043c1c0c22860045428481e0082041c082c00e40740c07080d41c400c450600130324180407540341c0d660501c907088428003e0411034072066051126010ba0240c1d00c40c05890b0300400e044e0a1185082e80503201420b46d91941c40303864541a00011210416990030306450981d48010020040e91010009003e4a2040d500400c0344c600300108805c40d0210307018031034810343c034108005809846020845084a415080080d01c031b90355420072a500003a407040042511543e214004100848071001e0800e60740070304500c0c65200c0e00c1c620305441c0d034807054601040200d100d10019100051031080c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 726381492 1250 726380242 726380261
    0x102190807090e0103080d1419150308070803010303091a0711120105071e180509040204020702030609030d110301140d030201021306020606030d0203040e0f1b04060c06150602030904 80
    0x1003540d01143c1c0c940c4040d40e1450280c204681c0c41d80001403240745c080c4070780038400b201c4074407001c8a0f85a05240d5036643c070050030b000602141c2600d0750600780c0740140c2000b01c00019504120301a644075032925113222141c2c400d000890104000d20030118090a000501d45421800c44c84c10a26140b195100d903085201c070001c0c501d904c0443c82044281180c02070203050300400b4962221400c2c20b000c961007015690314400c45008014543c1c40050b071500c000011070f03040350002d03180608591164004030f8040c2c03107003940c007942510480040c020700d8800000103040769480d40808020084007089000301c21311080c4140500220310034645030891030107240220005e4481d0000510788000809081c10b54440742c0d12540c0560010010000d076400c0a100203082200e03e407025501d001d06000640004034800b405590b0340c040c9990008072040400700348580904060745000b9100d80c0d80b08030041103681945400c540c11401c185103205451000c032404010b48100790042e41c1010070500c01e11008090707011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 726382742 1250 726381492 726381497
    0x1051e04020409111206241806041509050d0b010303030c0216060e0102060c1e0d06080303010306020322020a05010c02040b1c0506090d0f0309050a02180a0e0102190807 74
    0xb444003420f114031030f0700f200d00002d6145c817100d013084446103031000200203600030036682c415104201c41d02c0704c83c00710004548908544502107126410080162800c0350340d000b007070000300401e0881e84001c0320700e040d070110350700c5074410f07600e46081c020003c00d1818000c00420802005000080c0240c01900800307000d48112004003000b0544c1074806000e9500040101d040040c543c8a15641880301c15449040002e54a01c2c0c0a60f1482500105464002030909180c011500358056507154103c0d000400484040b00e840796160304020000b54010340b02004580c52359040c0c02001c40074400c449448a40042000c00c0f21460300005499408c0b04903c1240c0c81950b40c98100c0700303540c81c240800c01d00c401c000e0303006d410242030749440d85c034100700a841200c90394482c40034a881c00c0c0e808070340402c500255290115511a0610f840c51400e0f007440c07802588805844500040e003030420b4001031040401e00010311098846442240c00c074070800743e035440d045185540200d00f45010310501a004003051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 726383992 1250 726382742 726382747
    0x10c02010e041103150409050a1b0b03091c020a0b0a180b130b0603060108060403050f04032004150e1f0e130b2503090816111801051e0402 61
    0x1000042d044403251204100c1104010082c043d045038411503c0d41d0030301041d01c003000001c080c2e0729680c3d81e602000a00501001c00001c0c0c1015071414000c014009025081c0100c0e101c1c14041c0380a910340013001e0040030600c1e1081c0340c034a0980e100080901100c0d4224145810580b1644400c001070b05a4002c403440903a507100008000070314100b601d620171540c440b10b400c07441481c0c1c0380c01e040907100034103158032a50209006015903680850005d4010354503081140d900c07500c82e055100c541c02554000741449141c0c614207000c40c3c0030151603426400c005c83d800c1013880c0b820040128994801d008454106900c01c0010782c40542081040003001c0410040d24503055940c0500d0142070000c1f50341c940c03410060000742040200c03018820f500a41c82c001080a00d110b41307022115288001045e0030101620b40380d018060103850422a40044c3c220070703e900000484e4149002021a41083c0e03d0094070480042c13407000c1c1d48001900d060b0341005015401c041d2120900c3e4580c142c80c002d41c0d83d07110340d08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 726385242 1250 726383992 726384017
    0xf12040308094e1201080d4407030c12020a0909090f081c0509010c0c080a0c0b360717070b030f06130501030302190f1401060e090d02070302010c0201 66
    0x8401c06425641c2904441c4c00d40756042120aa061140800400091024650111403140266050088600021014401818a4003802e92000e4001d0304102003c65050400c1c064034a03810b4019048141d202d0312940340300c0060140c0c082c100d128020084002503d8940207000c80c0c10643c2102c040326000d00c0c441040c00da00b5803a89002c56111390310030001007404d010080413400540c094240d101c1103642c001c1120004640c0040d01036007140000070203480000546401e8103018080c41485d06401100d0700869203091001c03503043c0c066201071101d0302032900c0351210f207060a50b101488400039044c0509180e0785425614102d1014008150159000d0407801040b1451000040d500c140c054207114649403c0400a010803000c281d014148254104001400425000210032028120b405800c6207030303400702c4c00c042c8c40c010404031004000345690303141a42c2e4040150030840c01e40302c0c1c0000340c98098462102d21a600e207003412440d405600920010000b541c02030b4003582007a8018146404c00400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 726386492 1250 726385242 726385393
    0x609040203100501020f0106030b0f0c0c0a0c0515040f291606230f060f0a0311100c0515040c18060303030612030806060f1204030809 59
    0xc070b400081d5410200340400c6103607030410105403044000e20007000924215141c001040000800c01024100c03041c01188101100c1011126001040d500307480000f110b41c680b2042268051150070b119140000903014403140382d000f1601100c240c28070301d210052904008229106580301c06004980c1d8004003840c01d2071202c001455500140b000c0740c40d08000d141307010001c95400d0310f58010001400c524090081030610f2700e294100280364095061951000d0009443c05c0702e512440f034000000c0d440c0042080780201018100c0f640403504101200c0c0b135082c0072116050200c40140c0070b43e01035030350810002000d4940341d4220703011b10075001c0e00d03d4031081034000314980804011800c40c0d4500c42003081c164544158000f900209800031649006034034010603190010740a14456070000403510700c031180380000ca1703402003000000035a031441d19007400380c10040122046850b60141e0200c1c0f480c0e6900343d0f0400b500010903900d50a40a022480030b80910380000607840c5040200c481840c4103071030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 726387742 1250 726386492 726386497
    0x6030103051f09051914070801051b161b030f0b100902030105061b101d0705010e060706020a03090b09070918050705060f07150501080c19060e06090402 67
    0x60248004011094000718408151589120b000401a182c4181c03040080d50114418800028581d940610136100e4204038030700e661004004501c0c0c0c030030a0f1300040c1c46141900300c24456000c0c0c44107100100c502c0d4214540720b10071800c00800302107049c56034000154081c1c113944c6180013840c244114007910307a0340e20801e01120315419175403444000c3c01c2000d0fa02402c6403020143c08050025420741d45844003007105801a440c0f804600d03041c03241421000442000b001320b410b2142141401504092100034802601090300940107020341100442c455000b00c00c4091203c0c2d000d021980f50003c20345444009410481b82c3c04100750311050707110041008544107034016107040000c0e007001442c0034110b8003105d40c0019066105010500d008002c2840030810000300c80c000d42d400c5542d5048070380119003900c00c5400040565001891401c000361596000c1e034143e80e6000111001c4000c038008010201c09401941c1640220a6500744a094890344641005107000b81042c0d045c007003008000b800380e8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 726388992 1250 726387742 726387749
    0x4080f090301020a05090405060a141c05120a0f030c0e04180b0c03090d030e0a020919020a0c0b07022b020a0b04050a030f08040c23030d030605033c010209060301 71
    0x745c0301103000c200604e485d101e50b50700140119a072642140c41c0ca00101e0103004202206072040b400e0208100c1e200030308084100620758804240ea41030380c07100c02241142d80003450b00070000341c41c82d15240c5417103029102c0c07111286036944420710781c400c0840030440a0320703809141c050103061591460340001e03d400420390040000d82201c607100d240c54012145000c20850024007050b007440440c00780001e0205c1c01100864050300c80f804075036100818010b5842014480664040c400500400041d40c40f140d042c42c084d00c43c3ca81804184c9541500304d07540c01781000e02900d6440d00345119000342c0341c8650941001c41c094010b890f060780b06600ca04080d80e104640a0300c443c0c000d8002d50003059404a51407400c9401c3c2d081541103402c082c1c4aa13250310a280c068488000d0245003640d6654141402c1a0300d181b00040c00c452450740c0f100f4005000d40028410107000e8480c030b103202e1103d12038140081c11f45c44589000d0320b17140c0c490300403050030320128290b080c20255030801c4206000e880b140002c40c040d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 726390242 1250 726388992 726388997
    0x519020d151409010b011209031b150f021c0b01210e060901060e0c1630020d1b0206280e0415051002070b3f04080f090301020a 56
    0x12958114542800c40c00503c6081283d141112466060780c01440d001e803603422650000600c1c00c05c0307142c1582e044021040b03409448089003600020400706070880c0e21506480c0c0c0c420b1010204d5000e03805c059000d14900d488001c00710054110303c2c40002e51014441a0052414482010007106140b48138882081c0d03480d40c4a444406103d00f080b810840103410400c448c00030440146000d800c492940f04c05030030100310010005008030290400f840940c0d4640d00310400f040243d1040d0f46100d05c51840c250107800749080b203682c0ca00f01310300201d414005001d068440f0010110642a9020740d00e989450480c1c4c800402d001006481c030101c107061155240002c0283c0d0b8140302c01c08013a2003600c000d031016105a0a08800f103c019040c42c000804481050360308102890f400741042e03003889142d030010045110080780442d408142c910410110041c8111121071490f203070070703403000040c400350b030507024007150040402c0c00918800e00070103040001c40c0140d4104810540040e00b681d0141ca400d200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 726391492 1250 726390242 726390251
    0xf0606020a06060e040807030c0809041a011815051e18092404051305120a1413170712110103050c18010f051606050114030a0519020d15 60
    0x10803545100f040054031000810044e00c0c541651050150b1140380c07001410400410540c008103d1683c00b03403034120300c000f802403141002c444040507441211640642c0000c41c2e00c4441e148500380516403c00b524000c400c0c070214282e581c84103a61581c0a1120702c001c50383c81d000c1035401c1e00141c0740503052104c0c1c204a102d002c04680d17010846011009041031001500741000850f5540464075102c84143e42510041440d96801c0c800d400c03203c80c10040905540122880c034481c0c0c40068000740020b1900392101504407403481510242401503042495400510308418030000240c0258000305130180000c644420b900c800c000d511005482d10100c40900803065002071f95a014051190b00003158207119080c0503c819101d0004d0340703507541da01e060140001381100100d100740200c3d8140000c410a400e08121180342c4203004000034803422000f1130b04043e07440300d40d14012038460721841d00300000300400707500078100d2882110880f40881c1c2c0101401000710005003480400300031621f03503410028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 726392742 1250 726391492 726391513
    0xf030303150806010302010c0f0b1509011a0d0506040b0312070308010501110c010c2306060315040b041b0905041a060a05181816080c01020109020109050d020102010f060602 76
    0x5081e6071911108501244058a06115000000400c00c1c1140c0d024605a055a4601d003440c5040415800e005051640080c04001d03000c0280703051581c90003400e0302c209006a03078031140302000e0307550010311952003041040308600720041754000c5900144020310008602c0c80d00e000203850105880c01243c803600001c00c400701816040318016005000a007401d210f200060740c8259140e60520040074148081040c0600a016130356030510301503c0e0010341d00440c694541d403850340e90703201141d84510900c20408100d00e90000385d20010b006a601c0072405c16641c42e01d565403030103c0d480642e094080315a5201c00500c000031802114001d6000b08001c1e0840060f488020821120040c5854007503c600301c402c1025440c3c150110749038803c031110344207160310740c01808203800c400712106614510803440c045604e014800b40c03080407a8220022200310154030030059017038074500c0e14007a02040310500104160700307059880c540701520510002400c1c1490100810486103241c11042c0182c0c401038118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 726393992 1250 726392742 726392747
    0x114040c080d0516030e04110403050f030702011704060f05040c052418190b0c070f0e0103120201090b04030906170c0405010509120a061a04090507030201031112010f0303 75
    0x1402074054107000e0403040c681d00701c014001348a0381032240340041024075072070103052040303041030780c45d12004009001c0410741240c50400768115001c1a500e5000c0c880d10b82100481c00002c0310146a41a100ca0490000d00c140000000600400540d0000c0e161840d244d0b020381d03a0705c01c1a114034414103080b4040c0b41040b0174403035084e020700810b0f0041c20100b1003c101a84601054a00640c1410101041920103401055084501000130702e01034448013808560f413070120f009402c001c0c641da8110351005541d40340340f0706810707030b0743c802c01c1d45015002006001003000070042e80f1038030181c3e00021401d244030399940c10000500311400e400140001d081880925404119000140210102c40c0e5107810300110b500700300d1045102d100d05100002541d12580d031246840d0340341c41001c0d00142d40811a00303050030005044106c50610f90500c050908002c5403401c3d2203800341140c1c06c10000c0156604581c0190010f02841c60010200300f0300b03010003101c0045180020740a4402a4007001c002e07032071454007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 726395242 1250 726393992 726394013
    0x160306060311040b0108060f030a150e12040609030b0604020f03090607140702010504212f1c02150c01090c0302120106060212030709090c0206100504060605180a0503011404 76
    0x99074801c43c1407043c1c2080f136aa001c42180d42100003180e10f1060000f02e0f00010f81382401d20314009183c1c8440c849004400e20380790f0f1060320014505020781c0c0c0e4105100700c10318114460760040c48d0110f0034000d014008240565911640401d0242005160290406802d49030f03030422501c000c610384c0700340100100f140d0b02c8451030089155404516003040843d60018020f030080740a60086081c4001c5031203907000160035481041e130342154020030150340726a8401400701c040552407400c21341c5084a1209424550b800302c05081581c030080003650101d41c2000421614407000c03000b050300510030040442020310030304003c0c600c1180003001c0c031744c9148103002e0100d0940d13445079501d92401300200081500440e10300d243c044004003d603030b240c3c1d0302c1c1015544110540c1008004074501010440ca0540004200b0700506401c003440d803615503240f04000c00e0322824003c1e5400907034140181c4481c680b04c3d44e04056804401024081c0043d140d00110703003100c040804c9000e001020100323003c1440307500c821 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 726396492 1250 726395242 726395273
    0xf071b060302131a2b050105010f360602010c02060604090c050d2108010323030904111b06010e09010902030622060510080129121603060603 62
    0x20158101081c01c00c2e054904143c44c494201240c40c078a803116003404080040f624100ea10b4601c50400c01c5c02c1c0c6410004030032407045100b400705d00c0c0c070001260b60341c05000140d9103441150744e40c0394004881c01c9800c00d100310340c8403400d0404d00c200012440a280c81624000035125a500000d41c03072150800c02850000050080d03406545000b003c5c102207079001354500180ca03c156203020520f0708038603000c003400301b9403100700c441211390564a00c940d9a1000c161070489004100b0141e564541c0083c00310404d00901042c1d40507441000700f0202c50030700b904000411446e000030350342010440f209504101034004220f41c9160800b8005001e0100a61445500007000340003c03c619051540801d954100c06000320b00c00024102d07290301e2202401c90007a40c070035400b85091090b4108505411440d603a58010183c45500340316a06900000c1e1001503058106850445e01c40385452000f0f0259442c0c42e150584c005016149103624190f0305440703800011441103d00242042c914107080551300f02140c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 726397742 1250 726396492 726396497
    0x14130c1e020f15010305030f1e030415060b0901021c050d050a0c080c0403110405220c0e15030a0b1b0a110c04140a050a0b0a030b060f0409050307080f0f071b06 70
    0x3c00500c049940007040e0707202e8101c1002c4440d5100400d0034602d91140c16541e2201e48210004204403c000448030764590310b009441c3e0500410751a84008031050060230703425401a070000c022040b80010590700d8009407000382c00e100c0d20340a2808101c4c400c1d2a0308840c416000d5803540f519000499100e217560380d000500c0c40010341014151368030803071540401d291311031140c0d03184c0c1d001c07558101313480b00c1e400f1048030f50305000b4800345280c0c44c00098a41003441030b981d5980c00316000401201224018210854008018007840c4030b035070740c0b240c81c1e42c50041e015187c604602c2e019000c001a0220084c91142c040c1c0c1c0314841d0228090069510740307880480414000c508048051840c040541400c41c0c01844410001c203203561760082c00c100900c2c0182e04076500c540c100d58008180100888680d004da5016581402e40c108620140000ea581e28400102260b00802034040811400030180c100f003440400b0042c90850013003e0311100d500102000d5449040c03407031207070014514200c01e850041c407850 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 726398992 1250 726397742 726397783
    0xe1506010516081309020414030d0e0d060e161e09020a080a090f0b010b120a0b06041e0305010504140115080303011a090301020f04080714130c1e020f 66
    0x20100d126502d418900043c5141004510031300d180303c0c850341c01e9002d0041c1410842d02d81d0707551440c1c07040c480483d28003a070190060613180032040d8400e0600060100004d440c800c4012040c0d52640c0040044480c90581030050b9440300300140a8913490b00001c1406400781e80040482c0122014440190743c000c880c194410080c58038242d1f00698150340c0714034081c030001004c3c681d504040c0d06248912000030080b072034030300c004100452410043c0680880811814035181d503034402d480202c0d01c000b0f5041e030344200700740403c01114410310743c5400165401d442c8144102d03500e5886600b900c005540c215880400700c40070b4440b0200034030420340c0140c1c000942e40c200616000d007894891106016903604045203050b01223210785030404075030341d484000c1e00031560703043c100340000350a4015000300c0189015078800003a582c0c0c026882c007036414500070008600d0b4040100e4a2008200c8131080070107102003881a0141014040100d80184c410740e00a407d292621345083ca00300101c03c0390258050411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 726400242 1250 726398992 726399007
    0x1e04031506082e050903070f03030c0e0402070c0e041401020c2b090312050f0c070602010e0a08030106031e0c08070806011805041d07030f0201021c2c040e15060105 72
    0x6510700c4800003143d0004507510789030030301c0e4214498104080c01d580e03d601d0302d4900701039055000e81280d08541c1d40f020300c030b40754031000c20041c0c1c8602d500181442840700800e20410074800c06854100d449400041882d40d14170701001d0990700110711100c0c1d250419041014105240c3d11498201400300302c241c040f81e021864007801c1c0c0c5030a4040a020582e1b2800b85a070303100e0040307080344c0f10881160445510350030164940707507403010140200001542400a0312481c0f0b1800111800d9941c1c1c040d00207030550303080900440040400c41c4403c82102c01c0c1e64403203490005a0707c10810810f007150750b10042468241d0307000d04014406085641008107080d01c491141c03120502210955031700304c03404651b40003508103807840f02280c4940a42c1c1130066007400010002501404880240300b81c003600e40e060703103e0300364071054529010f054000c41d0310410241c42c8180ca040c0950003c9040110111502d6510310104003201d0540069081e01d51111560701100080000c1c3c441e0300040c00d20700b1030310b02505c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 726401492 1250 726400242 726400303
    0xf0b091801270c05040203220804050402040312110601180b031e0709060603051621111c060b09131806020d0506030c061e0403150608 59
    0x1801025030194505428a1009003102034010020311000c09032820a9040205822044621100c400f240e01c601500000100c07418180280c0344903c517410040100d60540707000040798505c1c58142150608001c10000c07505945510191000d51300543d02648151000e030310240c0000355100201d85240d203d0344c0100950f80000041101160700c881020445080701d5012a11300320b00f001c607400f1540002c07980c0c0360a0380c4001807150200c9032106000d2100541c0c6020540c101c0d01c0a898080004c5241c0d0041000b80d4056100100d82040b03603d0140802240b00740f6240c00c031024800084103802001030266441011a24108807001e1800020000d0302d103040f460a11500c034010706c9502440b80c11052032440c0400354401250045c1c0e03039030070a0b40d680203450080000d502c40559032610034070b030401042d55820b00180c030945000d0054107951a00b00814101c81003007480080c0c1d03030050442004040700280c4584003109203c0b203d400d021030b4031824081c80d1401c041d50f210542032014600f0404035000c0e00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 726402742 1250 726401492 726401509
    0x10c021c0804090f0b030d0f08010b031306050f070e1f0c1b120b0a0509070504021e04090b041b0e060a1713030f0f090315270302010f0b 60
    0x11800c200399411090325055850b401a5404441c00c0303850211074050001c840e80143d10703500012010b903019a44200403e55042690304809000184c0d41801400105002802190004175000091521000c550382d00c50136100708503400d00161104e081400031281e003005840c1031101044400900308243c0c41a441003400e481e2011504100080003c5c60600c401d041c403003a2a800310146844070302e61074401c2da20b880c41e81540c049038001c46070300000380520030038441e4038091420740000d000518509010032019401c52110804a110b034181d54000441e0144010801801e00301d8000c01c50014101c1000112440441803041448120078002c102e103510026030507145008a650315103400c148413080307400a44a6a201510103007400c1032240c284844114007018a100e03a86a522030900d0500c01c40d03000c1c40e64099040401d1180c001031001601e0303900e840c420894000b100280c0c9a03003821403205905900300e494062901c004011005042e42805081e11000b10b03d00d082c0140c0c0415000b040020303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 726403992 1250 726402742 726402769
    0x6080703230c0405120606130b0607030e0a0f0303090504140c071205040b1c0c0207050d03050c01090b010b030907050a0b040603020a12020d020d1808030609101d0105040b010c02 78
    0xc072000000300030380d800741c043d6009070202502c08035219089002c92513603514140c6280b44116140d44600a45d0f0803140a107440e849030140ca07440c1002c845540a03504188503032141c95018110f030320003040b864040202080158040d0f59001009072a200c1031100f20340c8080d0f5410b42900001c0c0411076540b240303a04442200e64445050081035903036080c12907130350103143c001518501000402c04012204a2003030f1881c00030140f000c00151000c804180d0380c6001c05c0c8500d541082d03207a40b920010034040c40c003500e4030405000c00820b1002003652119a0060242c1000d40c0051012052200b841c1080240744098441a522164a00c0c10502c124541c0e01981c03044200b010b0300040c40990017842030300c2711400b0b044400310564507803003040c884802942203440e445e800f4a1900189100d4401c0914180481c16004603095145496070b00a1000b40d61004000540e003212040c3c000440d0700c0c02d410118525540101880f400754100401c1000b40ca90444005041100c2c51701b031800944d64400000041c0f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 726405242 1250 726403992 726404051
    0x9030e18130f0503030c0702030d170105060c010e06090a0506090f061306200d0f05010b162102030a08180721061a0f0a0b0f0d1805010606080703 64
    0x3411901e142400340505480002820f50201209121500500300d01070315445100310309903480c103051401c04560803a9281d00f10710440f0b0341c20f03004002c3d60400100400c5825589800400c81403580760300b0300d150175415035440c0e4050344144060000d100c070a014103074208481c5000340603222091074406980782d001500c0c1c81940c510b24032004082050b00d80c001f1140c1c00c9449240c52003625420641078583d0840746003104407505000480d00d000a151080506071060145d1850400c110701000541c00300c00d01c40c044642c2d00c042030403075001c03010040d00d401c2282e106a000350b9807000c482d00018040c4030013504105503c00261026440c43c03e0114840041c0c1c1e480e40c1528101041d060b0f82482d03009080c08000e081149072000030f0b00c1c95400c0300078104824600b0b444810404050a00784418142e143c03041066030801402109500300c0380c10010f0124101c032a0340840d01d01a01c441d031001070346081d00110b509a641d042d003041101e4008081c41c1c3d100d8001e040811503071803c4089018000a41382a0151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 726406492 1250 726405242 726405271
    0x106020607030c1704030e040e031303060b0d02090c090a0b0403030806010e0307170102120115020d050d02040f32011b0503070f120305100f05010c030903020306070309030e18 77
    0x354400e41c8400300e2105815206204c500300f60402a100a074080b41c41e80c095402e140c0d5025440343c00008542c9a01d080801e141c950a140d5102c182c000c264035034401d6032207044207036604050780d504943c1d0b5004622050b85180d0fa55034003030412144507c107a010450411040c401040820307044001c840d8020030a00700700102c0359a40000900b4010b150300154501d189681c45000030b083e055002c0d08600303c4907840726116988030802c500200e00b10440d198016444036100000e4144500d000d0404041941409418541c6031003d0449280b41a0000b088030304854152120000c100d030301246010600b40590544004607800003420300604c2010700f00d007030b022440702c0c1c0c04001c0c0802c100c2e40800c2c2c1240754803003c1c0405203170071041030181d0b01c840d800007401c3c800481e58083c0d1010000e41100d00c1d00038032480aa03e00340065079101e07803d500940621914130000409614184610b0b8440c010641e8001400d05407890041c1c040803c0c9a00140101c2411500062208141140a80180b040c022000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 726407742 1250 726406492 726406511
    0x80601030c0b2b09050c03010501050a0611030412030f080f0c18010203041a04061409030a03030f0e0a080a090e0f04030c020607050729121b04050402130e0609010602060703 76
    0x354402103108001c40400781040c0d80c401c12030695228a2800e4803a0046e01c2d60354501d0300400d42610400c0c000c0583c0076007004400c021040c012146c4032400c0404500343e13070901da1781d000e4040e9607280c9101e00703801050702d080d40f101d01290700c0340304698064800038900c0c0107401d14541920340b501501b42281000c400f48840481c0580c000c00c156401000b140c410f01e01040002402031315150424450003001c61480302c503822980854605840021401600400702844140c404a010781070902c092591180e60300c0c5d0300f00180c4410300c494001107004070f542c41c1d6284011440200580d107146d2002400c121040140b024070b030010745030b04d5041074051030641e440300c010b0300001d00c42d44a00d100081c1a40305034940041e440003516a071090020101308102070b000520b802203000ca110340d604526404003510002401088402c0140203866145c4c003003075040544840210b8100ea00c8400104449844003104022011200180a900c40d000341c440b10525450510082e641e89405040e01c01810303160340034031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 726408992 1250 726407742 726407767
    0x90305070635070e0f03030d0b0a080a1a070c0f03081803040807090c0201180b01060806182e090b10020a0206161b09050f07030c0c0f021503100906080601030c0b 71
    0x90817000c00101030b2980d03000e24906000c010410540ca4600501d00400002034801c00824040542c94008100541e45074036107400140d04800141120180720054440301c01141403600c1c0300e43c00c00e00c6500da400040c00d005410a40600e81c0c4d002101c426841084140002c0e42c000c1042c80407100c0918020070102c3c0b0a41080c0d002d4516655050a9032000b120440f040c000400841d5040741c1c4a03444200c0140c0b030760414080d55402d06d000b90680c0d96074010108031665171400140d660520260150700c1078681810384014800440d9100182c0a511019580c00c2d92501300b1040801a082d40024050346500e5408a00c2900640110301d88070f002520181c0144540c000c50b000b281031900100c8070106455240c0c4000a107030a0b100b0a07007441448000580f100d0080c42003940d8556a0344a2140150440d40d4042d80d540c444401240c114400c1a13242416030504400b441c01003a004004104550500d060442103800325802005298868401000130400d14030350741c2c0a07a612054200d0351000c2d0141003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 726410242 1250 726408992 726409009
    0x131515350715020d0e09010e04080a0e030f03070302010b0603130b0c0f040e0f340309150506030d021203010e130209010e191407030903090305070635070e 68
    0x22200100d0302c003041a90390218052000724403a40314800803600c4201880000365003401100a42c070016000f180102d04134402825403900e051030b00c0b071401040d4001281c103084144208265581c404121481010340a025100603000140c2e80d450851410000703202140c603450b04041c0c854045603012912001240c0c003169510480c04600550380e50341c9801704070100c0021036408110700c80e41008140c2e0030540c40d08101c80d44051f0562400c02401e11004101c043c14074503c10000d142e40c8a255a00240c20001803007400480d6050001d2039240140c141818800e9130141541150810042001070316030440980341940c10115041509540320b07844207036407059110b0040e60000300f4200000710101a03040e0300344148074505945070b07000b2212400c030055136004c0000c5482c1001d00d00000e403402c0e200f0360080990900034a84114800d81d40d440311810941590050b400048501c190681f1300c2010b07280000c400d054030b0140c0c88506240c111066040031002d4100c800700008074040c0740761513940000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 726411492 1250 726410242 726410249
    0x906170c1c02011e050301030606120f0b0c090415030203010e0613060b011103030a05010609060e01050403062a050d0c0e0d02090601210b040e0c0a0306051315153507 73
    0x144141c013112030b040250140c3c00903c022143c25040c6000803c0030743c8810342c1c5c207980030fa101c480c0301140d60460740c40d5032245000a0100903078440034000000c1c940d41314091619001a41c0c4820740205045005140c2035440104112640d503201c40d0501c124400065a00d84201c0e0b009440041d8038030842004940010a070008512a48408418000324440b03560000741254069207420b21030076030381e40e0252000c6109484588c04286c0030310040000c1001038001024007601c40c061104c0840000c03000f001c10500b01d4544200007240422407425203419403051740c140480d50b0600d190a01030380000508007440380e0230024094a00040400d85590151000406001801d4100d25a01c4044280e00c00200507801113184154201141d0895400001c502013000c03050241010112900f96110340e00030700700251403161a58940012640460072550130000e0000c414000800d912454040307051807040542c000c0400d0020800b01d005c4030440c42c901c10401c0074600e00303000e800701e48050710603800e080c000c1d030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 726412742 1250 726411492 726411527
    0x415140309010b1905062212030c0c1a0304060b040e0303090a03091a0f1c1407081602210d1119020f1e0c0a0906170c1c0201 55
    0x105014401006401824641c3c00540c0d00d41400100340e1040c6940c0e610a1041c00c1e000351007000040101c441c52542d1004111100000078682c41c3d69001c080c0032246100b030182c00181c800705e01c1e20100b2007400100f100a001c0e00d1480031703d03001684580b602500c03024000602d00703980d484000d131140d12903400071000c090a0700152510b901c2d04240a81d100d400c80801280046c4c1d03c5000880c99001d2044014a07030301551010506003003070b5040703100c005e0340411b840760030305c5040c079030303c21340c4e04140303006408080008a540d00c8541c1014000509585000f03400c4030342034203100c0014111680d000400c03042e40004082a0700018001c00d507002504e100e0490380170340c100d06080911f6240c0380300c04024210300305910201c80b010114604120b88410181ca038050043d08403000f1101841041040e0f415841d0056044d144c00c80442d80006d40100e40c0c1e9800910305545800042040c5a10f60181d0b008551000000e03000034200e100002d140c100a48152112100404800b0401e59100d00c50703902c041040030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 726413992 1250 726412742 726412747
    0x20f12030a030608060f04021909020406020d03180b0708060f090a020307020606011107050d240f15120611040e13150905030304060e011107140105070f05041514 71
    0x1800015180e600c00e50901010a00f80480095492000120f40e4400c81100000e40907988070f9a00304000c0243d40d403004135030010440d002041c01c072003e10040c401410150001d1440c015a4035018041d02c0001902e050848159080100411403078092203501080628008985941d80310001e0401508250066042041801000f240e508107600550241c0f41d15021150555944801142c8285062141180503000000c041090b41088a420f42003035106103d2485844c0160001707400299081c1c07440039400d611000d044c1010200340c41400307151944141101002402c041800d003d03001107800c0201110340e070f0160703132160803441400d550142031150030005441c00c000d03080c00b8207004820301c191000840d1071092962a080c0780320b0034045079405000785003142c0e55a00c1d404020451101200001d54a0724206015100c3c543c2c001c0c01c4031841403041c0c4c00c85040c00a025821144010541c8040c44081d4004003070042c0c101040e101112005206641c1c01003500c60111001d1003400807555010001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 726415242 1250 726413992 726414019
    0x60304050318211609020903100f0f020d0c0f11031605100c050403200d08130f150201050109151505090303030709030b160f0c05070b03040605090f0a0201090909020f 73
    0x110300c0c401354082070304100d190310303031500000e804901c14625655815440054003080c0d480e46900312240200e8109030010b1403100c106078020683e400360315020900d5031b9075072881c0d60003600180344400b1a42e0900d4010340210003107428658910a1804645003e040e880c083c1c0700b00082046200c503010207590051000b0610208060b101c1d4015010445926243e5200c0b1007103000b501d229885090002000d5141c404290307203582c3ca45911959580c461055030744008103100e40702c20300700001044c422141b00340c61184d0190080c21030b001a0425004941031000c041c20500c440700c08042651207503041c1305005001c10201362001d21034880010340500000c001c100025400110070070469008807581219039440c0e01c281400707020400c0d40f060100716845180d942c00740c861600354180600c01d00842d64003588490208040d07401c12901114800c0d01d031020000741e00d80512890032000c4c040030045c0001c0e41183c0c000381c0301011a019204000c0e540e000810107541d00c0790701c074440c0480054500703d40c9000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 726416492 1250 726415242 726415309
    0xe06060d11030a08042c0106052a06061e10210f1a0301020309121b06010e04020415030c29180405060d0f140708120301030b06060304050318 62
    0xd4843c0c1008462512289440b201803c81c0580e4604100c101480f01e681c00c0031001d8a542d0458000a0442082c04449890003070741d80055070500c10342b48001b89036a1078800200601744210303402c82120491802003400c09503e440e01d00192a1070181000c00018141540307040741b2a041404100c2c001e41801d08041080c40d003903211407132450f0b02c5030310f540c04446500149420307488145c4202445a00a0843c2540728800802402c510b4659581c48050308054007001880c1c00c03400c0c1c0154401d40a110180003c520f414880e802581b0020307044020032a00d5511207039166050380c4611b0002e048030600704000c640750700b90410f48115002c640d040d00d8480050105080405801450780260301d80b001050140c40d0002080000c1680003160201d52007181c5d8440b00003500104d51140f0740c1c4682e00c00030401034024029449007011440a40f0749070b43c51828074013000e00c0301414843c0074403410018440814008011107040c90711601030507002030f011401040341e40c5948185411100850400041440e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 726417742 1250 726416492 726416497
    0xc100f2918010e07081503010603081216050a030203061c0308040209010f0b2505240f0c070209150a08030a0306090c1e02101a130e06060d11030a08 65
    0x803041c0c940c020448003907035072407607519420b0051003856a403501c009880c40e885048843e5005d5540800c20b80e4040480340802c5c04c1d519039800449540c0c00c0860121496401c42d004180c3c407010741400c1c2e41d4440141070020389107100b203220600826800000168007030f116140d42c4d89031150725061000e1008500d0400070080070040d50102d110741600e0000280c481c000e0342c00501552900d8010a10300301081c42d8215906881038400c4460500101c1d0450102e43d052000c8091070200800c12404070804410482d492980148003030501c05010062210b407400d10015076401a6042c1d41116294445901115007007071000001c942c44104100e02050a4001002400f60305000f610240911130f03d50031503205840386d103080180040e0084030741d07080c807400d10009200e909505005480d0003982400080c3c0a58009144c6c6c45480c1918616894441c106041200a9072402840400400b0191010103885180c0a0a003500c03405a40c000c8609201d902d00300284200030080032280074040500e00340c1c9164 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 726418992 1250 726417742 726417821
    0x41b0c08131d04061506090b0c0f0708030a0912050316050f1c030605040516080414010504030e12150a050603030c1e06180d0f050409091103060601050c100f 69
    0x50504801e481c0561740d1003040026203003d81c807100112810600103900c6508034a1102c070300c91203030122000b100780c030501a0740301520380f413000765684800c6080050700d1004d003503000820a0302c83c80c01010200310003105841740782586001c91000003140c0e0400c240b070704045280501c0203020300401e0b00000340d001e5421560105507528180060303503980e4200802c64000700c0e040b03581c9042101d8240b44941c81545181c1c0d01602c5a05000f100754a0341080c01d00715241101c040b40450000800910300e441c0603111811402040e034014000211080c540005441015003040b43c481e40f150085000e9660603c00e580720302126608888070242200340f01042d1743c0005521011502510001c14400582c50302003c0e51459408000d00e103006c45000304030350808804e070542041203c184400b040e10300c0c45000d404505400f0700b03074404a8251050400d818010050840707810f10504018411010740c0200742039407155042e003c005964111551110090b010b07107110700c450a00e103425844403010b185002c10200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 726420242 1250 726418992 726419003
    0x11010f03110a0c0c090e190309170c041d0c0f0604080307080310080102030412050306010212030a05040b091b060d060f0b0a1412060409032309041b0c08131d04 70
    0x80f5a9515003140c1110170303180070006c094000c1c0041c1030504c050542e0b083c00c0980f1925114a645a072030041642d120344a40701c4c4034140e04a0110107080740342a00035001c0340b00302c10000c1590201001da107290f9032280f442c49240500d0b0851000036540da110b00c2990018941c010a03a1b503580400d140801855000b201c0c151000c1605410101d121501442075922483e0b1100030b8802d8290225000d480d070b504010510f0b41103220f08041040d08844050103980180340541010803c0d040c580740c02410224001c007020707030320380c0900a108104400441d2030b8030202426500540d5501c0140c00180103070000d0381040340d070302c91101000144001c102c0d00a10001c0441d81c0c60b4207210031040000d60043c4207002c00c40758184100004200b49140541c000303ca42032081c00e042403001c2c0c03810341d807440f2003c00d441040c803480408070f440c010a091a00800d160740720800c6000c1400c03030000b40050030301007203018040d000103404076680084010000300178000d8a244803840b1380d03060780428035a08604049404a46 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 726421492 1250 726420242 726420263
    0x5130213110d061716050105030c1306050901030e0a1707051204030807021518061b0d030204090605032a1c0c05100e0907050309030f030f0103030e0102070311010f03110a0c 76
    0x6200c0002c1410b03461a20001c03117448410f0b14040044525400181c044448110208004404da516114146000f0203060710340c981c4070800c20001404483c4441c0119134190450003505000464100b03205648a69001c3d266489481a061140c03510440440f10403c0c1c1d84005000710601126001625416201b12102c00300d0400310181c440003030140301d2000b40f141700e0600007400a403a080000d48070050404140400d9081420300c111325000010b040d942c0400c0d400034040c0144043c500800010340403e40040500c041100c881c040d12092420001000c0c1658108002d51a5140e8031074006448046076090500541e80c105a1003400c031a1213403d02c0ba1110401d0030381000c1c05440d01c41002c0400034400c1c45199901d04061f603003075100410600b00b50000b00148040e055410002e1409030303a10b014001c031a581580b501828000e03100c9200b03810f40d44000d00030000240703003490003003096900b1702e40f80040c41084c030310980243c03400026200c0841300c0441d203884402ea003c2160887e444c0961407012 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 726422742 1250 726421492 726421529
    0xe041415011b0b190606050c060a09060b03151008030a022503080a030c080a09020d0f020609120102070c1e060c15020406020c10030c020d0e0609121005090105130213110d06 76
    0x207d40348182d4080201e15084140042c2856185900c45c690725401001c001c5481014540040d040225402480c00428042000d02003800f0b041c01c4114040e01c0700500443c0352203005000690340340c030136848011000144810300d03100c910030661150300565106002d142c4a108610700580070b441c070403082d000020703580340020744102d0490180503002034010300144070001c0e042e12907c00311401068241c0c7c0000d0200031003000e54841e00584840711200d80300058892030140340c400005101036024441540000f0000c03404d140514000740e044890a0a004020380b509203001c0d10b200e00361509100b41c841c80428001202c90300407d40d846030420455612107400040402a4222241c06c4010300041c0d104c205035000751802007541c001c10300700080c14141440182c0d4002407000e80700228007201508416010002300085015240d003114022000340710724680000608005460303540068810741d49410100d00400e01544582030010314136502c1d039952820b00900d00c02400d028410800c101d0b9551a815 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 726423992 1250 726422742 726422747
    0x302010f110a121d03040311030c181302180604051f140402090d0516062604020117012c091c1e0e041415011b0b190606 53
    0x10400001c968842c2001600e03081225507000c030801a1105554680c4031400300840078481007100c100010040d80d41b00c0c1545070800104440050050090380400003041c90f66403115019403801d98400d0100c1041d54591042c070000018440f00070b9008228000400b40b250075200340c241c03080c001550244050707210711100e56001d00010f03021380081c1c18170403010301042400e10b0680c07000c494010005401d015200300001d03000360b1181702c00c45995104003542201c00400588000003414503042c50101c8404541007045111400d0036071103900c0c0040303c0020704680c06021007000b403100c4103003400c1c110341c0c440d00409503c020b200200c0036030b88205003104c025050485a0240309a0000024007840c2c2100d20543c500703456001082801e000c3e42c0c180040d074800140102d02c0c00c8011746d40e1040746214891041c0011078091006000c40180307050100802c1c1110790820615010302840e0203403081a034418030f0390450344e10704d000818a510703c1d0240080c034500b020a120000e15442030030460180d1300d0000703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 726425242 1250 726423992 726424001
    0x3020903390603070807080714130602210418180c0303030605120a0f0809060f0901090504020403030503040312021c0203061009030b0c0a2d1206121b05040507020a0302010f 76
    0x161300000b159100098405881031000c1034002d881801c001c0d995022421780c0041d10380008440c1400b03100d003440304200007a8100010801d180d0b80e905c07600c080b410b04041c24200d0f84940c0c000d41011900350b503801c1c59030b446913a103e01c142c1c843d9007410303901c0000c4515151040c440b4510050380064240340c1c000c101890b11070503190a280c810801820003202c01d6540315126081c800303054034204400c0c0008041c2d511a10020550081c2142d002984c2c1c84045001600d08402500210b0090b0b2040c00103000181c1c0100840703411541504222406070740e64030010700617119144000d2700c022000100204017902c02e40145000ea071080721402c411401c1d03400c0c122900d4501c0d11010b8040340400010626030101c140050145002038605184d040500312041000c000380030050607500746045811461044d8003140301101d0f071041d0f01080c4040c910707040d05210050807203030b0064280c4d0480a03681c0013401031401004c006020140c03060003d490700b140069200d8504440c250055402d2040d640503a413000e119 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 726426492 1250 726425242 726425251
    0x415120b011205041e0308010801060e1e06030a1b06080f0903070f11030d080106120e030405011b06051501120219030902060c0f071e1503020903390603 67
    0x5820142d031a071100c40c54080c20700548240c460010743d918400020142040301d01229000751620411549440c481350700b1103031140e000b038480601d03110a000440c2d56524030f400d846c1c000c0704403055568440c2c40020341401c07a400700040404511610700d840d0303a40550461401c0b92400e0f100d440d07090396900212b0150500440f04030300e07a90000c012800020310800d0b03000850b6070151424050b07841288010a00e07010152480c400415412001000083c2d4001f00d0043c201c001c40000740900e8032030110441c2d0b80d0049009940c14001182e400741290021480c48020071500001c0a10080c24410514409000741151060006944526082d0f64506500031546480c1c0700c9078900440010b442000c60040000340801c07a800780d410000d100c00c1c0042003080b000107001e00d10280859514198086c1c00b8080d400c580c0144a01c04032400b04440040130043c440207024070300740541e40d48040e0000a080c03600ea00301780c1e4040303072010410075146400d00b0180c541091092511101018006003084000d000454 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 726427742 1250 726426492 726426497
    0x2153306040501050f16050105060909150703110f04150e01021f0f0618050a0f140c03060a03050607080924040f02030f030c0f070e010b2205060415120b01 68
    0x410480d440b42d0002c00e4107a200101440c201800c015242a40c0003034080c096847c0e80d111782c14412680b034034044281c2c0100c542c40013441b0081c40040e2444000c000200000140366172451031840c01440700089403445002e0907400780e0b03034584402002103c0d040604950001800ca1001c0b06200c0d4000504400d107902000340001c04070031300b41149009841849116002240c44400000b0a41060f029010891200300c0c004035181c5803050b44441160b151700000e449560400d5124550705c0402e403d03860f0042050380781c040c2d4070f0f9284404500194100d0344020040e1041c0c44c01c000b8002d82c0440024041e0010078180c91840c26070100c1d17409140b035134a2500c11007505070000301d40080c85840c6d011a81d54800b6040e204142280781d206411500301e4000300c1103d4012642c000c0155005000f03100240000b106105c1d01541043c480d06064051191540300010b05070105903058100141454000d2100601d91171395140c40f0600b202100200c056048041480420b06400c000d0440c0103079403405106a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 726428992 1250 726427742 726427747
    0x2030301090209031e0c032803030f141609050303040303120c0e0a0902040e06090103050c0607030c0b10092915070204181703040305031602153306 65
    0x22580000f9403001e00342030352600c00c42c0080c464401c1a0450741060704807103000b400c4808404014181407094840d07a00440300703000d00712208000a0103e120250381c0c1c25190000b40a010000f141e00204150200c19084100003010041d1100c1e0070744040000715602d40d10501315130741e1501850350340d0146000c0100407480913000c801c1003903100d50000d000380460385040000c284034030f00840c8111025400c480540c54000a05100030001c407803100e1341129099032040e07055899501e0769611024802c054a205900008001041c540f14091510000d900022142c038a4101030003403903450041c81c85180d06550070801400340001c3d44c0580c5100080003400f4040d08000d445042280c8a0141c03003002080716020312074080540c5603072058410905290552560f01c15040c2441c8070450041140751007404810000c000010b07900c2010382e50020280384220034a01d8203404286e007840c0c418545413052950100070003440687c00034a50001c16818882c541166091384c000d000712910003100c03141c004c11304 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 726430242 1250 726428992 726428999
    0x10212181c03050414060909072708072601060f0e0c0a020a02100c061509060e0709060c06020c100504060f09030219240c0e0a12150f091a0601050a02030301 69
    0x2401c440707000c0c405c0148000e140c425004002180351005032640c0d0005a0340404040d151000301d644088038075032080c010941680740040c02c0b40e0f1035019010b000420b0205400400607081c0e080703405078001c0d0a11009200c0c0343d80b074000050100e02d8510540400308003080105141403960b8084a0700e036819a80940b540c492690280050062220780c4001006954240e00c1c001c62000d01c0b1300c10b40043d6054a449642e444e1019150980c2d1403a000031003591845814800120b400500140c03c40300e15040c103d001400034106100240100c100c2c045007802401881f8641c000c84e0380c003061040b44190820061500d07141e840804031144010005e0150340110221b94040d81da080300003a095114005565111010045595842d080d490b40f10711070390345030703956042c2d02500100c40103c9001d06640b152082441c00d28001100c801e2000003808400003145507402440030b0746c00c03618010300c100f40184410b40a84ca004101090302103548400a1030b58000f055a81d0b120308100d078a60102c3c1d0707004504507400e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 726431492 1250 726430242 726430259
    0x2101230a0b060c0d0e010e0a080f1213060c02060f030f0406060902090d0212012304121e030c03060803041d010e0103020d02090a0618021c09031409010212181c030504 73
    0x4d00d0b144150601c404403000c02019620f5985808c050007290018004c6a1000c0e05507510741101291400e12542041c45140e0140016080a20858061b480c000c2405c0400c1e0001c03c0303940c03007a01031000341d01000200b0040e14511128806000303e104000c1080321a946a2950040740030f4285403d03803010190340c2901c0903141c1305004105011034840002201c1540e80c0150840c40700003040010060344540410090244101c0d0010000511382018000c140560283d0624442e85d1501c1a040c140d403450200800c038070a5020b2009003070b22204a990f200c2c1c482400b8810752442d04d0505242d152480004500f4003444c01c2d400d4100c9038082d1050048000315070030003400740002484018815550f00300010491814100c0001c1280c05101c01030762803815001c88804928030b000c0490803241494952000030f0b5014a1100790380000c05881900c400340040100c1c24428480c907180c0f034650001c5071001c00d11810090340740403076008540d104603000702603540c1000c802e20b0380340283c0890b00c01e20080100c07c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 726432742 1250 726431492 726431507
    0xf062c1504020f030106020705090c0310060f03091407050a171209030f1005040201030b03010903020a151404060609051003030e220c09080c0d022101230a0b060c0d 72
    0x20000340054205210f030482807103640c00c00da00030001640104010400b504264003002d410000621403685185802c070703101c003170103442881076408100c0d070300c164240d400b4469800f4100c1c0641c405001d2401d0301c11a4000350f650034903402000d220b00030799080000d6a048000e22005070f8004100501540480c4101d540740740e4100d1003460303805000b1130001c5404004140181300c100c0840d85030014850401e07000042c115030140032040e010b03a16010442003c80c0c1c000a0040f44641c1c029601042060702e12003800140c04040b09034460b07500d80130700b800304121003a0451000d480501908010690300c81803c100490f07468030015001c115051254271090800001c80341c42e01c1301100543c11340a40c0c0a01d00803c648501c1102c40000305403200901c002c500074010a0712201088602c0100c10000740c00041e00d80301700e2940b1200009482d8081000340000390000c03125491074200810408060401043c0015011111034005514240b400c050341e1809c00d0650f010703a40380400400601c9800d080c11395260 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 726433992 1250 726432742 726432781
    0x2090717100812090109050a0e1e04020913060b10080402120606150703140f030a050a110f1303020d2301020721020c06030c0a1d0303090d0f060f062c 66
    0x6c10715004940f07a21601001002400340006107035041c6400058600034403c1e1456142440360791005201c0942e0340c4000b0960041c0c0440e901d02d050b059a850441e000340200c80c441c1d500056521000013207035400840c1c46220344d009980d140e0800405400240d2140401c40c0d1003903000d00682182ca148002c1440035240042c0310381081c0143c2d0309011114000740d001101140010100002005040383c841c0c001d03250807001010043c42803c0141c041c001450181c850b207281c00304000b09009118440c0112810700440d0007400c6120044601d0030304000d014003000d4080000c8802c05100308070040305100301c0d108240c003c00c2000c281c031a503400300c015005032509600c04512460070351205550f94000294013030002007004a5580d0490600607081450b061301e102440b4209440950250301c022045880f00c2d00100c50b8040040d20385d103002104a031900030050b203002e1904e8060104c0060719889031003030703070951240652403841e40c22882e103040034446021100030004501041d010400540031001d81d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 726435242 1250 726433992 726433997
    0xc0e03240a09051b01031b02100e1c020d021c020606060f130b0a02070f050901090b0105070501020a08180c010c140307060911100908030313030507020907171008120901 74
    0x11841a103c991030100e40b401440d8041d01c50b414039000340e60b010f00c120450480c0c8201c00007041d11000c60043d403900400c1202816403a1078000c40701c8900011300c4244842c05c8540b03a001000d1032203e1f802540c41040036103100c0584945240c58184c580e0034480078801a4499008005503510201400141c0d000780500d550b940c074052203403801782800c041000f0040c0203035580e4a034842c507814000915000d400e034049401d81810f50001e00c11030701c07036000a0741540d0711090081031043d003a50040b6080c0c442d00d40c001d007140d480030030070304400c40d032064441e4004c1d440d1420441c120031b0011221070f101e030004e41300036000c030741d0000780346001901c80c0c000c01d20940482ca050304e00344070b000e0300c4103016a20900300454000508a85001305454000b003c80741130003643c5070038034205060401c0c0380c1e682e100c09400e50740b1010404001d90201171041c1d0407a034080b0b03400351190807242032010010b03045140146c885940107540e08000740c800c403c00d0b05031500704c80d100d2004110300d03926258850030541c800043d00e0704 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 726436492 1250 726435242 726435251
    0x30a0c14072103090b0412030501060e0604030807050304050a060c060606030b1806150a080109360606030215030a050c09010e040e030f030907080606180406020d09150c0e03240a 78
    0x72a0014103290700c00e0707000d0101c947e9002c401035001801c84038141c0200d4240800c03280001103a403143c00503603040da6802014180e40390403508100d4650301441d44a07641c80f101290300816150390101d0111038061140c01c043c40b400d5217440342075050760714000e4402d0300181c01005482c200301c19403076843c0d040b00d8040d010040d8585414001d4110398480c188040204e80c880004000d142298450202c80c1000224508840600d20403d5150710010300c5542a6000c4090314104c184443c9074402c0008550080c440241c03c0000321010040c0d8100b140c00c5130480d4580380c0000c0c58414880304032184440c0c16503c007a001c6010004000003420040701640103031209100f941d00c0c211000e001580264800c0c00101401c41c900ba68180c5001402002c00307000d186c1c000420701c1030035201c088142d0080c0d448400540c40314070784e5014000402048401806d0512103c00f5003091030469884805920025581e14800c400c11206055891600014907079560020201e0750760105c0100041d190400358a0f0350206 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 726437742 1250 726436492 726436511
    0x103050606030c07020411030a0b09090c1c1401090f0b06180c0706060504110c0d02070e0714090a030c0503070e04051b06131d0105030a030905120a0503030a0c14072103 74
    0x720349030009c80d40540c0107681c07600d55032807070b01c2c201d80034951000c01c0400801c10400d4401c08030f1801541070505560100d0017611690401c840f0510300c5480e000d440c0001c0001c1c5545040000203643c444100380c0d03e44d440c1d0780201d201c6051683c02c02c502c8011000c000c034031545609619407403070ba20011069600a0b503d010100780c0b07589900035004e240c15024402c0d6218008540124244440190140709540c4036010030440352048a0340e4035841030440c00c05143e502500c00400fa114801c6040c0350b40d120400c00e00200810422030340706825514242c0c11aa45961100b00b00f000f504020783c1c018010364442d070039504c03404c11400e1503040040000f0f400282402100c0420342c0c03013502940c010119075248818102a2030395428040e0380100740c00c600070886d0085a86000d010100c6074011140504521036134031143c51820065a0469030f404012a9540d00d800d85405008182c00442e0100003011108000c0d4100f0565095401640d04602c0528800c1494041e1100b4642006990400d00d600c840858 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 726438848 1106 726437742 726437771
    0x22101060e0402070606152f0a060b1c0501020301140405041a04022205060f04021e2805030702100e121b07080f07050103050606030c070204 62
    0x10382c4c0340001d04107400074044e1034200300145890008100d403540c0d4020440c01004244200b0012503014421030350401d0a1001e41750a0940e0006175000003240d003e0b0310510702100018403a51220030711110111448005580c1500c490b540400100804003c510f0301c40e90008040b201040310340342640c3c80c6015221141d0001c0c9119210500250031919420091140c10345c100c0802d0a02d101882c4a15004d05811030741c840c0512542c140460040c14540262240d00070b01800e00280174034800001000c6400481d040f110320b401c0302e900d44c03041d80c00225502c1c16005180d66116039a00c3c10040180c5448030b101701e078000c2d0303502e00482c800d01580041048400b888032640010b688019112820140c1d82d441c04c4860f0306030080100014800c8000980c1070001c0c1802d00070741d4002961240150304640b41220030380d0304008104001a07103c06080b00802c00d031840100002801014190748 = true := by decide +kernel

theorem cover : BRFrame.Cov 726258992 726438848 := by
  have h0 := BRFrame.cov_init 726258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 726258992 ≤ n) (h2 : n < 726438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
