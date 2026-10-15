-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4986
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:22:20.257982+00:00
-- url     : https://prove2.me/submissions/375c77ed-fcd9-4aae-a86f-13b36bf748ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 896582733 ≤ n < 896762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 896583983 1250 896582733 896582767
    0x1a0a061d0601050f0316120e0a142e05340516150b010201020a05221502030408011a100c0303060e091515031905070305011e0c0311 58
    0x3505040542c01c1041309480441207801c03c54012884070980c500d1810040d401c0007203c0540078280c9001d21120b082007146560300c0429660007441101c42d9000c0b2046500706018900605000024a81c0c0a800104c0328100d04042c035880c00401c3c500d00000700c4d00c00b80c410489954601401204270010307085501001c0000c400b01540402444010427802c52106031201e01803084500c04d50604c0268615140c55404841108011906680c41000f0000e09160801d00381d40300b00065005100003221481c8075048905645d9011031851031004070b8441c551500400900103485491000700090f100046003051150244036240360805008640b01980e2031040d645c141090340a8200403030800d944015003962144115081d00040c1c01c00703091003584071010044241c210382c100700310b1401002640d000a881c5c424110180045000404201041050500c8104e00450b00140200003c04010100e405041d40d00743c3c540044503d030a02c2500406c0c0640301e403800d080740d220b100a041103030300c6800b07403240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 896585233 1250 896583983 896583991
    0x100503010501060e2d010f0c1208093702030a06020c03030414120403030c08090a080d0210050f180a1202030304110d0c0b091212180904050a020f0409020303071a0a061d 74
    0x80780c0c240f80d50010400b203102751264400386d5582c02c0141d150007100c0f01d040c503902031002060100109801c411400700c0440d010080e0307021965400c0340c0c2c441403000a140c6025560b005100e01e00105110030000404009140329600404910400c2c481001300c80740c644001034a494040d2030300340401e201091041c40b00c2000c0320b200e040c0440c580552000010303900485580310140780d41c0314180301c60300d851303052111283c4075601d01414032140c140b80030070b040316600041040410044002c8020741010701006134240a0713410a82e400d004903075402c0020340b207030b104503010342e101c03544038030f0880003800c1c1185494481500b01e0341c0031011078103298a0b9240355010720f040550021000039900f0ba0280180a46107a01c0034a140f01c5030b807000300e6141000040b198503c03003407180c1808010080421000324241c82c5499040320310b03544a00321074000800428010b400a5014800420700204000540b40b901c580041301c085111581e45e038810b44c610580b0f03410b00502c1215252903609180040100d00c0040e00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 896586483 1250 896585233 896585237
    0x3070e0109020730110d0903111c0605010f0b03190f0b030d110105180a0f03031e050411030c060d0b15030c04140d030e0108100503010501060e2d010f 66
    0x210003802c410011107400a441c04500d604001903841c0129001002034078290f0800000d07010031007000030090070166440c800a007500e80300140d0127250b60b072110b0720b0036501110b0580c0c42020050506013603009241c240295002007070008008614010044241c3c1d03c521200400c4480410150070450301030004107541a041036204c1c2d10245c003603501809014480c0c4007030355584000d0300301030303181d0b44c25202e0182c06105030004103a00c41800b1078011480351045a00f1a40b0150400c0c00307403030220010a5003000001d142c500942c0c111080d201d143e0000e6000740d00810ba80011800080201500e41408210b0664440810007200c0850602038100410a8034000d00388001c42440c03c440302a41e500480300c8101c030b507200140070700030796540d80d00b0321aa514064446017112a929500507140880c902d00c8603040c40008400074280100b6510300b4005440094001e00195a59890150407100440c200e41d00c980108140401c1100d41c1c0501c101f000c400101805d2802605000152501d584146135181 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 896587733 1250 896586483 896586503
    0x32c0a0203070b2101050102120a090b07061b030c081518070305090609030903070306021606060e0a06170601060f1107030b190516030b0d06060801061403070e01090207 74
    0x409039500340545002070016408159803030f4134821501020444404600ba040c155001c010310041c4d81c001650b040c0c10300b01c003003280c0da14441c1990603118500b281d8441c580000c00003440c00200801900001e01e40c00b400103400007030a10242007901a110a80007945c00180c41030002040300b5100703680c1c0e940480010300759206c20700404150b584508011070f003a80100703451b682442080c0504004465020b2480d138060f40c00e0109910000740c0320201880b019000c160085444101004070001d626041035025008000490342c1d402c20071106a41220b10009461a088000481c0d90300050554840f0203000d002c3c081503824040d060361100140c0414800300319030302d80c0d0755400e0b400421039200514041c581007105481c2c45410714150320744071040010140d05110520030840303000305255001d080641008602078094001207604800c1c60700018200b44d0910b40c00003111441075114100b543c43c0340f48042d40e0300d1640c40c245540c1c1c0349d0714443c00140c1c40c00007004000c0900ba9602034041c0610491983d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 896588983 1250 896587733 896587753
    0xe2b03060506030a02040f0501050301230114030412021002160210022103040b0112081218070b0306040f02130905130221010b0a0821130e16032c 64
    0x80b159081151240c1aa43e8005014000300b41d030429000c00070802417822614641c140044150185200b046c101d028058481815807aa030144450b0301e044150040c1c02916454170b42400320140e00c800080c1030150040d1018110340c0c01c01c40c000c541c800d98500c0c01201d003030bc00c158244070403031a1820b00c0100314060280303200c0084002c1a614a58014624080c0f0340ba8245400c00310008401a88640c071440951440e03400003d210030f069071015880b40e40358003c1e42d944c0400b443d001c0034901d01044400d01807444041090024800914003652003078074100410540402c0344000c030320550080d50002141807104000036030f9140c100c83d0740403120041d00c0b91342c00056408070b07001d200d075052100030310300145070000111002482038416990046076170340002c41c902500c0d41c2d107611150313003002c0030b00c0da210340341464032403d220444d0310002d98072000342000d50b9561907200c100581501c41c019650f040c00c9140700c0e8a4400d005058807900d00d0b040398002c0c496241c1310015138900e54800e0942c5409500101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 896590233 1250 896588983 896588989
    0x11191502091207030c06050a1421070203072a15023306010c02060a050d18060c120e070e220b100806101e030606180e2b030605 56
    0x840d007090860b0000d101d02030440c60300300010040ca0f08030004101007030143c1c0b0b0390507a10910b80001441620110766840c001d01c278134008e206664014a00ca21105c80b4280030f011039000008200c0c2c113000d588242030380803d1681034440c1250078034240640c0a011a4144040c0c0080e40d1100030240351030040316861245041d01101ca0f11041e0048102c10b03440c00b0480c01501d2800c25030307951001e02440c05402c44280360380001c0c840e0140020100410002003a5400038049507446510003000380c000d008003104151914a024080091041001824000008200184170b01980381c45407140c4007d4450107041010043c184080141000411421984541005007034518882c08190103010f4074505842e0400817911102000e611480b22980550100042c8044403008035081c0d40d031100c1e0314100e0007804840c0210742811a0009071143e1701d491030000e410700020141294484c0c14050500c0101559152941c480d01003041110002e80b1451003030800180921910000c2001c0741000102a5161f9000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 896591483 1250 896590233 896590249
    0x29180159010c0e090603072702031812031012170d0b0307060c02012c03190203010c0302121f090c022d491119150209 52
    0x2824100d955903200c000105511044408a00f282a10305200d0350504401281da80c0d170310f911640e0304c4400880000040000c04501142c059040ea400c15520f904098180c2c4c080824003c118541c00d00c2503a81c0d4240140200064a1080405512030914646413080d000541c0c02000300881d403070079112074200d0b5034018803400742904103544030300001ca0382e80c004103140c80d000b41034100c1410b00c03800d01c100400503a8820152000c124000d942d4000c1d0000c91000420303080480d08240f9814000c043e845086002c0c0690f4032203d06008034001c1c8021301c10300070160101d02c00c408203008107a0000d000a2030407280c0c112030003141500e0b0700e086a012580c801003502100c083e144044010b800c00090240001a4801c0c440c0400300007aa8610802180c61a03041c1d4400d55200e00b1700400c0305507015800303e041c81c10782c0d031101904020f02e01044890040c0b41000d10640c1560150041441211702c400b2020000a0030303407161706001d0300796485400301e440b00c00310340100302c48400110381c007004000550385034900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 896592733 1250 896591483 896591651
    0xc0102040e13050d05030c04090e1e0a05061f210c08070602060f0708010e0a0b040614040f0c09091e06060906080f090307291801 57
    0x2d80540c07640054604142400c000f0500380302007040500038000b450b030a20f000c5408503a031908001400c2950300d82058140901c8504803081c1c200e503408103404280000c503d80c1700340c80c840c1003a914a980c0c0c2508251414443c080034800e0740180080610115214842900780c900c041f005525205105a0b10b11441484c1600700031015004003104002c61501088140c2d003140d000e0080044600e01444020000541481a18030152184001c01c192a030254080c1051347c102402c144205601d07100c007071452070020b1512500481c90f041c009080131000c2d100f5202200c8190340c030b031601285040c02d540041c00d10468002c440c0003a4070040300301103640d8400c1e41c00070402d42c0c42c1da0400e0b5140010291110b1401001c2100c1e2106050800c024800088210b0315980ea001d200d0705240c1808000300014040891641c915640d080010f001003190506058110000c40e00002d1003a0007180d04c0401201c2170450800c070402d2401c0c1c43c88905200040315441c00300c490084600110b91130414040c01620741c2003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 896593983 1250 896592733 896592751
    0x1503180b010305100b06090927061015021b3d02010c0924050705010c020f010e16181401180c03060806180106120309140f06030c0c0102040e 62
    0x11310440c819480c40e0217041000c034030445c2c48074145415800812164107000b0b013080c0e07902e1600703201c40003503d09401c0d001e504a29400e040b50035038034101e858006040400c3c092071034039441094500305460300c0090040e00c0054401d50002404841c1028019031007003c2071001c1012038400c201e803448012103a8003003150303810303507101c2c00081002000c040c2c02c503440c442001c4100002003c0074040c20089204020395041766120700d10b9400d4000f04225154081e51314014415401c001104030000d03800980e0307d1280002c48000c01000d000302c4502981c03407c04a0820b9420b648200e0708000d80c0210306203c1c182e20302c0c140700104014050401240e000a400d0304407412a40041021026a035071611a5902c0c100c000d0500f002281d040c500c01650f9500028490b090300547c075009885000c0c4203410080040c0501c0b00740500c2154603140160040c3c589000d0011a845602d042d0a880e2405100303016140c0409090396140d500c0e400a402ca09621859075010259000c1000003000400c0407901440ba076100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 896595233 1250 896593983 896593993
    0x21c0203060406090204050a0b0903010908190906180b1303050105040b041a0f1504140709170105010b030606070c0f03060b03010506040b01124a071503180b010305 72
    0x1c6041100300c2c0c02c40d81203d019a80f0600c03007480317643c541c035000105840c40d103000103403203040d520002070140400c400000c0181d42c003c109440078141c0403415a05d44a01d43d240c1389012600c902c1c2c02c540000088501c4203140500b840200401e0720840c00a04901984a00403801e0384d8880e2100c5003516400d4030115085210b10040105011040c10000c012071802000640c990921020107000e46601404a410644250201c40c82c00e64039a44000501c0c03080704800342c803900c0d01031809820b01002d442030704540d200442092046200601c15681642c0c50481c01c5400c40c0ca94009000554003d0b810481c2e1190b0120320200300300b1034001009004502c01d03800031503091605414103007940d40180043d8000e609140040ea01070f03800002d0356080054504001880c1000422540ca9001c88e01d07904100b001c1c0100000250300b2225410f0195030b500b0041c6400440d8003052540d642c9181c107206030450321040410003561584260480d0f0020315180d14414903400c0c00340c80e0f00310032920a030700c111105e40c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 896596483 1250 896595233 896595241
    0x3090308070515070c020303030402090613060f05040b0303070c120516090c030b030a20060d1806050108060f0a0c09211407060e1017090309010e06070201050706050604021c0203 78
    0x203c8030a2070740b002c21882c1100400348554042507683c0000782000b40720303210f42d0380000c0607611411002c1040d1a10f6140034002c0b0350b03480c00d107040c0c0c00c0120f02606000b207082c8840c41541d400d0005c100c844056009601030001440c00138030b45800c0c03081300cdc0d003200d040c008c0154816401281d20204c1c3c01401034080000340759840700a000c0d045400482d44640250840064540414800c07481c441140348503501002c400b401002c00100c3c10300c200c6140381d40d000c0c0f40106d0408070160644400e6003c40c0300340001c2205989800b45141d50f03600c1140c8400c403103190f4034005481100da6410004080585040a140c1c00c4e8840c0c03030600d55004030325400c0d190103110403d85020b02154250b203068060500026020031824000010003200064401c14041c1c01d503800d0119429114900080340c191a0041200e980e007800c030701c15922035000c0e40c29503000440083c540500ca00d8048201c900d0303103034144c560916182691b52808080c001c01018207900a50910100140f449050912041581d42c518010390742d244c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 896597733 1250 896596483 896596513
    0x50a022a190b0703090303060b070804033c1a0103050c0a062f030c061801050901020307050306210d050a020f121b1011040303020c041b0c030903080705 67
    0x7000000303036446034680d40e0706400418040100740c0d0b048085071070045200b450034142900038042039442190150800618241400951009001170301d2043e10203146c0c4030710103100a40c01c401c8038000210245000c4032011048410240950080780c0705000055041ca034010f0b8200880710240e00550701d03a00400000302d0103240c041950409080513040445d069128031941884001030115008404c528580c84804c0100b03040003990a500314000484205d4a802002403452035294419115036600340701c01b05d910817406009413446280d082e5509030a5940f20400c00c086203501501880317040d04443c0070403508039000d00006140c044192a180d40ea505031080080c41c04920211940d0b4a0708611200c083e0140a1000c0f206010b1007825044424078045001d0b80c1060718903070411807014600408000e2a03084030b0090402c8a010780c090300d10082c071480030310054520300c40d0140c3c1d05206004800e103c50340600741618034103000746407001e129501d80d41e42038031951103d0026109640003800420084d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 896598983 1250 896597733 896597743
    0x151701090203150301062603120a020a09092f07051225020f060705030409060f0e060d0c030b090c15091906080403120b030a15050c040810050a022a 65
    0x3250680003044a80d140c0702070804a1350481103501c0048000d1f00780c80b003c0c12801c005450907010b0140480b4110b08207813983c04005d501101c01c000c08190418000100a40c140c86401d4842e84491130341140c0341c0703800d12104140681c4c01100307190090140b110001007074041000102d5800403c0805076180b031050741103105240c800e103070417460140a10918005071900008409612030642d40035880d40041e107441030031400303541c00c1031010f68079105002410901182010044507540381e0003059036102c285c00d004141c0e14022025128011043c006c10004110309001c540c03028145003541d080c80c49010000d5196100d51100c0c040d409004140e2100610f000e140307010303041c14000b007000001803a1060142c100b8100070005401d1243e000078072001da040d01d81154038030000081c1660300c3c0360a01c0c907194154210b0030262001103440c01c40040c2600070024200d405440d41c01e0002d00081004501d11800382c0307802400610000c1c0c0a01004032005040c2211401600102e51f00100350302003000158900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 896600233 1250 896598983 896599021
    0x60509030903070e06010c0f0b07030c1e0e0f030d0c11010e15030403090b030103050a03090b130b0d11121e070c02010e0f0a080309010809010e0601151701090203 71
    0xa820400c4811a0340da0000b400d2000c4446104c4443e40300e5440b000180e541c9100e45030094140d15a44010300b08000000605505c00c8a0b240c03001c025100455500303c90b941c0004103601003002c03c000c2000131040c0680307901c030922100101140103003001a00400e05188107c000d01001c10340310b400c00b02c01c021040b880b1b2504103d007031030320054488005000881003814103501e4685110000085000d15115a01490140500036489540d9581d00e2510b50756500c41b08205400080c03502402042480703982c3d0444020720b51701c3c40300d664803e090207010781c3c1c154400f10030101642d070b84983c03004100c060030003e040c200c01e09100c2c2000620301401240b44521903805050308220781c04c006c024000f500007545005007034085c6003000c542103588010482c40b1411004607a0f02c1503210100049a9030008020325110400380e0b00c4d48441e44412004e00d098402c1d007d074000d4a900000010311004503c041800254400e925007007418108455002170308880c20b80210100940000401020104211800e040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 896601483 1250 896600233 896600251
    0x201090b0304030206040b040f240b010206040203031b07241d01050711010507050a210c020603181f0f0c1e03320103020a05010503010f051003020c0a030c0605 70
    0x1d9850a43c1c1c1c0203443d901300a00003000403014201240c18000112010707560740e980078040312036800c89201001140103010314003031300301e60a00b405040d855102183c01c03400bc55001c0c00540c14104007030555141b80c0440c4410b004684505000003e6518880c01d1302080c40c3c00011160341c00001201008200c0b451180c0100c8040c0011140b081e0785983c044102ca0b2040c0c0c0025071480035032123420040381c0390b100c0c50002502d03903c41c505480f1b0501101c190141d4444001c91006009600d1254058551a0402d00080c2d44043c00b0720015910b42450441c1d0616403c5100c00e407030b5103080c000d11064290380140310381d481e06a134031190400a004584a04440798000d070510b00443c0a804500341000c14907205000105038442c0f209100c070390100c4050780f003014100803000100703a80c55440c5080d8460248002d80c810701d81604005181d5001c0c02c11a41610754881c00f00044c11708040500584c0042409032604055003008030034071016090101c9030103d486580ca51003820700508116054841c041c0041c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 896602733 1250 896601483 896601487
    0x10509030a0801050d020a12030e030c0109030302060a05090a0b090304030c06140724020408060429130f020a060e0a06112802030d110d0c0201080f0a0609180201090b 73
    0x246942c1c0011089045610494401c1c80a402d1440410007240b1250311900c205040040c1010415070450000b02e407202d815004c4400c00c0121000456680c04140f04c090050380102c000305070504941d401050340101ca4a080f07400d50035903940e982202420441318032059800c045420700070000750a5480000f46601e160243d147c0d503420380c0746543c0d4803910348010003904010103405540a8502100541454104411500c4599581d8219141c84084a08548804004400c003000c09064000c2c1159102e40131884000f035603030300c5e8200c191111640015681a10751044002c01070751030100c50310213446980d613405451003e80d414410441340355000320f002e0003101d01ca03245504c2c500041c6603600c190030418012503241451250800c040031500d010b90503010314204890305513004001d4070307268491502111a104413880b0106ca9081401000034001003d10000c112000000408250041400b03100020340303c0e030b5200450200c1d50405661a0f10302c0c24000c070303d07040d581c104140000901098036194 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 896603983 1250 896602733 896602747
    0x507060e2d16150807020c04110702090a060b0f0a11030a0908240a0b010504050d0c06091a090103020d0b0306010305010b01090b0c210c06480d0b03010614010201050903 74
    0xb482d1451504403042003040384130000c4c800324403c0004010001c4042d004214007655a100001c0b564056441a80109a1540803800e111107511603402183e000c3d0382100c0c1000c2003200f4807000c1d42d2100c01e28100b0042c0d064949035a03c07805200074810186241ca480540e6031424100508044420f0020740d803002041811000022480c0e802c40e80c80b01e42c1d010700050566a020069590340681d40180d500240c40000f01c8042001e1003200e18103980494440007141540c811481c0c01510707035042011481e100a01c0b84800e01e5020390042d0080152418000c10848030714000310f441c200f03090340301707581c42da454040c500d03002c1d600022080c0141900d40380300c170b2402414524040d03072105505c0c2030011201d62480b41051101c4001e060b40d41d1000803c040d5140d40c1003901c6980c10001481c200810401c0c104d2001c0c001c50000701c1300d0270b250b581000700703041ca00080b440308400071070b04a4429602c001d5117600c125100b9907028030410002e40807070307080d150f03074192110002400c5990040c000171680d40104090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 896605233 1250 896603983 896603999
    0x5070e0907030c2111040920250c030212072105060f04032601150e0f0409030909020708070b0a05060a12030207090203070f0e0405070507060e2d16 65
    0xe9100d00a00204141c10132030b4400c81d00200019001e503c1d801d100841e000c42d0303090b5a504240e0003101180080d01c20f81901c88038455240c8039080485200c00000d4218a040341e002030f075140704d20b42c01000c03a851403590700c1d000304603404120341303003095075811860b000c1c0300d20b120f102001071708004100724111007061305030b5880341e86200c05454140c0074280c0c80005020540b141c0d050b500023107940c001c006c981c1c5004840c1c84001d010300b800f40401d180c0c0303d1207010604500c1100b8016880800621780c9043d8071202c03080c000200807042050f410828010740c0402d22505900080100740e105a0a10381c3c0d842c018140801c061a002d0002c0c04100e00300303810302000d0f41d07031740725844296011081140315158641ca400da140c029140d0040c1001800071040195070b5030001c3e01c11050035140e4840c400e0102d1907108210884408a03041c0020540034040c041c04030f2100c0e070181103244440411206040340a200d810288501c240c0410750b00b2403140d8050408c48020701002303d40e0840a00c4200c1d68500300380007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 896606483 1250 896605233 896605247
    0x19030314010b0f091e03030c1b1801141f020a1703010f051c0f030305090d111b0301021e0307120c05030604050618010e1f0803070f08070605070e0907030c 68
    0x80c507100c1c0b405ca009421141440136104084020001c0c21a9a80c2554026041c0c070349942040211041481506c00545801c048661405520f044000720403a40e0901c2140c0350080742c1e009003c1d420115814525484041c00035880424000c5900140a82c09940c9040003403400950380a0f07107003e8041c00100308100c40c071900501600c5048548402804040d4014142705442c00000b074000444500000309041e0550700031801107032160103540051010394015110000070600340a4140d000b01c0b503c0024441c40a55444030784030040015280064594840c4118000c034032200c0311243c400014415525041100310340c2c0d400c20070b0002d000d40007010340090f00c64000100f64900860302c1e0320000310741c2e43d1008141103c1c442600300004a03540c4515018a800c5400c9680054450106119070a044d440b11031417030032203c1200c01540b50585171f030749080b8a100382c10021500d00c41d0502200000903403600038039100340041c0d5039001c0307403801c1c0c030040145001000c1d05520a05140119a40c144c03548855 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 896607733 1250 896606483 896606497
    0xd050301090c09151b15050106260a0b03120720030f03030f0c1c060602010e030723010e060112060605060f090904020609100806030610052119030314010b0f 69
    0x501085548200e40c2c17a800503e09940d008000c6002150b155000310104d902c000d060b41c8690340d134881e001520b02600c0d00c81c40d00c008540e0012201e05c0c400105000183e4014440c040c1000c3e050320798580b042e954034000380c0c2008030704641c03a03a8100c03140c102100b809210036040d200102e000740340c0d00c83e4801c40a5100d1001601000c5a0402c8000196080d032000d01103650200307165408030141281301c040c2074014a401e026880065081c151180054200001a02c80107034204962082844184a801d843c00c01410204d00140d52901c41170541117070700f4030069000f084402800b0701d415070f03640b41180465109401481c410003042c000e4480c80c0c94201c00f500c01e280c07000d80d10890213071102d00002d1250300032980e82e5503118445840d07a03002d090303001803524020603080d000c403025034503020004106001c5d10300495070000203684884198141203000b000040e6043c0b010780d07180481d4040c80103410b140588094000c607460310324801d207049070521184d0040500406840c03d200c188400c0344450320620f1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 896608983 1250 896607733 896607737
    0x241503060307030c060215010b0301050307180b0a0e1506040b160321022505030906070f0507060e03160e060f0102010f061d010905072c030d050301090c0915 69
    0x12001420a40382081070101031500301c00d140001c00e6a50400960314040004c4900c21104d0700400090901c1d4014280ea05844004000c0d0500700d0800c00c0e1140101d40307401ca6001d4a540311680746040341c81e00c80440026008031901da06642c900641400ea0080c070808415006910400080202605440949541f00c2c1c0d001042e10518005040861302c03105500c01d10b04401901c00002054940303030782d00404003c00401224176040c103421000219103c0204805022a0001c01c584d81451505100610041d4840c803814200003d43d07072212490000349800105c0407841e00c001030585403034200f09400380c019000301c4102c0340b00d0818007c0419080003404ca5030007281c244032408841c0e0300070b4014030020b050303134501003010941d650640e0742400c4280007a5403801c0000c2e800490701c00c1207802002d1169907641c0340c09164040700520449944100d110050360000e00703010b08101c1c0ea8050245201220315550f8660322941803254a5089880d0700942d4000c4c070024130010400200050039001c5d1022880c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 896610233 1250 896608983 896608987
    0x815100c02031005071206030b0106140c1915050412110a05060c0406031401080c010e0f040f0c080618040b0703020f0705030712030b010c060b060913052415 69
    0x108016106040d146000a40c1800391541800d003901c4290310485c4a80c0701ca989511341d00400042e42e500712811030001038078644862005018072070040040c0c0700b411100044041c038058402ca081400c140b0700d0715507180e503840c0810b50a400e202c0000300210340d2400c4d0090400090401342d440e111280104d41300c420901460141000985005004181c100c540180589403607280c003120300d1050360300602811010a1802c0c281480d150403c03102c140c1078850040080000103424401503070120304d1030346410b90060001c40142042e440d540500781d0302204c0e00030089556502e64002030106d0500826107030154800180001923006040b030f0302900150400590949915141c4003200640301d01c9521074080503002500600300000000104000b5000780d07403034510b080b4201c10880980d0060140940003030001843c0c0800310714103a0051100181c02013003146000f0021002ca42c144901c04040300c0b009503110104881801d09414510080310f1070b8252a401011030400078000c51442030b02c1c69100f00380 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 896611483 1250 896610233 896610259
    0x1502090f221d0d030e0616050301060309082b06230105130906030c17030f03190603120c020307050d0305030c0a0309080d020703021504120315050402040807150815 72
    0x40c1202c141a501001c410365035100c85500016000e043c1000a1295a1080300c0000d0318800400c8424004082e030769071850302e140d1906000314080d00c8400d0700ec1e20311800400440981307140030304054a40541075011000111402202031003203803007680c0004040c9a03e6607240c80351111a56079203480000c2401c10540b13a00c8001003018500200b0742083d0030322483c20ba004420721401031920b0045900c2801e4030204000d0814403a0741324019441c040d521300e034062000c00d130140760160f001e13554080c241d54001345d0b641da01e403106080300e00300700c1401020030ba411084d0703030039401c0520020307002c0c0509503140d001111081c2c0c0c009016200003009912040f6011600c0035080e440f907000401703200e802c040380300d07280d5194990300f030001e40c0041e0048016100c1d210a0214401e00141041e11550300400120004402c2d40d40c160f014086c2403c0190040503a00380100355946c4074400742c00508062002000d400b401c100072040303900f40340c0d0a80414007082c0020844000215201d000c1c040c3c02c2600e61141d904a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 896612733 1250 896611483 896611511
    0x60606301e05010602211201060e0301090b0a1514060304020d02120607020321071425060b010311040e0105040c0c080a0c0201140f0f03090304031502090f22 69
    0x51a4410070015040500001c1d400341c2c0013612a03030322a0305104138040d050070341001e5070880c8034104450098110385001000210300841c0104280000070f0004100f1195a545550728007800300ca40640c543e6131000803407c90b01d5a001342c8406480c00c0002c01c003900404200090300781c007005000034480e02107440080700b10744a42902d0650341d01154102d5042d4180298080e4880c0c01c0b0703802c2c40c40c4003c2c24503203041e1400031031001c040c042d0b031290715602d001c0a0300c40c1003c1e9159001010310000d42000004c024002c44020010526543c020000043d00c00c0300b86000606460380c00c0f98680204009202c1403250407000b0103032504444084500140c01460b03c1420344049180a0019100f4280070030f4168172a5001300324000014400d0340d482408030320b03c12406445004045011880c0306003030220307021010020005581101c0c941045a081503985d55910f101603104206210302541c0220750b262107414a5501c0419008044980d12017040c50920182c1c010062001710144a42e00e0b4004401401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 896613983 1250 896612733 896612771
    0xc071205010b1c021903120806042318071a0703090f0b0910020f0307290711010f06030f08130506031503190f17040b0706060630 57
    0x51006007090340060151103d42c4100755007610268040d42c8a403a05162a00180e810703801a070741d115000f04040581c01400701c6085500912a5030410b80d9040100310381d100c10784008400c08542582001c0300d103007610b283c01d1200700c190a99905640242001d2252800c0252504503800d0050307032094482c276140c1012505007a1540c42404101c0d0154000f14007010114014201c2980684001c683c8070720681d404c981d80c80175411030f5840d6410910040c0700085824001100c11403640220484941904107040300201050342d038080030900965061003d01c1080c003401502800010301045000d246403030300000504c8000c0c008254180c002244c0c5201c1e0b080d0380707101c1c01800010f0a426101d2515004401a61282c0c5802074401e02c91406481d441100800540030042d41c4400d00402d0700c03285035104150040803100600c140307117080c00041402858036020b0003071079011b9070b0045500b500e84600545022080d1440c10080d04020b034850b000e1103a600c4104035080350940001860030002484100d40f5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 896615233 1250 896613983 896614001
    0xa1203110f04051011030901180503010204170f010c0e01080a200c0c240f070b04050c090f0709180e03181005031006030f14040303060303140c07120501 67
    0xd40008259010300d280c000018009440054542e00704a05a48800350b920a454400030103d50780200002d410707551181e00710541c1e04080202c206440368a4a00017400e81c0c0003600601141e41e81d01c5580141403034100524810820240000c000200c1801c80041071012604e00135414810200d01003001000c90798001444004103510215404407654204050f43d0311907207800d8a0703842400c440d400c551800c40f94001d410418540940e00008a255440309a6000204150300d201818000e44000c6464400c0305841a445407001d000489410b00c01c022a240e0040e000810b4007ca400805c450240c0180e4030034155130559001c040d4503a035802110f4041c105403002d0104d41d0101044034101d62081e03000900508008445941e01c41d12102e800711154007080b40d41c000004550103081042c10300a41c490a09501e460381c000c1a94080c01c10848400c40c03094800700d00103580c40f2020028594060b4081c28070708405087d5070b15009092401e10780d1040a802101100c2c07182c0c40c0780a040010951004000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 896616483 1250 896615233 896615261
    0xa120b060f1f032724060e0414030708030709080712080304020909010e0304090516020604020d2015070308070203090612100503010c05032d010b1b16080f01050403020a1203 76
    0x10024689001c608041d12080e42d002c5007444d4181410009055006032001d03140003406e0f02072240e4854a03106900149c140030300b06240020007652000c80c251000640c4100d60b030340c444545040c039000c4443e2420b00d49600000c850381103400d08000142c2c50400301ca03040380e0115946050b03900c1d42d054642c01402c483c41c807540d49100000d03002032030f03010540000d071182d0f02c0e04801d02260400d07a41c080c1d8803048204d800943c480d905030650400034030a0b02c40b2200c0300300099444c0440c0700f809004608503000002600c50740b00804104c0e141090741c4200ca0640c0310345207102450420400c075020444034025410f00414224486001900038051540201c00404008009004480f01582c0207402c0c1e80c819600c0c00401c2036100010032044c2043e054090f0602601e260600042c1e00c0d1a828900a030005250f01440340701c05c9480c000002001c00407a916201e6282c0d80f02c0d2018688101180382082c1e42c04900281d07410401003001298000c20900403050b0400102a400712482d030b030450041581443c0152 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 896617733 1250 896616483 896616551
    0x4050f1203011e0b04060f11070b2d0d021b161502250302190f0b162112050103050d030e25030b0705070b0a0b0a120b060f1f03 56
    0x180c6a41c4000b400717542c0b09554a401000b032003510100c90700c9d00480e002c2c01d06440380c2042079683c44c80c0c1c0861020b500c040045048e640204184003466013079800010601081074012070307961a03511040d503000346003c02450081120800501c1c1012811125100710000d1003142043c900702c26009000c040d00424079031054200143e4642c806050710040c60205074055001c40c00648141d0840100c80c00a03200150a000411881c2004600203070f804001c152042800903007001e00000e202490407015003c2c0c40c03034560440d10513403000800d030030000c422f88407190713090000402c0858800b00f01e403031050074a807801058900004803501d20f48610b600a200d00040602c003c92020094140070302c050303d1094207001042d48412400b241c41d0700603040090100110000440d015510560000000c0304001d0240154207907650040b03078a0301c1e2400b6059484a40381800c202e0540b40000e40d0502462017251403040c100c619840d0201c0d4028003810130380c00d041d03031540040f801c1c00003108443d02c0b03002c1281010b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 896618983 1250 896617733 896617739
    0x30602030f0a110c030316210507080604020f0904020702031509010e0d050c0303060405061f02030903060703090f1e06020a17151818031204050f1203011e0b04 70
    0x41806142100c2c4070a0740d81c94022425aa108101c089408901c0e5280c011800d540320020b8050300c0c11080c0d005003080c01030f9120140c102403e0900c6070701e004194a20300141c3c1c0d00c1d003290041c04104000702001e20940c8100031b900302c17010052003a1060b290f0300f0390700140c43c0c00452000c42d1030001d810000e40200000b5104203c040d040c1500000e1110342c810f02a0307850300221010648aa0041501042450304103200265a07404c1580c08250310600007445003001c0025449048458081550801c1c0140c10014040d01c0c43e04040240607048403070b03494200400145900c44408400d8003c000500c1e04004900010000d011000c4107144c0d2034102c5000c556881403040040c08107820322418401da6440680001e9003504400783c5441c0f8141d0207044040c03180d94108611800000007011901c03071100c840e074812160101017002e4080c002e141d050500c00390810f400c1c01d0b4035100300f522890ba015400000c200d020801c454060701d04440d089a800803d81550407071584400c1515040720010900c081000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 896620233 1250 896618983 896619001
    0x206071b0b1f0f080c01020102040b1207121b09050d0203061b04050a090203090606190b070203250501080a02040807050d052e0b09090613030504091e060605030906071803060203 78
    0x2201112900c2007215a801841c20040e4287e001e140303c0c0c07030bc08800030701036078007200c010f00d800c680e04c45020b2a08111007600e034401c1d6000c4032407040881151804d20385520100c1d070380102080c0c000d06411504109072140b1580000d0740c6030001440805104803141e682c181c0d110b0031209440c0030300801054840c6250b00c03921084001d4004443e000e00034494500070a4003414400751000003012603400314010b50f403c004c07048030242d00c8000304030f030944248031500c00c03031509088d4480460130000002a10862a000004080201c064420210140304000030865540c00060754001c40d030003a0b84038040c07081541030541c00c003007042225840c1c0d0240103102c0c9940c0307042d074a4100c400700e0f195442042200b41403c248451104200c40c50110f80d803040002c12000d900d440c0f1400340c2140300e860510325141e1078090344800c3e02d01c0e5001000c07002c03094612941300d624446c00b40501428852810b85d06510f08448441c0d80c9902c060700303050620a01000c42c200119606184001568001a0a6649060074945 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 896621483 1250 896620233 896620259
    0x30b0a0e0115031d0a02010e060d051015080c070201080709050d0b01090c0504050d02090a090203031201140603060d110a1d04050708060f040818120a030206071b0b1f 73
    0x44800003916010b051040c1c13a562540c6403c1c8440d0b44402005d100b0300c03035030040d106184031000303403a44951b0070b010303180ca042c001f806001e2040c42c5d005e003220318140c54154210100b42d802c001700c100740414030041058020b400b00a841005409291000080e154050246c5a180880d00103903000040c851404040c0800c00c0350f01412a0171400040001362805041114103028070700034550b201c0c021101c0c10300540327020034400d07030405a00e20000070421000d5001910355403201c0b004c01ca034828800c0042140112902d6502082201980c5007841c5241000005051a42c1480018640070000c0c80090560701c54400c0680a04451007a2560311504d840d40e01d01c1c2e0080c21a000ca03541e206500d0701242c4150040366460280154048440040d1110396a03003042d6003005640740d140c40b03504004e1070425a6840100384140702403102034010064541002800c1080080c8100103001c0c9402e51014410f00f1180000c180a410001d000301c59214203a02118450035103a450b9018491060003242c000c40cc0c1c08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 896622733 1250 896621483 896621519
    0x150b04020d0509060717100605030a06050301150608011212110a0503130e01120308390d050f07050d0c091505030f0a1107031b020a0b040f081903030b0a0e01 69
    0xa0f40100c0311242046c070243c45000300c0e405842030310030800070021076000d400030395045030040d0030101d400354840740800c1c01c4a8061183d41c2820004c80c10400495800c02c0050740540920150501000d1550b10703405c0c201d044254410041181042036091450740600c90405d044e40c0c0102600d9461240c4d98550943c80302c240103007400c0e00302c808000907070b540b00c06840d1540700398141c41c5c1c0c00155a4aa10540500340310b0b4214080412040b0b54001981a0811074100002014011070b901c3d4029010081c00300c0700001c040b903030103500c1d0105001d2020f030014240c46100b081180e0100d400e10324110119445241a403144190038407400c52400202d4208015510603421b25070302803225aaa80e48110540320403025249400c10100040e5011078410030403040901d40c2840e0305101011968040766001c011640100e401322400326052100c45841c41304803004241d61300c004e1000072070240030030310790300300a20b40241895990b107944c60207034403000c0c0443c2c01082c0032003540b82e10b580e55400d44000a51501c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 896623983 1250 896622733 896622737
    0xf0b03010c0206100905060a030813090f20090d0b01030c05012718060e07120b01050a121d0a0b06040c030c0e12010b0a03200d150b04020d05090607 65
    0x41c0c0e80341c8201e20005401d40b1a0000c5610900624905a044401000b0251610360000761001012001c60084001030503000c8000100c100c0007880d00d40383d00102e032074452200801e2414105018401181403044003607420908400c603541c1e503440303000201450101d42d030041152401c1c100000c1809400c50140d41154000e80b1070041c2c5034403403040800180000118000059085132040c449028401400c3c42101842100011a55203c20000c88161000c0351110b0010321004000f01c280022405103e40c00322003800c1c80340c2003003901400900146c401102031004183e9a40004500c0f10071040c4815404100700242c0301403c00d41e040c50181d01d03000300e590a01480c01c00e49000c007014481d02c0b440101d01443d5455484101c4000d04212440c010759410300382e20764030369000c0122940c0707550303034803000310b00c40c02e03581c00300c008421805280780040c00780c180d2180041080c010086140c0212200c21110342c000c00044012446002030024011000500c60b4145040104642c1920000b5298003a018507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 896625233 1250 896623983 896623991
    0x42003010219020c03070501111c03020f04030b0402030c0603191109090c03150a05060406080402010e03060c07030915080c210c09040b041e020a0903080a0f0908010c0212030c07060f0b0301 83
    0xe01c1c015180c440e26812708182540c03200880c0206071070007150035225120540b4007d840e000c02802003040c5a0069042580d040111600b40411803034200404264244107540840c01c61401b51141d840581f0b101403c0c22090762190003000b110a480400c8880c02100101111030710b043c070600c01d0843e90400c075803885150342d090b8030801080c07401290f040e0807103c0c01480d407807400d400d10304202d80c64800540120f050200c920128282d03a501406468420340c4208a8103803100300d85d0500822215180c1c4c05003444146100c0c040d65416480f0800e00e0740020b0903c155541e807021800149103466240c8481c2081000300018048110942c070001c104100080385c0070b01c00100c607039041108030341400c43d40f40d400c54844040c6007072101c100c2c1c028003444641da080c4034040e03ea0302c1c0c030745440a5100b5500000012162110800c106030410046009001e00c000204200f038102ca0380a50b507000d13107a20280b1481c45c040001510200780e90101c880140e40920103100c0b4001c07005501340a8010b83d815207200c2d50070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 896626483 1250 896625233 896625239
    0xc04050109050609130803062b03050901030b01110c150d110d112b0b0d0609030908060910110405041e0507020a0209040b1b0703050301030c0608042003010219020c0307 74
    0x4007422036000ca50400340c6c0340d155840d60b401f00045d000114000308680f41208214007210383c00861242060307070013603c079140e941e541140010200c0d442e03501c0440c1801a1f20103100f403400c0c000580040e42d45000d89030002c80a403074400d86d203114021049040788003418100015030184150700036007003c030714200003840080301c05c0400302103c1c000c10b860058a180540650349222241500720400c0c1040904009420070036000414240d00302481c0c1601c400e40c60300c80300000c15038018032000090050360041c1a81d0b00f44207407001d41703900242c006407102076143e8400321030010344401240c00411000b0810030882e4402d0b0181c050340702d2906030590513180740c200028242400490403002c02540146403900030754855503214140e11004d0000e120309100b051202e010000c87c00c00410541740641c50381c0713449600d1881c0905508507280c010800704403400742400001031140382c903402c3c01400040318407181c0b11804007082c0240510451000070700d40041c222955603401040d4110b01c84c905900b61041030391 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 896627733 1250 896626483 896626501
    0x102090a121e080d0c120f021b0105010e0114062502130c0e130609090c171903052b060e1005030d1d0a0b03063f0c04050109050609 58
    0x5001c000c081e03e1402c00704281425107245520220140c0344500b0011220750014171520111140c007680d44c0e540d11341c005072113542d07411f2a00c4250301840703031079000348030303541c1000005440c000d011700c41c4004c0b031000d00b100250307613540319070640e0200c82c01c0043c440c00c0310150800218142c059904164014660f00040e005102000c1c000d82c4140c004948800000d4112601806048001c0046046c1125650354000c41d11044030b004142c100c50180c2101000642003404541d44c4220507501400264004040c0781215441c0303c00149a0030f0705414001c1d11081090b0340180c2050540c07070703480c0070b081c608010036072520f213981e00c0310065034210125100c1c2c941e42e604c00e1074030300221400b0351580356000d505142c0b2401d2180d45000c0c1c94500d04460510310106402c003050800350250000204402e000c4200a11401c080588400c0d02427045541e804191200361403902807a1510140180101007900a01c00c60b0010881404d040d031025100b00308030360f581d9010300300030001034440622508800c0d0110b08400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 896628983 1250 896627733 896627783
    0x30b0405090a320601060507120503070c030e04021b1605040e120a0908010203040819051305090c12041103061320010c0501090309181802040b01020102090a12 70
    0x1640148500302e4010507101c000500a15051881c0e030514024a80d20540f0400307220b030b18000c00c11a250561240c01d145400383e40c0c060b2610311801001002e0040140c590380c00b041c0031503250381604080b140c0100b4000407c000e4850540252000c00c002c4c5a045611800040d135510300c0d480d0780042103052500e8500300800d54490b03103116003c1da0300c180503104281d2441d100a001e0b07181681403d401040d9122121420390700201d805032001c0e02d012030008403203400b604e9550707101e0015261072440c00b03046a02c1e11240c26042c2c09100d020f230503040c00150301c0a07a1882190311160b841d00b041c1c40240b50a1030114821614120400c7c0640140f40104120241014840715900d074031040041c040505002c140b41052804154030b810048030f01c070a035020490a21904000a000f030740e03004006400c0c4447c914a98241c0b0034440022440d1012001d00c0000e008202c0c4c02c1070b64110f9020400b8014640101d000e4080c0c0a0140d9120305d1702d4170000f51038052503940b2203440c0d2040f0454001034035007981c003a41072 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 896630233 1250 896628983 896629003
    0x41b080a02092d040f030f030204050d2006040f03062d0c02010603082206020714090a0212010b0a1707091e1a0d050a021305010807051207030b040509 66
    0x46030b42500800e803482c2c0315034801c4152210070b4040700d00f505003000707a04440480603501a80d000c209810a50701707150744480c0c4481e40e03c0c0141425464a03141802241040700c0d0380002a00089000c118400b6201030907500204241c00200701c140c0f10368440c8400c5410008520049561500d446401d04004580d01030b0741c030341c082c04a010501441107074401080070340341d80c00303c44046550f600c102000040c1c051000d001c0e0020300d041070b04c0c03248071b10142004c0301c8100d54000070250b510400081000004152075542c044400786d034400119100d222809029008000d0840c0340124000c00105030004114040c0c07201d440301d030762050701007040480e040786800000d445240000b0021141440b0f0003c6d10798940a060f40d10120303c2244c9940d403003030400155003841b0000e001440015000f44e245071305e402115004200b8000c11403034445c07040741c12856500e40b0f1003414144000b00700050b900a001c0d9081c1c0300f40140215900000c1d280040000307006000c0700001d0383c49503113080041081184001445400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 896631483 1250 896630233 896630239
    0x105090402060f0c0106090e0d0c05060c130f06020d02061b070b0c070605040c05031e030d0507110109050a031b0b0612030702060c2b27050405041b080a02 68
    0x2494a403a000d100340c980c08989903041410b42003048203c910024031403e001003004a45c0042c5807011394481c0350038101d000e5241070402840100d5540812804105142c01c5840c41d401c1a80d0707407440042070224030960b94045030415101f03070b0780000ca5030303004500b4071407107109542500d00380d0399008003444070306000c8403002110f0368050208000107000c5880310341d004201c510382c190800003565100000c2e144200c0b412180c2c000440c0d81041351b418104201c4100e4180d49039400141c949840c01039940307018613110000c10300e846102141c0030798010019282c081103090002c0c88461031340e0030f283e5a10450000100c001814203103a03000d044041c101e2600b4081c1d40038040d682d680d10f9500421030308000f11008094140030030081000140d03510750040003991960405003a17011142800f800c00780c106034000c803804d83c03c1421f2101c0610b5100340c44404045000b0b075030118a000c10402c48000c2c2089801c09a0403034588014402800704907210007035101c0e082101c1104051b115144140c494407140d2000350 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 896632733 1250 896631483 896631499
    0xa08100c050a0804030c06020702040f0f15080316060914030a020d03060803160201031d0708060906040206042711031b0c0a080f0d0c080a0b030d301a0f090105 70
    0x10019100d03810914500d8011b10f1f002d800c0446580015040368200ca16210b0135a59408d40352500c5803c80c040c04002c0c01c1c280ba0f40300025440c000d00d43c0d840344614030900048441143e061030407c4030a500074138000b40c1040d422040700d610290240d0f40c0391322251114001d842282c14003240b00744a4080d51081d1000e00010714103001c440c0c84a542500d1300c20740b0880c141a00e4203094408001c10b46007502504504000500586140000084c00c1182c064480c5005070803e074100300168450000320f40807954500c4444055070001c2807203134141e4200f015191034003030a1542400015424401070340c050350004c0914085811341750080041441812500700d042e4010f101c0d00c4022417440005030801c8820080759615240c101081c0c0e100b11035000a031325002ca14610305001c6103220920845400c20000d41c0180144000d00070041e02c20407005100351800d000004603551010030601d0500303104500444180211101b5800856a00c1d11800d402ca005032191446d00015151461406040700c7d07010708604 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 896633983 1250 896632733 896632741
    0xe150403150f0c0e04150b030c1b07030c030b040606180504020111060108120a050415020102071502030411060304050a0515091911091b0409050703180201020d031a0a08100c050a08 79
    0x5c009002d058642e810341194070080010340c02903140c01144a9140e1020031580c0754040301007440c080841d105081d0881c1d200d40d205000040c002d0400c1820342e40c000c80145226500c501d040c1e00a0085a040b000303001e10795094205200b13507242c014034045c51003600d45801c0c10b02c011505990703c00c070034802c420303c0740d1200b01c140d82000c8410703004104144a924200385859241e000780c0c0300c00043e40c407494006130b5001481905002000080b9000540035950551840c146030f1030382c0316103e500303800c00b91182d14008081410400e0401c51000760356072050a0310b4601c152403084031a0312030100d480c2080e60255416040707001c603980900304000c903401400c00422683d09001d100c521580200308144522008a4903aa03592400c40907000405110001040034075040e00d0041c1519441c040d42c00c082d02c1088140c000507030b00450001c40d9a40c0c2881c0005c1c038104480145007480119241041d00804141000320354120007281c01c0b0203034810200f040c4480c1c0e20100e802c54403442840021b02c00508144007203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 896635233 1250 896633983 896633989
    0x13062405120c16021818030a05040303181715090f060a0b0a23040b0a14040b06090d0804030b150d0314130b0a0e040b03030702010e150403150f0c0e 65
    0x141054140c40b19156075080307120b5000c1000026009106017103039088608000c60000000301304031110350680051810401d240b80080c004d4052800020144250019a2000e405100440b50010640089031031842c85100c0354203910b0710311076040425514400b0000440d03c40c800a60a81200540381c010807a45d0784031a000d000404a86284540c80310103290005000d075402000d00452204903040b4445020b00c0904210440303541101140c000c100e103007800c01031446400c522a900030700659000c80c9207440440020840d100e003402540d0b00071144503808041c0b02e02503000d40183d0780b1410084109454402c0d4260303408044620242d44441c0c030540c0800064420b0744400070190a41c1041c40c01e100f906410141c02185540182c11815004520404440c2c0e0000702d01e00c11540569081000122000c04280c43e4070130520080d0500842000216045d00d9109943c5100082c507200684c5698a0345020210074050460380c044403824241c1e481907400c62885000140f00e1151a00d40d5410300d00018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 896636483 1250 896635233 896635237
    0xa0b0310121511040e01050108060d110d050f03090a0b03090c100509270a2c070b0a082e030b180703030806131505010e13062405120c 59
    0x4125107a03996202c4900c5641440d00440316044440780745691143e04025100e003610310140e001c907040144480030b004403900e410200340c0c865030b04803448851058003003010810640741d660000342a4401e061003841d00c12400320240c00f5580307044891100c41e80d0394441e0a03600307010941c0d1451079030304a035480750164075207000512095411401d0540c2011003001c0010301c0c002c0b603c1c0358601d80f0054080030030304010020034056440400144108441d02030150b908022190920030035900303014464101240100420484004005480c00140e4500c03640034028040366058502880b0408060411003028031450054807085003007000b00c0154504c0e40e1188450031402500781c50a0000700c0c1e6102c0c240f5001444094080e60190f12242c1c07581c10b0560501c403000c20b60207406014549000c0d015200800c006d00d094085860074038200c051a0341d0000068401c001131049035104c24a4414009401c8642c1c0d420040740c041c20511160758007190307020035a06032103004c000d45028407460000850300d02900c40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 896637733 1250 896636483 896636519
    0x10c08160227061f08160207030b160f091508130f140f010204120803180d03090201181401081b0406050c0601050d08070312020906040b07020a0b0310 66
    0x400c1c562101c0001ca001103680900885001106500380704110385410520310040142c0b003209900307070002072081c6009112040281c406c2100041c006840c8694620803c40000955008240c62995080c500152100c60381c0f030024500104183c1c8041c0c005e51405007020004481040c0c9040004030100481291030300002000b441030b0400c40c0380d500d40418900d00000c01401d20400d00c85050350a03000c81a45480049203010784540e004000c14007034410081d410000040e4000b4845480b511901a00e003400c035042c071003c001c00d1007000d48540409506402ca650881d000303880e0300000300f40d09002501d00e95581e00850b00001f0551a072442d05500c10700c0c1583d400b150f01d4607842c22040c0e448040084607481580114001000410121440007003400040c5c01094101d95400111680e81c0d00e1341c2d03103070103607002c040d040c041d0186100c00308030003580403901c1600c8018a503542da103440b00c007010715030741100c00d007a40a280800130215428a400d8100da00480080318404000c500c0c000d50284080c2c1c0c241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 896638983 1250 896637733 896637739
    0x12030f071502040909200a18180b1608010e16051c060b041a031003140708060415050a0b010801090b1903030509130c140c1501080106060905010c081602 67
    0x400a80c0c1100340c171078141085c1c440c03220510701b4628981d4030b26120101c030818500c41d04402508020807a5000c12188504190130004201b1140c42c0f4a2550b00102311a005001c10003418108800d01c107090034110181d0525484500c00ca90302c4a540484104040300d0340300f03001c901094031401c41809603010b045070b18008642d082850f100c00d000d1038103641c4154441a00a0380c04a400e03c2100480500c0880c0341b08501903030b43c1540b82c80780d480c0c00804040e00c40600070384065004100700304810301640c4094030807003044582c42c0c00c0c20314011b05d0602d074030200c11030601d04e0b09005c1000e6100314001c4000c1c61740141e45c0e0406c41d9082c05c02000c001c1050b5640d281d0300a105984500e503800702a8a041c00540c043d8580f19211515001480150b451483e5020405031410031040e0b80581c010b40b000c481a90382d6145d00d80c0350001120604e140501a84540010b503040d10000204030005400010076104a65101e03840e1580d203000558010441c2c000040c0b4410051008240ea4415a02c0c0a21014001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 896640233 1250 896638983 896638987
    0x904080c01060f0f080c0d020f0112020f0a0f0302030f15121b011b0f0b150904231204030f0302161401020106060806131a03010c090512030f071502 65
    0x151603950840d403081c2d0151128001c07203c3e04000c950307001d004100040580401501d5200309850020b03c40100c7c90310028494015140c0030800f0342d12403106401941da020030219a1040c9007080d5a185400088001340007d0207550314100b0584039009407809480d0919200450f41c03140e414049140c10443e0895402852040380c212a14400300803d2103200441c0d024501c114080100060845c4650000501507032007080d000400502c1c420747c030300165130700694000b0707040d183c42500c100c101940c1c00700a135002c2c250000b48024071102d40b8600280d1090300c61080c007911005040c4a8403001c0a111202d244c040030320040020032541e00c5041c6025100b44180c421170407185c2440300c184550340d00000c0c1180c10200c080c410958091182c0006806541020f1449207041d80001e4941d40c0c50300ca80303901c89500e40780c0c0d200b15468040107810048400030028082c1030071030b0000400861540c86140e100b00042506040b034003501004440c0c40084000d41c541c58800545c079107800000d24481411403803503007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 896641483 1250 896640233 896640247
    0xf05060d1e06090515040c0503160c060c0e040b1f110f0717060703051005060a02012c01060f06020c0913050604080703020f06010f170703080f031b0315090408 70
    0x218402d501c0940181000080c250820300c03070700c0304a071103443c1c805801240b500424506250300007007541d52003183e080310144030790079101c0c0440781e13100004001010207003000d0720f03501c0030f0750400c040c002c00c000c00750b904200005513a410840c4940d214180e60101202c0d0140c00049280b00c0c81d0300300754140700101186c020907202880185450081e6002442000f580261750091030414800c0740c2d00701c401783c6820701460a004c082038403803001078424140305841c00a50742107018000e410a011015101d0300c81c0403000a100e03d4050031000000044200d5440d100020845000000b01001507681075802000d00408003418000c3c40c042c05030404003050410710754070002917420429184203921071840300d5126085854003914280003140000c01b075800c00030040c800446000110400c440d0030012080c072104800902d941801c00b240c001034a44800002ea2810100343c100045001d402403198060700007884905030a070300e0100f40c881580c41c60110300009250320781070604541041c024138804e03103420a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 896642733 1250 896641483 896641541
    0x2030a03080609070306030314030403170135100203090f0703110915220e03071a070903080d0c2705040b0d05031b070b04120c0f05060d 60
    0x12900100314000340c80301c410420799051200c000c58000c442d030706090140c40d0450b0390103400f4142d030100c10400180d01000083c141407183e0443d011000c41c100c034211035541c4840004000c0c0002e801050540070007040c07512f11040781c0b502c56095450006002e001c2d9011501c1500004c0c1d071002d40781d4030707039842001d58204203031205004000c000c40c17140b440e50703c401c5001c0051000241005105890171520807810368030507140c21841c225051400c1d00d004401c21603180328400241440d07881d900309848041055020828940f46c0220382c1846002c0c0c031001990703500c00840c1c54400b2030100a00c40a000e0140d8a014482034001140c200c003241001c2e0025420540400050503072207940300001b8020305020001d905281c4035039018840152448105ea460640b20240c1c2c0c0d1068902e9202c0b041001030501000c02802d0005074041c100c17201f00144c3e07903643c0300c003000140d01091030161401850424000360352880b0444e05800c03a0009000b4071308080d800e0081c1c83c000c241705458001490280180300c03840d42 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 896643983 1250 896642733 896642743
    0x70f06081b090a080d080a1b030f0204091406040e06190e0727050f060303160501060b0c07030b090a020a0e040c050604090e060915242101051f090c0c0203 68
    0x10248020005c443d404000141243c0f0041e011400c8140340105001c003c07800740c03040680311409428082031000f03400d0a882c2c020b1107994003c1009501d0100a8203140d8201020b40d0f014107400c40e030500500904d120500d481c2c0400f038800c0340d4074103101d06040700544400c0d007081340030a441c40c0a80728016503810119804082030725081081039401d103980c0c011017102d84074007500000c018400b110310f0f1505001095403440785202882c010b0b0300008000007000004d400810181c1a0050020303251110b41c04100e540c1c2c83c850008486044030701000410651002400b01070981d0003c003401d5140d40743c1109000c11590141003558180c5031144045856107400c0b00400041805500c002807408070080100d040000c003402465480d040041d1180c21180c90f849050380001c120f155010b040700381c807003401d100658000800303038000307440f00121034084008080100d0301000d800000e01180c0d6070000000c08146010b0005a80400c0c5602c090150076041d5000c1ca6200c00141044004007601c0d800091400b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 896645233 1250 896643983 896643989
    0x111002030703091211070513020408030a03141e010e04050f0129010c200102031902102a18170f070509012301051207080702070f06081b090a 62
    0x480d0315450500108400142550710102542c584940310300d9200c01702c2034070740409215282c420b1002040b1944040d50a50403140204090300482c2d56643c5d0540002c2d001c2d0a208071001511161040015a00d184001c01000c0028503040c05603c1c0e6800c11517074590020020b40305840910031941c52800184003403003104084800402144203400e00e081240e403500300e00c04017003410000e4040800e000500500546610038004c2040407000030f50444c0100e245000e0801c81c1c0041c540d43c686800d981c242c011030b0008002e030241200740100c0c0c180356214408004030024000c0c00300a04c1d005400d10b85c2c030900c9103500e00c516041402104564a0017142840c081a180220240d0882e20b000131405208020850051000752450010340d8501a641101502c803d1500512805506d03e002007980c0304000b2510703030f00729028205000c3d08200c00010544102101c0640c0544240d01001c101a004201e5000890740d40d65201d1003140e5a404042c0f1440b1001c155074200e0039400c4c48aa42c05544102d242005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 896646483 1250 896645233 896645237
    0x513031a0105031c0203090d0204090b040c0f06210504060b0a031a0106080103021f0302070807060207060608011e11042c06100f0f1206060509031c0e011110020307 72
    0xe504003002c02d4203113190350100d00d90520018805041041c5c000c01620141e01007194045624803450010801500032400000d000c80c5d43c8070200801c01400f50302e0001a0752002228808007a240e00040c0e80348501d18925103201d0394625001d03500c0419540103164003510481000c40d42c03024110216991b6049900100e4054100708000146a81451030050040400340b070310090a52468000c182201d030702426134844810780054507040035000360100c2e00c5171540b1181c025551801c5044c408001c0d00000d8044602c107042c1000000c0c00541401204980d40c0102580000c88140f404103000400d00c0b12024140e580c0d05000000d4101900300c410200c0c0a41c420040f181c1c900c807000484a8454020643e1344106141c06c80c0c40000d030b41c408400710141d082400c0080308900d40c40c5059899440b00c03103041e00080d080c140040380c90359006010303119202094040760322240d0a0001c526581090061080014a03a004190a250702c15110b0b1001464400192503e0741482460354003644d0080b903503500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 896647733 1250 896646483 896646533
    0x12110604060c0213060510080c1204030e01110703151a0301090c0e1b0f0f0d06060201020c0d17130f050105090c010f1d09071107081e030301060807051303 68
    0x750700300481358074202c0d140308008200b414106000036200c842c0d8204d1480c1042051800500c2041480007202d00350000c0310002101c80c0f80601d0700500e400390920080340000d40461035842c4181c00050103105403a80485100412001903c2400090404043c0c000e6a95000d4078075603540d4a083c4101c0d0340a07400703194041815400d0a0742c401d80e441001d000c10b10b007817400d040900b24107407a4a09450002d906001096501c040d2003000c01c003d0b000f0710394001c020611304140014101d4055004011241c0214107403842d610440d501a00d41c504900c50035a40c0007080c0340041c0c80c000301348640d2541a403242c890000c1010050702c8113421507030101c54a502c2584404440321456801c8000c20501400c54500242c01e040c11003842802080041c00141c068101d8a0108940074058982c40c2c207804400c2c0200d1740401d1359080c3c440d40e00e840090710250b075001030008140180c2400310482e03041e100c16846010060701c6040342211650311000e18040c500c5203080001c000681c0c11a011503a0812110b0844 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 896648983 1250 896647733 896647757
    0x3010f06180b0903070e180f0312071d19060801050a050d0206031e0a06050f2706032e0606050f0f030a06091e151d0a0e03040e16020607091211060406 66
    0x14a0308c3e5104c8107441856000303012a0b100d1051310034106a022a036031904180b031f401041c0204120025102c0ea803a4804002c1441088100c2c1858803103084511075541d004c1181d90b9002408410707040b43c0601604480c4002c194400360500500650300310005000304080709144010212030f03142d080d268221802d455a0040140d490300a44206044100b01e50194060201148850b8083e81154810240307030801000648940e0b0280301c0c81070040107542040703849010b6040710800000e040703915440701a00e400004603120348180280c5041800003490145444a502a10700303140d0001072840907025116400840c0195503030080c0d80a110001002c04401900804c4140648a403140c81e42c2103140c140e5810001d1661041201c2c4080e07014002c21403080d1039800106005d480c1010240c844d034031001030009621100e040406200e0a01500d981742e00300c0c00f0900403a16080242d5100c0000b034502d81003403010a140c1a4100b03a0075100344038039400940302001150254120307610900c0420103100f448 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 896650233 1250 896648983 896649031
    0x90507030c090b130b040905390d03080a020708130302010e0f060a030b03010b04050115090e37110301090f14130c080f0303010f06180b0903070e 64
    0x20029000e05542031140d01da2050105103130030048004007801c81d80722a903030340d803680300c59100441d2290400d055948503912020903540c81c0c00d6032070a9907000340704d02d04480310a442a0404030300b240c9000780350000161090300e08031841c003c080c040e01101982000fa080010301003000a0400b0004180d811605610358000940354140030513007030703018144480c981d600554030311007100e20304411070a0003d800e03c2e1741030110b0700400703a0464054100740f6280010420703250084124032148116510460110784400384014100d406842d01e007898140135150082284c06410309050f003ea050400072030001c1c2820900050356075101000c184c0d520000010311115159000311031100810301414051000041d000c040c015170010030b01118001c00e0401801008220740c1120000d00d503510442d034201e00c44c014810340b00d60083c800e0f400724410f020f40020740035008440a03014038140c0000b12402510f0064000d2469004a90b07180d4075000e1840081101055401c1c014011f1002600b1a0741d00c03240c0c5405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 896651483 1250 896650233 896650253
    0xf1318050711060603100c0314010f080d0c050303061005121e07030204140405060a0f0e060f0103090b130201050c010c1d0303090a140f0409050a030206010911040b0f09030109050703 80
    0x4401c1d907600580104452914001003500708004500c030001f8110f038803250300301d004082810300401c010b0110b000001350106501018030545c4e840405403000441644c006a4403030b4a070f490000d041c1d030401e00008009182a10001d40f03400302c1c60501c540b81055405140c81020b4007154480ca900c0c0000640d11840402255104c0d8800200d0a0851405041c407110399845024000030521854640300060090384900c0380c1d8100800210044180c100e03103560380c504540100f190050302640e01d1a1104010350b109003e030712101038003e48440b04540341c503488440310740c10900d001da061210030410302580100920562146401c03550300c2105603200c03d0003103a000c80e1310340300e11486507000344a56000d560b1110700050031144086010302c410840c40d0045141100003070440c642c450310345405401803110109103151514440c0e8280c500070380e280d2600508645010062a420f801e09110502040d41128000e040380001c1541c0982030400060000342584c01e440000c69490b0002c880401c200402645 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 896652733 1250 896651483 896651507
    0x17041e030f09081603080f04090e0d020c0103021e0306031c0c110406030302060f1b030c090906031b0d05070504150e010609050f1005210910020304080f13180507 71
    0x50561111480d040c000f00594901000d4084000010350b80d03481c0c2c101e07a0454000302027400050013000340f23427010603441c0c01440c0e0205000d03014952041d40ca640c424801c5030441c025070010404121200b0701d00a40a80005150580521804504010701c00340c030500d15600502c540c1c1d506444038510b29018400040030945280148d090030340c1440040e40100c0d07e0340e40302c0c8108203001c84079591004680c031120b1030803c144c20212800018090300d03459200003800a607805861401c4a03403030751424990340d14008401c080c00e03880c070310042036843c0c6400c400041655020b0030403a10000c4d1035000240849400140145a00f00030300000c028003e41220710900400282c14031404152030900803803008141c0d07880c0c1510541c03424050b0241580250240c03000c155920001d4605072401300504660484160b0300c0a8440c0301c0c0039002c0040c080329000b16841a940000060b0804141c9044040540c02417a880140a030481d00b012607440b90074950b200c0601c045010216560401110240020103540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 896653983 1250 896652733 896652749
    0x603030904051009180c030f17070510050603030c0d03051017102f1303150501031e031d041811041404050d1215030c05041b17041e030f09 61
    0x40c0320170005c180b403942c1c420704480e044407420700070f9452840c1060702c06050401005c40348102040b980180140003503106500d100003d401c0240d43c50b0b0104059803030207203941c480e4460f8410404070121521030b81000350040c41c0c410207a03000c40d8441d20a03c0307010a510000c0348056100343c2d12118019054002c502e07250451038100041030f080000050004420510390311091800007450020107040608024011500200e9040941c10122038880103401c3c207100c165102070341a40e549801e00d00314420445030a5140e1a00c2c5603180208044c076100b03034480701b81950b216550344d40781c220500541200300b01c0241328461440c2e041400408100880c4c80d420011025a25030f8010403001500c0001c2e0b950b4100120704280140045544500006e8543d04007038a6514580420004c100401411a80142c2c0d2044509000700d054003030590340c3d222200c522100004034030425401074041c41503500741c0c116001d8009070800b95800584005003c0d00703000214002864101d150b00515440764482c2c1c0640710325 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 896655233 1250 896653983 896654021
    0x109110301060804030e0603010e060907030c1d0a030813030309080109032f07141302120c0a0c1e0b06030d050d18050607091805040206120603030904051009 69
    0x8a102545240414040e0805001c4401c0104050501403c1188540000108000e0f0759603181c07008482c0383d003410380300c03140101e400c100403031003880c0240252900c021466852560f0860f022041002e00d00b9861a200d1300081d10b6031010011070515402042001e50f4034801121840c40c5180080030582d0325440307031195900d40001030002903400b5000d4031100141070003a540c0003010380c1051854044100d002106407246000015541104070720741c0104a078100e41c007540041041c84080b0070713072160101d146e071900703040b00000352502c0c140c4001e851141201d18000e0282941941e8107000c01c0320580264684484800f120350400202c5200c05130f1040e425409044030003400c0c500030f01180905420405035948a409024880960f00100880c841c3c00404a64032414000009042e00029009003402c041920407a500c0c0e0403000d0041601541c2d014000d070f440c6c2000e00e50030b404a00406000e5940c18003080201102d41d0b1340340d0140710300421160809400c680d1400441d10103c1d03c00d503a04804034400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 896656483 1250 896655233 896655251
    0xf050102071a122e06030f020301030c06110709111c020c06010e06030c0d0b06040e070f031212052707060504030b150d0803090105100b071b0503010c0e03060109 71
    0x540700559a0460001c180d40000d80c42e19800d00113103011004441c0b0346159044180c006000166020f142101c02c2510100200c821118980d000c0c1e01c000d00000c3c001e09609102003042501c01c0003d002c1050b01041565021303030311891540f041d2010b44403402e41c011400f08420007600300c04030800c2d005040c0c40f2000c61030003540d07802050304c803881445502200c2d0701c0c040002e28543c03010f110383c104190b0014603a0b00455858034102039100d40a8a856009910340050b00c0c1003071000040740c2080d162041005e1210600d950307100400c0c1759040b40c20004000c1502c0e003070140001d642c06124050341c12075070180401203c95000c003010411203003c01130b450340050800c212658004048a052b00e0f003019011001355502c84a0b1200c00031107450140e004003000007444103100c940005035015112100c002e10007501c4400e00c3c01211407a500804217000b030f08014200018502c0720b8180500c2503000300040f4420b50701e00000e400c581d1511421000b1669400c01441685801e00005015110400c010401015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 896657733 1250 896656483 896656529
    0x2007060f05030f0a090c0b0f1201080f0307060c03060306110a170c040b07050115030312060e1e2509030303050610170a021213050d0e03060714090a0f05010207 70
    0x15014244c5828107640b4100c04050103d4801c1c100c0103400700c3c540650fa01c491400000280d5440200c0c00d000030994100081050500070550724100a0910001e40c02c190b146c0c0c4031800100440038000302415612100000003502502a006100414085103034603040c10200103042d0300403541130441c22801c4002003003598040201034030309407211200c00540389d40203460b0803401030041568a00814903480000420103612030b0020503612481031042c02400d81c2c030b00400070200740503254a0390107500914101d40c1c05070005081540555040300600310340806460720401c030418003161100040f1520000c0c818543c044c012250429401c0e601030b1071600301400001c10901c010407000007455040b1010500384100d580688845034030501240e6810b00b03000350070444240070140308603000e0007600c20040807030b80071b40007150803103070050041e00d00307a03072208021183c00b1150250495100c200340950009611440170007805803003901c040a12845c2850000b91411009500c0610030b41c2c043c0c0c148002440d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 896658983 1250 896657733 896657761
    0x15030203120705010e162409060809100903020102090f010c0f0807080c01020c03070c0e041a0a240f05220c03020903030d05010f140d122007060f0503 66
    0x110041580300c0b00b8034079025025124100845600e841030300c170b0280d81803c2000c440c1044a48000001c400305a4080e40201c0c1056075814a0700032901204040050038060354907642e100340c40c042996050155484c1c2541114154201034005030350101719200d40c1d0400c850410a548002d0030710802c240069a62801003000300140100703c58000314803001004406420365583c401d0800095480da0042102c540d40c9800500040d0b40c185040ea100103909960880024000d5400c030607280841c00c52807443c2480c140000c0c0c03031852010360b581c03503111450041c0444c80c45060b0030b12506103e464900030b040c84c03010070b1035040701d0310602c0c0e40d550110340c040390500d9250390b403550401d000c9075691780342c40c0690082c05901200c9415000004044485500301c0d403101e81610114004881440d480740c0002e51100c458410301600010b0490f4a0340c003250500303030b442d10030b16018504a0200090039021440400d010600e110041e44a00c0085c410700d41c009060452540385840e01900b185040380018181d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 896660233 1250 896658983 896659003
    0x5010501140412022817070e0129090303070819210b0a030b040b07030507020105010609090b06070804171902010801090e0f0304080d2a022106041515030203 69
    0x4100d9046500403100b41305c0307044104021200024254a035030b0326000311555403403680c00129800307514030100741c04010b180110306840c028020010340c060203641c4400820000c1ca0f284482010601c4a40c00d01c3e030b001c00c0100712031403061000c19252011707000c000c40840d40c140854001d00141c42010019030303d0000d1105900801044c000c6252401e40700800d075171201c0307500041c282e16040300400084c010550442c41c040d056070780c0c0802803a502c216089023202d00c20702a2400065690800b0030802403903810200740c0c0200107180c40d2400905588044555000e0380c0904091550411468001c03d014041c0a904071505803074000440010741c0000d280c15414003600458a940b91035a0000c3c890030018884201c04a2040300c0e0344680340d805082c0c0d96600d482c06100040c9110b40d40d0301c064210542c10f41c2d080380b01104856140c4600e0743c2000500c10111002c0581d5200840078107006050402400c0e010314003d520803005103001002600544148e1075034200700402c056410001a24001048006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 896661483 1250 896660233 896660239
    0x601080d0516020a0902120f0403020d120b060c01240506190c0b041104200703140f1201090b1c06050901020c010212012d0e070e03100501050114041202 67
    0xa03555002103103081404210101035003184c0600400310b0300c00a503a005249210b105030501301140d039907001c05c403c4a4021100180160015401c1c45501c40c0100b0454900220120f0045526003021011500a401a20380d007280c03a074413418241c02401d41e8030000103052100c4d01100c4a01400d000205180d44521141d003146071040070b80454500f44660229070b801d0380d108040c80301505080c00d0000314414a080c606100b280341c401e4104880c0b08203071404c03010042d00f1140608003040d94a050792f5030b0181c20a2000030610400c0400b860551550041a80303500c0e0384c01ca400c040d41070003c60803c41e582550304e140515510a41c410b1b620022092418a00b680020041503644d03c2c020068007a00032010b051880d90b00101ea201031407944824818180c4079941c0b83d03280744c0382d2440050445415480c048605030354900409000c0007440400d0035500c500241420421501ca03400468a01081660301c4000c4560b1807005009039030740048101184103500e10074a0500b402c151080104070820500244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 896662733 1250 896661483 896661487
    0xc17120d020d090b10050409110616023c06180f0d05030c0111070305070b071b2003120919080a050708160e04020906030a062c0601080d05 61
    0x1040c030601d0301152002140c1c580c007840070700190701c0c2c10300000c6800d480c807142005421101284500b82440380e1642280c020401d50004032421083c4012607100741078114640300c4c200c82020140c4c40d102103040304107030741c0070080e003150f1029050021420700941402480800e4403070300410581d1118142c848800c1c00303400c681d81c20b0b01c0c9000000c450b2480c801090f904004145070710300030b100000c00079005441840009020123640340700c100505102e12000100459028040080880c1d2071b0030382e1640c001241d0900507a46d0075007880060302090740100440303c0643c02e869801d000ca41d18004003032655001da00030020340034445042e450602464101070f010300f07071120b00c90707540000c07400350100200748030b030700707882c0b0510b0302c0e0034580c1d00d172101c901844c40c3d24810440101c6449142200c18001c58001c0707140d003400c507280da50801201100152501e0350611580441c540400c0440c480e007041640740307038407004460036402a1000c0c81281810001266006100100240c0d00007060301e103002d41207407410f15 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 896663983 1250 896662733 896662747
    0x30c1805040507090f090204080f0607090b07031101090809010e0d02060301090c09170a0c12080901050703020f06090c030c0315071803060204090b0103110c0c102a0c1712 75
    0x80c4c102d00c041e880702410502500c0000b51801c1e0360f034010001e50b00d44406944071400903401203690741c4401d031070310000189030308020828074040b500582441ca120b0320300f170801c02036207091650a541c043e00d404e55030070100203004401c0d581c20000044ca0010103603081155a50f00f80c0000d2114001449511481604d403807844855602c0707030580703e000c2d001d01054191501701d10b01d0125620b1050b4803007280ca54441c0319000c40c00c1c246901100301c00590280c1e43e80d25100a02c0e0044036149c0011a00300e0561040021001c2e09010034442c00d0311a040307500050028840400c2003504d8034450000d124000d4009a0703810074130040c403070b100355070101c10360401040791080712900c210111444d60010300324034404074000c5100c0111790400000d0305400d07a802d21a11540c0d00401c1454429421003071115804800c0da40e003541411125542860050305140c40045440c1400003031062000030100c0103520901c10a404200300d111016018007140c1301c1102e0394500aa0301d036a5540054090518240301c080340003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 896665233 1250 896663983 896663987
    0x6080d17100b040e1b07050a173c09030303011406040b030c0c070f05060d050a0609060f03140309030a0b042f010e01050901051602040f020f030403030c1805040507 72
    0x4500104041c0380625501d5940c0c620021942000f550004038a840d117809500a070340008041c3c59050360070030098510007809035903200c021703902c50081e400d0191090080c4000058003d003920000502c40c40c407401d85c40741ca40101150454070000c0e482c0350050610152043e0b0328004240c034107403883d20904045c844854000a111809150302501004000008120702a000080902854003040d000c5a4280b038982d500e122408881d801503070b401100500c00151380030790384d4022540000f0528000580e0329124056042642d200d41c010701c400341c04142003041080310710f00e0b00aa695511130040c42c1019050030010b038032080020300142003e00d140011a0138052455186105010072841c840c0e0045030404014060821412074107000c0b98140c0b0300c0304c074194000c1c000c4a1074136005941d40c41c50804860440000880403000c06d0f6001a500d50240d0200101c601c000c0c50600c800c1e04049032245000c2c5002003d4907002d0494508221010f40283d86060f090302d40c080503540f00f02e80c04140c81c6d41b00b00c42 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 896666483 1250 896665233 896665261
    0x305092b0b0a0216050d0f0f0c03030b0a0b0d0b030c0d0209061002030c0a0c0521031c110307210b0303030a2f09041a060d0905160308040906080d17 65
    0xc3e80300050a1844c20400c03500140b0410450003540381c0780c943e4010488240d40342c150f0400a523021030040c4030030400281c4603a202c0b8408041c0107021504103a00d60442c034086402c0904a4290560341d26000180c0307107410000e440c8210780407105030a01c1c08403a804260640400f030003c6008122400551421900034415620b07051240301c1201c40070619070500c2e00303c209080c407401d409030b05108203098403140c0c0c0c01c07c000401c4040000942c5080100500328240907210800f0013034840c4d2303c0b10000b880d6a038000041d03014803401c1c6d82e080f400440c0350107030f051940d0380c00d07030314025a62519540b030150303440110070740358404480400002e026091401041840c8042d00c160002c1e030b220f0a43c07903d52803130a60301401d0403100a642c104105198081441400800c1d403035100d61040e0300303025840c181840782c1c101529652090059400003581c03c0103440380004a0740044444040105051081d60203d110300b40080201d4801002c488001c00c0010701400d81e00c0c0c2640d421700500400287c22505040300d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 896667733 1250 896666483 896666497
    0x50c03120408070308060301090c031212020c060a0b10080105130b040e1b030c1f0903150203040201020118110f220203090d0309020117100905040305092b0b0a02 71
    0xc80c4049600d802d103811002540002d000f1004201e4801c003140303042c00d052054600d05944180d090344880e055864106003032029004540030003480740d51000c1201142e001078000a900700340103110904100e90000107442c0c05802c028025188400c00c443d80607440f61030903046503020354601d044110000c180c00702806484c0c8421360440d051100401d058500043d05840d03801c542c01e80031b0a88501d150406454524008180d41d2050b0002039030b400c0500c41aa82e4240309019040404002c2e0352a0b0312444a89407405038814026800710821003903580a0041e100400e06000310100070100556400c603008001083c2180560844c0d46201e480740c8629801e02c443c1e810440a00f8610727404144a280654800c035040803050140040c2c402415000740180c050030741c2c0c161a050841034241828180e61540140801b1804845002c001200342d080c0c49100d0069001e81e13030380759030340c1a80824060b41e00c0c1e450314003038448206003000da045c003410042d860456943c0814100c145443c2c0703500c1c1501a000d998 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 896668983 1250 896667733 896667757
    0xd03090b03070201290102060703020313020f030c0d0b0f0c12010b090a0810021e13030b04050a12081e0f070e03010207120c020a06030b033d1a0402090d03050c03 71
    0x54031501600300507040d82d184030170241d08070369113986c1f03101d003c03802c0c3c1c08280c0c0c2d0042d129400c0c2914200600e0300703640144011401804641784c0d17080440c000340c3c88060480c0f05440d0354080c102030100b180c0100b085c1c10b030700184c1c80b19218a8a00300c502e11170884030b0144100343d0a50340c04154144a5920011024020180c5004844e101c010704d42e02d1200035800088100ea514106040c0b491030b00400906940d100300c2c1c001c0961240300c1c03a545411b41071140080c0110ba07a030040440340350015002c42506032541d9115174405603546003044031800251032100300c80700541202c2c000c0120001e074032b49059502203d5441c14041000107c80807a0180c0100080102705d0310300300f81c05c00c0280341c0c86019000200d0003100d6002c0c1c041d640d040b0030f4044074689000c00750190060004116100500c0b00310750001010010f0b05404200803203115284018203400c4c0c60342c6c45889050f20300c01800702d060484803040040b101145050b510b50b00085010703800d5603009041c0040070820740e224000600a81718410219 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 896670233 1250 896668983 896669021
    0x1b06060b0406030c0311070303110c0d0302031e100303050a05040b220614090409110301050711280f1704120b01092f1909080c0d03090b03070201 64
    0x40da41480d400e4110340160700010780781c000320b030009034841e000b00500220f021450b1407414640ba1011800303841020070040c9064000c0016544200e410001c8059905280c1d070016241c0c20407007020b555a07030030f0701c00e8620400c81030024440c0403000c0d01c83d6032044a078142400c56569000c0d105c00d41d01030046a0207501110004900c02114400000c0322100c1d1650080e4003042941e1a00425122080d010b034004880450a00202c03030142025801041d2031401681940100512400041e0949408841213800919810301400b14034008003c0c04009426a81401680c1451220204000c13802c0c510b011f05200c546100310700504c40c14912955241802078441c550700d5485400111248168450898542d00c492000044004040c03286522036941c4800d50001c640760070082c83e40043c1d02c8242c81c21851800c10088030481591a4841030a428546600414914001d00e103410705401c421030300d0041003074481110019910042c44015258488905512526415822401440c400301c031032810f0616 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 896671483 1250 896670233 896670239
    0xe1510030b151602030c0303070507061d041b39020f0405040c0602070806012322090c080a020603180a120804060c090b04140303130b0a170c07031b0606 67
    0x80d441050f036900aa0854034202181014541d070b900c07403410083c0c400c0c0c100040070300041e80306104405007054482040d0b00c003100c2c0d84000608442003080c101c800038440310034010440340c00000a5100350b245000411914400740696040d8098482000c6804407402c00040e0455480c1000908000400f0300104100d2400b40b81c1024008210302130360000d032250031000101c640c00098402d05880d0320304416a20540150302288c1c44036003100016600c98848402d0b2085506050610300c4820715a92001c6440c5415040840c03880704180c001010541003140010003507281d000489030480101e000c190000001c841900d403c100314840000c2c903103080502c100c490a0790108030035014900509040041c0c0c9850702051310a49040e01c100b0090b803a06000c20803c4036140c0f03807162503021b00a01a28503200132218501c3c541103040d00004080240420f40380e500503406a120b940707500124040c007006042c11000c0c1c5a8a0242050003810010054029803414907803604c031284155015909200d0f66031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 896672733 1250 896671483 896671507
    0xd031403100303020f030301050a2117090f0f030d05090d0501020708030609071e0f09080303091006080a030c0b2806080c0a1a0904020c0d03060e1510030b15 69
    0x81d144019801445003a600780d0401ca0080112030403110010715045000e0300d00843d00c00203da1144049100520900e005c00100c1c03d443c00300b8004201c2c03801d840780d40d402107200300800800700e042028001c40484869401c6030720001000a4102c416080c00380d247c2e403454000482d0b0080015000380030f54004078101c0c08000c500b4014502400044030340001a5036052003c59415602040c1c2c0f24070310207250b0030100f0319400f4006100120f001e40c5002ea2006880e85034051855205641c03540c59030b07100481140c003459081c42080007820380740002c2d00441e4042d0304c000304003803414800500108010400302c1d0406640007070f204110000111804c6030080154882d4004000c54898030394140a00600e8900031710704800d0f001e00f81c4103405004207554203007422440040d00400c00c440d4209508000000d0b05880070002d100f080d00165802041803401d08214070b0310044c0140600345502503600c007500741640ca1075400c2031114150b01d00000c154108100040d41e842c20540008207107080028600106c04c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 896673983 1250 896672733 896672761
    0x11e020f18063018191b0e09120c0604144201050310091109040f0606061d102c0a080d0203071211060106030b100903020f0d031403 58
    0x580c00d48140680c07130755000b0f03072400d060002d452048015040240345a103210b442c04400c01010b40140c09440c07030380303019030042c01010226403c4016082401410880e44210800001c05e440003100b405d40e08288060a01c1c90356260040c000610740310140e008486001c80801005642c071b000c0041c0c13200800311000040364500081c417460847c0705458641c1c0b9910030255503549040f40c0004e4000d0110138002840341000303100d00c1d8400c50300400c440c00c054440d50395460f645030149000710303680d10fa40c10451a2540480365158448018800c1511903003041d51004d800240700c088007514940306403206140215003190188040c0925400303103200b480b0680d00745000ca08082c10040e9020740165071160002650b50300154409001030303204000305c0d800114503640c0b18901d9001d50408254844411010074203001e0309801c000d00003650758124008030b103070040040001030030a060510003107003190003262001c00300000c91070044080c11540010117205070001c91920300d541c0c10858481c101800803107505 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 896675233 1250 896673983 896674057
    0x10219020c09060109090b150c0d2703020607061515030c0302040b0405061309051e0f071e050d0e03041406120a05060f060a02011e020f1806 62
    0x1071181c00031100590038034995640c010001611802c2c1064680703140d45c07000c0e240700070000b5084a1040845920751201c1d5000c0c0010202203c05081c8103100d05600905039001d0080c4015203422400e8160000c1c1002d051000941c0d1301581c5050740c50141c0d0030104c0241460310210000c48601000c005045040040241c0f00700840355800e12002125040403800d9010303501840700f013800c00b04820821880d00000924070101a02100b0407200c0d074508000701111004c503058107401181e07802d81d040084c803400c0000d0303100100c001181d400b810070501c0140000c640111581c20644074561044100707003d0000d60707110b104010000d01c2052404ea02a40e1250403900c40c809442044200b282c04a1511750142d0343c41c8030701c00001810540e81e1003c0d400251001625040e0001800040804903483d060000d02c19030301e160b000442c48101c01d6190038500c0350000c1000c0780e006d1050100203640310441c0220791908011322601c40b5140c030581e001074124800c00104081208007062440340c181c1030358680c0001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 896676483 1250 896675233 896675237
    0xe070f0210060b0313020a0506070c090606030606021e25090606020718090609020d1a0105040509100b180f07020d0f0c03030c09230310021303080a050c010219 70
    0x10503002640780180c503107502403840c19080a00000317003190410307071410500341e0000742040300e2169581c0200d1981e9019910a03102021191000d200d0740480c1d014141c01040a03240c1009401d1800b02d009440310f1100701701c200c501c0c4004203400c099841c200201c486a000714042545001c201500c0c1c4e401359080c0f8419401158203008000941600106075032040301e010740390807440f00044500359030003406104022103495668034103c2e800b5890342100c6404c010320494000008247e41a0200f003100ba050340060300c903500b88000c020340c10b0008070f585844005100c0c800b103000070b05000050b0700c40603d10764000703803071060100308a940200302d21664081c03800b40d0259445203044c450211580c0d000e095014010510f6070a10318000b0b4800d501510301c00c606494491101519000e0411002928420861081001c1e140000c4540380074003015941185c180811854880c50011019203215144405445843d000c104000a2405002114018031600c0000c555a101c01e080e101c24108803000c40d400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 896677733 1250 896676483 896676493
    0xa02030d0302132907030909060f030302010e0a0215310f0605070c031104020c390d0201050901050c0d0804120c0515091e0106170724090e070f02 64
    0x51980b0300d485101e10185031301303203800c40c20103109007038650180d1050200300d040045a007000150b071071040c426100500719030ac403051001495400d0007402c0d81c3e17004000c8281d503006100c0c02001696130388510340307622040140c07154a406100001b0a000c80188146605050b20030381d0248421030043d0400e030a54480b605400301864480310111000c3c0160700001341481007540052002c142c91035a400302c0124001c1016150092608105050040403000e80540c0e400508041c86080820300e441141340d41c1e60240002c000751282d00080c4042d40085029041c00000185d41d0541e9204034101d8421030412802c0303840306981074100500d044421a42a14403070500080354035421302c21445c00d440d0640000040c1801d504140c91281c008602900d010498410040c00e443d0300341c628884a61141c0083c000040c40610305112024500003c003954051a080103000303102e034241084c110b16884a00010252000115801c190741c0002141c000005141d07501c0100b0000ca903000b015224040005d40c03c0c0e075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 896678983 1250 896677733 896677739
    0x150f072a021809150c1c06081c02060603010b0102070e130209130618030c02040c0e03070303030b0a0603150902072609040b030304050d0f020d17030a060f0b0405010804050a02030d030213 82
    0x3a1507820155051090445d0030010810500030300200e01868a0b15514000b8065959443c0d0303515003907003040c0e0210801c1070495550b443d6030301840001d0b841301059000f80181000b00c2d000039251426800703814212404040440c0c004110354048507485035000d0200380f59400d10781080901c010b9100c40c2281c2c100e003003241d6100c0902044140c1c203919941074650a1014155a08000c00341801841c06803c00c0845001c5101a5030100a0000250702070b450010380444000c003488514002070b004001418140f142003403039010361500d40b00448000d5040180c8400c114a0700740309005035081040304624400c02140818140da00c028124454210340400ca10b100e4031050540301d004078400c650740400d018030b580000c070300e4503151510b07028801003070002c0721101c5a464040d00300c007800d1a90140700001c800c0240c80402841020090708040391681c002e1841d004560000e0f210b54020705040150030390206041010070071100140c168003c040d644002201d482c014025088800015500000d80f1000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 896680233 1250 896678983 896679013
    0x2130b0307022a09222001080f0108031e070606030312240504020f0d1a030d051c09020303130b0901091e030305070201090e09150f072a021809 63
    0x203c01004020340311242030782e1601000440211680000c1c0c44031101d02000400107499030899070801a81c031171101c040c8091010004210850007000b503210000000014000940004181e603100c2161001440704442103404c078941e6400303240e80003410181044000300c01c054000050040c540c0800300c041064051000c0009110049031860f42d807410076001040c00103052680052250103000a440e610b808040007003002114404448801d60000150f020040c500d0240329041c10040303c1e03e0300318200400d401c1c034a044100101c082c2540030b41e42c0c1c2c03000c80031524244156240c0644103400900c0c4656a0b0028409590210a80354005401c0d0000440c1c10200c0f80d0610711413010222880c0d1005040d0b40d820745459100305010f9050020002c8000380c40307e00e1801a0340b1440005000d48146004000980c0b40100c000d05100c207144480c0003040f1155500160501c10740c1400c081e801e015104022042c03080509010020f900070031200c40744440c000911054074040c0b141201112a454820303060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 896681483 1250 896680233 896680303
    0x60106030614100e041802120f010b010f020303060904020f0d0c0e1305072c090c090c0a020a02090a020c010e0304030507050a0b0304080d023a0c0203040902130b030702 74
    0x158101050140343c01841130705240c0d12680501e0015414012101c280d43c00040700200100740c44101c943c81783c040004000028001d1081d00bc0c02820b14180300741007460069128007000f03000700c3c01084118002030541d690100380300da90010141000c00002d03900e04040040440c6806140d2601c1c0c41345010901c0d840109940302e28654008001e828200d04200c503550000c03084009409000c240100305240e07401682c01c0441c040c90000c00207001410702c80c003d100320764100510381055023000b032044000e001d40126074070389120703070440e008081d566030540004000c0c019039503400403561a02138a0041980e0010040c0140c0f4010390841e481599030702d080002501540c0130b084605a0203001107000500e10038040d0111101003130004d810610181d016103001c032001c00c00d8150444d039250140d82011400e18918000200b400000d02940651250181d41c0f032040b441074a1100c0da000a8107000501022074070400303858603000d4140e40f4104010001d54940180c03242c00c0d2202c4000110401c1e40512001b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 896682733 1250 896681483 896681509
    0xf0c0e030309060a1b14031210140d0f152f040e0a1e0b09090a080a0e030a0c0303051902070501140705010b10030608010608030306032d060106030614 66
    0x5185044d0311090b0480304192045c0c059025984032410190006e4502c010034035820660100842d00ea202074035403608003000142100090071802e0030144806000b5401007590035038281c030485482900c61400455040ca1041f014151146203021078007018099085805600d1000e40d40030380540d44c8003a102c10100607450226142103003080200702031140c03080c03007588c4900c0b814400902e9004e050350072074011954000302d03540c0076a141e044090364a40320540b5604880c0d002d004000c20b1025907100f0348140f150707450482c2800742080a854555404006086813550b201c45042070080e43c03441d028141d0b40058201d50000e020b00c1d070582c420340d840040c0c01c0085810503035409050080c5441e80512540c0000000e40d12075403543d520800e56240e4101c1e4604465180d6400110149071140d5542120355540040225400c05c100b4004242c0e0300054407420031414240d10341240f000054000750303601e0b5880118055000704000044d0168142d840b1008590460001c0e00c00f1011017020881c2c2c0c48074200e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 896683983 1250 896682733 896682739
    0x804080c190504050603030705010c052a0c0f0a0302030109080304060c0c05061611010213140402120a020f1614070518040b0c1c02070c08120304080703120f0c0e030309 74
    0x41d041041d45400d42016803c008040d003070303e10f0710705641c680381c0c01c1d22100084030010a0002444420301d110362140301c14643c1825a9127006150f808050585a107000d541841c0300c1d0007001d418814136035401e50128021036000300200300a50042c03a00e0107050300202e400747e40b81c0b032401100500301405034010b4100b50f50320a000e402a07a42c1d5051401c241d0103004a840100554004010600042440180b040c4107004440c003070346c180740c900780c160101ca103060498040d0b4018444c01c50404400c40d1115085440c10102603158441104446900e00a6411900b40e8890150b103910900003855600714880d444072003a111266114014010080210910b8090560480c40002c0101e0040c034030007900080203804003403030000c500c98955420404a0312068200354001656800c101d082c042e160010441e0b00d014060360350902040ba10203000040029040c000000b40e0341003010311580d101d09020540380010410918160414401065450b2400011640c2004030b50102d1a000041e612440d07002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 896685233 1250 896683983 896684029
    0xf0f231f060c05100f0905060108070b090f03012417030a08010302010c140f03270604120503040302040f02030429070e04060312020622021e0303070b040804080c 71
    0x101c40100d46004203041c0c251018052200c0d01059060381d40140070f074907030340b18070007242e0513020341007550070100180d0004109610140c000c008880982041d2081d0903400c81c0c13640072921080c00807a0140c01c5110b4040134068000001509411003406010148c0e0454202048280000e0701c0196883c40798090100c08a800da9004000540c802c14a0001c041d10489015044440301c0060610f000c00d04095480140c0020805c0c403081d1a480e608a6680c0180d6641c1008034103002001c00e1807485180900036581456195080c00d0081c1042210300555000d00104050427101e41458025041642c0c2120002c00000c4000300301500c2c510900020100b41742d0102154032104000c0d6a4400810310071500b0607241c59000001c01c0c1d4003000040d036075515401500c3c40c4e24004082059489104203030350400c0c4d191100503405030300c035009803042d0020f8441c1d480f1a01040c190010f4950f0041d5207005144641c02070400c020000c1c0301002d8000c8030307501030803a000200540104010302151220003c0d101d0a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 896686483 1250 896685233 896685239
    0xe030d231f120204200a0e0a030b011a0f0309100e0102090a14030a0c08010f05071103030109021305090907030302010c030b060702060306040e10020309061303120f0f231f 75
    0xc214000d182c1c18802000000c1900754489050000000d02d5850344003210007042e04919a60002ea4020b1a040304440c000d040a065540f03d003140c01e0180101585101d908100c400d1800742c050441340c0e504000640a41c40b0b00c2e2111100b0769a111407204503881a0400401d54142030050003518511000101600308450900c0d030108400c00d40510140ea042c850a0350250203e02c00d90380b10f10140110754004940317020712184c071201340c1300040c2013a03007001824403038043c2142010054a055584091015990380d94444035070450aa99402c8650701000c03500c01c1c0b102014002a1181c1200d1094000384090005d490701603044500800401d0741000c4200040310042c0340c000c00856100c134000300005505020641c0261030803040d003c00420f10b59002040c0032525004200544d480700880c00004840c80c0d8503a0024499034850a100045685452400c01502e45540203c01d500c2c09140e0100650320b40102c0e5141c0072201c4507129078200c0700e9600030070024452580a034042c11510050510180d00e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 896687733 1250 896686483 896686499
    0x5010c12080c0d09080301030b0c031b22060e03010f110406050c1603081b0a03050d090309080d0228030905090a0204091a09060d02090a0e030d231f 65
    0x500103060062080d000c1004404114180c41031310301c028011a0070036101c1d0f0461030002c03800350780602100f000010a008103c0c2d40070440500941d80c9100034001e98540350544c3c000128a440301b0081c0c2206d2802550104041c0e074011601c3c000c0038000c44c0240018050941ca0700200d851a01d21200f103000100030600407240144001c003020201141224a85c503080722144052801c0c681046510000000341c480c0040007407182e04000f10300140144c42000c005940c0500031784550040501c841e51640c45030014540034044103402080440240c4207000660724009448145200182080403106084659008a8200d020100683c5030f25002c405c281814100804028001e040b281d800360208400300300c120250049030380005496807280c1516a071034040045c004170080c0070b60300811084c4040c501590340c0c03d075141d0300844c84840016201c1800d098603411441845071118080e03044c410301c8189041680d00d400002c00710090020b41985696071500c000d076081440d400000d004c04407082c00800c0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 896688983 1250 896687733 896687747
    0x3010b010e10140c030c07081e0a030305090c15032202100809070906080c040e06100902130909080a03050c030403021b2704020406050d0b010e06040905030c060601020705010c12 78
    0x5808a06202c4c200f00030710019a1866000481510b61504160400c104000b03082049030b0b0014289400070300c00080c3c0f20315a583d03032402000040c00305902e54010564244090014820342000a0003144050800eaa039103101c80c0e000f030310302c041c803050000150045103006400c0c91625a500030329184410007126021103540f403011b07000003554061200d0005a0150030300c40c00004010900103001556002c4041000302c80d0606e0030502d20b0380141c8200040030350000040d80680d050140c0041e00c50042e640c2d0f140c2010690340014207101d141094240a1085000103402e494095950a003c60384e41c04c0182c85060005550080c0568410343c0003100301c3c480418000003c81c00940090080b03501d0800c5d04000d20742d84441c1c221440e103100300f0b000550400340207280c0588800cac1c039a6186482c1c01da9428403518014456814074100120100310541e07a01e030400c0703841ca07800108a948860000300126114202a1122405445001d100042c0c65000e2050004d500d40c00500c0130221101d074140581e440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 896690233 1250 896688983 896689007
    0x1801091104020903161404060b0f0912010f060905040b0601030905062406030403031b020304150c080706020c0d020105010e16080402150406030606021212160302040509130203010b010e10 82
    0x18000d1083c24000040f60311080b03002803140380071b082e44003028032091008440c4243c22134104044104081c5415248450071280301210aa0360a0407071828021480d005285a037042c4003503506140c0300042c403c0460b00514021802000000000d0322040015030466140704002002504041c0014800501f01d005811020f101c0410b410450b260400010b0920707403045070200c000c26904d41c0c2c202406151007201d0910b2020f903000541c5054202a1565056900c49040300104aa003901c50401c01c90341d2000d50308416400503055440300b0840446035119400c582421004bd031030708000149004c107508625000328215400103400098200d4102c1d44050001c00c166007085c9084100d545504100005000a0640b542d0020341f542c14400000d081c20303c119500b00200e0001d101c235000d03449010f00c41c070750014075000384080c400700c81104c01d602a01590f40440d40c480c52304401c2002504030701e000200124401c40080140d00305440054849556615010390042401c0b4420241d10303004445070091 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 896691483 1250 896690233 896690239
    0xa111614070f03080c030f03010603051f0e06120708060403090e0c0702060304060b0d0b1006031a060a0f120908070303050732090409060e0706020706051903060e090618010911040209 80
    0x14011207d206503031135600070f80c00701c800266170f103081094400414800a81c07040d07150900e105c1e00d41c503210303203140280e0005d044180706400b01d1309030f0980141c0412100e40200010800c0e03544901e400c0c240035051400354401c002140740b98000103508001d80d041100c9103294010b2600f8155115901e440c401130841c0b5803826000582c00030380c8000702d0550008035103e8074580c0959180743d07042c01c0006040e2244482c05490065240400c8402503a40006541c048001450012412400b4040858014045188482c1d2042c1380c03401d80014000040000c1090b540280c500381b20720b031a8078000300c9a111400c150b0300c100c6004141c1c41822401c9a00b242d440c59220441401d00b0801043c00040032200c595004446080d030710780104684546c00d114884c001d20b00c9001070441d003803030900050618800e6040f41a008014000007182d00c0340039174010409403031107410b5a6903500d800c4d0304042da2100190790714031501c442c0065001c4d040d00c0501403000c2c0c495025400300c102170b18007814000030303402000740164 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 896692733 1250 896691483 896691487
    0x15041101050c011d12070819090e040605041109091504030e060d1e090b0103142b020120071e02030129010c0201170a111614070f03080c03 61
    0x19681c4070074007444002005001324003a49903024215a440c4c80444201070408170b8080c801d500c0400d0004040d01d6503410031a408800024540c10110b41810141e0040c40201c0d00000c284014811180d105900c01d0744500c618034580e01c81c2400700200348804480c0c40800341d00c44a0382e44401100300520b40d030414807030700380b8000b501c1180002810a400406e8a0700446944010310002280d02e03c42d904101030f400c04040240301c10340d071a0040e60040501001e00030b2020780315241030800b810810701c0c02c90900c0603920b50541c480d0304000000c0102c110f0380400192709000d4030001d48100c03a000070f4164814000f11510b4800b066490404040a00c201c1c50044a1020880400f5803000c0c056070381c0c0c00503d4241109640d00c0010103140d201c2641c03007007071304010741048550b00507600a8203012800348140381040a994840006c0b1000c0c1410040c1e00c075070700401041e1950a0100c10310042602d40c0300d001240ac00c02c03406241c0e10350b40c03d210f1055144003505210100041444003004281210302001568 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 896693983 1250 896692733 896692747
    0x30e01060e07120b1c17070b0408070c0b121e10141f0507150501080c0d0602073c0b0f04020a030c0609051206090a0303020313051b03010e1504110105 66
    0x2685c0d0180c003400c0e44a24150491a4010010440303151203009090600301402d2907465141c580c2040310080000303141100010702e10041c480001030030b1300201210351040c0c2d0b40d07200344841684806001d60703941000050740c4045012568030b0000d6144504407908001c0c107070501d4450302c0d103131100881d1800d5801c00c81c41800500b114407035030301132064100c890b02c80030f07a41e12362494010703600d96050007442105031501006011280e030104070b886c040d090843c0d0f501001342003800c240e8000d00c0b030504018000004901c500300c0a4a94100517400c000c0c1c00300f5000710340810940013a2004c0b103002c1000b443ca5500c1130020b510040b52000e66a0000d001038200b80320742c3d03103941e9160b4100841d600004040b88015100f0481c83c03509404c0c10050402e144040c00f4603081c150310440c3d403100303074400081c1415000b0001808420986140c80c14858115040355641500707460345c8146502043c0915001c0c0d401d105140d180588001444201070080c81c40d0001250b03150389816407441c102d0000d480c10000104880d03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 896695233 1250 896693983 896693989
    0x260109030804111c0c03050609031e0a090b07060b030f01090302030304060c020c03121306030b090708040206130902120703051b070c0b1b0d030e070e0402040e0a03050a030e01060e07120b 82
    0xd1291389200c0c149000d0000d0944c2070440c6043e400900c0080070758410801001911040f40e03400b4030b2200d1302e00e00c00e51501d441100507148e0b00259000700c4132484001c41c41800b8012070340c00c000e8801c8410340560340c0f60341c84c0007502c6099034801c0c8005000b40c0c2c070400200c1c000880950190324110258810344c3c82100c0c01400113820700d07210404900c001100400e801c883d0306000e1303603545c00620341c0e0b0a00300f03d10035011000c00e0078290300801c10414000140b0004007952980b004598503041580c440840690300d50b4100002500702d0301c20074088101e8840003440c0640030344203650146c0098086400c4100c2002c0c500c54495001410440d41951803440c00203d141c0644042c00c83c1401c072003041c2900c4140c9410706813426074244a21001c150801c04e0300c0e02c0c2e0460208101083c0e91800b50304c04203607603075070010030080c1c01c4000c003c401521403c1d0144040c9540304e005800d416010f03560a100d034480d001035290a940700c5004078a100200d07400495030311402082e458903406031804010036580016400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 896696483 1250 896695233 896695279
    0xc0a0b18090f0106090503032a120d06090b060717031816170a170903030913022223040e010c09090f110a0507020102030c0726010903080411 62
    0x144402040c01c0500500299400c050740e1801b401c4268021824140303080c81009043c150744908083d041c01060300e010203078205200050400042c0c110701551480ca113601c1d6001481503124800b00145801403590b21842d10b4003c035120550440d44a1a4411526600e036020380c3c00684810f8041c04d83c4920307082488410301914032400d2515210410242c03405901c1494980704080100c201d82001c036441c0001004000c03c1074401002800e07440c0c4551400020038514402c070840c19502142001e0a050520020340040504079105c000c640d4000485210342e4429407128000d181950200301c5400d007440c42c1c3d122070781081c0d00000f0f101185103c007180603642112410300d1944005600301009000c849041c1c0101909170f05e0207902000081c0004a4030b08880c06490344020810600050800940e8030800a490702e48007550113a0b41c0e030580c2d07019072081d11625035205a099035907140c00b43c58202c006119007951a0b0300342e155051580d0301c56540c0381420907046a481e030301500d100079555030b802104031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 896697733 1250 896696483 896696491
    0x20f070c080102180105070c090c0507060615030c171b04120c060806031603080f1312050d050f070b09071d0402090a050903070f050c06070f0605090c0a0b1809 70
    0x10b0356584440c904c81c02440c408085a818000e082202c4030001d54650500421a00510302c0003507401d121203001c6034148a1000c0c01340078282000d00228034180c0310050f50310300140c80c1d1020008000010001d0300d040091201c41c04107103a40344000b40030b104005845558900941010526083d118040720070f00b00c0142106484603010324800344021600b20251980260040300142070050300e0f0020544800224040100354103c08690009a6010081a42c0c3c540b441e61003031741034540d11181d05003905800b4460030307550391140340031403401d0b540140c040310f003000309a01c1c80d00e203004219100c1002c8208050210642445081e600081c079004008c00c4000e481c4518001c1c1c8440c0c101fa0042000401d0003030103003152a807806080c0a1804000011101403c0d8089800c2014108604140f1304008403400e021390080e20004000e0108422041142a5284200c10400c8952608124503903074030740c5001182c1d00942c03100c8052120042c0c43e00a001d40400514001c0041c1c8128404280301030b13400c0ea = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 896698983 1250 896697733 896697749
    0xc20040905150c030108030a2f06070e0a471809010501080103030c0606050405011409180d0c050a0602070606080d0201020306030c01081f0e150f13020f070c 69
    0xb580201c014101c0161903401c000c0c015901820b40d4104200070f078a900c07501003618144100c0c3c4450b100c185040312498215040d02c041010710808450701003a89601303041700c03180001041410040d0740c80c544181d04809a4043c0308144105c140b0261400400001104a400007444650100115940c102010034107002484060a88410b00d140d0311001c070503088002d103840752060340c005001c240d03804102541100e41515000400c1a0141807050092501d5040309421a060000108010000c20781030f690081003603407052800c0d51085001d4881c1a500516825284c1002030b05011981c8910000d218007800b070701c00c1d070391034509550b6131104907806102e04a50b41621503c003086016030621800396000c040d400294594944080002d0300c81c0b20f16400b10341404070b0200400c40c151000001448030701d00d84031403042d080d9240c01603400302c108101c4126003c101d100c0b004145d10b0134184004442d0010217014041021641d0400b40003a40101e298640d018000703000081c04242c4403603200380200145 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 896700233 1250 896698983 896698993
    0x2030d090602010f201308070e0402120c011e1103121b070302070315020415030504050601120218090309030601090e0c0603070509120c040e030903011b0c20040905 72
    0x18040e00f55030003d4003010250f0b2410b20304004840c0460b1041d151030301c4d4403441d10b68131b0f00014600c00c600c10f001c2d0040e050f0382c0301c2c001003c0740117841c1c0740307505000e98000c81d40088003600390100243d0b1150780e005014006100b0b0035800d40c0a00c00005000180929400d282802c008007807040d600d03603089480d50140c1c24580d0780c2400803e60200440c8001d1144600c8a41c0c80c0071800e46010f542c3d00c2d41c600c4014440c4c401c5403401d5507452080e0381554094840103500711000408558010043d00e026581130f1781c0350007850700006041900107041c0048943c00780c4061442015580c11040c0e07181c005004c0f06003400100007103211540c2c00c0c8400c40c003820000500140040b040c0d038049d803401c050b041040e40103442c200140708410380c114050b10a070000440e450000345110721a92401c1030303181114150040d0600c01c1500b41140c02001802c2c40d501300382c008110021007102e072803800e05400700340300022074060300b14040401c05805000310710449440071a107101d490344022500311003841c0301c01d641d40d03008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 896701483 1250 896700233 896700239
    0xc07020907141210050405071e0504030f0b1506041401080a061508010e010803030c0711040e01020d090b0f0c190c080f120f0603030405040902040f021303030207060216030b070c02030d09 82
    0x581001c0d8130141030103441c01c1203145003004020b845000e090309040c8003020110a10300c03942c2d1103203080310084e580c01f8400185401070b51900c0e207012030081c2c5107500071903004203081d01941081c205903400c9408070b540f0f414822070124011b45081101814a118083d00e500001c1000410400182120740141d9500c020661500588010f0f041c2c0c11303008913085400420a0001c034004140c1521021782d00005c0010211803050001000ad0418007c844141c0d4008204514046040e502c0407002c80e0180308001e18542e02c14a00000400c1d0450318000c100d6030a02000d00d070440a0103610306811024103000308440d5968680c054550003038034154034103e2000610000c0a24158581c0c0c0e0081d001103044a1142004030009403a03001c2d07801014001c0d903803540760700d0565480350850310400104450855423419a40350986ca05440703030000ba40584202200022081e01c0020340e00f41e82c0500c50b01040016041d55250100300314050400801c00480c060890b025a40a01083e4507120b042c0e100d072003100789 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 896702733 1250 896701483 896701501
    0xf023a0c0e0d050d110d2f2a1c11210109030e01020a1502030a1103040c03050705010219020d020607021804060b060c10020d02070f03020606180c070209071412 70
    0x1d1051440c0c031140c2201b45039544880e0013500c1c440b0100002150001c2102d0101c010160802e88040c420702a44244551003950440505400d12075195964604042011450500160302e8051402025808000714680040342b08a000c0b044411802480f40b811145561181700c0c501c80c000c008044141d549400e60810181c200c4000e400f42ca800380040c212000c1c00e610b41410a1200082e0349034516000000644120301a80c001d2030381c40300d207501142e06c80c18241031030303141249640800c90300d03440b0313088021816600001d00c68ac84030f000640d598a030340312254240040b00410700c6003203030403040501c1500010382d40c03002140ca0303000ca074000b100050300d00303402e290003540e02520081d4020035081015409100c00850b6000340d180c04402c015039180d0040f6030301c1c0001d100f00c643c00340a03200c072040b1003003c02d640402e00c54062681200c0b081d081d01403d2811340d844001c140d9444444401c10413845006040c1003070300946c86000d50410110250b000c1002800742e03803015040b501da0072820401c11103008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 896703983 1250 896702733 896702747
    0x7020303011d0105060306040c12060308120109020c0d030f110304060f0507080702100b030a1205040e01090506130b0109171509031809040f05010f023a0c0e0d050d 72
    0x80905046140c079458013020418500c000782c80c45015a80300da00a048440c0180a032000c0f80c500c3c0c000c00c00000766281041c02c0e40341c016845d8000d6203000400009a40703100b0b03000ba01e1034146800d0140845100e140b20907801000642e0403642025100c1030100c5000e81c8460207103104a008000100b0200b891482401c200c03803006050700c00f44a140384c2400461303540014440702d000170329900000c00134001c0740001d2805142800080044002c6014602000e5104010b00101d582440c0c80d00c18590300d0700010b00075038904031070f4184c0000c0e419086c9a0010520b4208107156801070400180803a21507000c02807112400011100d581d00161070400c45444004856a02010000103142801d1004030588070880030003500920888aa001160600c8282c01c8a50240366105d0000c00280f40310340851000307504940f154641c2c042c481d0400705003481e0040340c030100d030703400500c206805140c2c1099540300505143c03003c0f1040000c00f503180102d98554036000c00030280160014000902581c600412003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 896705233 1250 896703983 896704019
    0x100c030b010f0f0207051e030726010605061c0b030703030e180103080922090b0114030c0310020c3a0512040f0f0602130303090506040308090405090708060702030301 73
    0x1010104214a065502250340c03400d56804447c10b1100403100003921054446c0b0101950b490b004100300054030140340320070302001c400c04003e0b810b40000000c81d05402c03680144241a00800c08009180c036060106012030031080c46614001010401c0c000441c0c40c05003150401c802050308520000b000b850644140c0d00f801c6103e0054202e0740d0f04580e14801180120182c1c94040c0c0340f0003090345400203000d003411810340c1c0442e41c200301907015400c1c03001c020071080c400c3e41803400042446030007130300300400c066510340030245c01020a503607020440c00c020751084a22070481d02801e03171402c142082c0d0599100c40d566401902d052200060b03551a400040031f22001300c28420304001c005030405800306240d50158100540a00203402400c240c200d203120b4240040401b0310024441c0d8040c6400c0103584142ca0081c0e1310f07111055101e4040c0101b61056000c050b00c0520140032085075440d183d000039910070b0240c02505d040b10f541c2c00d165450840c060f120a40540c101000601551044404c0d0040e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 896706483 1250 896705233 896705237
    0x41506050d110f10050405090109050702061816030c14010516030815040905160902161b030b01060203041815090f14070207031a15060c100c030b010f 66
    0x146440c000015074544030200c4002d0007010320180d00e101d00d556407884441800405020503030b0f00ca0320400001c0c036076806801200e114a03070150004c00c02003041d1082070311401598004201944400303000c0c010113050390040102502c24980f07408112600080395038000c41c4901d80b1900e040d4102802e0324410a00c4409042c10071100380601d0440ca0100740c2c4041040d80c140c140340c690342e00c4da40550f2052044100c070503504107090004450400bd400900701881d0701041c40f4086005481c1d281e2003080e07115641d40000ca1b402580070940100d6212030303452100c5280f203840314801c113036641c0d90007410030426403100000d0b800200c0d003001003410600801c001444440300411143c250301d200c3d41807a100b14000c0b8540590b0b00e03d99008a060961700c030038582002207104503007030b2408020080d6608000d01017101c1d002d102995055401c1d0b400d40000d40600e404000102c42000f250040c03241e0342c0c01c50f80e183d071940e20a85068a002112501c1021501c0c047c581c2d011500c0b940388000945144006511401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 896707733 1250 896706483 896706491
    0x17030d0605041812090905241522090e030901021e0d120e150106020114040803040b06060f0d09020a35032701031107050d081e0702060415 61
    0xb0b8820100d4141803c05070b1006184a00ca0703e41982200c040d101d54000d54502032804040c030600c0e0b0303402c44502c0140002050b48402d2000c1d80070600402213525440440440d02c10711025078804520345001182c0c1c0c400b26400070b501c65498680b00242d420440524030780e0f8000003240ca00c6541c0c1880a1610400e10031240851000c100d5120395071543d00d8503203042000b01da02400035000c000c94010f1003002654108940790b1809040030090002801c0c80b030040550b20300303801803411800c140400b5100d1604601014116034403501d13659030341d20000780f00560040d410014043d00303480c58000760215603004c2c00c00140902c242e10601022803050740020405d003808441e540c10b2503003811623025843c03180e03d6002ca110b240ba03034032043c91030203408440c41413411420350840c81c155440d17a03c0c5007007400c240d805100001034180c2044292140340c1001d841504110740c82d6106601a1044070380020501510045000705c2c078850901d040e0301540c41100681003039040c041800381c140413100c40c052090900704 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 896708983 1250 896707733 896707751
    0x2f0115030302100203220309151b11042706230411240d06050f090c07150903020d080705190c05070801111c0903081503010617030d060504 61
    0x103569540c0038003c511850350000005400210700c00780340c800c541648141074021540030325026101c2c0016000d2040402801c883c00319240b44a04402c2d618107481e003200d10402c20307654a9960f000c0100c0f0341c0301a04561645010480301c40c2071413a034040200d0060300079010b4040d42c90310a06a83c0c9403110111661103100e407400e11040c0c1c0c4030310070341c00c25800030240440b00325000105600d507079a020b100d0b00091000480d81c90700032403203008107005400003608202c010380b51400c02105d4000d0610080e0070085080c0000c003036048007001020428060706044601e108009045016210308000890040c0c100141c2020346e150800d080340d0b004101c0b402c01e2400c01c410182240c0481012040e04030803c18042e070302d002449400d000040143c00b034503009114400f112004580154041c1c076102c0d00503070440000040000403840b4030b180055140c4e40d10180e64035580c4c2d405981c1e40f101c10b00b0503415580c1d4080041c0340348680444543c10540391015507140e00d9542c00300000c0701c1c02e0340c0c0316501644c2407102c08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 896710233 1250 896708983 896708987
    0x91611070518041a130303060e070c17090a1409062209030c0f030e011202130e061305010f050f0409020303030c030718031127060f012f01150303 64
    0x100c4001903910208910b07503030b542c0c14004c40212181c8011150f0300280c4045c00501000710940428203030282e1403c0c01465a0741171030b02d110b06800c84907900040e1803070010000080d808101050141c03003000300c1c18107088480000904098240d440b040f40c0c4170580d081407eaa044c00100564030201c2107039901d001541e400c1900040b08400c054a004456540c02c180e400c0501581c154180035401515038101000c15181c040c00600070148128007241c0071032a80848441507008a96001c1c1500c85032031030440c9000000c0d0002e00028002039800509006241c501021a00c1013900929103503005c1c4161503e00b00c04c0c00002e0a007003884d14082c0341000902c1300581c600001720ba81100003120466a00d80d16108215510100410642445429480d0000a11128004192a259044070310310f0b035140402040520b010b01d03c100407140a902d200014105240280b41c400746407c0604002400f030041c51100031103001d01c2c00480c2103e10010072207031a14031091013005501c20000781d800501030300715100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 896711483 1250 896710233 896710249
    0x60d020312043003440a0605091006140d02030901060504050105040902060313020609030607020309010f08060d030e01021e0f1c021f0209040c03050f070801060f0c08090916110705 79
    0xa40e505001000402e5040c440d00d001c100ca00580b0085142045424541c05c5184005c0e410f88000400d10704200c0089080d01d44600c1081c040e8144000c411045407411506595a01c1d410340d04298503074044c850324a9054041c00210b02c9806184000507001c2d0811040004585042e0002c9000b103142041c4c010050f220001240d8024070848030039000390036548000b8002e88600a1103c2d01805040c0901c05c02a4000000d0f0843e100240c86403a902c41c3c086070211441301c0e003194030070303480103c80806030080713030180e041c0c1042d03424103105540b449200600c000c6004180081301c4103203948076844e2345800c1542403200c0c0c00300050b40845100c2c03403088030900075524801060f5600c0304030300b403200c60394440495a04444100c0c5001c0c1003400311610141010740201000c84550b003107007180d074000444591240c0c02c1c40303058032a10313111490342c043c40000403241c90644100c126280c00080004034610744e1580d4801c0d1284c400114040b9a080c1729120080940080040c05103c0b6032016009011990741d00322 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 896712733 1250 896711483 896711507
    0x6021803150c0a0e0303040803160605070813020919061401020f03030106050a120b0904030e01270909020a0807030b0103020a0803120c0a020a1a0a0605030f06060d020312043003 78
    0x90702c07686151444d40002e04620603a40a81414480001c1e10502c0d11480d02d51f89030464015541000240d4030010140c8800404860150030400b068405c10010b00c2d00f406896048000900031002150440d28104200c0d0810340000c0160300c42c0d0b010b03e880329079041280741030340702c80d45000e0740c00d552410001802500600d0240c1003840403c1413182c4d11154076a01c84000200010015601410181405414543c2c41203800f400184030184512081115044201e4841851a4a200c9841c500040d6000070201e811003280e0203034003805c0002c3c1c51001000040e010b18000e40e1400303555491407042120380d40b4141c0c4480c1d42c603041840041602c0384030301079844d0f00c540c005070b0055903400105000c0703041181029006045069407101200403242d0a103625208500081e420485640c456040560f40c0c1e02c1c1883d2108554040c00001b440b5051540e800d60380d0a00c050100c80e072180d1190090301d880c1d0030503000810750308100e14200005010031520080e1040d40120b1f0b000754070310107890082020020313036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 896713983 1250 896712733 896712737
    0x1a0f030f0a060e1002070b0601031a0d02090703140103230a0c15110f1b010c0b060d02190305030a0f092d17030702030607030b01120b0a0306021803150c0a 68
    0x290f2040c0414000e00410713011000c0b4040840d95802d5510f040038500606546460020f031920842c82c824900360391212810240003000700c913071034107103a08000c405640140030344100b68480d80c0307110050b2155114180a14407074584107050504072034000800304010030500c2d441d9030004550501040803984e401064034200783c020700c0d0704280c86d84182c4051003c00360407000d1b8440c0704003403505440d010a440b02080d081402e017007000d803201001140d005912a1010f0411900c140204440e0b00c0c1c03242191922510140c140424102c25045001000b46107502c20303a8950000180c8180840d0320000301c221032034540c02c14810543c01c15086071020b40c111207020311125101000745803803a025420120041c59500060140d00c18400215500c0f80c00c2a075049000b440b4143c0810300c1240079004100626a040c0d6940c0c07040b1125001420292030f403441680e80106282e20048086005d40c00240f417201c1119045404000c1c034501814030700007445560506000621040c4070b2006003260032150b0201c164 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 896715233 1250 896713983 896713991
    0x14060d03120b09040f0b0702010218010507060b12030d061e060e210c011206051c140d050c06060414180705180f01060c051e101a0f030f0a06 62
    0x601c1400010400d502078203500c00c0c00341040000700020b080c108244684100c00004203510380400503030030307801103511108401c2c0d91390202c52007551060024012540c040c03000070071742c441e50740003090701051a00b1003405142c1000480d81e42c41c000da40145802051180107420404092070010400f06426003d5a4100070084040e1209695a43c1d108850308400c0c002e06c0d002040300c451555980c41c404584c40380400d0180d0040c48566000d44243c1d4201c54024280c4880250030076007060b07040d1786003602215000d60302000050b60004c04c11416010801a844040d035407400b90000c0313441c024000b81102d11031402d00303070001000403c0d102d800e034100491915140d410b12481d903587c0d0415510f90441600070100f0703010b0449500f0f0b181e1a160180f04000c041d0b511903602d410301101c024400c440041c1c126400850310200c003042c0e45036041c0360008603e040c0d0305540c103904c2070710b0191155452407107000341408844080a24043c0c003146612882180100ba52804000f0041d44840281101521507035036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 896716483 1250 896715233 896715257
    0xf0b04030b061f03021b010527071809060f200d060b19090f030b040813180b01020106060207061205040c0305060a020403030e10023705030304020414060d03 69
    0x2071050f9141181c2c55030301c00096020402c0100400a4004041a0a40c41c203442d8041052031418440d944c094114014002550800e04509081d04040204d1106013441107010006281c6100716402c68410b440020200d1407501c01e040440640c1c001c40d0401c150340d80f0707084c2920249503000089465032014040703107503110300d03850602c4001411594401c40300d400c000982000c0d15040c00f1841900c0030700769200c60110b940c840000800d400d00c20700004100e42014000308000c524040060b2481100700c904c2044125204c81211051802c190f101c111496103c605880c075079030b020701483c0040c210343d200038400c0340e2400340010002c01105401800b200c0d0740703902060501c9603d00750700010b10740100864510b4100660404029072082c8419800615143c001b1501887c205001441000d0158010803050b90002c030944d1042d04802420070403181c0e02d1400d84250000d8a81640019000310050f64a0346003a0050200b9039662000c1101c841e0082000c0110541e6041c0f0401c070102c1d014500800e0403c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 896717733 1250 896716483 896716489
    0x1111009060e030f040504060803040807030f0602190f110f0a03120902300d080412020106030c0b040f05031c08280603050d0206060a0501032703180f0b04030b06 71
    0x10b0b24424011140000540003000d01d0842c1c00404c2211002e54041017815510102a6103a000c0d60265070030940100c3c400300081900c4564000c1100e001e43d0700145804240240b003550000029030401c00b04455803415101584c2203002c41d80f90300345030000340140503005a001c91f2140b5044200805200c984070000b010200c06502c0004071a6028148040341440d1304c4051401c071004c00c80c3c4c80c010300c0c454406034001c0c42021070048100030442d1601c915940311030b5908101d0b18450a96030301103642e03c1380c00101242068407550002e0040d012130503a554288a00038081e44c416401942c0244d001d00002226890303081d600c6000c6d68214a4410016107455038000d02d43c2e0760707008641c001243c0103010002045281d41c004401c8a105e14221500d82458042c11303611040c003211300980c0030003444402c2002c0e5001e900421032800205044528498484000c130803040c2c000b850a13000609412941030904040000c00c0300907007900200601280d1400100700003c3c070031800300419a01010303020900c923403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 896718983 1250 896717733 896717741
    0x6091a010f0f050d02130f0f0801090305090603090c042a02010605091b131d0106020a020d06050901090b16141207230a0c05010c110304090b01020a050f060709050111100906 76
    0x180c4406c40c48180c15542d01c20006602c0780501601110300c0045800051280f0140302c2d105c841d5034141c807081d0030454590304121490304018800754107400344440c042240c1c1d0700c51050038038914041c1e10107101c44a1354090303143d245107040c001030b081d0780c5005000c0c401548d4002d55107a0042041003c44100c1440fa0103000da68050318198205821f481c5c2008141c261065011f0f060b001c407050001d45650380e8500d0b08a03503c0070041d4000c0d4010540d42070a4011035015044154400b250301c00210300b14040359940100e01c90201c0b5007044811703000c038403801145d6100490621700c0c0c1d50040d03036500304018102c1c00030340d80001800c400140450301c1103807d50511640040301c14201490726950316202c40c40303c0584031216240c0101d55a5180c003880090041c02440070300d16031420324005609140c1401030403c0204060701406040d80304040f11100015000c001e201c408940d00f00c00b8003441d0030104030207030511041c2e4020505020001e003440c40b00520000d143c05842610300c2d0003058500090030004024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 896720233 1250 896718983 896718997
    0xc08060f0f100e040c032901020f030f0702031e060f04020d1712070504140402090414100906080a2d0501240f0b030103021302040906091a010f0f050d02 67
    0x88540e00503040070043d00400d140010f0030050382c080c0040030b03a00310103c084460381d80c450101403c0045860f90360561080303aa003c0450306004a800204c03a80300b02c549144c00040d0010a107000000d4404210300f0140201d000000c1c00a94000c41d07403142000b0303140c441000915144100100c0000507065540c0c4d202d0410b910381c4c1000700f010740f80e00840c41e04201548194980c1c42e03003180f4203000c15052ba102e03200720b50446019040440034180907034100700180d8001600c0c235a110f41c48156404030038200d041884c0c0911040d448000d8400d240852181c16112580c0c010805a00300e4040080410305104502c0aa000d400740e40c0c420592003088981141a000c000207421036203020284007080c0039030b420203a44a082401c681d02c61940c3d503138804050b040d2602603c01c01c24420300040005041200304001456101d2a002d0305094450302001c0403120031741c0c001385c5c2d0707181c4441c441803c900518003101b2800d4028640860780622640015001d41e0341d4100100410800040c0103041c0c84855041e1342c81c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 896721483 1250 896720233 896720239
    0x40e041511040905060301051e130512030a0e06220f05010e06070824030d030c140a0804021e090c0306060912070305070f06090504090c03020405040302060a0b040c08060f0f 76
    0x102c945554801000301400c6038540d000398607050104501050040f000c2c030050f0003001c800d1031244c0d03855030188842c29003003204450758421501600d800700d1008020314800d0f00c0c0198005144d80182c041246070810140c00600c0c0d110983c55001c0c010140850320550081e00078107105d800e9003442c54003d00400110010003407038002c880a0050300e9510500c0540107a01c40c0f40c0704268481d0150b9803507028010703042c0540e4154808a522400280a50020074040009042802c0d480705a2003426106a00c04104000080d200e00100f10840c03501c0f41d0514603048846031180762080800011602102d409002c200302c8140c00300c001405a500d0b10110351072032030040d10b0804a120f0360300c05030b030380c0e0041400222aa030242c1480440c002d0000380040084582940d01c08074001d1070801800010401e01d8019100314142e0071010001d030300c0d903004640c000d500c07030b80c001c0005141028012040391101c0e0709040c815401c3c00c81507a026a4802fa141e078002008484281041d4810b0f4000364000204155a50b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 896722733 1250 896721483 896721487
    0x21260a0b0d061d070603020c03090907030b12030a030f27051006121101020c0120070f1716080a02040f0902090c0403120219030c0c031b0812040e041511 67
    0x30690f14148040240c101d640d03084a003034a4440200313030240e000d1244080010351060103c0f21709444e081b46884d4109200e4203000030381c100d0500100b20090807580303840c2955400082d503041903c0d030502c03580d00203240302c0c481002010f01e038680102041c03509003005402140986078003818020144000c0003440100c2101700031640c1e032074503040c0300524280303020f0310640780c030400402d110350010685400042c4144d40e442d034000c0c00c546e20794144000254804159104160002c0303481c013174415003d80030308114044108682074003440c0382c1c42c0c111503210801c40035018190801c01004005040440b10341d04075004101c03140150305850040c444101d020790300c080c180081c4401100c1c44002402940d029218960034895049070982e940c2111740e134403020074a4000b000c280409d105440c1c03d000e69110f225024022a034a480300701455804500a811400e0515010804c102d4100035072402035a2180c08141403e14100980c00c01c040c00600141c0f0380c02c180003100250701d00641c022010031145540c180d07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 896723983 1250 896722733 896722751
    0x91b06020d020c0402040e1b0f0a05121003030f050c01090c09020a080106030b13020f0702030106090e250b0702120106090203011a1318060321260a0b0d06 68
    0xd6956041d491101d016001d1815180340d9030030640221410b440da1180042d800d80c032070b56a00307400144061101c01c0e55040500425000010410040c0f0102e10940d40d10f03a116840c05119900e00000a00341217121807406904000090704040902c01c0c2456908009880300c507221103503070251006604c01402d009420101149020320f075400f0b050100015a60414a0307a00e90100b501142d0700c94240d2070384560075041d103c0181d580b41d002005584d10f80142c840c100207141d80445c1c2035034410b030080b580e11901e9010488081070308001610488d031108118901e603003101d002c9080482001c0c0200540c01600084620554585441540400707007404004c022080c3e45030f169900030b41082c01044aa009004540200034208030107030f0352101c4825401074400ca16081890405035100b0940000994950078008045444612038825156410f002482e4031400b0b44030007080c0302075481a50181d100d60099a468454100c0440365000b04d818600003806407503040016001a04240002d1100d07080108103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 896725233 1250 896723983 896723987
    0xa0201080721150f1a0901050f030f01151b060b01050c03070c05030607050403050d0e01110106060801090b0105120103081e0408010e010b030c010c03120e12070b0a090b010306091b06 80
    0x84800584468000141e0751140303000c03884101503120300017440b0b1504c10f120200a0900c401000c1303120b4141061b07031818400d8004080140c00480c0c1c101d01d1445c03e000104181c29010a8205014416240090083d11420101003c1040300c84011309155514110501c1c541d016204454526070240c080780d440e40c811307107000307402e40c00c00d40500d50080c010100414003280c016001d49050729840005041d0306001030104030b403800b414540c0141004220f01501481c0d92084c4900c034040c0c0460798800885606050188055928144009042001c100802c0080d00e000c0c40099055a6001140564641c10b100302c02d02803000650f52baa40b202c070300090004081a055100707494119850b00240310346444801090b44681000c0f00a901241345e110011300021f10415010f031070b104003568005a4403c1c10040e00e032400300560352214403218001840c505000d545070219074061300103a0240001a626950700d0f9400a0601c00182002e49a01c008810085960b4000c41542d0f40007030b06514541d42d803840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 896726483 1250 896725233 896725241
    0x314010f02090105040b090d240b101418060f091e0a05120a1b050306060a0305030307030b06120903030106090f06050702040c020a02221109061b0307170304060501080f0a0201080721 80
    0x44082ca40c540f074ac9100003418600e500f80c0e029501503e902031600502401443e10364040c0340f101d40700c44c400382c000100343d42d1440f000d0a84498130012043d120b000c0e01090007a400c401aa80900c080d4410040b0803440c1d80702600001a81c1041d52405600010500824580307086090000d180315012030f42d00700210745880103082182c200301d04a03151926054103110394442075000203045600200005a0000d000b500014048032010701003e2515031548440c1c100c200d000d41c2c1c0164250000001003010b02e50240450024015905c445000140344c10009401803041400003406191210710401195000307102440d00c1d1600900112280c208402407080b89004074004040e4040c982840400c0007654a015a840c13800090081460010b545003a40344004007606000c5052004105800000e01920360b098a40103480003030035282d0a0a103001d40070743d54140c02c40c4a150f0711650318103078640d0000840051040d0207080c1500c25499050303040300c2c9442c10300d0005e001410403080520300030b1903642c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 896727733 1250 896726483 896726543
    0x20d1704141003020307200a05010504120f050a0f1b08070b0702010f0b010e060904200316030c05221502031213020a27060314010f02090105040b090d 66
    0x1510b031410000011003602280003c0e600d090004803041035500034407815860851f1003c04040440307100c45902d90b111400c0d80d0007120100c03080d2100c4248001115040921800d40000340d05040f0304202074113100500c406580480003007003045580004903108084401000d4075500501515070307500290034041c4941c0070683e59240150b281806800c0c010303515200d9610b04640c140d560800218205003006036541000300441e600035520381d00e040b16003a0602c054a40300325100d408588a10301628000c484401a82e80c49003411b0918113503810042d40403080790700130144020542c3d040310741103244402802d015005442007407440b5008070341c210303000130240030640c81c0202d15030259075541d50030006691002c04025000a8141414803041030310b001505180e00c07030600c031501310300ba42050070030564603158001e40c0c038056070b080343e046c5640080c060150b1055100301c0540c600060580000c190784958424042c03010008103000002c2d55459034a480b48980042203040001c003a17405861449003101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 896728983 1250 896727733 896727739
    0xc020414090c0105030112030e0f0a03030221030735070c140c031c02010b040606121a011e09080a03050309061e04020402030a09051e0c091003020d170414 68
    0x10111810302c1d8030513011a8140c1c0c41c1404c4010060409540c1a42e0040c0125070655100480740d40388551078072000c100c8001140a58024103507524002c90803040c108005040c144441e80c00c0040001544d007143e0050b00c40d1080781842815000100d015100500030f401180d81c1100c1603070203020b9402d51042211003541e020f00c01403050715800b400e629640302c005600c1c994140c0c101c1d060403040e5401303c007501c0d100101d09000105514030303120009400c550070764018102051459841040001032071280c44081b850030034120003481400800a0b00c40c4051002c070407601c140c4944165507003403241494200800d0480d089440c00d103a10314010b48250021983c0f903000b44100f6000461400b0312601a6032008022100100b140e2125020700019500080c4044e00d120748440130040002d40070000315900c540d6036044140748050051285050509001c07405115100d80c01c1031090b00320302c2389052401c9030384c1200c2c03010491520f80f52030521003002582c001e402c000080340c0002c240030f01190006140c0700407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 896730233 1250 896728983 896728993
    0x406050627131a070503160201060807030206130b210f0609010e07031119030c02060f07031a091501020714031c1106010902070c0504061206090501110d0e0c1804030e010c02041409 79
    0x7c00f4101c1c2200e0081c41925910703802020300708050304100c4010a021000301818140031919104a02240e500c203404000d00d00100202d425401c40100e152560401b170781005807502400e007440040ca04e44e106008284110358042c0100d0f40d803a0103035202d1400f105a8403101a1909074148030750220f8080190180003007421f22040030015071020031514402c1065449060f050f8036054400c5008001d40700034480c0d030007039050384450281d4440080610400c440d1210b0340c40000740300b0009040c20266800b06181c9518024001c291765808506030040800500400704e41700e039020f800b220311a403485001411409120b00115018405400070500c460050354500d48080d80c0e101407108580c0b0b544207441120f43c03040d401c00000346243d002038071020301440000c201080c03262030324660f6600041001281680e0307107104c10100702c028801240b03000d800311030035840e1500c1c0c0c920240310000010030042c200004079807048032680c055920b05900c1c1380c000d0400c004000a094104903d100c09481c840d203039201d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 896731483 1250 896730233 896730271
    0xa030b010314030a0807080403050d0e06041a100501030e07091b270308091927020901141303230606040b060a0302160b0406050627131a070503 63
    0x41260301d5004e540c2ea6410302a9140b01d8115107411001d0030480401c10108507209c2c652807e0b0003442000c100000103469941400e103402d00f0500c103442c05251004441c0710400900c51518242c59007140d60a003004144401008807460034801300307410150300c0c0c5142205252003140300d05e440305080140d40c2c03110034a8178445421100030746840487d801c004000f912041c800601004050041400060100c40e40034914002c80c6065207000e421079100800c002d50503c200318076146001400700001881140303410701c0d06000a1001c4503149075071203101000100107244c0c1500b000418015034014200100b071812035400d15400b10080c5810000d00d11032100451030515240c49111499080100308a01c0c00350303c2c084c1900603401245408107030f040b02c000444003141101d13000510840c8620310004442c504071042021f1004109028030340a505d08140d8014036142c0c1911a800014400b0303800910300888c0380400c01d040d4011000a20040107006000c44190000702a5000c1c1c29003040701003104e01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 896732733 1250 896731483 896731523
    0x9060909140303040b070e061b160e06030303040201050f070f053d05270a02150f2d1c0605010c02130507090b070311010606052703010b0a030b0103 65
    0x1050310090201d560440c08103120900880c406094214064403040c101312442d000780c0d0300c0c0a01410309c081c150b002001c0c01c08010080c0c84000025220800b40d0101c0381c141080801ea49010080000341881130002d11300502440003001d5448442d8092155140340390541750841d22200b02042800c09079011414007803110504418a07250ba49031a0b5140341c030090700304690350107003c000c0c1450207a010035040780301041140001000f00703407114000414100240784103106d4580554900410028000c2c0201680c2c4168002121068143c1c1c6030740c1d04072400c05450300e00c2d0600d890801400100000110740c103a50040e000c0501100810079004c10426965200544e010204640000e50010302407108510050a5510158010f030035480c018101d40c2e02c8116554a0740d000300804e8000c03401000600b0042d88003409903130041c001a01e4418106035074010024114a21008903191001450304070700a1614250b003c03100d2244020024900c41d1383c1d03402d184001c803100b03002c103031030f00c408020721505000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 896733983 1250 896732733 896732737
    0x10e0708010f20090d11180f010b0306091306061d09070e010b0904050a110a020604060b0a1d07121b090905040503071209050621060f2206090609091403 67
    0x180c42e00e203c03186044a041c08110000241d039a0072201b803d45080c905c4010388a281d0301d41418103040700c00c0783c82030801c00480e111782c11050788080c0a1030010000c21035143c0300c00128a40000c00ca0102c603c59403520b1601c00d0103400c0d5608040100858681700c0d1540c42003070f10406014511003401d40e800151036500c0500c40c82c000340907182d0420800c0200c0728981c189a40400c3d480300100d08000f039040c041042200e4960b010480c0702d40164803003c144000c1c01064480c40142c020202c8030002c840349440d5508990b800201c0362065a0080b000019490310300814890000c0c1444c40b00400c00203001c004101004143c280b0848005840000040b503000d07114441c540c003664003d8000d500701003140d900d095051040328240020030000760000140758483d14080c0c8444c0e0001260001d1910b8003071207100b10010014019803040c00e41a003581c029441ea0780800c0c1c0040000601070401c51410780c42c00c8090304069121040380307407501500081c01c025a620880c5094400c070a14100840150007207a40d81c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 896735233 1250 896733983 896734031
    0x405040b0d12210e06100819020405041e03210603081602031906060302360903040302180f0c0f181c0b150a031106030603010e0708010f 60
    0x801040078405890b075004000405488000220700d030415400b20003a002656143c00846503a58441c00030b0116407960310b954100500091130007841a540c615038a071201c40720040e40603021320760300c4021500f44480d00f04036880d00398200c690801404c0302450002c003014100190642010307804a0590310766122030081c01d0407030f03403c0800942004e4060030705400029600008a074148a2241b0b603240e01442c040301c9401c491f001d182e0000301d03146140144205501844402d90030185081a5401e03074040302d003e00512051499021141550742c400801d103144282c2d040650b2000c141d425440902c029510514810500150807090586030008001c032030740507990742d1101a6209000c1144880070704800e8045004000b0502c007406010144120141c004000c419140703000c084040112160742a02040c030800e0040d15114070042c07640c0c90301d04032007910402c20f0340310f031000001144c650b0743c094019080c0c12034110191041c0030b40d240b01c00e500900c00650309441a81c00c01c1442d1000c031907101181a10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 896736483 1250 896735233 896735243
    0x110d020c130605090a32150f180a1401080d050a03021b0d0906080c1206190806090d030209010e040b0d06050a020c1009030c030c0503040801020a050405040b0d 70
    0x2802034100400241c0d00c9548203045010740e840324001056912804014001c01090f003000448007884030003d0340306062103000c41583c00d4204070040305485940b502a900c906407520201da0507550380005144000300342c03440f0754011003040840e030906070488400c070700511240c0c03401c00844d40f101240302605036003440b5080068101c800012101800703003004101c02c140c6032500601e04001c3c02001d40802c220b0362034110f419440031b400c0484841c4c01c050b2550181c0040d0420a22602d0440010602403145104080d00a8804000f044460b107030400b1111016814112802801c0d84507000c5642d100d0302154152160f104500701944624040d00c200c40c04680182e440c40c02882d190b80070b010150228500d0641c201c5403507555040402e0340d5100b400c0c000c0000980150340c440300c1032120b61408905071340c000307040c9161a07894170001350041c00310701000364541840c51500c1050300b0150b0560080758402003095000081201d0200c3d400f000034816a04102d40c200074500040041c002200340e07075580286 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 896737733 1250 896736483 896736493
    0x403020a080a020c030307080d05060a0f12060204090c02010203101421101b031508070528090912020303090705120a080c0c01081803031302010c02040e0a03110d02 72
    0x30200798140000c0c02c01c088280104c40796101c6041c0860300d507602c111815506040d012a20300320084980c018942c01003401c42745449080c1c10400741010311691889141c0d6100d580c0d540020811006806940042034110707010080d1500f80d9070060b01035401140d0030401c0a030055808035041c8000948000c40b4240681000d01c000c1288004100c2021780072449000c91081262007558040280910b0703056484030703424008807028600e8050140c0318150203019a1000007041801000c1b00003558004a6400325454040d41601420074868101112030301500650901c0b00031032451041e80001d2003491180112002c140b05030034040ba107d00090390480110740026070704200514011868000c0d640c424800e6405110403541d503103410b0b520070100c006803908504110702496810030000340d84080da464160386034000d82030343c0f0358a80c480100320354120760000c0702840c25079114103407030400386901900810070385400c0c0c440b0654806414034224009941038044000fa40310100308800c4500444d00100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 896738983 1250 896737733 896737753
    0x71104020706060503031612020318090a1805030702011d1c02030f07030b161b170912152a090d0804290a0804020906040f2c06040302 59
    0x1001039808403038259401d81c0c0f541c0011505540510050440082e02d000c0c1d05030b03002c0b842c50311045540d210803200301903401c02d00403442001881c00070003034900c104403060203155071440e4204000304403241200c11000c125998110401000000500c1528004d8031381c40c1301101021864030088a42100d030325000445130b090a0300071040e1481d541d00007480203050312040002aa429841c0040356401030307602140c65420f0002c03d55040c4450042152a032038540c841c5400c0c2d41c01c0c1002044814002840c0c09128a8080c45191001059500b0000c00410b18502580305403e0165901e41040500d050f184100c0080350045080c80030b03103480800084000c0c181c0301d83c2d60081c2c0c08190000040b164000c0279230740301940090700305401000500800341c08103c0212901c2e009413030007006901003044500d404c20030305c000f15812840d0598041d6040701c04485568030b0300b0220b00540b82c00d0401c01c0a460528201c0c10b1881c071018418858020301c0d084030340009500d695010358480081c2c07800307030142e00001208 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 896740233 1250 896738983 896738989
    0x70503010b060d0914061905010f0830300906060d30080106170109020c0c090c0904140615090d12090f090b0a0519080304030b010f0602030711 63
    0x4c01c1a103000d90001400a140031114500780781085510f403940c40045501100030030700c548100c03405440740c814045505400c04005035521107240704801e480b1030341c107154081c1c01394010b0310700350b140c40010302800e48982422401e00012180d100c6218800c40201c011107109482800392184151f8030380c030040442d5102c08041c001c012007030303070000c1e19180c0d9130519a1440c00a580e180018a080b02e070f0f1508880f91207004000c2c948001030300f20000700001e01e0310000e6058181e101040c1960701c002c00060b03942d007e944189142031641048607400c00c0140040203c00c2000c41c1c0504407a00042d5000d10010070410899a000c1c0400c80e003180c0c1c01604030400c00f00c80e558110203482c0c2701c030014042c0644520681c0b9030343d41100c0075240f401c0004180d07142c02c9c800709001c450783c1c0e401898084000d0291444510000314481e1040c081c0c02d0027120041c54081e220701034104180c0c001d00281043e41e9031a40c40307003009828181e0074001d081c603628060f4000581d80d44000111074100350049610b000340b059807020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 896741483 1250 896740233 896740241
    0x501050d051e1014091e031206010e040c03060801110c03030103150603080301032901120b06040f06061d0607050703081c020a051902121605100518070503010b060d 72
    0x4001c0c1c25101e40544204224480e10840850310910300c04038000303181100105e45003ca905001408407a4407a560040401d03001050b03c401600500c0500100d035a2000100c541c448502c503882e500a080085094000340c02da441307201039910440027403203c158201c00540c0300b44070b10002818035500c2000104007180c0d100f43c4ca500d4900709601c0101e5240c0d980e0f103400c06c0d541c00170b8005480311000030b4003121015108e10281e40d80901100c0090000d90301d400750040c00c000103020003074559211180000e426640d02d0f400048096450001001190f85424009040c03034202c0740c0c41086110b103c00042c815142c032009a92840340d000008102d41415955540c099411080c0c8a5805036940307500d003a201c1e0001d0001c1c0c001c00c1d40f40d40c3c8203600c0f080040310054020113450700101c1550001800040a4020f00703045a80c03102c0d4051030b800d00d40c5030600d40386203800c0b800711011000d64544810700545446204c0c007030742c2c10110303001183c100a48903020982240c0524001d181d100c481004840101c240e142c01c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 896742733 1250 896741483 896741533
    0x70608102714010f1e06051803060901150806160f02120a0309021305010302061803030c1912050307083106021908011a130b120403030501050d05 64
    0x2208030440d0050318000103641c00036040b007511107516401400121004480075004040710192089110580344000c500c9404500030401000b00c001907140000c0748044080306c0a440107012900c2a1500301c408034000c10360f140301c0c1103540240080004000a0009480c0d0003001c0400142c5115080a001035030700c042425510010f5001700000c1c0041c00c0f00c21406000319185a0f140810940384501c10048000c2c07070100700502c4985414018800f6803540e106446664180c108103000010404000902c0d6001c1c010001a00340b00740c2c81c0402c0d182c1403c43d0b02c0703500303a84160f030309401e9507150385001e403a0381c001291242d0000f4612800501e06824610001400411f0001c0f00480c0c040c04007900201517910b110250759840c0c0006640340b40520200c00d918014046151081a65062103030f20175000701c0040f10280d0943c004180360f240481c01528020003440030a114654844201560000c1050200c2d403d0b0301191074000001418189a02100e1000f6170000180c02400740000320581d2240e0410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 896743983 1250 896742733 896742779
    0x304230f011d07051210020a02031c020c0a0204020f041a0406180e060d02010c0b160207080304050d140f0a0506090601090605030d0f03020c030a030204180c080a11090d03080907060810 81
    0x2d030000346e0320b0820348010081111654081c550b140480880010001248414402c2c03880c8100b241403004403020404101165044401594580740c060302c101e50340c01035402c81c0e00c2c07208500d600c2d10b200119920003807044607804e403a4035000342501c0404001502c0326125070010780040d540081e00515041c0004d2612030700c141403148200c1c80c00d890703154840784103c42409110462088100c2c5058040049500030a03003500218501400c0001099003940408402026041410010715111005000a5641019600032194ac402d6941003850341d55030192900e940c00c1c002e440011a40703c40b54006d400a031a0054000c0c95141e4150400702c48144080201d6801c0503401e0060500002043c00101861011640c0c050f880d0307801d00c01c07401c503000081011180100e20b8a050000d402d03410901855201d110362600150301c0c0000e1814040c42c0c850059081c1d400700c0384202c40e100b00340d0050b68541c090050728040350185034561000b83c410910584000070a20f001c42c10800841503550070040c0201e66503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 896745233 1250 896743983 896743993
    0x1140d0c260901152306120906060108010504111c32090705060a0f110d170c03251e031416210b0a081f0c090302060304230f011d070512 60
    0x103107c0c91003050030a960004507074000d40d042c8001d0350307400034001d800340804a804000001d500c0d003290400b031240c030101c41c0c650242101003070701c220415441896502c4034006110015803003440700c0075030302c00603041c0544082000302c0441d6850000188500941e01c01610072460104c2501043e11070b2070061441c181000000d984110100b5410f01080c180422640c95290300b020851102d000b06000007450080e0482081c0200555030181c5080b1000d0003100c1482403000d0010700d003045400c00003604040700b214080b0318840c83d1080d07140d070214140021105400301c03c0d0301d8548126038220003103515440040e125020040482180b0741a020b40080e545600207100742c2c124000c11100b0215034032150894021103284601d07908010400096130030005010031500c2d8100030040d040d001e26020281c024400400002c0412041a4502800042d8a90801c81c41c0080d0389a613980c400e0180031001040d402c14015000641038103480c4c00c4129101d8000c0c00c1e41030700b05400e109100203044407a900c0e520403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 896746483 1250 896745233 896745247
    0x170f12070807020a030b06030d03021204080901020a120503100602010b03100b030c09040f0302010605090f01030b040303021b0a14010216020409030302041701050103020f01140d0c260901152306 85
    0x80c402e42a00440c0b041b10007003100c3c0303400020141002203a881000c02e050042220bc00c01d503030084041070381720ba0300c03003d055180d40e11600100c0c039009480900816040c14800c1d0901030030b8210010f141300303030009840d45088684843d000c80c281c40300113245a8065012250308a0101000d4020a500203000703811030703c3d41e02c0f07001c000a070802c13429070702500c3c2d0031081d0b4103e50034142d082c081c290150006580e401c8913410030340c900000e00c610501c800307003030b420680700440c04042c0309404a90001b0100c9144050440da004401034455030003c008541d60340e400d02d01d00404107418000c0c0d4800d00c00d4000308420804c0c0c3ca40912010344041301048003016420003000c40c107030004007810100369102c040002059030540c0f040c00840c0c001c0502e02410310003c04424014540101c046070700c1d0715414007020903c00711a4200f6544500c5600100c807030f007401d4076082c14500c48500d5500d4413032192203009019142402041110025203030143d40885111000c0142010141a144d42c41c00040a8101881c100f4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 896747733 1250 896746483 896746489
    0x204080c0d02150a05090f030c0a09020f190e0901290c0304320301200c010615120b040504080a0f0504030f11030f1c23030108010204170f1207080702 66
    0x840400180003240c0c006ca250803070380c14503454001e07000e20190002c0c8072840002c40016840d558921421400e15000078900d640e01c9000815a068046010760444080541e8a8040c24101c200c02c51540210b4841c0300004c1c886c09446a4039a0140071803000b0109002c1884401c04a0f40c8628840c010500c030811000500701c01e28007092843c06c030160310f540045400100c040740d141141c60b40c054821380c140f00c0d00300a0300940d0f104507042e078401c03a0051691100800e040c1c50241040d6803000c00900a450f0170741e0f850f2030700041090428180c008040100d00302840800c4119002502d010f820324005100f1340e03030300500448a000b01000281405814a960795566645038641c2020889035603240a90701101828104800380702070240320007030a0342d00c030310a80d00032400c0d0000d00030100b00030b854030341750000711084405071912044444a2641d070750f8550042ca03010394400d1041e10300494800481105503d008150203060500303550180c03d01c107448140c1d000c90350300004d405403440360b402c10224006a03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 896748983 1250 896747733 896747737
    0x50f0708070c051e0a02030f070302030c01120902040e0d180b0901031d030a030912080403121802040e060105032e02032e0e130b0f0a1b081501030204080c0d0215 71
    0x100c0314028417002039184181804c00d1114013542d4095400344009200690703000c16800b489120030710341003c1e264418a00000030b0324101d00040e400c680b92001e0031505800104070030341d5600c2d003a202e09100d10186003403408060340500c2095840c4100f480110090342c407a80200e85c4c0152140c5090f00408140c140260565020041d40c03004241e603548000d0810802d030511102c40059070038806598941503c001d40801c06012440c9100c83d030703810124044802074100b01c26540d402030001c1001c2c8214000c034603030343c01c002c2c00741a1092040c15210310100c00d42520541865a0555901c9807142c6a144410041d410181c80600d2515482048101c0d64104821344600c2d05000c40c0740089a41c41e04450080c3d552024041a40d50307560000714202007008010101d820041d1200388a0362075a078412200010040104070400d41d010016050b144641c1c0080e1240c000c0b180007014041c0f19000c0d20054040f4403032881468031940007103c03049031074584446500981400540091040840130409034655 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 896750233 1250 896748983 896749033
    0x220224070c1d18030a1808070f030c08030a12090515041b0b09010504061d15031b031603180611040905090c062b110409050f0708070c05 60
    0x2224800380c14401e0261010025040070500d45001c03c00f0001c2d254a03520381c4a607069601c00e010342c804031640700c40c040d8a4590f00405000054801d01e91b1511502103d6070300303502c019a5500d140701800f1400000100480e4a2180f0070348500c0d0642c850406007002030400d0110a0710140511150036400c01020344403135114a00c5a210400d01e050817914444841034113800c4100c52502c240710003841660060102d50554006051180e600a500c5401c0d40d450003402d41001d4210600e04480b83c601c24150015602840d001091a0b6245015400e01c1c1540c0c001103400241440d0354480c140d2001c2e0190b0b002c1c00c070102c0f80e6004280302e0107041e181c51041d2008030721a200020300001d801c10040c503851150301d81190440b00500514004030b00016017600500416040301e03580e2801c01d0105400c201032031008080941428407000d509540d0b40c079045e4101c2c2c401e925686080000203403001c40c82d202d030719106e84000c1c0c84400140e10b5001040301c4032500010129068401d200c42580d40d052201800c00721 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 896751483 1250 896750233 896750249
    0xb090c031203160306030201082e030609020a230411090409030f11060402130c0c0c0e01150c120e0d08040f08190b1605160506220224070c 61
    0x10b2410640d5180340c100e049400c4030f0080526181d014030043c2c0c0d100c4c400c0c0d900919010385101d96180c180d805040c122907584c1d440c040a4241920003c1000306640001034040e00031510390310300b42c1d42c0740351403022540d824110404072107049415a5503454191320503181b00740d190032410709161142c03002c0780440e40c2c550001d0380807174903082c0b5403214141d11160007003450752004041c0c607040c18690302044001c07400d803a20450303003602c0310300050b040c41c401c0f4540303c2e205070005000d1064503510030603095189802c1c024001c440324400600420980140180c00c15140d021040d0f0403c0410108212090000c1907059a880036503000310304003080c5104050400341c042403041c03c032140d00d0308504c070349481c03a03a00310300e440c240401c01c540e40812110140142d01108038441108002c4c100901212180300b4524154040e05619101d0014810002030081c0302c1c640081345003586000000240c0c00c0d0340c8142c0030095001c0b01c13204098084411000c0ba04510070410a115820003001e43c0c0c0381030640155821050f5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 896752733 1250 896751483 896751487
    0x301020d0f0b030304030b0c0a0c0b0c0a0332090709020c0309040608010e0d03051e0a0203100906050609041e0c110c061201030b04020a09110a11190b090c0312 70
    0x1942201ca8032510032002c90880046103014510340da080401d1400a01260700c20310049100390125002d110b00034401980100c05074290326005245461036040382007404d00007841c0c2a0034070001c00d0036031801004041001c03031b5196411074580c606603d411008000950a000c7c001c00010300c1a014000b601d030590300c00d00515160b00500045c00212801580306442c01d070f04041c15a80f200c2c10204800720600c943c0d15001c1070581c0d800c0c46072848402c01003101b41003801c5440c2003003078441450380a54080c1d1068045c000c083c5a40f1840b100a90303c6602030070742e000e0400c00c1560080d140981c04690004901c040302c20090748400c0c0d04c9021500c3c9e6244c1d590108042c203c1c041c00701882402860348990003243e0751402c214540d01d075507807107070014000100385001e0b0101040070740d9105942c00c0001c2484081c103203c04c8401441e44843d940040b4003c1300881c00103404400d01e040042543e01400c0c101c0410303425446469210700c86000400b4050364590b0045801d0810961001d2240720824104008015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 896753983 1250 896752733 896752751
    0x300c09110a03050604060b030f040624051f0503070f0c020a06090e181009241b020105010b120c040e040303060302010e090717060319051011041203050d0b0301020d 72
    0x40c1c10f0315001000644194540070061244124207801c5d250031182c0d40809064954031403a03c04000c00f1589031a14001c290311041c40300f0b15a074411034030195041907902002038500c000101000f10907804060740840c00510000d2045803294103850310034810b501c0c011410104a8000c1040340c26240c0083d0002500120280100d4000c02001ea8020060300c11801005050041c83c2c0c1d203072021510040d1155481e0f042600601400e60302c09250b07403140d00014103140c100c0000810003001d407a00b0540501c5c02c9481c02c85155070061041604031031240e0b8a0354504005940c010324440001040d20b03101d50003d20011400d5450311100c184140d101c0d0324009070180c11400090f0102e100c078044184141c4800e02008400c1c0e50107002c0c901d1010f041d606078200b13911a80000303428520400184000340c5440222541485800103000e89003a030312880811400710080681902841a801189001c1c01e40ca0010400070344140001e02e40180c0b04503002070705150365000203003680e00c41100701c420039031038901d04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 896755233 1250 896753983 896753987
    0x506030c030702190c0b13180e120c0307060c090807060305070311070312050417120609061f0e01090e01080c0a060503061e0301020904020f1201300c09110a 69
    0x1180c00040542e899134030024042d82c881101c4940c60055141c06940840c104808400040b01e45000c2d103400701c3c10082c019401c0d80c1c0c100c010850f81c018549503201e40100104446403034422110f8100040d400756150046a07160702010f0710820460700c0403c01d2080d0700003500181440a0009001e50355400b103081d0400c000000e05450307a1055105050f1400c10041300065000034540d86c0202d10150081045e03600c0c0c0c14015441004159a086001400104000c0b1400001c007054450030080f81d204419440300024040d604240145039181d204040c00c02e5201e04c1c4c001d02820600d2001450076030002c40d15103008500001003071780245141da0202e880140f00389083c0d00d40801500103450402e0540c41d0090002c1c40d40c02c440243c101c40b007403038000c1003402901c082d01250003504018005541d0f070b0480d501c1012141d0f1202200f1419402040c0000c980c0092a01d43e010300300c0d216a142c0d4014400c0106100c0180b07001102c115600d5400c6100011111030070f00a07601c91001e5000d902e51150030a100c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 896756483 1250 896755233 896755243
    0x20105010506040e01060e0d080a03023006091510260910090204020735040f140103090f080c0f07150c0302070e011415091503100506030c030702 64
    0x514442c8006000510014241c1a10103045034150300e811404401030030081140c1c03511000c0050b18000e0b0009980725a184c040c0c000301182401703030400e01520701c00d070160300e84200f8070340540780340904141022907014a0000d080c00c6d0065110100002c6002044000aa440b0307032883d90b46000c0307040401e0042d6111461079a821080c4c8104082e1009454031032016038a520080c0a002c0700c0d01c3ea541d8144066480301e505946080703601444031180070b0443c080e4918141c80204e43c001e0000b595150411420340001d060b10200c480f51080d4906c81c03810a01c040c0700c41ca9140329614101961980c044012410500b0402401c5010300c0d6810b40e2000c1d810b055505226034060440d1032a44202c6c000c00186404040024010060340381071003002601c1d240403400d2440c142d124003c0a2100710001c10004040c810045104804030354452507410744240040180c021003896507401400110401e80e1403803400d0043d580031400d03003541e800d0b403603d03040004c40355001a035100d50f810901004129030075404100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 896757733 1250 896756483 896756489
    0x70924180e1e0a1203180209090f0f0c040605190506030a02091f030e01200706060b0a0305070e1f080c0d020a0e040b0f03071518091a0105180609030a080a09030302010501 75
    0x2900f40071a00c20b0700b8041c1b581c0303011418028020b428000010b5400311050203d03d21810741001a00c80300c6d02240c12050340d03940143c00c5140300320b29100001a1518101c0010041d80008011246400c0c4c03421040240940000f400920b00341d40801900400760b4900b01094000070300d2015500000000140086c1218500130146103660324142024595035000410844c001500484150350b034481840d006019203d541c0c0f1010f200400801c00d46c0c3c00c181c054000500c502038560381d41c209203400c402040b900c241007105580b8405404005d0781507070782c0304825043c4e1045002c002c035454514200101030880e404601c03c040010150f11400500e850140550310781c000d41100d080c2041d4544c2030000b500c2c0c1b042b41c4101c15011880d500341c8040c481c000d0151868070481c40c6520100180d4650b20f01c0c024241c811400a051180c0300e08030f849540c000c0054800105000d840c1c13000309034100c005d2100760342c4a0800198984511310403140000c04450080c900e01410303a45040600c0d140d85006800e40c2d00c103070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 896758983 1250 896757733 896757737
    0x6031b03050c040e13020d051c0504030803010b070f080d0209090903040b031617011203390f0519050607020619050612070924180e1e0a12 61
    0x601800310781264001a1801c0c1c030b2500c02d90f04e44e152140d280f664880c130b8660100075045540b40034090f0a2140102e1550003a078481082400d00d501860383c221014807550000400841e02440144401824a40031f4009036103c1e140c0352406007600e03181d0010366084210030000c1a80c0014480c2c005040002d180b40d040310a03e40110304290401d502c1071050f00001b400740ca4848010034920b540c891145d10361441c0c400f580920b000d013550b140c01901460484450040c1c001c20105030502e061103a0103d50408104203140829900480d5040e15400824401200b0344041820748860710101d0024402d9181c0903581d0b0b80c585054000c64a400750414078010113650554110000708000c2040f0200400b0704000742190002e120750318800081c100021003a800d4140c0d204000c0040340342c0415510a004001c4420600c4464074103400c8410442d1300c0c14000c2c803003415006039006107446495002058140840410740e0740103088542d8291412280712540542e662108100805000c54240440302c1d101c814 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 896760233 1250 896758983 896758991
    0x20d0e09070305070c0b0c0d0b0d030806011b050f0604050f0d3f2c070905040507150f03060504020f18060d02130806060f0907121506031b03 62
    0x18000040419500400034001e05441d18000756000e4400c0c0010300480798004a002e00c43e04050030100350540101003040001d501c0c02c800c48001346032036942086181c6e81591207001543d110401104d03d140c1b0034446a0544904100c0200015814000c3c01c100b000910014251441c040c2003580c9000e50380315405513036070003110810340c0349540128214141d0b0f405c1110b80c03a030400300014400542d688003075405241e9108243d0440a80520f402c1200c186640d2600d4294a40040c8490200318003140d003401d2032903012103010000841150802544680604141c4000740d44d0341e5051008144024841c10024409100c10703c003007a014070541002c0c14080c1d40841c1080170a10f9103041c148148005826110b2103400060416603800c41181e1a07803503142401c1d0744440003c10180500070300d5010300215030041100081407811310294108030000c00800320655604c3e1010b00307a6080300c0c484c480d00340c01c83c1c5862148000d2028000d004004011917980012800485018a50601d00511000c0101428 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 896761483 1250 896760233 896760257
    0x9410115090608030f13090609090605060301180209040c05220e01060b04050d14070603020405041a01170901060509070c060507111c05072102060c0a09060807121506020d 75
    0x3c0002558440d10300043d019580305659048004038440d140d00c00000c050410700b01240203039054000141c0309105090a101c0b80c0c80c1c900c2094244c540c41d09104441c814007584d4078025203400380c0039603041030207101c4259004c0c3c0c4440114441030459a892441843e08103448042c030b42403481190310182c03440e03000f049103a082c00c0c00504903114901c81c0e5803061500d01c42c0b05c018080401d400305c010541002c119480c00b99146c001502941051044e41e10940c50540c003403c000c0c04104801140d440141d50b01100c3d00a090040d0f1003416000e450300456669850010590340c5680f00c080d40140d5158481040f040381d2032410b02d050f64801400303403040100e526a003200f0204009101819090802450303200045a1402140c01c0e00440c10058840c03c8510420a02c01c098014020a803040c16030a4407500c0e0f94001d2940011711a88910b000051058841084201d20500d00990000f8051a10481038000401d4100039114036503180d51050600d83d100700034032030701002009040d5609050105ca0144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 896762589 1106 896761483 896761499
    0x21051f0501030905030301060c0807050a0b1008010b220b0306010306090b0c0717090609030d090609060906020601090c0201020702060a020c090a094101150906 70
    0x444060100d8503520901070b02001a800c48005d5156918084080b1225000c2220581e140701090140d100022020302030010381d1802a08992078034100481d00e0084000c07550300100c6540e240c04030491007a00d030000d0744680c41e03010440e00f000c1d0010705034148015004002e0855070502a0b40008403c01007a58841d5031101c1c02581441c2003a80d0701140426184690080a007264070589400000f95400000805c410200503100500f082d054030046454040b40301c41400c042000d4100502178903030300c900f0060041074240b0380021490300d0420003944582041c099804031584403900c284846000f501150b4499034080c00c550303079401c1c101500030344800900f41c80c82e100d00300351804204102e44030b008680d482d64103c98200181d4500b0b020501038510510440c0c03007603075010030900425a41038211030498003900c0c07002007000003c0c030760344141d864480c0d04402c811516110307045c0401c40c = true := by decide +kernel

theorem cover : BRFrame.Cov 896582733 896762589 := by
  have h0 := BRFrame.cov_init 896582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 896582733 ≤ n) (h2 : n < 896762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
