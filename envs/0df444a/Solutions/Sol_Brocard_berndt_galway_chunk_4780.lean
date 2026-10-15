-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4780
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:42:32.524982+00:00
-- url     : https://prove2.me/submissions/03850ed0-c2a2-413b-abe3-af875e883621

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 859532374 ≤ n < 859712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 859533624 1250 859532374 859532389
    0x150a060b0c03091003020a0503040602070c03170a121a010315090203040c0612050408070f03120c020d020c0303030108120d180309210b180c1c0213020a0f0509010e 72
    0x400741d20207142d68041ca038003882003c2020035548030415104002c2e00c441180c0c0a400c0d2604640d0003000540d0320f07440f908184941080d82e03013014101c212117000c0700c01850780b0b003002444a007016803a9204080c19910001e005c4454112828491810400e9003441543c405d5002d041e00d141d42d85521044a521842c0c43c408903082190708503131001c1c100320140a400e4005030901c090b04c102e98014070140c54141c1e1029554080c103c1d0042800c0d580a420b202010301500010202018000b400c01409480c800c00940e18000b071606240035016001c44034132513050120469041e600c5040c0101003450302401481041d83c4156100ca1401c3e40d200039002c251092403040280c03050099503104002405d000b4944000076000e44a101c006808203000c02c001000d504525500002c80200c00b00c0f100040b81c982420514880c2d2015805501000000314407125248020005030082c1c0d04425608000d62015040b48a0741e403010b404151035040c80a41e451245006049245040c580040340c040001c0100c6d448 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 859534874 1250 859533624 859533637
    0x31201080a05060901200a02010b10050405100c050604030f021908030a0f0507300603080c070b0708120711010504030206160509011b030507050708062205150a060b 72
    0x5420021840e824400100703c03654003c6400310007003280c0e40c20b9092840e419184500320052622010506114890003940054000000a0005209003a031201d0040090344203006041c0310300416000381e00028403a8481c40051a885802882d9a890355141070342e800c0c140c0f80c0c0c000b0461091078144182001800380b01c08610740705102e81510307800c02d40303014010303180c882005038140340c0307804100140c00d90b02c1481714081030301a444d207401c100860340910a10801c0844001c2519051400000801c01d1200041c12001d030024207844420351541e5011606103c1d1030400f501003101404000209240d80301200c0c1c1200f4181000ca021001c000e0400d801c3d1a0111001e8025030000341c02c01640b0b61a0000b90410410245802c0b498803001da800a4007007000c0c007248120040c10381d98030b2010140100111a25907401c00308032030000d03503260800c96641104565126600304440799200c44040f000124040b070070ba00c500509201d41600340100c882d054001c11610708151540302c00a90800000010200e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 859536124 1250 859534874 859534889
    0x90d0c030308090709050402030a1524080d051c0b0d1401020d110a1710050301060b131d0406050402361006021e03120109090303180804060f02031201 66
    0x2c0741c43c09844142c240202a40424856401c0808200041c6e5020402da003520707034400181d14081d041209003500030300e54142170112410350440381d00700362840c0800e110b0071580c1000403542e43c0c60101c0f42c221014001e60000c3c0e604140d450241d01d80c582143c1d0801c465080c0701400180c4400003e03210840050f02003600d2140300d9600180d4a0354801c0d042c0100600d41d2160b18030b0524040c02008010040c6a081c0c284051003149440440d041900300c034080401005c000b002403107100d849035080c1c58568400717110185858034410001aa9110391102c7c00f4000f070001003048020b82d12a110701016010080007240d0100d0480d4048211180c0042e8500d61410807181000b0241c242d00c3c3c80c51507004016250109100110f201080800d90010310080c490708064204100c50701c02d82000c0d45540102120307e00d44164240000c25038404035440201c45e58041da40174000c0102060002c3c06492003c580500600403c210510047d0300640010010813083d00c100c03441d00d0310310302e10364803055000c0c0c10920 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 859537374 1250 859536124 859536137
    0xf120403060b010f020318040e0f1513110d1b0f06090608190e0a051b01030b010e031c0504090e0102074419020c040e030f030c090d0c0303 61
    0x106000c07451103500301180b0203090104011890240213542c0c1e0180b80007020364419245d00d0300301c143e01c55400c0310081c9904001100d032100714040901c0e0310f400d1404180602c490303032400011448039001c040d580c41a030300000c1640000301c0140c14402503a06c600c01c1514013078010070300d502c07420b4030b000940401000b0039140c1c0d00c04c0908207900248003107100d90055041180a500303000e1981c0500010028205907980d00007900740600011034144580e040001e002402403a00300b9016800722a81300690003002d9030300701f10309080e210040d42c0d495622036005800d513001d6050803880c00080c44d2565580996400d0aa0a150791100d2076410782d8007850700c0030220707500411060304003c00304030809201002c003c0070010a19030a003843c011503562000c2c800702040c003001a0100100d9400444c0e4680240394a10070520844050195450301c6034500180039520348542940030401c084140e95944803402101842c0d62500b040c600d955411200820354400505005400002c80101c01d04000314880c0e120b61 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 859538624 1250 859537374 859537379
    0xa0c0603021305210c0a0b0d0e01110310060e01080103120f2007080d030203090d0e18040308090f07060e0108041a040b100506070812044202040b0412050f1204 70
    0x241c01e0802d0b800000703000364580002032043c070741f58a043d0342d80107011311000104030641c104401e0151101643d41882400000203011a4503100740c6a07900f071300c1054840d0140d46210b5001194441b00901c4041c106124160480303000b20700c2150816800c464a180050a8000c0f00d03c0c2d0f4200da005118420304150300222041000748400e0012650025550408500354078182c03e01135119070400c00e01c10100b03c014a26201580e545403445c1c410700a00302c0c10805c2030b00c0d1a25002d44000415a460301c90382c410441786072100c2c0c40c0016944180c4c0d04c40c0d901c600040900000641d8013030300140c0304423503881c04102020f0401c0402c10038244224000c5140700400d081880340c0c00340340d40040d0003182c003d840800003280401c01d0002140d80c903c8404060303004a40d214141038141500c4058401c1d41440d441d802840070421042503810040607103141c01843e04d030120320700003c030301c0f4512844078041c00c00d02040041c510f0000e005060b8a00681c113581c00e200f00300c11020305041c94034a500e100307a10080f405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 859539874 1250 859538624 859538689
    0xc0c0f0e01080a0507060c0813090b010e041e1a030a111c020307060c140105010602070602010f2304030c051917130b16020a03080a0e030a0c0603021305 67
    0x1201d0040024001030020044582c881c2da4a40c0701034012030b000d2103840d4a0880030410710104884110019002e950b04294407291080080c1c90b8030070b446070000d8070100303018085207014818007524440c0907507200c8003034400200f54009064429038840e4089440305500ea0b49031000c0c044006594842c1003c0c2c0004080582005040d0070091607204c0014001d482c90310058a000590000b95070003800c004041c11018030b001c400b295000c003440205542402c000140082e00002c102007a5002038000344070001c020000c071030441d0449504040c000d90020088569020900ca00c960054020702d0842210540c60725410720b000c0301e4428082e1500404003203001400030007801200d091044001461510580d030405204182c0c02d070045a240c00000602245030400440002c0c5c3d00035405082d8001d55075803801c082c5c1a0341c024a0710a008617041c51094081d9140228800110320344c8540c1524115081c440110000e4008140030b070400c0c6000e02000c01d1941d28404031240310950f514440344003160721000e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 859541124 1250 859539874 859539899
    0xe030711030f03030108210415171302030a080f120f010e100e15060408150a060b1c0b01020c090f040309140f040b06130303050c0f0601050d060c0c0c0f 67
    0x20742c40d401c1d0828801406458000300d007018940c0751803103051140030014104a00c1034070640c0e100c0921403a4000083c4225074000310000800200580c81c05d10680c0c0d0754103460900482c070200258590011745440000501801c0600702c0d5070f880c0e4510078101440c00b550108220b0f42079500d200c00148a0004015507200d080c28a43c0c840103c518244c03120303207003c1000e200000041c0c038070002d401001041115030f49504007914001c0c015070040350611100960030440200341580c407108a00e040440201d10340d8509070880d05191081581e280b012801c0d081014000c0c00310400050450051142c405001da0b40e001134503001d12410001000c1b1410031385006071021116030701004c1c41e10745c01a5200069075071036010a58610082da4086981402d00780003412a224240008041a4a440d004030601d1f5020010b0000c003803501044540350f100d066070380c50b40e441c000d00c1126031042c1c110750307004001912504552640e1100b410610881509551181d919010503002003100d0b52180704104034280c1c0034071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 859542374 1250 859541124 859541143
    0x30506070201020a092c0c04090b0409020a030221100e0d02010c0207210602032505030112021507060906020c0d0806060a0c0c0e16030b01300e03071103 67
    0x21413078600c61080181002c0301601c81ca490f5003050300080440004020000c403000c190842c0000c0113887c0c8900c0102c541e4026000700d000040c54018400c016040510a44401c60b400500044105146500f007112100780e001c070400881540c804418501c0d1020014070011421001000c51501c1c200c00d5400d1a050440b2158011603050400080e20180c010400400342c840c502d031200168410307120400a502d5200350700605151000080001c001e000c1d5040c0d2107001918181440710740c40307405003114140001c1c02000641e40341f08402c80c1c010728009415510152010061a0908009132591021100941c00030780e0080e800040d9803040d4031081c000c0c030146411608141080d824144042203081c01007680e0401840301120400084c8510305038408010007168518100600d0070550032001000b00242c04000710b410280301501560159480108243c816030781582c040c03100c4542c104150700304002003440a69a008900700702d6009000600305240200450540e40019600307040c40d101074003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 859543624 1250 859542374 859542377
    0x50102121509180a2f0d03050a030f0f09260a05070209041a011503230601142101080f010207080f0705070b041d090d020d050c070504051003050607 65
    0x3281480700650b20036902d140c11400c2c03040314422004803142c08901d401c82d113540180980c3d032021549a010284824a190b211131040a008241145030083c1b0402044052006022070000d100050300248030798050940e4075041c0202080c810b6000041c001100c1c015075054490450712443c18401d0141d50300702152108507218440e20b40b80c4031440080c4180905240240328192030740128023804180e00e8070b4030140c0414011420156914602e40e034084001012030380200381840315034500380d214510a000501e140c0740c1c00e061a6540c4500444082000c0b408451f004003051140040c1103900c1042c0c1215440001c200e00c546506112009141891100c01921079030700401c4a200004c400342c06448a240070301c0b495a44807903c40c070b4a1800c0580c41c3d00030080c00380004c00c00080c1c00014034034a0340706407500c3c00c0402036501d492020b5501e62034910180409a840305c203143e034900e4411307002419010000c0c1c0c21359021580342c10000b030036a08241c8134000c480b1340c4c0e080c040c01031000a20042d90000d070326 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 859544874 1250 859543624 859543651
    0xb061908030d0e210d3c02031b28051305120a031101320603061005010f0e0a06200105040c0504050402060912030c12400305010212 58
    0x215040c2210301c19131081442440c0000c140301130340002d1a0400702c0b00d03150340011110600040316052194202c40000000c21041314501c1c1d5601028178402c0728007484070b04130030240024614003016a60350103240040d89441000f099a81c0840c040384650b0b0418185544444d0748204107020380100d80c3d043d400c8184203898515410b0261400090790101480c0e050411000700b0107103c01032801481c07901070002300100c400b410703413880c1ea1800c042d55020143c040303610301c8213445100c145691400100d4607000e40c000c1c600e0040c03100358080c008058002d40c1c00d02e408800d9194100115032a000ca41e48040041000b1481c0728111503100c2000b450f8444030100200700310b180c55200d030302c040c5440d4480d25005591f50030214065483d2142140c60703542c00902221700420b60201415500e0740130030100c60241c01080d1056841c10090022078299459035a41c500d0610003042400424400429420400d100c0800f00700003205901901e80e00154003a07400162142c24010650055035002004035912020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 859546124 1250 859544874 859544893
    0x507090b030d021c080702250302130b090103150624080702120304030f050d05180d090b0712031409030c010b04020301030320240a0606030e07030b061908030d0e 71
    0x50204e0001030240151a040c100d54131046001c0e030511580381c05400f911176400c6c0003502d80801003440700085a00c04d030340d1400d03000702040b50b0000f258001c1e901260f0014900307004001007110750b603c0c42d8205850303003c0010543d544d100012120300811001c1d8640c01100e40c401410660050351751640805c10b40017030a00c110703070b15808184a00c0002c01c006e00703001440c10005408d0b445041a540c030034103824001c102d182450201041e20711500e00400c1200c1c451484240c40c1c0c075100301d000100b1a01e2400c042d40c18010965540100141048202d1003010344c0c0e03403190307028805000b004602842c4044099a650f03803480c111a0300303480c05010206c2c02035004000410000303a201243c443c0802c954040c0030f03881180264418200120030558000050000110000d40600303507012500801421000f08032003942c4010903815503001859040c80c0d500b040b07004101040c20040c110341e21480040401e000103045d400b80c41440181900900b039540d001043d20780910380c062058114020300c050041040a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 859547374 1250 859546124 859546153
    0x309150215130210050d020d05090c0a0602010621020d0b0415050702010b130c02010e0607031401081914071a07021e1509010513120b010f0b040515070507090b030d02 73
    0x113141400e903800700080082c03042d11091080e8190b030441c0100000a1003142482c0043c980d468421142035407143c0320141c1c00203403aa005214500442c0c1500fa2040224610046080304190702400700340d800c0803002c403480300003401d01d0001d0f510907882204008042c0703011071000d0003264401006803042d617152040d0300f2000d83d03a80e441d00c148405040c00c04200e12030030080403800b402d080404a5030078819a02031201c0d43d501500440c50204044103000302681c0d032042c40698a2a0060f07211140041c1c06c0c0c9410b01048840d01003481c2056110f084071109030f594845940a608018107134000c01d5004149802180750092113030402490713903c200048015400f00180008001c003842d110400030000380c00800380d02078000c0e581c20001c49a504d0004c00e0351072440302d03617070900e8120031241c0c00d00c10fa001050f03412240b8000020f55041e403504500380f034189414000444c21200704400110001d2002d0301c0014810031007040600010400404ca1209040c00c1c14070b440311540303030703801550407211156100300e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 859548624 1250 859547374 859547389
    0x1060b030f0402011209030f030e16050420120604060e0f0c030a14010803130608070e060313060e0715050c1c110706030213091b030903091502151302 66
    0xc460340003100c0242c8079071005940014602e0b0b60080c0300c03400c220121051540010001c50185010303141807010500014025880e07144074282c20010b556000310503c01410594001c0440a43c440c03907a45489011082e41902500503103000100060b4801c1041024181030040d40001c144180405d00c0300e0400c01016505000700400c034a040c0d00000c4002001d629140d00401c0d102d10311009410400d58403803071203d443e6880380c02900c10300c0c4849800010143e11030b04590388031700540e9440c1240c0701e410100304002079001401d80540c4441d080b48100c0890a40d200740c0001100d00d074010b1500030710307100300c0da5844514280c0440c01d00c80188046e24080202041c0c0d00c0b5030a104100d03c5440044410003900c00e003111920200c03192141d03107804146150582c1c020003103a0140040c40030181e96a841e560309035503e40c2041e000d03070415002c0803c0094040c2e040000f10a1007810003020040d01e0f502112501c544240d10440117a1140d40c0140708140e501480300d4020810085101d6110030540214401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 859549874 1250 859548624 859548631
    0x3040801061d040b1308041214071208031f0512030d0b0102030f070b060319050604030206150105040303050d060312020705010e0f03030412060b1003064101090504140f0901060b03 79
    0x307050b001402e8010006150700b07d83c00360001041c611003911940c20100c07074aa84604000308075120700c113004218811311915000c12280d21521091071665004100139070700c0d40d004a802803020000304080f0f12030390f41c032050380f100d0701e0400000c0d0380b54080b02200300d0541c0e0800351402c0c1550020040e548003030051104503400c01e50840484001d035251840132900c1c01032031001356080781280c1316041081110125450380614025404c0b250300d51100303900c00c1140551207100c03902180f020801000041d028801030007400400400c0001e01d242d880c0c581807640c65a410b01840103810511050103950b030008040140b101095a01c4410301007904003003940c9104501075000c001c1c1c000c00c0e00404010782a00420700300d43d4060302000f0b03603685609024001d0310b8580161b581c40320080c100f0800d4190240301002c0b02032810502c0c03c250001c102039400c40a0340c540c811070304110701d412012540361554010400b200941200c107254078a0300d80411b024000e4040c080320702076410107504001c4200d202c41a03071340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 859551124 1250 859549874 859549891
    0x71a1315230d50010b030402010c11030a060e0706080907030305030903130801090204060501030903020c01110a2001021608070b130504050a050609060607201203040801061d040b 78
    0x1e04010340d070301c10030708111407050343c07019060003646010080b07590140808610320386070100c90803501c10705003c0110450034007a00d050804c0600c0014090762080c6841c0c40294055030b080b40c4401c200d0f1000c41d060181c0840e0556040b0345403070481d1000a0200262002003d19150400341800c141c0f548544440c0148400380400c8804804600d40b280c0c20b0007250461040c42662a03031f10b030780e0781d6070040c064040d98400b6445a0b25091001501d54064060f10b0f80c0c0907416405041602d90f207800645401030b0000309907009103d4410710750002445814510071581036810060801450400024a8031709040640c45407001c95507010071543d4000074000d41641c0017111b03c030340c030350106542d207550540c8264040c9511074200f005005040c50643d02c02e601408054401c1541c6c2d40c0c6400601c1018464040024040c20030010840c000e0000078800d4132a21a0003440130b441c400300c885002d8a550801d40200f000d42c2d54803541005944a110500c00e4482070342010408149816104c24101e400000c04054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 859552374 1250 859551124 859551131
    0x303092001020616090e180106140607020d0c081203040b010f06090e1302060d0507022b111005010e19060b090f010e06180a090905071a1315230d 64
    0x90111701070705d0000064010803410381c1c0d81b8500ba1100d901c85401c0f03c024408554079041c408a0000700101400030007001c082d01151400d40103500b803011050011000307980112407103501080fa540d00f403080707200002d58401419142e0400f402c10f44c940f031006078441c0303c40f402e44600c01c000854000c4035103c2110a10400c0d842c403540c4c0d0140b1400c0110201000940c01140011500c0c120300301688502d02440c296402c4034041d403090081c8011003400f802d031612140165101c1105030521881c0e41f1102186c00505071000c28800d1911070013130300c20a07000b21601d43c075000c0800c68403401d180306602d4000d00020061041c0380c640700001040e4481c0300010303401052007202d0025241d0089440c5c2c80d00b400081d00459a940c1140305885428400b140079501c04c001c08900010000040d000d4100c00170b0b0008098003841d80f803c645000e080b81c206154000402c01840442c8c44200c4c4441c20074000c0010445d100e440c0743d1900001042da0f081d180201504078034003542c0003802540d44040e5490b02c600300c1d4002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 859553624 1250 859552374 859552411
    0xa0c05011b020d081305030703081f0b041403010b04020f0c10020a0e090c12040506012606010b280518040c0f050306060d02040f03030f09080622050a03030920010206 73
    0x3c40300700301d4817002d0054480029103500b0158000340b0b641c411111070702e207124444420100c08640135018030802c0c800c45001d01081c440d9014a0303861500c045402800002c08012540104003640c1080c00a07012221700456034980c603a00c28007003400c418048800451400360000000741644560000071030003180200d002840200c0581c00f19030280c88401040341d402c2c6001c1c64620380d905003d005000340607040040c1d15941182841410100742c0c800350140c0400e0b0f003420462200c81e005043d91000820300045141e1414007000048201030360700f5598103031381d003000003020750703680075500310303003406145404500003410383d0004100245450341d1400755605e845890000c3d56a0080824828040f880010000b0303244d0381e50b10301c4804030383c4240c0711009400c00d910015a40d1125030701c52000b81390401800128100b01906e07006013840300481000248440d243c0fa03845c07401034000402c4020030b903104100b030b05008003d00182041c4800940ca0041c40d006200001e4440070b000c2d081002000d80180740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 859554874 1250 859553624 859553641
    0x50a08070609210b090f0c0105160b06041e050403091208120417040f030203060601050309061305031303030201050415020306030706111c1e0504060c0206130b0a0c05011b020d08 78
    0xc06800f41d80140c010032071402c1a294140e00d40c1c403030001c0302403c0c0c80707440c0d05613407294054025100c2008840881480900341602c03290a0340c07500810f00d40d405a5560300140c0189644983c581e80c1000001d800100c61030306280c050820041d54105c200c24440b2031081d0f60000d410380d4211024440d50b80500c1d065901c842c13404031200391441c2c1c1e001004110106012039010044410a01224000c400300e80c45615104011745680c4000e40e03496000b50032040c0060313800d905401505000c2031262085a141050180203804901e0b0182c0003240140d4582c0c00740024407101a483e100c2c0c092064034114a0350034108002a500c1d50244544420b0100c52030000e20b11450a0110090071801661603105500101e01d00404443d042d00b4801a110f041ca0700d607050080c402c40564060328095105c2052440098003000065048a811901d00f41610340300816020031300409824641019101c07690070306000d203840c50a54010b0070a1900103d00c10101070392080e800148035800041c00d0a2a4450f84c40701e0741c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 859556124 1250 859554874 859554929
    0x809101a01120b090a150b030606030f09030d090605060405090c03030306010f030624020f0304060e0d02040f060603060f091418210d0c0c1a0a0b1306050a08070609 72
    0xc0c0789500c81c03000000c01560703900a030409604840e28180030035141d507c4090f1002d0600041c1d070300c20b800c0301c02030000a400751503a0100c2c42d0842d1660b01100d080409164502056941c1c1c050b08803032258a440034401c40341410700440c0d401403040c6003d449207080c00c402003640e0b0300004105504000c100446246118001d41c01341c400340541c04c17840303210000c2104004500c40c0b40c61001c1c6005104290012039104808410b8400f41c03010707640e03100840c070407120401030a009140d01c282e901030303a6414284c448090318800c0c4001001c10380c50200b5418980b0482102d1541c0d5a482050030f40d041c0403903003480d2082c00140c107910a2404051109148640c88060315210f0007000f0074a001c602d030041124680780e0040070304840e074103804080c04a40302c06c034000c440b24804854001d02a28400a0b1500400d072025010781d0710036030803040003422003c124001803c2100449403080e090740d5070032060000c3e0820405901c003a00c40640203180c16842c151001f003408403244201d14002c180014280c29043c042d80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 859557374 1250 859556124 859556141
    0xe060d030315120506060906062529040b060303040b030112170d05011a07050d0c030216060c050111030606040b0f1e2d0a050c1c0809101a0112 63
    0x4440f085070481c075100740e4480c4161006403045000000081c01460240c0448448003805c20500d040c0c0c1c100348014141c03800b039031b10702110b500c0b5208091132400e0105024071140d15004040c140c0e07903802c007420200002440a003103d40280c00130001800040c0180d0120390448900301007598201505051040b000480b01c1d949e60f202490000714500210a590040d41c140c403544e0075030070f802045050000d82e0b68840c0c044010700c981c0120741c04819041c09800d95080f628040c0c01504c04141452706040c3d0001c0058001c107010a03506190207007407060074481c4c3c501c40440c40000c1e5141d03080c0200000e8590007103114240702e003030000480c12002d100103429202c074143c0e10b1080e0f2041e0519500100c04c80c0e0000c0001a00c00b4489101845000c0304140e011002490b0180b030300b901e88480520100d40691002035800755520908000c81c0e540e001c2d42000f250404d4840d80c0d44881070800c50421801d2a621104588015040c400d03089a184041b8101903040c002c00d00b009800720a00500c008007403c03920 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 859558624 1250 859557374 859557389
    0x507050306010b0a0905030a031e090b0c01020705010e01020a08060d030504030503125106070f0b09010b15071109012426070908030708070c0e060d030315 68
    0x481c0001803480c41e9901034120450b4980f1840042d03500d075024540e1303404a01c20040c0005511245d2100040c2c2004012251001c2d070349082180306032030f84040c0c59a03a1114500c408107a50000f220300611600303201e1440c4087c040002949401d0301d81400030200e40d00a49030501c126001c0001d0170805000b50112001541c0c00070030350352210300310052108001011501c1c90b00300a10707040c6541100110110402c61003c100040c0c150303003407504d400d48040340c84511101008003003e0700070400c6940c8450152001c0351261600044840c2c03245020b1031b003164098500100c5a062400c5008250f45440e40c2040d03c0304408803203a1220740500380144032034131021850360002440e200124060718004000c8144091107414810300d60440f002c210703600340c0504034410b2040300c103514840d060482228030a40001070b600d4005038107034494800d14256480000212741d02c20000944004201c000300821008120320381942c02c051825901090b000030342d2400003010943d460a01d6000c0321206d010800140010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 859559874 1250 859558624 859558633
    0xf0a051303050105070f0315090e03090d081e0724090b0708070f090b04050613051003090606060503060f0d02011e05041a1c0221091005180a0201080405070503 70
    0x101c2c00c1141c003c09081e150b140c0010400036140207070758000d014034865103180c0303030316407000f0ba1074510100000c0c42e0070700d0b1145050108120909080d0342e000030410409014007005030355051108914401108102821942080e0921a0101149124580c042c03c0508450244070100c0ca441004008090000c0024400c1d0384d00828007140c1c0764003c00e03a41c403850f220746070001c50007086203040d2140303802482000041e0340100070030b12041c140390000d4140c0e04440600882055210f00010b049050100421000241e54030f6644d000e000319800360500030f10290501a1840c00d108001c40c1c00c02005c0007216028400f245489811a446000e041e985000f003009200c8124180060061a9034820b2140314500b0610100c001100c0002000300c4490907500090840c0c0071407180b6515010f5000500541041e120040c440c041050700d1180c518800e001c4d90000e01030b01000380803004222000640540c106e041e85000070045038000040302030b000707602420424400e035a88d11f46585849566080039405005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 859561124 1250 859559874 859559879
    0x10315060f03080309010506240705030f190915090902071103061801150f2904090605041b080604112104020306070e10030b1c030e0310110f0a0513 65
    0x3c0480a980120740000083c05142c441d03004009010105070038041d075140c8a0601962400303154002400418840c0080d6828000451081c440301c1e008054000038190700404440c003425030200c40e035009003115003034890003001c2450b0001c02e08d500e0380c025100c5290740003c2070402c0c0422503000e0240d01000034111038145c64601410b1207101900c3d6403070301036917003030024013408080d20f004160f0079034550103000d0554524001c03c010582c480900c40c1035030218645034000606240100410250050000100f2001c0c41c01045c17004441d40d051081c84c0b101c4980300340303180b4190f02410054100004690105485901c0e1a6500e054410320079016041c828180d03850003500400d445491142e0300031400c0da0580e0742c0785801520141040c03400554000091404850721601903030241507500005010707550b1440c041c1b40284c01c400c99884080d00410119100300c0031514082000c1b68911400850a112071103c112005903d40601d0070142d0406101291101e001b5204600741c5203001e0340300308050140e82d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 859562374 1250 859561124 859561133
    0x11803020304060905030708030919030605040503070218090d0518063001060c0609060b0316091d10020a022b030b01050c0303130c2d050f0603010315060f03 69
    0x2c1c0b0501c543c40100b6482400054245000700b0200d00b2a1081c0000d5850012005c04004180f9605030341c00444504011011002c0b0b02a072281d14402c038030030001144e43d8101801080500030031001d428114010380340802818800c08110641d03580000e04005885450403003d090707206a107011082d40164022502189030800760151300724002002401c15040f0314845442d84c0f620b2402d00503400420b00040803c0d00180d619481001500d0041d440000d0341d410300c6000904114012050980c0d070200a00d091181d064544140048500682070305110790841d0000d03140c075844400178002c01d40c0d5012900b00d50f064001d0082c0b92203401460b9510301d444ca8404250a194000b040c20100040d00d4400300300500d50007242107032400c0f0380341c900460840d610107115100e00030282404175000c24040348000b0302003427a0100c00048010074038440f88110302500c414500184940c1c0311510418000702400c0035501c4542c2100c1c1582c1c2c0004c40e81d90021024000c03000500b80ba54003040d520b1100304000000d10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 859563624 1250 859562374 859562377
    0x910091e02130e011d19030e030703080a021b011b061d0f2803170624210112083717040b060f0d0219030201090609060e060703020118030203 62
    0x40001c6039032403075071811700040541d0361400e1142611412021400450210380510702105081c0d800800301e40c0e280f500c0e0341c0c070362520350401010710000d61701c40542414000e0640540281c440002e18104085104000c0c80240380d440394500a80303000c1e83c60300c481d1600c044e803005d681202c000b107100700c0b000b160a01014036a06c0341001503400d800c6218004915296035041403034603456030035030b0b2004a181c154044d82c00035041c01810030780c1e07c03281c8410301c00d44000000300c8690380c24404610680c0c03030766551080142d00512001511445804450050009071120342c0d1308100315401c14007031511910454002c600001072401d101e80c816070110000e100040520300c0b0440c01c2150f03540c07569103480600522402919090390001c10180c0000c00045181c10002c07480c2020400051141c0c0c5c6d0399041e40c0106070345000071443ca481005900e1018001d650b0440036840060506280c003c565500c2c2c490300404030569039425031f120702070020750142451700c00d410a103450b40050241d03101d000c90a02c1c01940e603 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 859564874 1250 859563624 859563641
    0x1509020f090d03081e07080601050d020d0f05090d02070b3f15061e09061204050106080111030408030a0506060706150515040e0a050402011112030910091e02130e01 72
    0x500b80b5404d074078811940200206c0c0148841e48980e1175079215000191902d800180c9189022075080c00100050700c20340c0110f150100c5042e03400220344c14160348450a01480c0711a80045d5071024104102d00ca1005049642260043c142c11050300210104555010754524900140c40d01c100301d440a100c0201030206e0181c40d41e4035a250340c1d40039080034404103000d2116034401d0940441c02201c010350404004001d06880100007600d801261041914280011358064039580e64034002442082c000b4418240386000b11580e82e411803038286c0d16162140303c01014030907810b48800100d081515440300b0786044950060041c0180c0d4480c40c601c1c080f850942c0f08840c440c00607419031039802c010039030845060360b50407011005180d0b940340c0084003030700001d002241040341d0b2003100545c4200030302485606d4446020f91343c0e62418984449868007000c40d0f00342d8052842c2811100021b0506100689082d00050150703005030424000250340400c07118440301c0813402c03c0d0b40c0080c140c40641c0203102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 859566124 1250 859564874 859564891
    0x80906120a0209130903200f07060c02090a270201090b03040b07180b0f0f07170c0c06040e0105040f0e100b1c0506071b051b0f041509020f090d0308 65
    0x201c4003c940203940aa46076101e015011494102c050b01f040380003401d06201c140545021144000d04060031719140c2200307644a0360014814034800c03c01c614007007151581001e5001d00502200108105444500448a01da1074041031218020021039010b200000002c107640322085850f490142403041105104072030050005061601da109a0310600b004441980e08030452581030455980c410741c216071004210a4481c1c9041c00014002076990b5940b6404040c3c1c1c60306551103614000703200b40b03007500344020940300b20001e101c2401035401a4070b06a045400485010499403500c080031401428040702d462954040e52041c921659202d0700540110b074000e0300e18080038002141010248250038100606d150045000700d0305413031040440103c1b40401c0c446000c02c0081580d1010310386408140c1c0b0320004c6d01e07096059041450000410040d10b241a5010302c01d00342c04807032941305094140200d1030074980c0400c2c1100428922011786001c1507020b40000591801ca0401810b02d880407100b490 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 859567374 1250 859566124 859566139
    0xa090902120f03270d0302010e0601080318130f0501030602090a09090c03121103040e013611120a05180d0c020f1302220b0c0a080906120a0209 63
    0x441024001003442c45058818081c6003080c4002480f034803001c2a02070602450541e12426481556400c00303640030440c40707a000018207000c0e40e4200ca0500740d05910108c5c00f9002482408a05d00040c82c0d000002d03501145c444000060080d40e03078004110001021007110300d0800003004120003036000381110201141c4005440b0f940300140400c0d04d00100300104000e03002d840130000104801103103e81207286042042404a001403810f15640140c1d00000011900342d00400000c204085607130140b175031100810520107000000f802e41d81564903030418801d551655030000c40c03008101540e8000907540326040003420100c40c1031020b8642520425002e2995038a4610388000020381801c03403803c640c941c40050386a6800304001d080c1034004082c2c01101024a61268101910040c020300040031a954850280b48240308000361003134200300c40952003000707041011f05d000200c404005038030584803a070303540240b80401d980b8018030f40e0149221b01300e94284008100c071a006030490320070695102 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 859568624 1250 859567374 859567399
    0x3140d09140f0c0a230909010b150f220503250b03040512210703201c05090109020d150f02040e1303030b03070810050901020a09170c0a090902 63
    0x90f489010301d940781c03907001d4411002004010a04503516601032204108004045100d5001c00c0b07900404941c01d002e565560807400300e09141c10394900510703c5000650703d06042c56a00c001c15584529502529040003004015045800034048040079010141c25a03012260b42c5060301c01001044544107080001654041000382081060b688100c3e0018000c109025141c0601c9480360b001440b81d45001b440c02c600c0c0d82e44841440041c0d40540307816500002e010340d01a800f01c43c05503080451801c1131600f0000d1749404c4035601c0c100710312004240c1d400207050701ca600c0d2039801030000742e0000313410120b020f21300b00910000400070b00f0780b20395001c0140203000b036100310f0404078800d900034040354001c3c01c0b000c1522030709200d41c1104e010341f00f804c0000b084c034001c10020307107001d0455100440550043e01c851558410501440e904000303100000e5050041e41da4028141c4205030080c00180c40d8111003004440c0c03020803460200ca5400707011070340314a8450040c000a0312520304140c1c040d25060046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 859569874 1250 859568624 859568653
    0x5010e010b01091208120f070e030606060a0f020705032e06050108190902031203150105031308070f080a02060a0b18060f0d15050a2703140d0914 64
    0x810344007a805035141500c450a020f02c1c0581c4451854045d0b41c3c0ca481404210488050214010302918845180ca00d6a28020400904980003440c0d014041e40103001840700b0b680f6040c040d00c00c3d030401400c00000082907460201c2c49e00c600740e480142d061040c0181d04000202c0c44400c200410868001400d0711460b044850058480510603203001480070390000304620012400c039040c0d00c5aa21002c64450a0341d000a0f00e0300d601d440c0b0b0090088400018001c0584407010310100e48203081c20600d0640c58814501e040303294020b5005130810320000703120400c101c00808403040035a4003803581c50f02c406107040000e5076000103c0702000440e01c0c01c04030000381c0c1b401121001d8202c9140d980d0495560340c17a028402c3c0c1c2010f103107003242c018240c000765000207088002e1032490001c0c5403034000b07224501480d5500c151284002c2d8048865202e104840601c600079a10f4000c0d260141840d074001104000002c2803441144414013280c0d150400b1f0038204081d803820325110110140407252007140f004c46 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 859571124 1250 859569874 859569881
    0x804030c0b070b01032301090302060105040507031401181107030c050c011d19090f0207020f0f01080f0601020c0d05100c1e0c020f04230c070210050c070314010905010e01 75
    0x2c060508511140100001011040ca07003950b90058003050301d2200380b040713545080da402c0a0742280940c00c003a006001904203841082d511940c1d503e000e10480c5200820070250b0744060142c0320004001d4040000200030a80040c010380100340c070600c0d0386d64406d0400510940c3e0544080300e4038014500c02e05010740c4201880346e458000e1700040e020301c0b45c0d580100024400400440a14400005000250340f02180f040c10f03185540d002d4090395929041c41002005054195483d116002240800340640d0b4006c051607485111361300c075182c1c591907041c0180e20f041d00703440415a0003100751141804000c00450700d11694002e805c401c0c403090141d450151603060440040898540b102d14803481d006100b0940f031401c440c0040c08a08801d1000b1010400341c1d081c0c41c0751480054115076848140c9400650040d40c060402e1030140c0c14248145d0006096031420b008403000c01501080c01c51b058001804001d000f15840030001c5120040020054040c016416080e502e41d40707000c101c814845010702 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 859572374 1250 859571124 859571137
    0xf03040510111201050d0510020c0c01080615040b1e04090605120d0f05090103020c0615010906020d050412110d050c012d050c030c060a02120a020a0819020c0a0804030c0b 75
    0x2c40f0003035a080c0400c3c040401280e0a0a50b4584681d90209004044501c010458400740f90040d010340105d210014100740000b80440f4042d100c2c070700c0b489495601e0300d070599003510744d8111301c070303540e0999080a0701e1007840c1590268441070b400500050105070319171003542190003d0344c4800703410784401c0446895110080c8080b0120748101c0b20640b550344148004c20300c42405050041c00c081c0041811460074808542480c0d0881c2c82c4e194001c1c5a607003260703c20340104040d00c01001c804140d46001000340c043d912424450b04406182d03001000b11200c82c1c44880304002d0b00030320394001c450130030039903034425034071004d02180603001440d511a80040c0300c01114212684500010460398100303c400364002c11444846000c18480e4041314a024407405010740046103001d80c80752900107148214520140015000e14030400010001c2500610081c1d032103a900b1170090380c468149903400e0007030b00c640c0b0040802c81c06901c1c05101000400405002030b00e000b18114094641c542d81440d50754070904 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 859573624 1250 859572374 859572397
    0x18080a0f090b1206010e011209050105060a0e0108100903030b0316031b1428080d02010c031e0e0c0d0c1d06090a0e161712030c040e06060f0304051011 66
    0x3d0006002d0f500036044800c507050b041c54151840398400f6015011a00c41040407101a5198004d2008620f0b08845860280a000c130350507103a5450600300541d503904c1600c071103407126110010001030500913400046c2442c4050103981e2440680f844030322070301d01940000c903030b1414038110701903c104015040c0300a46070401c10222a840880c010801c4040303c070a503800c165490424181518002401010010318085005280f00020480b0207400d60700454161010985016190b40d00000001740588d41c10002250004800390b110b0305103810400e59030382040e081302c07072203e455080203202d482803c2220601682000714001090f582c28801505aa4490b80103000c0320210b0908032250f80105a0400c1850803202c0c04c018031002e50b0040034481d4401c45080d0300414000f89900d44c10f2000102008002031002d10710310782011190000d009502520074206030320740008515441c0c100c101c54603c6c01c00c0308400c0c3c80e40740c1407825a940d03482155504c2100382c00d21022901c0029a0707c207543c54600b06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 859574874 1250 859573624 859573657
    0x1120203070f03061e1802070516081015060c0302070e090d030b030f21130e042102061f0e0109020c0f01060f0e0a14100503120310030618080a0f090b 66
    0x1e08126411200c050401b1441941d400c111140010300100000c030107000b4010780190503149842085810314661743e10022000e400c0003180c3c411060300709a00c009544031400c003041201020300f801c83c030f003411a80003d1105070039441440440d000c0021180a10f001070355052144111140601d912a86101c0080d501d0780d220641c030360760000300c0d00c48451b248500415003c2c00c0c03040984140e03940d190301d80d02c0440e0307440003c0140402d000500d02101c07140c3c5400e0f108029800c1c1500c00003036a030900288108464060800311107a031415a100050007002640c3d541c0e400703540c403075120000a50098011b000716118592070381600350f0040c09480c003281d03544150070b250303145018012890341030000d00d21100c01d0358401c55111030824207480c0c0c0f0700400424035120412803c050901d40783c540004540407c1d0344081c820801c01121a031107200a07254004004030351034803030207200402c00007110001012108042000300c4600d40c002c4000c070255400da56100c00e02c1c0c0d581d8070b0440c1d5610035400000d0000e584d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 859576124 1250 859574874 859574879
    0xd0c08030a09080f0f09180907060503090106050a0b0a1e0219080403050a0f02040606031a0f0102070e070c030e0604030213110915090a050117130201120203070f03061e 74
    0x1c1a440003242c0b9000388201031030701e107503090340048039840013100003d00d507400f095401d65406c3c803041800c01d2a4000c82c20a219041c410380321640c89940d031050340d081200c004001030315a5000e420840c000c1101925000c03242e82c4a550203100d5401c00c0074190b00042111040d200480c10440c14902d50f00300e1600600740e0522815a4900d00b0b21100c202074404510802c00000007603003c0121002c0e480c06a0100600026584100010703604181e000c00d0800d400d084c8a0b02030112040001f601c5c4c1d903000c4450707800d40c0250b540141c0c2040e1841d03000d041c03004200b8003006a9181c208a01c0d100c001d1284ea0b5140e000c0c1c614504120a5006078000079401c075020100300d10845109500448100e41828845814074043e000018054443c11b0100000c0c010003007034407091230420784000e1010b0701d02401d000701100301502401c140f40600030292840d800c519109842503901909080c0001451080d0a665030b2a061401800310a144903002000901d80080000d819040300f00502d003e80c80d40c80214411072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 859577374 1250 859576124 859576141
    0x20909011401140c030d1103060f060903010f020a0c030f08040305030a02031510020313050307031a0a0605030d050315010c120e120319080a150303030c11010c09080d0c0803 76
    0x1100080c1c00e040c00b14040c4a04a5000b407003000c3e042e42d143c1c0000566441c0700c00c0b44090b0a461034070046a54440003442444299581d815000240c2c400c250b6005031501c0308003000a001d40250082140301d18800510450803039482450610894000c1e21581c2c4450003103403081316414401c07100680010360078000309044117115001141c20502581d0348444994180c400a40c50030b01c0788a000016a0001482e60100045508800000c01e421000780640515541701c007107004410402520342e215140d07001503680710660b03000c9000303040064120384411428150182056000380ea001003034400840f00d45107103620031014040d07040d07404100d4683c032809540b4150340c1c803018030400980c00720709080d403156010410005003c0c402081d80702846c1d2950940c0000d06000070203804100a10b05140380c029441d070203c0707010f50031250300d490005502107189004403841c004094142c2d01d59403c4c00d152514a036444148001550001c10a40b1114401c2013800e0380c82201d40800101196000c0c0005130000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 859578624 1250 859577374 859577399
    0x302180f0114030f1b01171501050f070c0f0e06030613140712050a06050f01060e010e04020906030901141612230703020406021b013009050f010c0302090901 69
    0x180060b0403120101019840c1c130741802c0340c1444503501d954401c1c489581d40d603485a4004080d52179404a86468140084c80500d02c0e0b2521000c0d90612000080c0500e04c854150f04442030741d60814000410303280c0380c2600e00c03030103620780c0b103052720402c06000403801626001c038140d40a1481036514200601e85aa1151040c005c2181d070842075008020b4001814080c2640701c0d80001d1003007000c0d1140c022145800d0b42120805840c0c1880c41020000500480350480d203401141c9509080c04a840c0e142c50002038040d00c10100300c150001c0c03010080c403108910540080c043e500080740d640f1650f507100c2c802e101d0b129500d040106c001818591028800314000e0307001601c2c1c0048400c00a5041500f1500004101803c2c1c4000d00082d60000303040020f26810322115201c1200d0548010002c42c102000130310080000c100110380c412640780151761400d40b0040360000100348030703041c071038004182841c0c1d858841500c4055929400c04400c60360091107071003296501c3c20004c014140c9a401c010b41442da0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 859579874 1250 859578624 859578659
    0x1c06230105180a05041e05010f05010504181806090201020c03030f0f160501050709030311030f0d020904060321091703121b0d0902120d0e040917040f0302180f01 71
    0xc801c83c20007040e40d072911b0180500c15541c91080d4080d107004500e80004075201613000e403c400100040c203010b1613a2040444088901d1054181c090111000401000344014881d0b000c40c024903084040400a2035003014044600036001c1e5101e0111000506440744580400c5d40506034007040801c620036114806480c01c07911401080ca5411201c2e81c0d8242159402e4841a0204240d94410020558060400030742c52103100d01440c14000d0150710302a59002d055a500401c40d0082250041c42d102d6900c4180216007010308010400c2c1c01030820450390200640b041c1c001002080c2c0801e00c1038500d0b4800e204a0007100041d031810071510304480401c1d03000383c0a000c0a8510824840d10991418050940c9a03081e0400080c041c006104000500f501e00011740c506410990011180a070413042c00100100141e4001c54562043d1400411642c15504824444000420300cc1446062001c0303000550380709031402c1c1003c1402d024071014001d0110b0703507000940308020043c054201242c40a007007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 859581124 1250 859579874 859579879
    0x3082a040b1b1b1003020a020a0b0411130608070f030f0b0915010902030f010e06090109110f0d1d12040b0a03060b0307020c01020c01110a080703051c0623010518 71
    0x4804032818150030403006003040c204501d580c00403c1001e00c1c0c01d681c05420f80d103050074110b1800c0010080a5200c03c9494405081a01c0e0703a8002001d2214481c06d412040100424042d030703c18019480c44c0042c13610b03028034401c0b40b00b1990042000070303600c815036060b05c0e0444003040c2c2e54107041d44c030203083e0314000308900c000307001d41c0d05a80d00080780c050314203000e0702da184405612450b0110501e0740b903110507400f924165120f03100f48200c94481c0000c0d035064035031102c000305c0d044030020100500e5110705140c8586031000081e40f81c1c20703d00b9541c000c3d0140d50001c003000419202031003200783d43c0d207129114081003090420080101c1d1104000038a05840395040c00b00d225695241d500c0020707081200c80401680009084000e00d40c0c1c1885800d20b41707030090070501002062003120b42d0340c80f1030601c402020400c000131041d05260141e015650064a0700c4040310901182000090207802ea80c8200d2518085240300b0b16499080c0e03060151206906039220360401c03042003040729002918142135078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 859582374 1250 859581124 859581157
    0x30309090a0b06040b0403291b0c0a0606030c0b030c0d050603010605060a020f0c0a1802070816030f0206070801030b0601050d060b1303200a05101b03082a040b 70
    0x80c0a0f40369103003d400201780c5015807684891075400e2641004143e0030b9400c107515543d0920500b1001c8811145410901039100103155020403a020101449080054005031080700e060404021803a00020142c81c403d42001589694038018034000340400d859686c0404014040710000d03a1042d0f101d030741c9c0300307100500115010740e0700c1c0c2c0030039a6076004803801001030b00b208a900e046140304024281c6046003c1d1496060540b802d40d800400500c108080584260000307100700c00d2140c08001e0310004042401da280030007040e0714000d0442c0c810b0848075400750260b40e0002c5c031214081c881ca94126508030b10208000ea4600e001100c0f9075000d0f8a40520f2030355140c0700403480d443c0580140209188076524040d4050940c240054142416203201c800c2070303806020080300d600d910b041041220740030b80c1c40e000c105000903001d641c40380c0c550141701900810000e81109056100c99828000c042d607101c010300c1e40103498540e000ca045980d410040c50441048100f245080001c0201454080d5007001c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 859583624 1250 859582374 859582391
    0x92a1703092809020d05160906030903020c04061517040506040f21050c070f0b040905071110061d07081803070c15090b16030c210816030605030309090a 67
    0x1510254181d81102d06040d6020941c4950055940310b05500305130481f0307170701b10401c02d40000202815201d0254404054032400c292040600810000a0321400208140512619481e0740d814881002c484100020302e00d0710000c40f0103080c800d5440c0181c0d0024042d003100c1c0c2c0d803510358082a80400c03404a036010390002200c8805020602110288452030751000e64070300e000002c043c5420344540107040103078241d02c0c0030080401804100d1741101d1071010041030365950454207844801101028055500482180101d07441c450740c03084043c0c4100080d070500d21040d1948c881a4401c04842200c046980302010402001500c0f07600f8000c00210411203244c005580c1d42c17641d030100304d50300c450300442844803849240c070b411410101c041c0c400d02d020141000c0340e420300c1349074110407104043e050201880814003844828004003008400050b11441903c105c40c10041c00e608003120100c03420829a80d405003924841e020741c4040b2040140110304100c02070041040e180780280c00e2109180c1d550518 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 859584874 1250 859583624 859583689
    0xf020f0c0123060603061309110109050a082104030804030f0b010f0e04061a0a0905060909060709140102150c0a110c060403020405150306091c02010b01090612092a170309 75
    0x91201882c4101c0271603c10380d058100147c070b40011908450300c01e0b407a42200307019904d000205e80a421502082d0780009203503a04403200035101365000900907400c005804028000c04c0420030701c89920031083e04480e60398035015404c0c103081b00d00441c0300c000c800b007001c200420065004020500c2410910340c081002e20b02c0010329034589540020f025540321010050940340c0500102e0344031982c407003c1c1c2080e10345040000d100111a0180c4040314600c211a40c3d81644200726440f000a107003a40d40c1001d00302110121040d0300f0480d010000070740034803800c9101c4000886d24600003840501082d003401d045500f00b10103050014040240000380900c2c0041c82c0d901003007598000d1140c1e038060000c2c0565102e1701114241c070040c2c0c503c10340e814800040500d9a21100c44000c80342e4034640404440006820140a000c0441008c0c1007603c060b140105c182ca5186002000c039000001c0c00341d145903441d142d80c4944200300341c0d4201d6a42003801a9034060800141d4003a1103280c241044034941000740c0c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 859586124 1250 859584874 859584881
    0x150310080c0103150512072d05040506180c090306010f09050601020c090105101211071403070c03080a02030c010f1e060f03110a0e040b22050706030f0f020f0c01230606030613 77
    0x108c405411084c02d1010b000156401c81310001d01400d8600b0700046c6010030101d40c822520ba00740301e40100d0600000303410f00e40c0040517640c801c4e0b0001c082d80d21650350b4840741200a02c40d40200598140380101040f8598000202d160000d003000d0041001ca82ca013600300442242c9031000c20060081e0000b00c0c03003001d015449040d0807860b0407401140c6030307111405e0030810101c1c010000142903204004110120710340c92035000440354400daa03103a9410385004120309600960003146055820104050101202ca411620140461040840600c2800b100d540140e030310f144a049818602120b0070300100c1c01d91050809000b030040d00c44803115980d5202e808178618125800c0e504038890806010b0294020744050300b140000032280c2a00207604d403229a201c0440e80b0509040c1030740d6140c2036540e09015040080174040000c800c41d20b80c025604076003096481a4030a80c00d65182c08264030329040005007201603111000407a0100380d866000703114159001502003540701c0b000000800350955a0b01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 859587374 1250 859586124 859586159
    0xe090705120a11240304080c1b09090a0308061203070507080a060f020c0c13240312080c0403110d06110c06100501050711150310080c010315051207 65
    0x10700600c000031150509000d0000c101d20480d11551851080121121400c850900e541c0c004d0407103513540351034600e006c00c03461041c0c1a070b0301c02e5806240c40d0320501200c10500c00b4040d6800f82c07244400c40d0350344881d90303072203032603028000380070070b82202c003048850a00b50140844450710400301ca181107a5910340b5131400c8029446030000d94402c010070380400030a4002c0040e540d40b0b444080d0f0600010b010825196007540716054001d030704d9194406446503280c0c201c10300c110917605498980218003e940c9119503418001a0381503100030445403c0c8a216a10a611445694140d1410315081d42d40c0c8203440d100320049240d029480711001008518035129540f0b0384004809203130303a61101071800509060b4010701b11010b03400c0b045010042179810404443c00681d004580c40c20045540c80019400707800c02c041484103c80100c00c024004110280304426110494101d580d80c40c281d0004400b503920303240540d82c4000400f503040003107080003c10038012020110603102d10b2900d8021029040c030460 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 859588624 1250 859587374 859587409
    0x2215090b0a06080304060503220b010b09090f0f06010f140409020301081005060a0506090a230108180c060a02011d010213080312152b060c02160e090705 67
    0xa60500070048114460350b002480d0315800366003004e28104000c0d10301d000041c4001402065031b029840615440c2c15294040c0c2ea10403048241561600c2d181036061301300c9200b01d8051001c0d10081503515001d482ca40b0300c19032540b21401c010399240c01c01181d1000200080c00b00b8002130034401c480104580300030b04081d01010030010703229071501d034040745816400405050854070f080240b01c00368407030113140402d80741c003035900700d5841384602c000c50348288281d84041d8004400c035410f0700d07082c410000500608102680d9881e500d0320b07200c4c035100e8400000031307401102d98003081540030306041801c043c2c511300109000006820400c000700c000c8d81e0800190091a80e5030003d22749403900012852240507001d0100114200003904921880c900e9010b0814520082000032600e00c2d6030700c4142e0481c003206000e0000360700140b0f00a0380c0602943e01c0304100c46403418203a100d0f83d800e100141e00f40103078440101c115103280c540064580301c000060070400c070718083c0c800003040c00c0d15415890707140d90140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 859589874 1250 859588624 859588643
    0x60e0a12020a0b0a021801050a0905030303130c0e070c0f291f0509040809120a0f021305040b1f170f0c0a2d0302040609051608221509 59
    0x6514003c94100b2004111900040c411300c0032800390701c0c824010b150f43c1c03142820260f0ba141d03030b140d0341528400490352260303034144000070802c11220a80100800c00c42c2c4101d0050318031030307150310144582840c101e81c40e800040000306c01a020448400d01401118024034941880c1d4a84201c0d1940c2580c0110301d41c030200b058003041c80300524010521200b112031030312000c091542044005456810041e0003c1c01009003c5940f60484e501c1c03040001c0c1d4508014201d0f03e81180a2904c220304c9104128180d20800740210300310800712650051902c215030000302c000b465a15400f1042a400d21040c69100c0030320411004034911826281601c04003200c2c1004148841102c844a403401c40c4810b038042c090181c0c00c504200041d0014405c440000104140304208d020b110000c011800300c41d44040d6019041c042d001418000701d84c066030013a00e92060340b9454185001c02540c0d810000c3d502c0820414607080000310081c1c0d01c800482c0c40f0b0348241e2044840f0014040a901640e006c61020340e5803400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 859591124 1250 859589874 859589893
    0x4020403080c0c03060621031908040c050402210907080f0a0c0518010501050708220801050f01050f1003020403020d050f070f0e0f06040b100e040614030a060e0a1202 73
    0x7410400c00b0f010010440c0282800c1c03500380089075040b0502540d409a0103d480c01c42c801070728082c029201d03030f0401c44079011005241c0c240000c200344c1d001d44058070303000070001c008205030030903000701c4e000c0c0040002d00801508020341640301c0c02c0310003020003840b0b001d901c2000c990741c4010b00c090508072410300300610581502d4140381074a25280d038415071060300c202c0881c1d01da0f0300c4000400c0381150001d003880758840310b5504100003180b24030103120407500c80010340e162958400c1d48048090303410341e400030042a0f481d50141005564280a0154440030600111a1501e820450501800c040780340c00760505940e50301050101408a00c01c4809402610b043e400100c000c12080d0018a2a10014032203a0326041601e24640e00140501d0304007001d07880020380c9a00d55400c08000d4420161a01c00140381c0c0d4040102115140c04031148070714200301002880541150010164080c002c01400b812949a603508000b04040b000040040c000d0301004004980002c3c00e140c600406900944103d10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 859592374 1250 859591124 859591147
    0xf0b0f0a0b0d0203120f1e0316020c150a09500d020d020d05100b01180e0a150e0a18031b0318030303020c0f0d0206040f110402040308 59
    0x44030007401034041e080328070302d00c00582d0f80040d181320310000c07000b0300999602c40300d0012681d601c160a0318000111451b03005a58030384d100300045100c0c0d014160566041c0a040000f280c5440a00d09159446070f40740d04940c080c0790b000305c0181910482400e01c13004040e621110b030800c203012811802c4440b00303011054a42040001618070301440192031400002c94500b010700642603141e540a4040e85e0346424810854650180507110703960001e00e0841101d0f2249441075440c8000240c2100207801c01d15805020750148580410351784070203a15410170790800c1d11755074102c540200500c1c00162500380742145422078240c04005480c810307000c003400340b0b0036150b104282c0b82d80b03100c03548018030341042d46070202340c1c45000f6041c41158206550440c0d003041c207040f80d001070040d00c41e0481c1001d04400204041c0c050f801400b260196a0655a0000682c02026150540b803900400541c00c04000180021101d0040301d9500b80701d807401c05c80c10f0400b6030209040b81c0040e0004c613001c40c800140d440348407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 859593624 1250 859592374 859592381
    0x8190608101b080403050c0a021c020406050316030602210c0a0212211b220807030201082206110904050f061c060b04090b01050114030108070605070f0b0f0a 69
    0x26412000c00c1a00d0290b1000000c180010042000c0c007045404140c0100c08541840523040b100d400511400018644548080503580391060882c4036525107040090356007400700329000d11900c10f840700c0314481d02d5500c614001c0c1d0b00ca0840e094400b09000c80503681510018010b40c0a0392810038204c2d03c404013802c010385005420050900020ae080c0300d0703d0f0321b80b100d51000081101c026506114952912a150200302e180c242c41034581d01000318041e01c0c2c0003403008a04905095480280c0d140a6070391110b07d4031007450f0b003c040e0000b500c1c0b00004c2c0c6140c54000c8140030200e01006214030341d100584400c0200d9865002e00b220320203000a03039071800d02d0036014ac00d80100940034000c030203080000010310181d003c032104080c40310580e5055410300c201e42c1d00c8004160360180051180c00982d2510701805402402461b01081602402054071070b01407054038140e0382c040009100c041e00b080c40c1542d01d80c004d204100c5614082d40d4000e000201c0e009a080c0c000d650030b560046a9040040090058 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 859594874 1250 859593624 859593641
    0x5191403030c16110d030e13060b160302150903031005091311010207120c03120f02030304170f1b0106090903120b0a0503160504050601031b0819060810 67
    0x80d50040c800d210281c5000000c80c0c803e41610701110095803464549003503002813100109600084c10161641419042540e9105403034044038803203021101820150b0032122a030040709944941444440400c0000b20800503c10340030380102d903401c6100c45940d00300200101e640520710381020080c8800d4030601360203c0003a00c0f0403211070b1040c3c81c01100000d41c2c19006c0b08007800042d5a400750701074990013444914042c0c100741803545002c400324100384441d6051844111000c605402d010b54200d4800e0041025610466010710b145455075221000114041c078148040244100300c80c0c000710020000900da10030039066403d5000c194000340d607003110030350780c450103c0e40d080610000005c1d0382b0018000c6401c4154000241c48030005d4041091015941c01180c1c151052503100004c0314820642c05040b03510495041c400c566801c4011402d980d070107244100c0e9070800e1200306134064080c04c001031380519070b0118110719040f03585288080da50181d000181c6900400741e800031100d29401003030708 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 859596124 1250 859594874 859594913
    0x30c03050f07020613230a020915150f040512100c0e10181a0309100b0a050105031806011418040803130c0902030406140f151c0519 58
    0x5501d002c990194940c00028402551820406119010030400320f51500c0c21980e00b2450101e041026040b0b20340c1e81448031f03816032161140b50002405505c0040180011010140803810101c8490510541d075411140e0002903c0c4400d01011a103515100b8000035510b040303074001c0c4200c0005010550807500e15051420802001c05012012502c4003502c031503000c01280782620780144240070329020300303699030410b603000c2c2d242d0103244072032081c0c000103140518901c000f9196468409141002141c00142c920f40c2c000b00340100800003903000e2005154044c1900c420103064079a00d000f10b42c1400c00980103022048c1480c00303000c1450178032082d8003410003200c442603075050a040d107502c0b03203c0c0070061032a00203041c42c205030800c000902802c00c2c002e01c2d800e2001c0d5120700f01481c001d4040c0c1000d400401d14051818000750012520342110f071b00401c40c010524041000ba0307001e105224000404020042602d03407150400540c0c2000b10441c0b100c0e400b00c011003884c0c503a2500401d1001410314400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 859597374 1250 859596124 859596151
    0xf150921160f111806060a0215250306051008070c0b04150f09020616020307180245190b03010303171608190c020109110a0b090409170703030c0305 65
    0x504005003201c0c80385c001c9800c8884507140c01000c48105e2508104480e04d910071481d98042c031a01c0c10724110364411010001d03400c07140e4050114011400c5031040d00c24940d01c01040c4c050001582d000310140d07034000070075107050080314440d529285881c007001c0d24100c94203054600a811881407600c00c800070042594002d0124000c9074000820700d02038141a501a60712004c0315030210364081140a00502d550001100c8540c80003c8000082d000354550300311046500c46000c1111007c0b28440310035075242014040c0072081d000b0001b04a480c10110242c0280080301078185150305a1300c843d00400b26084002d030341f0b605501e0001c0c105842d107055081840e07810000e00c9082c0ba071030b5070f01081d0341d046803800c0810f6984460000110000c4a01d01c2e2106a1419001e10100ba5040d004a4180c41c01a5501c80c10490003006000000040d842940143c0c402070246245500d0541c10050700d450040c56030b482d92075600100d5805941c000c8404402013550390402e04051505030141990000c2ca501201c1d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 859598624 1250 859597374 859597399
    0x61805100930080904060e0a0b0103060f081b040618091101030204030b070807050708120603060f0106170606070602030127060506030a0207060608010e0f150921160f11 74
    0x1000c02c040600050503c000884c4103000ca88940c0e000300c0c01496134030170148190819151034002400344442c00c40c000303803d148000c192040404588412101160020821528040480e0010705441d203251075129407204000960703c503c1e000c01e118031581c03c402c00030701101d0a142c0400f0302c0041e0310b80d440c10b250040c0b01c1040890100480c4a074080102d040c4400c680da5034002c100e80394468400010300c10503010622841011140c950b00d40b00d400250304913411511118400c6440c140244643e00015035010502c1c80c00f04c4001254640160000e030126041060f5952450b060b40c00903003008882481d154080c04007151070030744c041184d83c0109400c2000c141040007051350b900c0001d03c484003844d0001038840410102d030303124000a10061000300250010018540e48403480c007a00c5542510802104da00d0712491140305501034170040000780307113000c8040e40c8800d00241e1003007000414030003480104c1c0103081e16500700c0300462084429150240c81ca20b0038600d890803000c04640615002c0145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 859599874 1250 859598624 859598699
    0x30309020a061101051b0909220b07110f07090b030a0c060e15180103090213060e06031605030604140a0b0a020918041a090c121b09040803010618051009 67
    0x12034041041c00c2e00d80707080703a51703d4582403003c070b003001527811011804074400e903004d00a00c144418020720320395851050b0f02c41100d08040e5214068000f0b0b41490304512001c00c0711404075401082035a8025060b03841d05145611002e00c413254503808007011406d8150000050300e4004000d146c2000d00500060070491462300c2503480d0801c40c1751030360515a50314018019541d64a1245501121501c81840a83e031a28a900c004005c2982c0031400381c8601040507041c842d6490310042680c0b0b000c0d004000e1070780c40707071990000000300020110250050310f4a0b02c000c682d401340e07010302c030300e032038010140e03072044038000b07000000ba10100705030034031242c020611002a2168000745030850007040301d0800c64540c026800c0c1064074120751a5070007103004103500c032000b0005c61400941410100d12000c0e80403101d0034407004450480700200b540c07900300014007034503001e0202c08281a094109036403400761034001050748441905448804070390251400c0050381c40e074404580e000b40b000404403212145c00400f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 859601124 1250 859599874 859599877
    0x41101080702030d1508010c091e0305102711010206060a240201110406090314390405040803090111040b04030f0819180e070c0f030309020a061101051b 67
    0x3c81380c2040d6254000c809600305454894409048000b00800c41e5580307486019003180c10500c1060a80d0380e044020021113900100000d00b02c1c2d07009006806d11320300180280000b411100389031407070340300c03001c0c1d2050350b086580d2111440c0c61f01c81e810f58080488004c0001e4986540100841d100f114000428003014840f000d034054502d81960303244256003104c3c44260b0144c000c5504c0c1464480c40843c1c00100765a000c185101201e006405041e885131b07540000e29250351320b0b01031003c03200c00d11a4000d000c100c1402d50b144000107040c01c1c443d0ba0a1040c00004054503810f55065846103004024880081028407401802006001c480303440e09282000c0540349008612000c0c082d0750404400c1c41c2804100011181580c051041081c00c525000300090240140011222041c1c00101c0011400300801c082c0e07180944815105d42c00c070311040b5503450070340200c1c01c4070460400da101c241d400f0060b206d401994018011342d4603015441f04030140940e007140c1000700f481030200407030410105038000100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 859602374 1250 859601124 859601137
    0x150610120506031c030c030f0603030806061303050303181b01021b06070c090603121103090618030d0f0e0901121b0e040c0501030b041e0218060c0604110108070203 72
    0x101144603070307816001905107802113050800504038403918008042e8158000618002071351410009002090f10810469800340402404100c00b140407450a00d8048080d01111125221208810ba180e0b0745490442e0001d850024540d080c03029112030702c030800d120011025803050030b210840064400000d6841402106000b5089400c034088400c60302c5140440361132039044151031524960359010100100094401522085500c940d0011910710030b4811203c40c1031a10002c508103160881040460f0740f00b505500c0295035a541301c02400c1e28180700002c059002901c40c035088100e1004003400c180350315400248a14030303680040c4103424803066102c0b074590704a030b1041644101051030119004903a00700c0f10404480e1004c000410407c0d0b52840290b520a036002c1c0a6030794080c0c1400240c8440b48030030550004001020441950389501811581500c01e01c01845140203901103003455220140391800703500841c01308400e20400082080c0d1403e82840c0061071031070280c030029102d02400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 859603624 1250 859602374 859602407
    0x120c03020f192d1202031204032f030d020d1206082a0d082115040905031603091707180507090e0a05070f02010501180e0307080408150610 61
    0x7450194444040c4003c0b540c038142491800c894081c1d2034010302c4c0450440074004911a100301c0030600c180c2081042074500701c0703910440c982c181e030b620b4401e20040c00c00410b02c094040d9100581403806e03a9001c00c810714a49045401811a20710950001801c00c1050040d4030701690030070004000c100b03130008141d08003a8111011114001c0d04074440841c9c0010740035910361080152490401f4044c40308014610507440042400c1b00a407030b1807041d40c0000f0111500c40310102031b40080c41e20b904254010840ca14420700030340307240c042c0000a1404013100440103800042a0034002c0c4103a082031070041521101100c0182003c030b14040d80140c03d450700601e0101c201d5141d0f00441c40041c0900038800113001401440411481c02c1321414008080c12285840020100104a014140103208050584030324000c1560148109003000340500500c0418410302c0c8400c02040c0c0110720401f01500c041c11803071014100046007109142d14006000d071640340325488801000304c1c1541c000c02e0720303c40f15040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 859604874 1250 859603624 859603649
    0x182117154006050307031104061e090e1c08090703050111090f040e061f081e1615030207081308070302031b010912031b0c06031802210304120c03020f19 67
    0x7c500c0850050486a8010b40c1d0205680a0004075107542c0d501d0704d01543d0949104026a40350709841903514142c41c0076402e056203080d60b43d9280c00b4407030303004c06601c00b003903a007240d02c41c0381c6d0303945c840d03007154140781c40e4454039440800c000042d850100707891905600200d40c280528021020150703200d80c03000d400740c4460704c1c640c0e0449140b5880308829100901c40c00b4150350f007121a038408440c0c070b0603221812110340e0180d400b00f00c0c105074951000c0d07000e84501441801c40f022401509034001e61102a00b40c4002c90140312516642101750081c80140c03c640000e00180d900c0e6105261030b11203082140300559407060f44440300743c2d0b48040030004668070070308005010390103130505481d14031010401550311003906400380248160198000121241542e0070080031452000901c400c1c0110007000354030480c241441111035038000c40c6500c442a485d4280c0c0d107803942c2c50140c0d101500004100702c0c5c255402c86000c0081d881c0c60142d02400140c00d441e2514100401c2102140b240514066112040d65 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 859606124 1250 859604874 859604903
    0x5030127170408070f05040e0a120903060911030607050c0c010e010e0603041b1205030f0706110a08151e040f18211715400605030703 59
    0x51100c580003101c007105032000c0c2d566440300502519040540034601508143d80c038000750b05d003814462100e0031000400034004441d03c0b82d640138044900203020b0010002810340100101e0f80600c1a0000940300705c000307a0b99030003c2c1c000d044c10070000a00a00500c0803c3c009000001c0b4040b460212400091a1041d2070245034001070b40c40007d103124068000d2000b004000400c41c01910340c080280a0080d0f22503101d540f82260311001141d05401800380d001445100410b911038400360002070f202c6c2c070700030135203155400c03c0105a400c41c82c0d00340c000a026a0a0020600d158525540d40c18020b03650346070342c1001d40000700640e20024820a000300e03901c0e07128110810103548070f09519004403403241490b02c00c606005a903c641900c0040020f00c03d101c0c4e40d001c440c0643d0003c5c0000c0c00741c0c0c2c4220710b99900c88807012a541c214481068005601082c1607800c0034145850744401e0344405119103c4c0f615448060034008070709100d11602d0383c50a9014045641c000400008aa9000301c0d504403015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 859607374 1250 859606124 859606133
    0xc060f100b0f1207080709050906030d120b040c0f031512020d0501110a050405150304030c02091806040602180a0b0f0d0f410a02370905030127 63
    0x40f07440c058401d8402c40406102c0c500d0307484410f55000360030540d9500034640e107610412050020aa48807940f6a0040c0c1c0724900c145e00803043c18a01040b01e040000b4a552908003003015110030940b03400004288110f5400303e203030503100d50600300e800340344003640c1d00f400c02582e03644014000c030340030f44190241d40650040041c01d400c40b5840310980802d60361aa2a0404090050b03041402178074454440045644d003040d00349403e607889250107175904807049030316400344005044085d2030420708410040603880708031000c1000f24041c61160100507505c0341c03034241440c03031074850220407441190342200030445da6401780e090b40c1400c01000c52895441848140d5003005081850710398407840c2c10044c0c00c005040744070601203001c802c0d94140049509a040c2c6902032a0909015840010b003aa40070442c0e80000d5030280881d00c1001c0c8011840c42d007500b06140034048155685030600c4015901900900c4e44802554024035080e4000c3c00043c00001750043d081001c03180f0503008000d100c10040a02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 859608624 1250 859607374 859607377
    0x1170d2a170a030c08060306040609050a0506070c0c090c0807030f061d0412140f030601030b0603042411180102150405150114030c012001110c060f100b0f 68
    0x103a50103612a024071022001d00c02264121032045004a481c007021080e400d0302500e040c912030f180007006801c172030ba9107a640c40c1c010144520160f420303104000041000034010041180186400c3d01c44508040b0036103842a04070800e50094480705040c51900c114040e000310781540c001883e030130045070048040481d5001443c0517402498552840c04480150081d00c1c45080d0185000f2460010070184041080c2c0720181200740141da03480c010400149030000ca00040c6070001030514001c0746c0c03810107000040340c0740c10a0700c007641c032845411341000400407102e0f48050300034180d130b000780700c0f5074032030b124110840c010f4801c1c1c06081d401c60302c0160200e0703200340f20f020340d085c0d45050040c3c0c035428181082da50b552590040e440038a0348040001c10800c541041c050020305005000b040500300d81001100c290702d41507620b0302060700e94100b014160310280030b013030703c0c205001400603101d25140080360314015000d440c103201030a03002c6c14400f0b0240c110140105861003400c1c3e0544da03000c00c06800015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 859609874 1250 859608624 859608707
    0x1103120a1b17090601050a090e070b0d0f050114060706050a180302030c2506050a0c2301060504060e060d1a070c110108010620030c03040e01170d 64
    0x1400105001108541101e00c2d51004102c8081000460b540e83d0381c00d0b540c5030002e00640758001000c8034204604407080c5c12921400b8491810b61b50070a80d076418102040c2c103c8404030b10415140c0400b542e07070000e640708a80c010068070100d495074281410108450784500b250140501c2d4464000a07001401034201070080d4504140810365006c05083c001d440381c020b06000c020714019600c1da40e0912160901d40703110b14500005604440e03107050400c0e1165440106580d0521020b400704a01050489152404025102004481b200c04801d6094210b40c6503801c05031041d40340c82000d018202017504841e41c42101500c40c00340d07045c02d40c1801e002125841c2d08000c000c070b42440800c54040d900c03a07010340449200c1d0442171800306580f001951502800d00803940024001310004100d41da60f18491040c40c00c0940503a498906400501c034150b074030a400c020214074071400100215241540310320a4840c107440508032440c40264001d00854020030312450300b904a060109000d210310148018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 859611124 1250 859609874 859609901
    0x610090f02190504030510090201020318120703030503070e06040339091e0b09070e15120108070621020f040509040b1f06020619020708030106020705101103120a 71
    0x21400c503000d200400e01c1c4e002d07000c21039460181e0101d45148004a01660540903816006542403041d0003040d0728030302d0101000158044103100350021a2303030081c0502c0024500075a9410740c0c030300d00001302a00e061000c41d0103134000c0004100802c08a10302400c02c004140d4a48034880f482405151260380c0c1540c1c0c200841340d00c0b080124001035981950b0b01503221807000818104200c10080d035400b0440d1100a00c6913000380c400400035035154401d42c1003444000e001880481788105082c1e0140440e0015100f15403400030410060208aa041001c080100024500044000020892840054140020410001d802007450020340c811a01a20003038600a0b040440074a03090074110525501502d45003c0b860b01c1003004030118040008807025a80ca5800603d5581ca51105c180e50710a02d02140c2800c096091010314001001c910046008240c80d44c01008102e0400b0204103503650141410303014040100300e0280324078004400c1d11801039904000480a50359a0003030005400d228030720b00e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 859612374 1250 859611124 859611157
    0xe0a02090c1b0f07050a051507020d0c09020c0a11060a051923071a061e040f020c33130212190b010518010b03093c0610090f02 56
    0x3e0f0000041160884604540144400d9540c80c1409198854031110300001402000f00c1005030070b00d00740548800388141d031900070300c95841d1008012070304580484039198220402440a100f0a8640c0d05592072003203c0151800500404c0a802031003030002964800a40501480c191402811105d8160301c03110310401c0c4c0e101242542d4440c035400708800302c03828060502126884c4028103199480340b42c0241415111002581d400b1044840c030a08060f4410340340c101010000110f0700107003c00e240800003c003042405d991603607080e012034007201090b20201c200326465805010080941040c880e41a814201d50a4000301c0d10341c5102c0d12141c4141d00c6001c1d0308090361400c40000303440c000d006049501e01c9980710b500b017000c1c030302c01809098400c040080061020303d01c1c0034011500410100c0c110784407030b40c0400f28440c6036103040c1502c0049903007852242c45064044803101d0740d07170b10a038005001c0e540303441450003588c609680201c00d20951303101c1044074183c50701d070b0464018280740060328 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 859613624 1250 859612374 859612393
    0xc040819210801030b10060e190308040b042301050a210c110d051c0b060408120405130212010e0a0f020d1a0a0e01090b04230a0e0a02090c1b 62
    0x2c2c14400080c0310466481a5810000e03d0031130301c1c00c0010007505c0f01ea64070b078130400c5511403c10001882e070032071141e01442d80120010000b40403c0040000f4070300510360f02d0f143c070b2401060201d1904040c0e845031401040303c84808050f030f40201142c1101e5154101180d0f900310302c01090580e600c0d10f0424140c01441c1010342225560050710000215a00b0003c4a5040018036402c44180c0201e81d64416100383c0f008180d66150903680148001c1c00000e0300c1d041c2800d0b5102002458030b40c107411451200c03403000034280b00c1418500b1003004884114001036141100342e62001098002c1407194291486c00340000c1141c1040c01d4126680d84044800b00b50b4440c1e078180d1074200103284402c0e501d030900c0c82c01400041ca90505a07441070455003007200c41000c1340e04e09034908010304803d420042e070040d9601c000380c00307079030010441144081c00c0040000e40d610700a18844103d840c05041e0f01802d601c682401401a5a41c1d2841c07940000f4402030700c1d448202e010940e00508441400b58680e901503103558 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 859614874 1250 859613624 859613627
    0xa02091003050421051e070503040f06020724030c030b1207170708060a050901020706240503030f0a0507020409020a030813090c120b131a03060c04081921 68
    0x20720302890003446198503100f2440e100d413014000700044403020039410f11200d4081402240010030341c00a003440c42d440c06519aa641e415503020fa04801f814418108090051950400880001c0e2865511030707000c0e40b12041c80e0f074401d8440404948105a243c4a403004081c1c0f2a80024654000150502d0340b8103500954503622003400b405035100300251000d0a04002c0b07000110030084520042c00f9110030b480d81e500302c00103008000d100100a40d002c00c001000211f02c0d2044120108400b9800080715a00c9600f1680c4041c003a0f2020b032207507100303021400440103070700100e03000040d0a0030030582d030348242d01c04200600100c0002035486088164004103200390000240415082060444407081e1031311001c138100c5007000000400103140981d0b840c0d01590562025000c40701c0200041ca46401400104068030715040000602000c000540e003c1410208526504407003404140c81c14607082440843d985c000345584059540c1c400180c000500c507608004882405d04028a40e81c1144881e40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 859616124 1250 859614874 859614881
    0x90b031503010b03060606091e180106030e1203060d02011101140601081e0610020f1e010c0206040f0b04080c01181401050f06040518420406050a02091003 68
    0x3650301030b5081090620703440c44d01064051050740c0041c52541440b400b1010b11100905215901081c1061131000c0e081a9984030000b070b498502c5945041515030400c04010141c4000d000a28072542c0240d000c0002078601c4815258843ca0580f049400c1c2038007800121400040500195800d52030f0064440344040c03a044d0b03641c420134081c3c0300ca22103030300c802c10344a450a04080c03003210242c04183c00b2516502e44101002518512441100c500c0761903105e40e1401c0802a60341000f1407900b100c07046900071001e0140302038a10550025100c60301d01b5442d082d051507001d0300d00031300d400800c0c000201008500700564600841800003000a440030000c60b405011055006568040c0000503801c40f030b40050140c40e100380410f02e20706a60b03840f4842404017505026002100481480c80d030447c3e2900108090406c110040c042941d820f40c4550f9407280f00d807100b82c51803054540750180200c4c0344420616941e0880d6000714005855034400c40c18600a00911404a030322248100c01c2080145e170580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 859617374 1250 859616124 859616161
    0x818160b04051809060703050a0f050f0403020d0906050d020f07051522030c060506032a0901140d03050c120706050a0e0303071704020a0506070f031d1c03090b03 71
    0x1c4544075040500710240ca0f032908200c0d000d0025034000343c001401c8501c40e8100b940c110190640100c4c003000e0220704070040c4d032003c0b10440090502e550802060550400082c03103000f00d1410114203280c1030010041c194451941c60060082d00060f0925248000c0c50880303038940d801c64180c807403500110103080402c0354159244a030860b51101800c1c0304040782c82801d00304641c191502400c1051036074417070003d080000c05803989170040707c0a40c980c1d00d4141029141c41c081c45e0703011080354803032441045403c20301a0400e0150390b420080e20b000c0790f110b51501c0511590141011030315403084082c2c8614005645c0ca11400d03c00000c14103008001a13900700c0e60045c04940070078003803680e0049500d0358a010490b5403100041020003006240b015119039150004e001424040c1c440da144e80114166921949044a07402c0402904200b1305602c40400405203007820f11180b400040d100002c0c00c507030012010700319007124a100400805000b0300405c402403911500c1140c681c80c0841d40038010b8580748 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 859618624 1250 859617374 859617379
    0x3030c0503070228320117090106091a010e1210020f0703021c0516060e0706270513020c151008010f050103080412140f070312020d0818160b0405 64
    0x45801283e003421504040440708440440171039a50040d4118002d01080310a9141c107101941084020400c070550034940301d866154004152246016555002c84950f03540d8601c042c100d07840c84000c240c1e4009018440c42204840b0b90b01e81710121840c1508108a41081c0b0b011244000703110f40020607200083c064050181e02500c60705a08813001548a0b0820711080000031020404e000369108035216544803d4081c480001e0009403107842546000b91a070802000708844540381441885424030104d5400d542c0703000540381c585001d0202d42e960f00071800e560349039900800ea046035034004200340e003ca40c1690010141c40d052103003101c02ea42c1d1a40c040c803c031550a24455506a0185000315130417250b00c01c840500e03042c90282504070b85200200126049100c070449031506100801692481000c59400340c5415840c0d8036020010400c00140c1c1d0302590003500000c0002c581203001190311010420840c60340204000056040250404200f801c03c0e150203000308864034540060320030349009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 859619874 1250 859618624 859618699
    0x30a0c1401230f040506010519031406010504060f03080301061b0203010516021b01080402060f1309050613050103121815020f0606030109021c0305070204020f120a0203060a03030c05030702 83
    0x60201101e8040d00807a03024017642e122100402250424008010140ca802e0000800542c5c80c1e545210705400c8446044800d0b0340b21030014006481c191081c42c00901c0c410b41580c0c449455a9141000f9000500c581c5042c015241401c52800f200011412419a4020300810803454038001031080d248259202c40c005200e500440079650921408503070155030147c4404145641d55800c01c4141d51006c2c8041c10080d8007032021030300355075886a00b84040c056903072001c00c0034640441484a0f6080628031105e0260130000100007260581002c00d42c095418540100d824143e03d1801400c0b40c41c55001c1d101605144207407400085d03010500090944170501030358410344440b41003500740d42800001030b41c402c48480c40c020240c0c2e4003503031031b102042c40390030101e08048a0750000f070101d80041c800780420003400145440c02c441508482d61340010342080844c298105000844d9094001340002030502000d03500d000c05120b4104141e0380965030003044680c0440c104820042d0380710044482d280200720 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 859621124 1250 859619874 859619881
    0x612060c02100606020a110a0e0f01031a13141c0e1903030215180a060b180f1305070b03070903051605092725060c05030a0c140123 58
    0x1900d0007000100c038403940c011b02951009880f100c0c043c8600100e0154007030305034480003c4003d148003180b4031a1042480c0c1010940c0745003418908410200070200128150b0f10400044880c40305400b00c110303410004d508503000c80301000034644076002042103100341d280c03425aa01c2540c40110303c001c051095400b01e0b402c180e4445032845c002c0c814040100583c018000303001480703862100c0f01d036002803d401c031484420700414042e170502d4001c2106550b400d45400b10070200f400d01e2a100072420008034164a42480c1c2709250180e02c840107041da05600f18020040c0c41417141c108850805030005001e01c41d070740d05140101a005101d0b0344000c851134001c000041030780403040b21a50701255005410b040b590342c0e0303120078051040914110309041c101607072441401c00070104150001c1c0c54081c03d41c8000d4071603591044c0c520b0f10b06944403404010103020f84400203440482520a190301d0340c1070000e400540b03441c1406494040301600d222039841d0280003039a250440b1101101c1001d107800c40c3c04141c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 859622374 1250 859621124 859621153
    0x15050a0801050f06010f090e070f080c031006050c0f060a0911010503091b1507031d0607151a13090c12021014090310050a060f06080411040612060c02 66
    0x20b10448590300050201c03000504554000c014080501ca0107180000540391141101410700390309558000005805404a00380030303030454869a0030049011400d42946007101c2e141c0110f114500484042000114081a2540041025481a40c13807a01a5010b40c54149450801844520010380d0101380d400d0304c10050b5400f0f0001c41e401007480c1d43c09030841508014054a102d01030300c4060340c02500c011f408107841e0401001a1540e107110b5176800c085281550001640da5400300e5000f80310744000c000300b0340011005002c280e400080c1d6040402d24001e00c803408150454102e40c0950004045600294090302903031086080b40d2044000690060315241070b0030300e004080c6002908118010040c201150154064a0100c18004100b6107001c1d80040440d0611300f43d07040303c1801c180c0310000d03c95811144c0c042e1101502c0c0d0032414101841c6001c20050244201600c040c01541d02480d8030f1105072120b40006004d0280c08401814110701454090010030852000d20010301405401002d00c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 859623624 1250 859622374 859622381
    0x1e1915170d0509061204021807020c0f01081003061e0c0915020a08030604022d07031103091f020c04060f06030c03060b0912010b09270a05070e04020d020415050a0801 73
    0x580c0f0250100c0d081c40004a9000c09125014105aa214407010000742040340c1800302c0c184501c2d801c2d4080c010b001205420300100220100c0c02ca0305110200e8100100d110304140b03284100d9402140c089440c1ca984014056200290f00d00411000e05081460305000d4100000d68211030401030f0503024260b40b04000c80c1ca83d0594540141103840810204a161426802800c0841c1000840c05241d0003400d80d107403640c254000f00c0a01e0791001040000a08d038000e8405003080c034001c0051450803000306c00141c02e040c0c40b40d1604180300070304c400005e5001d2013004a080d0005000e08104103442d12074403040c21212407807081c01d00090070703c51b0280b8410701c00d0107008200e0f22140802400c0c042c0b410204a0072805000b8448001d640e0392030108420b0380c81d0f046040c004d40b0000c01c0050b4002c640f004103044c801e41422200f00300c0e401400004005580040e920f01250155050001d0a482c5d82c8000307602c5074001e2501940c4541006c14610358803204240360407c07100c1c120f0342c69040a507211032907801e9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 859624874 1250 859623624 859623637
    0x803010503061024021014164503030804120c0302071406070206120702070503030a050414011b030f0e150414040e060109141e1915170d05 61
    0x1600e001d0000c2401840c80c150480201c3e900d130b8010f6030280c414100c03004d412540710351602c188068001060002c4207400c00b44100a4140c24902248008415904040012001800f03034808100725024840c40c2d0744903070704108101d02d000400011107680ca00740181924001d0714292441d02402030826030540c0506900030000b80d0540240c15420b10f450400301c42d21848100c3c00d50003001c00c1000c3c0b80143d50b00c1004150840c13135400c03800c0780c43c14001c1000b89403280310b0304060b010754010821a109582c00c041520220b442c041d101e2400260020012514010202202c50801d101d40d100c7c6010150000056030303800e4003940e0707000b90030030800003004020065060112056041000706008000e040760f01e00304181805000450b106008251543c500a001d0340020320301c550701c1028a02081404090030740000500d800320810a40b4000c44440940c1301601c00c1d0380c862040b40200c17008201d560005450491040700c0d402c0e00b01c0d82c40d40403001c0c071200140c092996010b007034900058a4080c1c01903030f45 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 859626124 1250 859624874 859624889
    0x7080313061b0c0f150213080105060402070f060e010b0402160209060906060a03020306150c07031a150906010c05030a090303122c070e0705121302010f0e041808030105030610 77
    0xf80303d80355032180e40320131070303050303000d907942d00301c054000d000c1c40f1980c0001c04503134598515002409141440c5a0308550001c0c3c1420701c50b0b4010848607011a0f04581a01481604140000383c0c5482c2606418010205803107113b80003030002c2076200c0700310841c0b004801020300903030b401140b42d40c421003000000d0310201c5240b940228117000300c01800344a9405103502140260021140c003502d04102d00450b0000082540180d000b15070901c20810b60100384007840b65200c484c01038900380708490128a4011144441c0202e402c1400034003035a10400025003481d8010050707e5480348640001400c0c070300d0902080d004150603182c00124880745104401d82080c5018101e03410a60000c542940c16081c02001d5105214001010510030030300e500c414025580d03500c901e56142c3d900c0c101c2400e01d4400500b01141d4a80f6441c400c030140c3d82000c2110b81c41d62030751900c0740d42c803881e2100083c014100c0b00049800300e682c9201d944104030640b00110b040e24011802c413030072580c3d1000c103400781030142e004569 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 859627374 1250 859626124 859626137
    0xa050a0605060f0c12070804080d020303100608090109060e0d0f180311060f18010f030e0d031544120904060810060501090920090607080313061b 64
    0x80300041c140042e040b13008072441a102600c039048203100f01900185030507110010000741c100074072802000000c2c0114600e0000d1411031a0417420318014004c01d2213000240a0701800050048000b03600038400e40303030700c00020442c0079588c81030550b0b50b246048400021403803908582000901980c1e5603c1d010303101d2014210f05508507543c107a44074100d60b403d10b0b0000300520000000c0c0c09900e024003000e03089a0700404901500306c00041143e4480400c0c0024985000da40e02600480810040c002081604010984034060400c10046140030750001c1744090824110f441a8248403507064003004120818009401c0d407960a401000003448212071140e2040512039040f001d2007018115060000340009401591064464100041e003130701003040c00d554a505200960700812104003070910355104000620124050010103081035188030600702020500341940c4d0b840b03204444400d0380c40f0300d0460301ca007010320018072071600ca0780b02180da103420003104009150a00e112054504c0342075490300c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 859628624 1250 859627374 859627387
    0x30a12030b01090e0a090206071e1a0708040308060613030501020915030f0a091b03030e012c0607020609060a050307090801020702090601050c01090b0903042c1609080a06050a050a060506 82
    0x410080c0016a0100e8000b8000e2141001103043d18240945803150701c4580d214ac803072039250060b8105101c001200c1006000018042e1030741d4440d801c0c3c1c0e44036516051201482d1104000500d01e0300030702c9884021034286001c003004000c01900030b40b10040d01030781d4491030303600d040303060f917030b05010440e90300600c0b283d030710001004404250000704070b0b80e010704480003020301d5036544100d01030020b4000741d01103500702d0b42100a95a1240000c00c0b0018800c01300007494158002a0380e82c008482c0017580b0600340421001c2c00e642c1c51b01e0449100384001000c03680e9a01e01260064981d070000c50710314000c14001c403000100f4181c180201c0380078586c02440040079541e0b4400559042c4c0080c09410890365964140400243c6a0f0603034502032090032000710380f620300c0d000d010000301c2c0f11521486601200480546217840da00d0b584103030070804144980c54240c040d031004450a0301a98002601c51240300351450074402164072040c0140d140304401d2055a440c0149501610f14500c2096003080041000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 859629874 1250 859628624 859628641
    0x1120f1707020a300209180309030102071a1003080d020a1205070306090c030b03070e070c150603031e0801030303020d02130311030c27040c05030a12030b01090e 71
    0x30044005280461400d0020030340100300042c00710303000700c0b030300c41d00da41c0507a1240000c0811244204500300c850030200b1401d68049107910b08080c1003100350805000320400d40f00c030f0070700c1511031411303019008540b03480441c1030260012502040c040852501c04c1d000c68150b01d82011541e090f203401c11440341c5896a0304074a500250f111562170400c0000c01c1601e20300c05846409468001c040650b0080f58643c10006851f044078900765501003414030382007000140b620007044250481d410400c408030360740c1e503c0b9000d850850a486008201405484040392180d070300c0e6000d50103480c042c0c4c0d114290320100303080d1800051910311140d00800c281c03000400c0000c0c401e40041210a0782e205c2c02508051107148106c801c1c44403038004507803004040240f5000c6003000c12501c0c90034803086800d007075201d030021041d071084200c0845001084c50103c0006061140c40701034400240b13009000c0f65456021424030030804c0d8a11460f0000003030070304400700010f40c455458642901c4140604586a0300d440f00e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 859631124 1250 859629874 859629893
    0x7020714040216050a0209100e040b06120f010c1b0812270105061e0a0306020901180b030717090d0507060f02220b0a0c02010804060605060c010f0501120f 68
    0x140355072081e020041501808143c01c10312400b00d125400400307152000b40b04000304c44800070100c20801e1900c0c40c003000b03280322510310b0541003904200504056283e100210b004099445021040d62080c8201c41d170146030158021403400303d41d03039100c4a14a02e400000409107020a0014120880030300011040544195980390080c03005192080c0c0301c44814814a42804100004001c0741d40d207c08001d1242041141103040640e58810308402c03c006100281564420340070240007543e000c5103242c20744c1d01a02662020100316035094541990790651101e8950088851500003074042014440c0b8130103401071140100c01d404041e080b415002541150b01d43c01c0300e1000da40c280e403039070b58094000c2c2851000b8811150200d1100d040c41c10303490044481c00a0781e5102482040c41008400405a1b012040b601010360900c0c1082d4152110b0800f40041c08181d040b20390b10000002c3c525603e554150300c00380011030007000c103001c581e81e141103415844a140a0141040f84201500400600300e10b1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 859632374 1250 859631124 859631159
    0x20109150507121d070b07050a0f060e150108011820010915050304050d0c05030a0c081b1e1f27030c020909010b0f060906040308070503130806070207 66
    0x80d00c0d60b420b003c00c0b5252420345030708259596500c0541c0f14050520001802060054000491483d00c1c090055403144c2d07688031a050301606814407403802808004180c2c2202c00440407800441d40c1860854a44495160083c40307800c030b896288c00b09030300705d000424110003030040e00245803118841112004490400c180d100081c100a05500085822035401030341c4042c5000c84c3c2e580d15140c2c903142ca0001c2c68500c01c1d20001c0144079660500c4400500000100e0b48000e405190030140081207144c41e106600801c0c140302c0403a4081440140d5801e400194800440801d03e1113088401c1c0c41c0150300d45030040d600c040040210308644040c0010603a801800e05a4000c012030900c40600060011916082000480c00903060048503801e614010804540041d0410000c201030501c0800090303081035801c043c41d0155001040c3c0300c0590b0b40c0c460030366008580101282d5619011480c14507120750040d00e4100034002c55000200e5030440001da50f900c111102c0e0010440d80d030600003140d146c1107201 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 859633624 1250 859632374 859632377
    0x70c02030d031d07031a09030304080d0903030e2514030616091d040510020f0703031508030a0905040f050603062e091b020c0a060e0a05062107020109150507 69
    0x81601098203d0f040080b000198080e400d44c0026451240704221030324001781050b00303568024418400880c180d202105d03080e0841a400090006181c90300780e010b040d100180901c01d0051402d101c081c05180e070681200c0381c2000d000c480240303885010b031700c240c1004845035a400d680001c00003020050380000314102c001e038030f08003458110f65079502c4040c0c0d00306003400340c5041241c0c0801c0c0f000308181000300112515154405604280300e140c0c68a80900800b24050201611500da8008003d011654040a01208400e80b581d1380d2f41040e014102d4001c61140754051458103060010030303200d51003928049c0341d004024016035180e62040c4e0741d17000c0312032010503844510109500368012900040344001c000708040852103107408110103600d021204c14000541d001011a56090350300c000c1d801e42607520a0808800e80080f030070104181c0581070300140d400000000c1d00b0340d8904101c40d000540e0240c9503800040700d03514403808074281c4e20702610042403003549441104280c1415089241c3c0a6000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 859634874 1250 859633624 859633661
    0xa0305061201320105100c0c0f08010902031006050d0813091d100b03120d0f050a1b14040315090203060f15150a080702031303050c09070c02030d03 65
    0x20790080d4219012001c40e0f410300411450000d180300e03003014550211040440304003006601d490080b841c070790a4607008800f04a2040020b6080000044040340074280e41c208004690340c6581d001c40c000c3c400b8000c02c0c3e219200381c201c146686112401540b05840001d04802c0928006a03140d0640c0d03003064440c1043c5a055803004180e201c1c1d21720443c80042600000000710748510300300c0c11300703059070a4050040d41e41080c20403201a2000581c1c84528070740145103945d200c0000c004c135002803020384444491182420144021424650082c0d0113006821401042400407540c0c1601c0420b624035080000040034441040403070100e07189046424025100072445400c141e00090500b0022980004a808100c041c880c00e2081f0107240d81500806441e42451104609508101402030088400c2045024000140c03010700c00d00a60341c100f00342c0008014076503140d103481a250030304561414050003800c8005002c96121308800c409d010340240203041048100c1404402600e281403a114030003a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 859636124 1250 859634874 859634899
    0x32502030304080a0b010f051f080a021e070302070b1606090f02061303060614090c09030717061909120804110d05280201050a08040c090c020c01140c030a030506 71
    0x3408041310541c0310b10001c6449606200012980c0c0460b0b40000e800340c02d140c00440c018080b0b080d08400c60030b5143c20941c456035a48a0380f08047e20804008214181c2d1402d445e094070320310a006090b80340e00c42e40992b02e00da910380b03d642c00607005e0444400a01e0b2946d0321180c0116070035605c00c1385a14040d0300740601c0c4036115004a5101d0f8010031502c0d4001c9000503003002840301920450018002c0b4200c090703180c08000c1d0018070b800c040601060040100041c03103c1990ba41007000c6401070981c00c0001c490301980c01010b0303490318005c840070000f81402081c0c020420354981304588070f441c0c2c0040d0b2515012600181210b000c03800901c21a4100c03445001d80a240d03460031902561540300b40c00a01b690000c12403020307244a40140101c0d0507101d40040c600c0141e0b00401034950190591400121070764071410050313000307003080e030000010313602d4098004140d607808500b401c5500320a813030313034401194140c4130180d8a02c00d5840d112140d402c1404104102c0c4d10903044960040c10003801159482d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 859637374 1250 859636124 859636139
    0x1314010c1a25080901060806070e0405101205030322080f0a020f011509150b04050d05120f090405090703021e06040f1502060c03090604030e030a050d030501080f032502030304 77
    0x401000070b2004036880004200001109004042c003030420758002e0101d81c14403007000740c85560403062151007107407180001480070703541404250040c05030f802c00c00f81001071404d015071030b6802501e101c121008500107800d0701c0052540410f10f1580d01000551800d10040340d4080581c002c03e107200118052605c00041072042406020011a58083c41e9500c2c0344c540815403049802c41034419407102d850501c104a0320340e070401520701b02c032004d642102c46c01d030306c80c5841800c0503515400c10710300780c00200304118000103c3c4c010302030864066400304810b45881482e10381d5410710303110088d032112240220108100a0380540000e541d4081e1a00e4203298980c0f8080e12441d50302d07000b120b07011034100780410405604210705504601c81e81c0720145141040c000c8030740c44800051001c0e040c4074411504444d0368404020401103103070030105481d0300121100f00100685000e104454183c800c0005142c0c0000011013181c0d60b900740305000b0b0b0004540600110011001c031441a81d241c001030000103241c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 859638624 1250 859637374 859637431
    0x11806090812042a080303010b13031209030b011d0402041503020d050102070501060f0f0501081b030f1614042112020f3306040e031314010c1a 63
    0x50380f04568030645070498195201a04000f1350f09240180701e0b82c0c10401c85040044100c1e0f054501d40c00f003065484045000d4602e00c0d1495500041c402c40c09a411245480d07400000b940c1500e108189000007640d840501e0442d101c5583c1c02a1990b006200c00300b401480e0541c40850341044112a1044c400c2ea280c002941c25040c40780151031036500000c0e03030420400c0a2146c500a454000d40c2d26014508080560b014407905005039814412400003040400814a8010003103180c0245500c2d540d1034210b40d803603940c0341c00ba41d996a903404c6c061400104c5500404c644134a0f900501e07501800c0c140b612031100294912f44010504602c2c80c02c0c00d0402154501d400c81c06900590f400034008902d02c0d114842c41d142038131900710a42c005411000c480010211059160300a210301d003a5059150701000070003c040004040080b844009403022910000e008407c007220035042c4203c1c0303446401001074a100002d404000d0640d030440c00c4000700c004411000540100c08060340761041c911804000d03061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 859639874 1250 859638624 859638631
    0x9060605040c022a271605070f080409020f0a090f06051e0d0c0206070f1e080901240e060f10080a0b04020406030b0f0d05030d0b19120b09011806090812 67
    0x1951171001100da03074070b4030081079400001624558401400341c2030010139500034644001c04800d000c8103008140461801134a010340040700c000c5554000c000c0720070f0030303e43c0b0411600010488490000880400303020082c5d044501a841d26807400400816020002002c0600b0f444d01c0030b411300050012101e07038420f0031440000d54004291604041c44060302900c400c002d02810002c128590408003071950f8407484c140c6959040400c12038582c944840d026164506181c04545c144a034000050b46102e880d8100315005185007070625122007050000381e4182d0000340b90070001c1103040c0f124603881600180d6000f0006900040c0381364104001400780e9001da8080d4000075164a00d030f0925251040040304102c101300c410030610781385a95035a44902031812a500d00e25522528260242c07034440400d80d001c1d00d03503501c0c0300303400f501e0703580c20404c4c4041c811041c5c0314101950005078041c40c0502c07c1aa4901e076100120b0f80304061903462101900e415181250524020300030901d0191458512a00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 859641124 1250 859639874 859639909
    0x22080d02090a0e041a09010905060403020601061205040f1218031101030c02010b0d1101050706020d0501080c060c06130f0209040605040203062406090312040909060605040c022a 78
    0x369121032400b00004901c0c207810020200b040c11040c00001961121100310008100325250f07600e03920b030040913004040d03900016019001d6042003008140e408036455060340d4007902c481a02c2808a041c0b03104a40b003c85008003404552404030000c035020a40d950020001481c042226200030881c510300102103501c1251001406560440d1541c1c05015180b603845551008210081c84500041c9082d582d000014008103d52803080c40c00d80d104008032519103409ca00e040d0b58400030f8910010080c4000d10035001c0c580900220325802e0b140c00d604a07090741c401000108196180c9209407410080044001c1701c42c0d00c041d82c0c40c580140c651039131491140b80224000100340c138050052504020004103030850601000300d101060005800c43c5800340d034416690580c4441e07202002c2031034002c04504a0440145c00f14000900e8145071300804201c1d0704c201c10902425550f00e00b40030999148200f0000940c10a4503a106540e05204810501500603492032140c49600d0000c600549041c808490 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 859642374 1250 859641124 859641127
    0x717030301092a02012324031009080d050903043c080105040b0a060503070e090a0c030f05103809090d1404030f030c030908071202040f0506060322080d02 68
    0x9900e00c5100c11042c1c05d4808140c00b940a500d4058039504903903c030384107d013100c00c03c0b00000050b15201080021001103c8071420004206a818844450340003c1192016581803000191044d0710200941e0300715240042168000c000c40495601d51a01c0a0000c13a5042c2d4482e0456419440d110b00c0d1070003c003d044000941d904007810264180c1000800c1c10345224180300041040340c40010b1360200300c0700b04600501498440c3c0c00c0c95414003c0101020b0f00045a00c40d001c42486186a8000d1003940b20300211a80003d201001c1c0303060f240022a907503410320104510f11804441c1410001d85001503a44c0d80c02d4151000c00080d070303800c4090780c0c40545076001c82c40005c0f019401400d8050350900c20b0902c181410b25680d1644d1850004001c000e080003820000402050300404684000d1700140059418030760301c0d4000241c0c510b4006c00c0980c801d034203156010000c07030301c540319190266001510903407443da1100440c1076003c10700758080724140c502c0e01c012000b19803600007070140a0745142016 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 859643624 1250 859642374 859642391
    0x2802010e24090106081b0102151f1409071b050106090b030f070f0b0f04080a150c08090a0210140c061803040e0601030f02091c02030717030301092a0201 67
    0x1100c0c415008080d0101685002003e01051200090545020b820b040d1406d82903148440101d00b003500c00b0f0061880c010422042c030901c0800315801c00d001d04400405040b00560b5000302c00c240c0255000101d1b0044224004104103d100301030320b420310340448401c00c04400c40c03035580908503441d80d840042c049a8070041801d40d407a00344642c0c20396075145001001e0450401014410030f845501c00e040302010005003200010165a0503280200494400d0b00d48060a43c2041b802d054005043e2101c80c501e00040300078854050240d8a0082940400410b0a409640c1c00d005520740f159541c4003d002e144800040600b001c03000400d0081d507464098609410000304890100741103424280d400e070400d00080c00020601100583c0c840824640440e00f41c480c070680400911403200c1203030308003c2d01a04071069510098101c030b8894403d40454200c01e55840302000c680d4000300200c01150000c000400c440e0101360000e051241f080c881d44048626030482c00100050400c04a40151751542c154 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 859644874 1250 859643624 859643683
    0xd1e0f020901080c090f0a0b03070906090c05180d05120414030d140a0516020405010e040c09020c07050402072a09060e0601210609052a2802010e 64
    0x1c40d00500031a401802c21103400c00c0092400301000381034050b1102c0039800584082c5464100601003030010b0700f943c4505495454180182c4441d00550018074102282035104034440c400725450842d00c81e23803103100404001c0c2007044141d85800103850510905105400c540c0072140200000d04681005c80d059525880c01e15042090101e502c20a0040150100c0c03180008002140d418225500d4030540c0d035802c5401c01400d0110701c500180d0003034a000c0011641c882e2409201e8015809007400140790b544ea2010107050307104010301c0340e00c160400d00c402c00c5a402c0031303000740030540d10418007030401e0b0519540b40c040e0152030341c0c7e0190440b8001d003001c118044891203000042c149880f41007100d40391420010740002818410030802401c41719141c4141c0c446540720002400c036915092000b420031004a4407007104000e031001d82d040320034504a0040c1c42003c06c40c0c04500c4c2200e0203a95020003030203094001241d00020b00c2c159500c848042c1300c1c03503400744041090003900219804920480c03602 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 859646124 1250 859644874 859644889
    0x6010e0904060f1a040605040c0215040804090c0302041412030f16060507031b0c030212031312020f07140f0103022206080a0b090601020a241a04140103110d1e0f02 72
    0x4514001c8d407401e12848122a40031500d1842501117024480d051b85440c60320100510440d40080380a0346003007024045030f54190010000c0300d901c000710130320289061082042401e20000e03e0788003a4004c201116044000c10003820712022039816902d00c4d4815a00c4d00c40507100100c828400007036171a00f02180207500080024030103891894614404003090740e020b50340381281482e00050300c0c00030000801d5030007540a00b14145034440070300300e140000c01401035540c040b00f000b10724050141040c00310b40d00441c0103850081440041c041309820a103c03006400960044118244541d10401480300d500d1242a14000911182d61080841d251410b5040101e40c0b22050051140503503505015003680d00003031030344903280c100e140c04c60f100021321030201805000e44000c240e8142440c08442c0342180c901e001c0003400c0020f81e81805406004e90414440725801d003c024001100c407000038005043c10004079900a00c2101d20030205800303002640805926108211095a5002c4c48501181413540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 859647374 1250 859646124 859646129
    0xf0806040b12010e19200402070501020c0f060108030a1704020402090915011713020411090d0b1e0601050403080a170112110a15110109080f030a0b0906010e0904060f1a0406 76
    0x240b491800310303a583c4001b0064099032940a030000e080034001e04079a41e550442c0d55165105c0e0003195a41c0c58030110366100d00800c008440b450050b0800007920481c0482143c0942983e40d6500407084c458845800442d00c018000303a801035420700616030319172640705d105401980e009603450044100304000506069074601c480306400310395001e011105440150a03092664111004611100078444000c5180203c040240d0700126015084085c8030b200350020340100f0341d1000c0c0d42c01d62400855244041c510660f0014006201040100f020410420140280b07032a82d2030424004030710041e04104495080e00203800b4050214408010041c00b9204240f500341d003581d141407820706d40b410900309d0701500203040f018401c5603c81c481c49a0420340c040c44400e640b240e0301d03e80700c41031704480e051140c0003220102c14152414610440a1401c4600503115000507951603003011400400e124000f000500110717615a200c0d140e10780380000b1400703400c1c080381c4040d1080c81540900c40c2000261101c0c3e9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 859648624 1250 859647374 859647403
    0x503031b0d0504030f030e0103090b07050c1b090c0a14040b09120a03020705040218030303010b0909070e060d0f0e06010b1306030b0a05120f011103010e06100f0806040b12010e 77
    0x800c000c20000d170b4a01c00050140f03405040107025496803000503400740c5034919004017604101d9040002c0c0301d400c078010f0020004408122414800d50025990540e03a1705001260711040d01d400090b5a81c414100800d410100e6240400f0411400400200c1a82154001400c0218086103100003800c120182481000b0104000c00c1401401d840103900d07030020340107181c082c50300007621040050b5240c0c4c0014440c8806012240d0b43d6a4640c2c1601c1c058100b160300d54419000b160102d0b924600c03980d001622290001c0015290a07922a040c1005181101040d074141d5200d5090021020b000c1c08400d00818401c0007855503014809032040948603a80c2014052515000c0c0c9540c4130b880720032808007510310075160812028800324400d0319040403411b000050b9800c120161103d03440c4000518102c1e059100d51390b21301e490b4681005024040a40d01c07034002050802803100c3c8501c04c10180d0340001e405880050192000004101c013010192040d000a80d180e4400c000e218404010728883d843c2017 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 859649874 1250 859648624 859648627
    0x50c100210020426011e050703091b03061b0212070c05090f0103050d02030c06011e0e010306290f041d032209050127020d050f0901241e0503031b0d05 66
    0x403c11044a4103201c10000001d4945c0c4200040c4668080e50104418030303040040c48bc404c10b81904191a00c60190000300c41031400d00b9034084100c1c14000403181310092a070082c00c0000400c01c2800400d400c000400d941e124806600060542c5840044078000c00220340350820a41c11800d0191401c501804a80e003158420401d184030814041035243c1076903c2c200f0002c98800c00c0c07000078200c142d02170708801c40207582000004104051580005c10000025a1101d2107002044481d81c1e2000413483d110f411400c0c0f850a4142442e26911000850796101c1c035901a004c485010185503402107110907032800c0b82e80071640310040c4075017500c000403c2680000d01142d810092548050703166000600e41150384c3c50b00c9113018000d6a0152960000c10750380400c428a4501c1c3c00d907a903820305642e00310301c5518000b0078403503510001d4880f100d41d0741d404400c40310151900c1c01c00840d118501c499107818000103900030600b550244000d18000410a0311f1500f090a50386030282803000b01101030050010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 859651124 1250 859649874 859649891
    0x40635090607020f1b2407140604020a1715150103140717280b0f0306061507020a030803130c08070612050702011b1e0c050c10021002042601 62
    0x3c0010b1018031003d040c80545a17241c141a000c580002c0d0b01d2241440074010348500b014128002030082c000450203040c4d2107100c0c0c0c070726881458603810140c4019420003401102403215515240610302c05404040c116408000c5020018920b44026120f006440d00e184e0410741c800d603070601035100d001c06a0a1480030038100312801510420440a5101d1014201d40010365290303254035000c03100c00ea0b40c640c1c0000c4094090b6040009210f000e08a5204440081641155040c0025117a1050401600c11144170303142280e51601074100200480e800785019401100150306d040c01386001d10b03240d200c03002e180c1d10f00c2e150044410001e50080070031607001580410801b0351000140400c42e0302040c0c00a0940c60783c1004a000d0311080c80300b54840a050a0758000c81d070741c0008903402000800c00802008010104208c030030866111028029900100b0928a03a140880004c1c42000c00c600496408510300f172a498141d8210340c0c4810f4001e50309140361a1344000711110520210a420020040001e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 859652374 1250 859651124 859651153
    0x3020310140a060f0c05060f070801092c071a0d050c0a020a022403040b0403020106140102070504111201030b06150910030c1b150c1404063509060702 66
    0x19070351283d07504114106200400707460081d48000b1780240c024058a403145811031034441003000c01d0760300c14009015030000095600403849100000b5240324a201300004100845110600c030341c4107807075124013414034001040316034510180c2181c0c03c40c00d466501d941c0c0b0759a03403104680008024544407401041140c20003580490f800e08416811507001082402a02003460000d0449035080d041c20320000500c814040328003000c5106611a50080c02515210380640e214440300544850145c0c3c400442408180b030160814046a16296042800c05402e0540301017001c40c2a803051366800040428485581010740360001118031402019203000210340c0480c18202c0c80c01c40c2501016a00c00318500701900c00d041c0307044140600d98089250f05100d08000340b9108200b07544c208100d01d07200841000f907024201c000b40c040d080b1007100b41400c0c13070300030261280751040b0b4081d0107100d588070741209004000e240002003c1244651485146014103600d4540200500704005550000d03206e60700a6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 859653624 1250 859652374 859652389
    0x5030603060c1804060b0324060f07060219091802030f060d1110030f18080304140a1a0114010914060a030f0906051603050f07050c100c0302031014 65
    0x240c4120b80040d034507151182c07810300d51200b0b1100d440d40282421000540c09480c100a140958580000c0d47c00c40002003d012122400b0046840c3e0840000e00c602412201e4050180c2050340c028400540f8140d190050114180640505d0380b000c41e1030410240901d0910349000d9101e054800340840c65030400240c480c0c1c11030310080041e0b11079610450034001700034840b003103100e001a02a0003a101c54100c10809009000450710b42103056243c208501078414000001e8007005030082039a904d951903540b1103000c401c2c0040081030440c030520b10a100091000c424229103003000344034040c82c075414030181e900444000c0340c815041000d0b10000788100a0b11900407803155104403880da50352203030400140e000d098040d040056540c90301c0601014400305800040c4250040c90b801404100c603030505400316034040d0365403009001400005100980140001c000c070103118021240b42d09001e100b0a4183d80a0b4144000003e40120900c00490236007252040a4a140c200c0d203a1440c8104000c10041e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 859654874 1250 859653624 859653631
    0x118120203030708011401030f0c0503150607020d06051e0903130b0309070b0306010c02040f0906060501080c031627090605151804020c0604030e1003020903150711101b0503060306 79
    0x107181c600c100103451fa03010f44d0041c000940001818800310780003450190081c2c01c220b49141501c60754418641c13561501e6400c42c5d10941d8020810212100c1648030900105002401c800d02100d124000303c1c012129070240501c188a01e00c010360781c4e0058100500b01d0148942d0180086104c14000d10969501c0071a00c10103480362841f1158907030381c0342001203401c042c56600c0a90001d00c1c2110b142140142c1d074001d000c2e03c0c7d00942d02800240d0f40e400045504400490704070f410b090090022850301c041c035007821181048146015804941d1480c00c43d00e0030703802e803d502184c241e4030b0682040740040e6070203458000d02084480120207846000c54001901c2203920380b5003001502c0030500186d50b215416640001c558000311007803840c4c54070780a00107900c02d540f2584200c1d40400c551422910a000300d83d80340300c02401034255007805000301d082c03065010306200c0034070462203400c1c0c0c044502080381c4c50781009101c1000c180c1070b03000101412001000354010307080103c100104552610001a203681 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 859656124 1250 859654874 859654889
    0x3070f0507051008160e060409150b03100311063108190b060415031406010902180409140f1e031e0c0a0b010f051c0201020d0c08040503011812020303070801 69
    0x100c104150404544501554854031f0307120001080200d45002d159001c808000351000e1940e803550348402208002d80801ca6401c8007a500c00c40c420300008180c1c041d404503080c0c02906a60900611107823074500c179403c103080c0c2007442684031039410006040d500250010042d9001600c0c041c18901102c029181d00e40d180501071100300b8000c00c04a44555200000c20300d951641c112400b81c507458072440d01c1264030342411940c81104004501c0e50b140b44225074504040010b008480d8404000b48400340010401c280c0d02c10500402400a0440c01d009040d6510850400b9122400c020b42003c21554800316251205030300a04c40705144112160041e07030001c81d0424403a8842d00b401481515020000c0c2005000b545c0c08000001c40c489580700d41c2d03040d140c04031340d4078202c038a040d1842425002e400e44081c0c010780c40005041d400c18010b43d814444c0500a0401c685856202c030082401c0d07038103000800480840c400042c04c00d101c0030705984040824648081c42c51401c0c148070040260300103014815 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 859657374 1250 859656124 859656151
    0x11401150513051201060303090f050f0d0f0f050d0311030c030f04080d09030806040606020123070e0409200102191e121e050901080406020c0f03070f0507051008 71
    0x4840241c0c00044800508005129450280c4c00300c04160207420389100880c00308520800c0801d09650042205069410280c01007144400080070000300c2841c000d001d80d203c4ac80d200343c03000443d18020f0038a030035a00400003050301c0140c040005086500e001010494120140240b0619100c2c00f8102c0b5041004c0b24078001d0a40c0700c9042c503000901c01e026410900c10302d003645041c101900894207600c155003c5a08100056542900b60709980c044810030a200b40b0084541d200051180039594104105251001498000e507012a0480c0c2c0000310030341c0d007291082403150503035100d45c008410703100c020b10280601c841e0b02c1c46404c0c40404c00300401814050950015954007040b480311031145500004c081c0500810b480024007440d15542c41c00c040e001040510b00019030003107007242c02c6408103940c0c40071650340d99100e5100941150010401e180202921b00c0844c41040000d040200e01032100b8070340703445035460000d14205960f80154080c403005104100c10302e801c180841c0c1d000c4022030301345 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 859658624 1250 859657374 859657387
    0x1504150204050904050c041812182c15030a030c051513150204151404051917060c04030b070306080d21050c070305070302010b0405010303030207050114011505 70
    0x400180c090780d00450341201d0305000b00400c1c8040006c0e98081000155010040140303e20746c0e4490055844a02801c1551000c00301c941c0c3c10b20807007920f0301d42e02000310342460007078560342c0b06540c21002d081e1103000481d0b850548090701c10813441e007541018442d06101e01010140d40801d49400c54020040c1c01d110240d0b5210003405400e02010700080c02c0d0b80c001aa2038a4044c2e00c00d4080000e40505403800d841b05401b80d25064034904c2220141c41140711070014a05844100303c0301ca40e8840f102100605080c0000103d580300c0c03c04000c0502c0350821a00400c6003000d00c4c921000c81e4143d1b4220240c1d0007002480f41c1c00d00312804407000e5940102d28010b00390b89040080d000740580b940304501030312540c040400901e50000b0b144110031141086d0321482c0a8030000c950540b10305071145c040ba88020000c4400007401103005000c03040c4640000f00b84a12200006000c60318240d006401181e00080c00c01d08004080c0306001c104070031400ca0404a5050141d512880244080003c0c284000001e49 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 859659874 1250 859658624 859658663
    0xa05070302060f130f290409090c03050f0105060312070c06050708090d030305071403010e06010c030212030a0507090803030712021e0313061b020c1003020d02180a081504 75
    0x859842e944d111a40e150300995071800415004034a1140c401c900a6992241e032101004032400b0031401800d01805041a08200421000307044c1d4540449084c8914000040011024004540d00d02101400020300d0310304501803600340001ca80369062420000c00444000803001400358090b10b842c1d1510903201c50941c50803985a1040ca00005e500850003000603040560507000740348140d080c4d541e505451301c440c0e0385001c110300081c013540010030b11400005000754810358400100b41d000380b0458502c6103038801155803170707417094800b0590b85440d881001500e40c1c00070101c1700100b100704000c601d1031601013001816000400340c14904190005000300d00340942500c000342d0aa018458107580b030911400c0c081032054a040101c1c0c9880c1403120990300007403051140c1100b070865070003038040341800100308041d503441648004107059080c0070702d09d80005148040c0840d001d102d083d010740496440104040311a1980c072088031540021000007001441d0341c403080d0407503400b0201d140c40501403200c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 859661124 1250 859659874 859659877
    0x90e190c0e04020d06050f0604030c090506041b17060604230120011a03070e0f060103020403060c1220160804030203120d0f0c051605150c04030b090a05070302060f 72
    0x40d1950042c0040740410810b5029400170040702c00c11610f945016038517030144a5580500e03c400740002040c40e00421428142d500826401036004000180300718542c1001140700818a81c81400107110f11400d050340710010110f2034101340215039260426281560005c00010055156000720f000350340d45e01e00990180c10400d0302d4000c0798031f47e2003004000c9080e0500803e0640c1e00340f10b1003247e0112201d03079414041400b1054900f401c40c207001d180da07402880c0400c044083d080c941010388c03c0100001050300c0c1c0c4940d400b001c08990ba04800b15024622480c15500c811401182c2d0103d6060b20320071a0409104950503910440c08a1081580504002840e0702803031b44041e415000d50b0041040c0042e52100a04c001c4610754010000124a1104002150441b400c07005c0814400c11105d43d16585070020b0360305c403a02c2401110f126544810071048020310580f06001e403c0b40204082c400c010140ca1050350000250000b00f030a0300d51034966076a9251148400381c05140001f072208520f044500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 859662374 1250 859661124 859661147
    0x10e09060d0c0905070f0206012315090d060204030b0609091b010306080609010203010807080703051f2a20060f09030c060405030720090c0a030612060507090e190c 72
    0x1a080110b8500300d44054001640c0c1444080123000301300010581c10141810401d42c4c0c20048075038500b001440d0244040b0344400841e03000152800d1091044c69540c602c94060102d11600015842e02c0c9186040c00202c5009000d851054070035508100c0d0842000034804038600c042c0344420b0324a081000141d00034411a00480d0090141e0020000740d180150020340c121052041255802a03030b40b405a9103804460000800f10381200c000a050040b89603800300001610040c0000c54540302c40b02c0b0500a21620780300410406505540b030b8100b9044182046401e81c8000c1094261741440d4099440d250300504040a5082c001e02244516400b0025584080d424070b0443d0520b0515050403580c80d00404000c03076441410060380e07080d41c3c40003070788991100005000380301c41d43c82e00e100440725900402901d404156603080300240008024005000b00342c083d01c0300240c0340c14403900041a40f100703a088080e444a4003010320a0a5000c100c05002e80760003154001a000310308481210840c4c400e2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 859663624 1250 859662374 859662389
    0x406051308130e0c0406050406050a03020d05090d1116030f03110d05284d070803030103080a12110d14060f0f1c0f05100b010e09060d0c 60
    0x441c182c4980300c0700c0d160070b0059410a240c4200c055079904a00c01d1148030744c0c00788000081c4241700800425020344090b119078000e0741005418800100c4014045a208543c20640c2c0d0b80030003080c4a100c0d402c0038100807020081400b40c64500e00e80c51360200d00c00c0c0b107480001d00d500070042c091400d052145098607034502c190001c0e02c111800003480100f094004144581e80750481c210384194000d43c0006211410041c5e4540264200c1041c08403204d03170384500b85407850000c0d0359010740b40c4442001031254040084c403d0484483e5841a003035482c06956801144942d881000107202065003401640c5101e142c0d4605024240f09030049040074144c0300c00c3d182c55940000c12803601d40e44194000c1851401030010b08001075603090200903000704040203940d0400d0301030700b089495081070b8088070186458181c1d10020f13110290385406000000d80380540e407030b41040100840d905802d00490910507001d203070001c980b038039610001c1c00b2010007400c8148201d65401da04401c105600c4001c20040c50b10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 859664874 1250 859663624 859663627
    0x4110907030b0303160c0f0f03110f0901170106030507062303060f0607060b0303040303050306010e030a020a090c0e060705011401080106230126010501090816140105130612050a140406051308 84
    0x151123015100c450720780001c44000f10b03200d0380c6400c24100454000c141100013089054140d292401e00d10480000004200680d503c684012020a804201e0240101103554498100d002d003a0400892004803184141030114100140316050369119280c00c2071031421100d0b550740703014a1400000515410080b075403d80008130f80001416044409548904401e0301c0d24418901901c0c00c050701c52100280003540400002d406014405207580003241c02c00300d034181401405180d40014040c4d0b00002401c941d160b440d86005034102c60f2020045004041e00070091080b1030426001c1103485240c000040d032148003031482e0340700300da20036120702c4070800c86070031005c100030074003032032065030307041c24005d850110b003000c00d00040343c00001a041052198081c40c803190f26003405055800748200c01102e604010040c448442590042030030b620060a02d61a2a01035207103007195a015035000420880b2078514128442c403141c48245002940980e10072800545590b030708805161440d80c85034081d01c00e100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 859666124 1250 859664874 859664879
    0x1b09011803060f0b121f02042112080106050a03230f0105090c0423040e031309060b0406020319050d090b010323030a0e01021504110907030b0303160c0f 67
    0x2410340c8010741c1c0c00c1c030640f0107204840c024818011250122510b43d0302d1603110b5485610b01001d4001c0003104411990300141c501135807a200038901001c1300c1d4840c0c0030080d0b154100802c006480d501d642c50b9200d03a08110802d58235003c409021406910340d070409040d00c1b1400a400d5455184503494030910701c8100b00034078142805182d64004c8240501da014103c01c3d4040380d5105004426541120800400302e0110080304428180d4a2103507a402508240c84124500f038000e000e101500b6040c005030944090203103071086c06001c0c2c64450740311018882040005000448e408421a18040e506904002c82e40c1c001c494115083c2c420420341d01849442c0805d1401003051018009040300d0168a100c0ca0741501d02e40d5108101050549404a43e40304214803800c0502075448269030782414019990348030410b0b8903c070700c511740440f8119480c50310107034004143d11308808001d4011a040c501003150403100c0c1d0129503203102d04d51201c1c07034607210414507000b08070f000040315025041400a40700c042e036 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 859667374 1250 859666124 859666133
    0x1606060e07021015060e060d0603050a031d0d080c1e0304170d170a0b090c03012d0902130b0f0429390606030c091b09011803 55
    0x31401c0d00c00d00014018954180c0c0c0c03400c103501502e0b098144078031040072a01d24104040e1094140c0c4081207401c84000e011a4140c4445032080000460184c400b92441e80c21600c0c005041075401010308403103250580400c51a0b0302e980c0312400c1082e0303104000c40e588442900030f00c1d1030170150082841e03080078422545c10b88240003001610403600e03020041625030803a001c1103600d90b04001e1091000485010a10b1602441340324080d03080960220005800c42404011620f9800100d8001c6008000040104014103002c0007030076100440b4841040c0c06030b00702010f09400d400c203200b40d4107034079004a0f42d80c1904481e03013868002001c100c001075985060030301000c007043d04603224a4a004100060f0711012258000072084245043c210007031801052102d00b104511581d0300c9100d004c801502886400310745d09024002410b80c0e2001040f151030900f0805203025410f460050003a810841172212204108051300c81014480c402d481d200c030483d000480710b03c414501c001d54000070020000042c80f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 859668624 1250 859667374 859667399
    0x2030910020706021b03061b3001050409021503060a0b04030f0515011224180b0c0703020a06090f02030a03051201121a0417040e160207030c0b160606 66
    0x8807104d07001d8480d12440c940c0c0125040352107940701d58142e000304000500351010080141c0d1800070000d1401d0078038685c4408213581c1e030042002461304013030340c160748840428020368050040100321020b120141d110760205045040070702856082d81c0010010913910b945d540c1450000d01800c02d09135442e5980c906010510440340c3d032096415001e200c54096803840017918040c10303549180307800b82c0000b400b95540c030000003501102d00203226400181000480350313405114001465603540b00c14440241c10043c3c1c05540c0540701075907007030041248000103038010900d0458030390803010000d450f4905081c00319441c100f001000b03605001d1780e503410040641090103000c0905003003510842503a26003000c1004454138880150614141c0302031179250803002d04420340d0052082466030f0790780a141342d2031012078000382c012080c0b41c0c1c812000c000000c0351421801c060f0010302c3c4010030202d031540d120202d1030b51160040f203200d1900083c100c5000a10450750f001d0b8950302a10400c21143e9030300244071032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 859669874 1250 859668624 859668629
    0x90901180318080111120a020409060311030d0504050f060c01020903010509070608010e060120010e030c01020919050603040f0f080d050906070c0507090b040e03030c0403020108130b16020309100207 87
    0x28a1042c00c01260803141441341c810b443c0e48201400345801e42c145102d800c4170300024000c810b42a000c1001103980c2c03040b4010709008610620583c403019805000300f505044c101c1076100100a020f000400007a554580c2d500680c4000313032040c0382e65841c0003105a01900c103c684a40c0c0540c01c16042c40280c0301d0019081040714200d903180c100e42c2e40c036182e042d8601042903400c03500054500900060654000d20050301c0c80e0480c0b000012542c150b5442c5030f0075504851154003980e540071600358864201f01c148404004c44c06046200003c2c1000005481c41c0005000501070407600c0c0307565010040980d940b4034460342c1000d45192a158905040c4000d00340489601415001c1d0750003040d4040d0107400540d00c215400405441440e0510034044010b10718a00d039142d00c40d8840d00740344101041403004500a03032080d68000e640314110300025001c4070001d041c0400501c02c458084020a0400d0700d0b0581051103000c0e04c90501586001c1245140544480c031603014440300c181c0240c25030001042c130f08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 859671124 1250 859669874 859669907
    0x40207060e0a0f0212010203151e1521040213090807060f050114011d10020a15021b0703080406050a0e03030310080105160e060708040b0a05210112020909011803 71
    0x30710910040d0910300383e00090b60843c0800827000c0f10480c013031502d10326100800c3d50303440340e0b036500c01c407079500003115001c070040000c0c1e4601001803401c0b007001c0e4403e4030012a201e007a00646240c1040e5011420070071302d02c3c60040031103075075042400401030000c0844420310382002080c00328403070500c40c0300c0040c0400e00c00d1400000740007109040039401000300c4150700c1c8950380002035503d1510140402080c02290400840c0210300721803001039442491301c0050842c00320016160011511155904c0d00210225502c60f40281e90410005492208840c16601c503480c155440d18041401900c24291100c0c00b19418000401080700c2428000c2c501000c40c0e101e00002d0050740c03180d01c41300800b031960212050001d510b441660486003030103802000d109108140c0145000c0d5110700d008802e1b0850010080014000900d41d50031180400c1c8101c500e80500c00304400c0e65241440c418200d030943c920003801000003d0000d907160f042903020607808042000b0301c0d42440c50340e240c028851620161000b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 859672374 1250 859671124 859671139
    0xb040f0602270f1c0f03050d021c1103010e0c0d15090b0108070315050d1106070c0e01081212090708010e030a1b17031801110a2606040207060e0a0f02 66
    0xb80f1034038004140c11118001800241414a00342d1170f20709144520300426400d004e01004503940c40080c1c1e100500c0c10460340c00c1091a042d51462001c41900c14100d00d03582c5564040c0014032101e030064140702e03000355081c20160f50b25a010155240038000f00d80c03060300d02c100d0035031001458400541100801003026607403030300c0d81c0d610400290100c1d11a6950f0004000c0b041c4401d2100f4100212120881e81c0a03042c2d20f925181c0c0c18000036402d07400043d048034511050141005100b0024911901520a00c8090310b400b00c1c0724015480c080c00303403d591600301c0341c00b400459000c2d1010301c0f20402400b0300030000e20000301800c07806545c0703074442d460190001d00c4035a0342c00c01940d03200c040c0e064007030b5009000d80b080b00201c00a840d1f0035080580142c0181c8074603040c280090809225410724214050429500e0f2024800045c2c0500e07000c405949071688001242e00b000501c2d00d00442d44031408907001600ca01c0d8508010b802455900c040040c030384200e5100f2024007915a03c00034070540b00b114003c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 859673624 1250 859672374 859672399
    0xb0709060807083c01090c0212030609270708071412030901200307030e1503090a030f020114010806040c080304080a0206070f02130e0601120b040f060227 68
    0x200d5000f4011504400b008075080c00c8803540f002d464480b04c514601903129064a0f07200064000c1c510741c0281d2009007505d030340d89082c41e0015014030014805407614035001c0e096213450300c085070b14910020018064061b502c0e4201e8194a1010001842c00300c404080b140e0b500d44980e011641c0b00603a0185038558501e0252501356858020500641c0744047e001841c2030818000065445c0c000a614215803a5141950590f10301320030030107040c0f401d0007030b9a49000c1c20440400e00515400751702038040d40d84401c108100302d8103000a1110521581032070491b01c090003031a4100d00400c0207448034901c0c83d408100001e200400021500d00a6000d080d109a8855941120550368810b030310540d07800d50003280306031002d80b44c4800070b081540d0040c0419402c40c2c1c070650004020220059144070001d03034540040b40b11110402c91980506401384845c00d200301a6100c1c4510b81034020002041451030132000410410a60181d0b0880100341e00100c00d81648811180c015040b0380d040d150048c1c100480b070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 859674874 1250 859673624 859673627
    0xd0c020706020105060319121b0309030b0609010e04120203190c050d0504080709020f0d020f1c0e0a022e0503011509120809010e130209031606051210030b0709060807 73
    0x102d042a8a48001490311155451780c126203680c410250038080c02c22841001e8250389810589d40922982d0340e84441825480c0400d0108005420b8501554002e4014402040c2d20103100c0e40082d080351001c008883c030300000702c0c9103204494450a140b0300c2d00030640030068120680d2200144100166505000c00700b00c00c407024040c5104825941c0d10041c000c00090210b0740c010074603000d00340c00399480c0580d01140b40301641c0c00259008428500021450020f0324106103001c6c039400c441c2c3d01440317800d000001d0281d03074250150f00a0f10030101d90b0003503000840b000e09100c680da0212001502c22400128000d0155002403044509078078a510980d41e08901c5114658255600c003007501c0c542803c107840c0e41480ea0041036007075041c00070640300c0500a9403900d855080641c003011025a482003403009145c20710003903410a4903294028101805201d400105880c3e404034071281142459481c0b90340300d0800c00c07103a4000380800e08600140001c00e584682950142c1d2001c1c0c8564100d6110304a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 859676124 1250 859674874 859674883
    0x30207020a052211031012030203040e040308010501020c01023d0e01020a120513080706022107030e01091511190305061f09090e10021303030905030303010614030c0d0c0207060201050603 82
    0x6a41c0006c03040c1120621020010000d8039402074040d1041328101900e480d460310442c042071b9401d902080d2030500401c10756a041181c48280003080c8080c1c81d9446c210741d05405280d01403010210203a5918a11645c10b20792900802c42c0480310307030803d0080303a59410747110b4000c3d0b111400c2c0030b0004100d4004e41195a02c58000e0744d001d03903000441c01c00207040c2d0f0340f00c5030040d1f0031070344048414503003c201c04100141c603842100c0b64007522201d0100c8a00b016807015045609458900081d80d05081c0c40c0c2000c07400b01305201d00c84d11014000401c0196000031000072510451158442c8890041604244651305a112905c110700507100320810f044034110500e100f807005012140082c0b611002840048c400d0b412031a00d420700e00c41243c2103061050021801d0341c1004006c1c0703070744c0c07407080c034042092540c0301e4a400c1c000c0609402844c40d550514200034488558010790045865001012038132080c0c4250485640420443d804c0000702002031000351101c25a00c6924010b40c00d05010a0b042d150106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 859677374 1250 859676124 859676131
    0x1206010605030714072012030304030c0311010c0206010512010c0e090603010914010b0a050f061c06091109130506010203030a0216020409230f10050a0908070f060608120a030207020a05221103 84
    0x18008d6003182d5a5960845030f41e42c50325000c4040101000c1a03140d8a0801d0103601a4150a500685015030620003440510131a002208441c0d030b0601c0301d034019882d000410346800580070b91b85d11400b90b40d0400424058880f0940c01001c181410b829000c07403500640c400c007000c14003195260640750343d85041040c03481b0000c40040e40000100b0491401c0b1605407026858a00e5038000420f60a41d03035002e41c012200740103580080c2c01d8001441e140189450141501e0319214042c0400482c101080003e689010080c00764604990004242c00d107840c0d503d086503002603005000b032001c69220710f46030652040707050581c000120740702e01550031910701140c20b010441c1c0c481d00130115101c4050b03241001d00000341003101c0300390f40c900d59100451541001881e0190080040101c407020500e080c40032204181d00580468201e81080c030240d0350b000044441ca400c65190140e202c0000d400050b201c01c01030b5020381d900020071810281340c5480380c00c00490504950408000c0e1500b89a00b080580c40102c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 859678624 1250 859677374 859677409
    0x302270c120606130b0304170a020109030224010608130507090b01030b0102010603080d0b0d020405041112010908040528081011040b04031b03050a2012060106050307140720 76
    0x581d0103001c4088045c0141d5802805038101d58080903c400d00410345034049006600140d464811080c02d05804029440340500c0b4501c0c8002c00c2005002c86016801c07060080030100208000442e51007082c91001065403904001507564655841ea5028000c11010600501090801062048560061003101c00f120341103511107190102c5d40074094002c211080c42d503035124000103a62030150301c3d01e1080a104501c03900e4107480d40420441081001700c0280c150846c01d82c1010b559900090b00300c1c0c00d0740c1c111001a00c6d104442c000a1050a0980d810450200512000312000164440380003442c0d54034106003c0e07080240c9012001640c01910540c000e803004144100010800150792000f10420080707001e10b00113801e61260364460034440744031130640e0300801c03202d0391104443c965031611002520880b0a071003c0840c01d20f010340c070340405200e14001d0200100000701580d0160302c8816484114008090742d483d503a1412130310711420000d551841c2c480504102c00d41e03080c594ad5104244404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 859679874 1250 859678624 859678657
    0x32a0a0e130204030503041e080d1704021206090c01260105060906190309050601050103180303050702070506040305280807141f1b080601090302270c120606 69
    0x300001c0c0050044080003052119030b080100002081051000c0c101614620030105a0701c00c21400d000f8a1170050f4201e4070031604200300380104550800e03144003002001e0154101d0740d94170b074000250f141c0c1940502000f5406031408020500c100414a0400f010b4240c80d40c0b46440190700d4007110507092485c145a03c10b800f440184503614140016042e0082d00070301551030704040701209005a0104842000840d455410b4101001340c2030262a016102c02c0c0b03801c00c10b003894004088030702088510090306041e039400c0442c5005200744005005004098001c940c1c99582b1f1030280d41c0c03115010301c10044d0424032250310300d454100e0401c80000325040b059441c00d00115840c0c152925100da141c21026200c0d4092504d000207400d1904d1031312814413040003803080c80750501028179240052049080004e05410401180c0e046000402966015502e98010624814902c4980410f150940301d940c05540100070102c01c0703400017801c1101102c034000302151208801c0c401c488c000c03902d1000240d0071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 859681124 1250 859679874 859679897
    0xa1d180402030106031202071a0a050d0b150307020f071d010b0d0b0301061502060f060a090908070506040602031e040206031b0d0c050a3209120102032a0a 68
    0x8601940340c200340010000104640e680e55042054041c00c0e00303620150700308100c10400200c24070703020000d40240300191480c2c007501041c000c1062081c0152004043d80d1040341c1c25607030300d03800c010398044000030b9506981c4e400c240c04040d540741d01101c51421580300d008004211019400800c10070002c0614600c06240d007805180300c0c96800c60850044540e944581408242d03070b09000c1e50f0000c0c02951003940f480229010004d0904800409000323407050010301b40120341d250070031020b08558014400094140580c41c003490a807180c044040c020740b08882c14030040c400c07d030b4000d60190104503003c2071200810141000c031444111400780d4005010310000d80e00c4208051040141c032660300c00d40c2c0c50900441139440440d0324010007000064004103040c11410b41241c61408680a15507000c0103100c1068588201140112160600c00e00041080071840d200d0440199210840c24000d44d00c9140c05594080b80d8901c6a2a00a804e80f00003804a400b840d580111000c0e20816980c43d0031441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 859682374 1250 859681124 859681159
    0xa0312030504081e090a080606030c1219060204050301052a07060603050d09151d0f0a050904050c033702150406051e0405091909080a050a1d 62
    0x10000340181d07070030b80e0300b04443c1400103401e00c0380000c2402072103001358a440a0303105000006140c0c1d0061500c91740700c58240106682c0c00039100705804422180800ea0882000d043c0c0e0801007042e0700c01340b0316161707140315408104d490380190081c1e0340d0a4008004540d20351501c8030204080405045022040040c003200b400c08003401095070718002c41000c150b8503078135501c0b07074a031800070b141400000740c1d001424000d4215490304803c2c0000a8504041c44801180011340100324211466104a07440e0401e48032540b0b4075601301c002030000800704109403030031381442900c2d1014413900307912a0290b0102080a007505413001d4206042e2680341000c1c510003c0d0400351110100002070340e000d41074031030244074a0071700001000030349441d036900c50300c440001840050010100d4010300d140c00e070600040c040b0f505c2d90513009a0003031400e58210344281d003010082000748244d0b00042d01c1c1a00026030481c0c2e01c2d40080013040c1e0303503065660741e8100f00300c0c4150101200c00d100c0d01c000d5014081007090850714 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 859683624 1250 859682374 859682381
    0xa030c0305070602070818100f050a050d0b0406081c0f0c020f1f0504060e0d050604080315060a0f08250c060b0a030f0b070f0221120703020301050f0a031203 69
    0x5100d403c0040c540340740c0d91030b406500e81190488601d12080041c030400242040717400184100340c50304203026440c946143c098050b01507207030920200003010410f898202c004bc0c001140e003110140040107a29200d0b00e244e51a079908034800100b405001a6036a103407807040010490340d483c40c0d0340b2400140340a03801c020b420800344c0c00081d400760300000100c0603600c65101c00c900340c2485071101f540d01c0d4035040e0007030000e11520900600c504842c054003004100c02207100e0f54415409040035035255a180305041d45003003040005500040040341c0c125200d41c0107081e400013442d035030311201d0080c3d550b428403290700c00e034000181c9002c0410018408001e80922018909140320f00408034010f051b40700071510485803075005843c04c07446c629842c801c0c020103282c402c0e00f004661030140d464103082c0030003a58030910810409420b1840c45060543c000040e0242e5036403850710304101c200c0c1d0501c440014083d40081c0191803007603040c2c03007135000580f0305046683c04503507120540c8008102c0400003074004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 859684874 1250 859683624 859683637
    0x5040f03080901230c0706080405061609030804060924020a1716060c03060e040b04030c02120109050f06060a08120d110a0807120b1f050c0102040e06030d020a030c0305 74
    0x18400d941d4085103004510804850131106080001510b8901c6201c50724985100b9a20110911800e5020320020132404907815500c94181e0344d412071804045002203c880300c2e1035001a2483c1c0c00450040b4410340c1c00005001140c0c0b45402180141e90351080800c4d04400750f240c3c41d005a0f111741d0043d0f00245440200c81d91052056106604001c0a598656a074400100c01250b409a65001d41d8035860380500c41c003030241030440450300b141c0c902aa075002c94101d0240024052148070203d030011036884800d400c6400b80c0380002841030080501e04941c3e155a0b040d00001c6c03d01501000403960300300409070004840c1c050000741203541000c890f0440b42e0b4081c8240c6d040003a21081860400c285680050034441c100e030760b501d011031500e52402400c0e400600c2500d150581414040e40300750ba030b450010749445070268510090404495025202c91245c6803038000d40d5400454000f648200c07001d01c20340b10705400d1701660501c0c0c0280c03d0498440c28420001404500c040d4401400b091243c4c001d07021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 859686124 1250 859684874 859684877
    0xa1a01020d181505070204051f1221051b061003081608120405060a090807152403171207080c040f2312030a11010f0507020a02010f05040f03080901 65
    0x159180c89818000f403d00c0d14804160114130000307004821410503201e03481e030006500c1e42c0c0906020010b581e041107007410f44194001400d09021040911000a44800c0304141c10000a03007050340001c4060055008580d402c4074801080b10191a2200041140c2c1d1041c0300c40742c0070032401d500b55501c07404da90f0840c4050a94600d100740d0004c0000350008014041002c0d1300d00e04c0049881c117498060700e800f00052215440e80d06000151000401c840255000a54008620005558031650240c01414000701408402d51100e1030709100c0d0303010361070740019a8011401000e031036001a060301c2840c842d0407081c0c424141d509001908182c8030740c80d4550408822710402d4502650b8219001402a09800c00510f0445411038012505a2076900400600c425030f0b000700d20612400000340c8138080c8034030800911070381f800c030b44080520a50001c00d154007a14000c22a074148503900079540d811004040f4080707500001c84003c0940103c6c15101200e01905210740020301796540d00c4960b070007441c0240e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 859687374 1250 859686124 859686167
    0x6250c080319140f040b09070311060a030b040f050717060604030611070b090d09080d090302040c1202030408070204051f1206021902010c09090e060408091909050a1a01020d 76
    0x44400719030041d004d65607054042500e8101402c14903101b400207004424031b640800001c00000c2c184800351244134a04850171521980d070344806601074506c8681281e0311034540402c2e400100b5481d40b22501840b120750b1508407000981c095109140c50949074a51300003014082000010f01d039400100e8800001d854040c2044410760f6001e001110aa0340380e510f80c0c01002c0355803241355010817140d004052000007411402c44480300900034410394000030b40078036101d0004118080c041c0507901d94460348108115901e1405040090f0303d60003a00c0201e100300d0924011440c0d040d9031b1800042003012144207841c8440c41c1403488245949010000c450f1160240540891b01c42c100303c0300701c0182d0850700041490001c0b0340d4020281c4140c0c0e001035200501c0c00100c507110100014500743d1096200011b2691440e4072030015221019551080c2c41e165a914000f01f00c00711103810090040004007404d00141124100ba00300c22064407110b94016070080c00c12034001440b80906454207901e000144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 859688624 1250 859687374 859687391
    0x9060306040e0705100801140d12030c02190f0c14150307120f1a0901060207061d09010602030a140f0708030a060306061214060c1c02040806250c080319 67
    0x55412031217071001d80b0220341c51000400800115182e84c010a18040f9828860b0340c003e030703039049043e5410284000c00c06035690040340c521070003006102124134881a002503001c14a103010000d00c1c0381c4813000c0f9451003000c00000741d019201c0101d1181c900b4000e0001042400807079002c0060b030801040b0904209403100c00b45a03048062046a488214440000c10303086421814507240c051702520842c09040c0758030040129503804604601175845030715041400130079000003440b0310308016080c203620503400c0300000340c065000401800900c2103921111542d10320420602400e008580c0400001ea50402c05c2e08005a5014010742d801200d003d000103001d0b4807619440d00311f405030341004014100800c445c1051001a0100e000f01d458600e0042141d40f509111210b12401031881103001d90a0001015400704000e4040d09d0282c81d00c0740c00c88665185c0a401c556800c4100d10740610390420301c0300c0040900f4421400b00441c6504811207900c0c5448040d11461100383c0c1c5108082200e5940252 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 859689874 1250 859688624 859688629
    0x110a12020f072f0f040c02120d0b15040f260604030807030e030c0c01140d0c0503150301050f24041407021c090e07050d18060e010209060306040e0705 66
    0x5400c075240501c2009040f5408854031441ca10301d600e4180c40c4000348000781640300c2d5070b140384204c10080b0955002c1401444c500c016443c140c20b09601c504120408034049042c900260720140300172100b101d41405a004600340f030119440380b03001b55a4a2448400e082c003444000070111840c4080c2030303800a001c1c441c01ca04090510f80f0942c4c1c00c40020b1901028080c209a160191100080350308004d14503052031011240d0703451140090325414417101510507402940e451060b00c036240c140d10003c0c0030402c05a200200598030485100035020140e00200080c1d0030144501449406415158502c42d00d80d0340d480480c2502c940c403980a108180700000f40103480d00c4c0104201072034078446450060400f118042e081c4140f52604c1c0c81e00100e10844e407200700d640f11920310211403101d0786001d000e44074840100c0300c0b032140500440d40d03107080c9002075802003018a00441c0c8140101c404100c800c0e50342c00d6843c01d0384505254150301c85024004142585800d6014002040c811012a4a00b9544e40003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 859691124 1250 859689874 859689877
    0x503041e0f050705010207050114030a0e120a09050a060c080d0b030f010f0501090f0903361d0903030903301008060105030105061c032102040303030f110a12020f 71
    0x2080b161604070100c10401c650701080500090b080900308881454080701c3d50302c8046c080202400c0182e62150025440601d05004510400c02d50390384070b560700d09c0c180c00090200c401e18429030f40180841c400014450340315581c0070030700725407108826140c5511411204040c2500c07944040d03050060503c3c407504c034002441031110841c501030020480d50714085410f01107491104a11030168181556000000c0d400301200d410103201c41c0390450041150208403030401c9803101c9000c1410034000c40814540d102201c02001d00716851000019603544182098590200340d8150f0415842840341140c7c1528080c442c1415102c62220000500c06c603050b0500707210419101150480074070720042c0036144040c404a0f01400b1705400a002500304200850b0b003011201034141c5120103002200130401d807240300d602c80000f02c10100f45440312001c2c40c00034000e500500c030032404130785440c00314413200030580100c0308152a0b01010500780b090110f000d88a4070780c900d804402240d400c0005003088a0340d0170 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 859692374 1250 859691124 859691153
    0x60933040f060e09031e1602040903030618060503061603020d0c0507050d080c0f0d0209040501030503092107060309080408060103380c0a09121407050604060503041e 73
    0x300040b031880e240a90010f0260710180c00b4014a82080010164144648992086102030303003402d0780d5501c3c0200304c21042c022454400035881030070005981c080c5607041d0000c0d41a122004001c0c0006d8801c050700d00201d4143c0d100d126099000000080c2c14100d58812008000400d400d01500e8040c41400b5070084031080c107582e6011034004106c440500c58100320602528086061002040c2030000c503150441c080e01d6640310f01c1610014140c1046203064040d44e1400001800c14010307561a4a0702c03903220f03080340c0b583c02c0c004d5401045661a00d080701c0c2c185080201a0b0f409000604d052031022405030183d54419203070258100300c00108060200034050003180940701ca107d5500c0c042e1140702c01c0b1800d8001c2110021f6040d4500800100400d00c80c6400c0340c1c550003015594020318500799010100340d4403100c0740c210800c032803405018042c0c5190305414040030a40300081c4c6c98508200480c00796004410000e0030903c00034000450320240030091b48000e0540c01c0314060199605000c005489 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 859693624 1250 859692374 859692401
    0xe03071a0c2a06030c030a110f0a02010c0809030913020310120c090615021f0e19020a050d03122418050604050705070609060b060c0304080606093304 66
    0x42c285201c074110600320a440804880841c650f0911003400649800060702281ca02d59480c040807513028031034000c503054501c42104c02500c445080c0d001030b00030000c0c4440314020640e044005120358002104441d0075050051000c02c0c40c000c80d00c2d582c0d0080d00000c10b1000400d51200c0003040000c50000c0425045204a040c3c425050034030101105440700c541c0001c030070b00181c002c641100703500800d0066000c18030045130010342841aa120018201c050948081405003c8200c1c00c080c009213045a6000c5c025591200d065603900b05004800031015400780c0000c000004030324881000e5001120070550b009941d84203003800907002ca2035a07103542c1c003903032469982081160030002c460280603032015044038100064900004054454481d4040082a0701e58491103034081124a034001140c650014085c207441d0044184050303501e6110b0b01401c1c07150312038800055040e10304401e50a06c22079281a0101254a40088107628100340c810760b603051010340c0d0b400580e20b0300e8601c01c1e0010394104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 859694874 1250 859693624 859693663
    0x503180a05100b0a141030140601050f1e0412030305061e0d060e10020702120d1e050702040f02041706010f14130e01090606060e03071a0c 61
    0x100750b801240d2680b442c040c019107200008001501034030400e410028000d403152514840f44502c116505248400b0310700060711a911450050382d0121014640312003810810010364880c040040760704042250a540040e030b0800032002c4008802000d002c0300200350420442459600c2e0220007950019001b0110843c0b0b0044031009265040c0606508070209031096210106030000030400b1004001e041800307400300e000072000700842c0b039201c019010003950a45800300090f40c6813074040d6121002c182e116008540200c5250680071410040c02c410680301d00c403c0000d407500d1410700d100d81144075400d1100a105000c0903858a004001c46540302c06001a034440c285007410540109103000c180300b41d0b1045006020f201042c0e41400c06a54a1820412010003801d00140e802d4070b04041070b14105040c080880c1d08032105404c032002c1c9038882c1e41c045c046141c13a48412a02d48602040300d5034190f11107070741041825007004120b14094400c00340701d842d01880040307182c5010300310305003042ca20710b8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 859696124 1250 859694874 859694893
    0x15060c0708060a05010b0c0604140c0315180d0207050f040209060d060302041a03030d020318100e1b01200309041a090109150e100e010b190207150503180a05 69
    0xb0700c01c4c1c5002d802c03459100360500486a6a80343d84160043c0018030002c030440c0d1801e400300d000c00a61151200090403a40c21460031022640903074802c0d155803100c00707100214110000b10118500c841c0001c0b650043c00124508007c000d4200283d819913500181e080100b0040b0f61a020028024a5440c130360100703202d49103106100450f030100b0301c04540c0c0004000c030007100d85c0e00070044807280c4992150258607500e4120a03140440b0180003501c05e10b00c104d80c0038081c483c105411501c807844880f070a40b41c002c2c00010000c00d40e4481c001e4486e0001e00c074030648510310002c2500c030020580d25032044909122141e404101181d03072540040104003000380042c060f62918000c901d000d400903000520070924136000e40114500f6a000b00484180c841c00000c040000c1d907a80503004250866500d0841d5039144005012a03200f04510310101808a91001205000049200840d5114440d4400c10b01c0e42c0001181c140d000a040c40f4540c0c0703a003e17818144080d013000149500350049015240a03403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 859697374 1250 859696124 859696141
    0x8101706041202160e0613050103050f07140d060f0e1e070b0711090415150303020d0804030914060c01020d060806150a050402030a140f011a070b15060c070806 70
    0x44900c02e65004541c400c0020000140d030440c0d40074102c0305500c031283c1d91354480000162240e2010904245010f140074000030505c903000a0b0162480240000d0b14022a124507a40f20041c1040036001c0c2c001030070130302d5100050400d038015109031085041c000782c000100c4030081d091071244c1980341182c0f511028807800001c001d104600007000f0405510785090720580d02d441d880640050401d00c1800f040e00050244542e0b840c03c81c0c00a0080720040221544c6041c0c0340c16040c0940c0015401032040b0b1104c074840c0d41c007032440d01c1c1c000c0c0c0c0c040c2c44540809150220715a0b840001c0507805030014800d010141c0e41c801c0034000f41800106030300c0301180305410004943d1405000402c032880ea8010b0302c0d107041858030341803440b00503600c0940300941c2e80e03591401e55602401c1c051307100242503407405040100c0320750001d05150584007010f004107515110000c2581e194043c45201504021100000c245801c600b605050b00e8031402628880c10b012481d44000e0804060b03900805464101c00104110741 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 859698624 1250 859697374 859697393
    0xc090403180b1204032a080d05060405040b0c130e0a0e01181101120603140f1c0e09060d080c100c030e03091003020f0c011d0a0b070810170604 63
    0x2002c580b0801414030420301c061000e1260094006001c1c00562811203114021801403080030700e00d5010208011056454000001c1d4400003d1058087c54231022542d41c0c54180a001d010719081070303103606c0341d480381d420051056000d0306c03d04ca05c24002e2200020b00c1c404452600d4415080801d0001e078000014100c2c81c00c1d101012404070a1803a401c03040000a00240318484400900b0718103c81079040450066005081c07503000070b000b054002e02104501880016031140079114142501c1c00c1844803031b81090074035822041d0720302140c42146441c440d410440c5159510003001000030745038030741e1900e4044003075101c041102019044100d041a00760a94000c1c028075448510342002402e1201c5501a00c034000c0000c628454111003007413500c0d803842034064941440010010580e12005142118001c1600034802c0e006000e900290394022840460070860b10f5400c03540d82000e07a543c5039011110b1110060804002c004081ca0210b915a142c040620908482c500105902d081ca41812610b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 859699874 1250 859698624 859698629
    0xb090109080412080405220c140405061606050c0a0212070201120e0a02102c09011701020c01020706050f0a2c0a0b040812010f0e0403110c09040318 65
    0x140e05100032800020000400c6a044450240b4804198071403860102e40a10a680c0015030080d0807598141980c50b2000c1c110301e043c084448100b201e0300c1035920640720110040c40904420009000030001420440014000c0d00b114800c0000d0400c9030340e4a28080b52020f45882140c481c021412941c8036070100610340c0c2c0048082843c07410003213540c0c0020811050881c0e0941c0194a90089243c2c100c420000c60010503070080c200c280c04141d0803c0142400004400c00d415002480d551402080c0ca4141c59070b40b41401600c8004a80c2c01e00c0041e0b1000100581c4e194070340d40d4200000d030340b130480a1001c5e1641c503101d19004038481c1401e0048664401c005000f620007180340041035a800c01287c01c400342d150b140e10380030300b01045011070360b01c2c10490a00c001424040380c4008000030841d4040c0201503c840c001a10341c09640c85a90262881c0d0442c02800d10140c00c02000c580441d00418402669101c1803003101d07180e400c140b0200307040341815101100426804242c1c800c1019108001101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 859701124 1250 859699874 859699891
    0x10528020903030a0e01020c1305090d050f0d11040308030412090b0306011d010923100c0507090f1119020f0f1504081306050a201e01020d0903020a0b 66
    0x414078150002601c81c4941c800c48000d02441914800c1d5503402071000709000e03070b001400184c0b00c5001c604c0800260404488001c007600440c4515a070b0b540c026826200308015003108203049c0400e83c101e84004040c00d41d4224000e050038040000001d400100440c070451203482800306212885401400c03500e1a82c108420303862050041240c03030303688500c0c4513003044400b1803948550105c480059541d004950002c202450b0b83c4c14400b10192000070002010420a860090450540d0401141e10030003405000b0499044080c0420038060150801d402c4110149000200040d00b6010325150703a00c400c1020713229442940c000000f9a80510024074004000c40c085d20b09008038841140d1240c0035482d5240503052041c001c5030500008400740c8140c3e40b420000b600c60305490781d8020704150042c0d00c0060010301040d11804064078116440010f2008090040c20344520303903001c1000e03480b0080c0366844150750074881c0d840004a01d01039500164001d801814480120f800c000141c1103005082a9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 859702374 1250 859701124 859701127
    0x60306110702180a0b10050421050d080a0b0d0302010c120608070b1804020c0601080d090321030b061317030a020d0c0602070218160e150a03090501052802 68
    0x1800741e2a18584500b000a420f0390920a9640312000d5100520f105c40c1d8482c0c005800c0b041c000d2900c0e41240c000e00c2565801410001c81200c008140d14450224240060180e0090301c080600b16000d0840580c20100041012448011050218009010130030066005070b466140c080b401c00e8001d0804070607610001001d200090800741d80c2035480c1154881c449050400280030300c140c0d145855608100c447c01003056507a0400b14104035a2140d00707000f41c107014061400c514100e1802881c0541c01c403a0300c035203203c0100d03003074220b01002e540840040000307043c0c807140e0000780c5540340b1300180317030150026203100510f0307042401c80484002030f00c4d101c16180d40108048003000f6000a590314020742d0750300c0d04888070030840c03400101a002d0032000a410441c00e51003e604141100302c0d02c0d1045403150f803d1011001c55200c100c82081c540c00c28540c0048940418982150358030004000d03054080c100841c1a40c2155a0203003140c100315130050001ca00c201ca8004807001c1d00868191381c0c2c0c120701055 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 859703624 1250 859702374 859702387
    0x150804140f071a070c08030405011409010f0305130507030303051816030b0c0d06080601150201140c090415090902010201182409061814010603150c02030405090a06030611 75
    0xd65480c2c0003070040365410f510f0301000704a025140421100c0159011462054069403007410947c0c0e034205003e01e03800f00b620703980300c00403141408040d034001c03000c16925051780d01e2440c00c0035401010090400101c0c01103c850315000714101704030b214020b51182c2d03000120b134948101d082600303520459030300b50641c0040605030721000d50800d001c8240c0b900040000910340b6800720001c1c0911850080041141c00c0c01c500246844000c65483c0c102d5152004184c008032400f41c0032401c94001d94000070481102a0114000c3c050401c040e04d002800504000384ca900440d0000c18041e10300d500010b105500c64000c0c00071540d080c042c0d01085000001940c14082d540c2d17803445030100f601000110411141044601010556000079001503045a410403c0900c034840c0344061142004084d03c03041d00030207507000400030510031901101d42100700c0c0c0c01079194801114000c2c1580d0078042007180700c103100100e002c0ea05c2810081c0201c110700c00008000c0e145142400a40d41c405441050b603807801e1011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 859704874 1250 859703624 859703653
    0x40e0c0f10050717040f120512041d1b0d05011404020c060c0306010e040903181403030406030b0d210206010b0a1b030306080304090915050606070f060615080414 71
    0x95620090780960441d90041c003144541c1c84c3e60080f03900c06403044c1c031300d4200010140c0d4144010000940244161168282c620080d040a4484c0b8420120080380904070f1004105110502e01d4100c5205030907040d21035000c81501c41c00d5044441001c244690b18001045440c07800440070384141000e50b010340c14503004540c0c994850f030f0f00411400d94440300100207407007170f841800301c3c10340288001c0c004c122a80c07450400501543d0620103c03090403041c0200843c8207500040d0130f41c6d1400004009500c0d25003000001c901800005117040e421aa0b47c0c10140300003142102115102c6444103114003254070799071b00c0280b41c40c1041e444110004000c100d000c10595200b20711030b0b182c45030900020740758409842c049004206661000442d40008100070980d501d05030040b01a81e8001c0c0e10314000002c11004410445500740e031a660310800c20441f001c00101440c5c00001c9190040c0380000b441da1380d07802820509000130b03030b00c0c9000542e0401007100300b211300031030012800e07940030050a10001d14180d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 859706124 1250 859704874 859704877
    0x914060405060f01080c090604090f0f11090105250305031e07020a1103150901050924060d230604120c1106130801060b0d060503280c05040e0c0f1005 66
    0x90150400c591100010080e46906e01100c89060b000350080d5034132950b44410780000c0942490580d01641001d0861809191900907070140c03440114601e840c0000180054400783d004004085500c00c810302c2018a00001003900914140207450340b5540380b07410a006641862100c07602481c0700c0d41c50042c401003e074001900610150300c000781c80c9805100100182c5007481c2007122100180215007004403035401904850b008001c40d030704880c0d0506000342c042c1c0090304001550340301c6440c6580010700c540342c240c48410b02c56028450700c422141c42100009907080d28589800400e42c402410712080142d000e9030325002e081146800022050039a0b0f8400e5010184080280314240115100084a020741046401012031030f00801500340d0303aa04000064000c2941c1d1604075140c0800020745080201d07908040380e0b505140e46119802e201100c0e20750687c141c8099441014a039004542c68465115201e42440010001d000340010f49003040500d6034071241190050384030b004d481042542080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 859707374 1250 859706124 859706149
    0x150504031a04030329100918020a030b090c0a18260313180c050a050712020c0a0909121b06092a030b07020118020603071206091406040506 61
    0x140340502d4541d42011000b80003e801e02e01005004007043c0da5044280c0760b00c10000f0f46064034900e520007000764003a11514813910550400043c1c0d0611402c403554030f17500800d0151b0503802d0000c0c8000c0c00c4008110782c1c40e02182d107192a0b840004403c1c0d0a1754101d640f40380c9070382c0441d90013901d2034100380307242d07030340040002004400042d240d0a41000b00707000d209a42c00c0c00c1a12001c0922656030300c40542100b95030b0203480340c110b07143c8501340c02d2040c8034400701d400f1114140c4501c0e01d462a01c0d520072180710040c0340c020003180692041056250b0f528950040141311403880481c1840e0181000d12036a001d503111182800014075000c09441084154a4450b5410620026440c1d00303504100882690041c002c488a82501c01c8442170140c10700030160a0324040e5041858650311d504090b0708031400a500b1001965061110070010704e0302c50000c40d4050039916040481c1c04185101c10195180c0341c000494241c0c5031450729440448510000f9800041200c1c00d016900b80307640440c440d8080719 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 859708624 1250 859707374 859707413
    0x206030402130e0c040506092e08060c0a02010b0f0a120f0503070308180604051c1e11100209130c0908030a0c0201090b03040b0f06030c180115050403 66
    0x400040c05641d55080c400c5030500c55008207200c11000c006166032502008843c0a229500d00408241c690900340c2e19607101d80c40c000074509080c441440003a60b0b600c00c0d128072881c106c0d014500460750072010310a050194820702c400c16240c100d50705001c0e0070b680350324000b18081c034a2070388010340c10342d40c00c82804102c3d179840450f80c03c410701c18140300030340141c4014007070140d110003d1003030209a0301c0103403140310b0ac10b04138010300d040100b1681983c5600e429900900305034046019a088c5103c040c3c0029140c1e007040c2808510010307110210709001c140c989101020031481d0500d400f440e44248448803110101c0303181149059496030026000030b9012001404442e41c440b0221045809040c01d4000703440b135041140d48801041c0001480301d0000e44040340001c141c2400000e440d031a08050701e0040e90302c080035440560b540704100950b807a00614080d814441d140d0f1340001c9448070b48002200d1300e041c0828410a42c10140c000d0348550500f0400d0041003070800c802c00c040b4070746c8400c031071145160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 859709874 1250 859708624 859708627
    0x2012306011b11090f090703230a030c06050a0b221418071202030316020301180305130f08070e0604140a1a0f0f041d030c0f060606160206 61
    0x1048012104404000110703002107050180c1001400318403840c803c500311085406030310b56910076002962400c0700b03945081c1e81d58400c0340103100240d0103e4040d940342d10b030103481035460080e1802071072504084c0341040c0c0100b20030310b04103403c1c040c590044640c84108003d0a0122000480100c0e07800d021681100c1c1c00c8005103101800c1d501d14503040394161540c4070b08054182c1c10b002c400501000c0d41c0014556851080e0107000a0b904200355038a0201600100611308255130200d0513090041006000c030780c035550382ca5900c41d1407098424803100c03503802603035400e8503503400350b500072440001a0013504141056000800030340c20000745680a40d0aa1040b80d0915100c540128000c1c1c0006600789448070449410480c1d0101642c0c01841210140b80c4c08551040e140c1d424852861a43d010082d080b1301d035040c0802103401d294100c8034030a00d0104a601840209202007403c542105424203501d40241020080001d020003116402410458030702c0e1406910203005100f01800070b000030b004890 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 859711124 1250 859709874 859709881
    0xe0411031b0906040b0a050a0207050901050607080c0f030a03090b0f10031403120106030902040f0923030c0d09060906110d080613060b0306031b09040b04020d080412030906020123 79
    0x1601410340e00184062003d91b03880c1e80301a0409031041c1c0020740d4440051059941c001610b2420a4006048801c09005586001c40030340301c8540680c050707441e124840c0b1940040144110b41000201381c501e0150703800142c42070783c174903000064020140024481c0d152420500c00fa0480305c00e0b010044039800780300c11445248a400d01400c5004040c0074040101a04c40005102038040d00040152442208d0420003041d000c500c820865004003005000514a42103078100d43d052046000d504e00c40302d80c00c40b4249042e6240c043d152694aa103003000150a24a00b0049550001c0d203000c0a40302c1414542c1e41001c501b2400c070346c0d810200f003291042003c0000030490503210701d1441e10300c05100c0319017880813a841b9000c00d0841e078400d0320114000d200f0125214100b11808051814030741000302010429200ea407110b98500c14054000e07603100720702c01507000c00104400000d000414005c05502a00c40e40b50a0180c491b01056006400f9a41031020417941d041a52401c884103241c140d045240c1c584 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 859712230 1106 859711124 859711129
    0x12150106170708070c11011206030f0209060d0308040f2409030801051009050d1a180601060512130503040b0c010605030c030c030d0e1f0e0411031b09 66
    0x20f1107004400006140c0c1541c846c1c1d14501491b000082645038100ba4084498591044921807222203041e4110304044009991010741160072017500355141c0c9014100c0340d0000c000a19032400342e0050010003a1094501107983c404000c1860303140344008007600181001403007070b004a10030b00000651842e00c54188118884140c0d07492010300c0c075020138445c848200000c219002c103007011280d40c0145510710501d01c00c00740d1286440580368400c606d40d08003401030b0030101c1005000c1020941100c1030140058001540c058100c1040c95141002030550040313801211041030f002a0f401680c1405401c0481550403c409442c640b403d0401056500ca02503400c954240c2c0000c810750b0030840c0a01e00400c1b02d08000f40100000111303c0b40e2050907030b80c41d194414040380300300f01d0b542d549080a00c58105024040ac030a40d2075424620a8200f188080031a01203001c10001040251038 = true := by decide +kernel

theorem cover : BRFrame.Cov 859532374 859712230 := by
  have h0 := BRFrame.cov_init 859532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 859532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 859532374 ≤ n) (h2 : n < 859712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
