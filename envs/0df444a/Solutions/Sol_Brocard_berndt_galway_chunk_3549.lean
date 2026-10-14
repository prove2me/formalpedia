-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3549
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:59:18.12982+00:00
-- url     : https://prove2.me/submissions/760dafa4-cb3c-415f-9b29-9381879b17bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 638129496 ≤ n < 638309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 638130746 1250 638129496 638129537
    0x100302090c18030f060c0d0204090507020115060206010308030615090301060603020309070501031a090c130308130605070308061003091514011d041506080a03030606021011030a09031e0f 82
    0x80f01d0b0804090720317094403054410704051700081140d00019802340710118100340240300c0c451041046034008921411001e041c400c03024000d40040007103400507401400400c10800c01c8940100d42501e0948003400c2c14041c114007409100034075a895400c001d000600d480d4550082d50107210850305498046a0380c03001501103645c1401c0300441880284020a83e918000c80855806000c540301c0030310740f1890350121402c181c442e820441d113207200030035004d24500c074119942010b01564203106207088140e80340a4002030006000710b00c10240311242c504940d101b90040a11958044100d14940d0b511200200103440201e81000c3d041c0d040c5c0e40001080090182c21000002c0000304d0b0404a450b0784d11108070401803003207800b00440d11541c6c001000c034004c010030802140070340c4c2c00007541800c000000341004101c403081c5065600741211012035407412800c494014814650010b44404c0c280b40a50b103c2c090703011a9920310300c3d514200d0945e260000c4400340c01418a6407512110052041000c28 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 638131996 1250 638130746 638130763
    0x1c0c1802090d060506062110060305060f0f0301060513061706011503020919030b0906010b0913020c010b120d02070504090f1e06150602060c1e03100302090c1803 71
    0x91041c6040418000f08003542d2119812607006000300c1d10780710788200980d00c5144141c0322501d080440c00100103105c1010302545014004a1600b40594106080002e6050b580da00e45284200c0c030100c460701c51035a0943c041001490b0241c0b42458800a4048900041081d4403800b401125030740c5c40c081c43e480e40410198140c07810074004403212402031030b04170025000000c810b81c000b020b0012142e8001210308266004503c1900c0c0e1a80c9440c0401c1924104241039000b680000001e00030300342c5075640d1110701121800d00c03410058441103c1038a0501506403080b019400c041d0301c014003d2258800b00e031040100940703030210b8404580d103005000844940d00d002805900401402400244103103000207034907203051010b560341c6901903e541085030075100c04e10500280d003100401c00d03035406004140d80320420b1401a07040032200901c1c0c2c884a42c104403a0528000004001008841890a22000707180c028080e541d040c94080154805035220001c0d00d80d04949480609611303160010700780d207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 638133246 1250 638131996 638131999
    0x9050304060810032310060b19050d02040906030b090606010c080901050d0c02030c070b070f030f05040b0f0901200703060e010b12070303180815061c0c180209 70
    0x40c034140c07a088044a060038041d0004050745200d500000200b5142d007094014141d0207010842005020b0301102e241101c0e4207043d15546013031900030040b400f01041500d0200b02c011040729444400c4140449a0344500801c6406551000c640807540e182c159200d1025030348250b42c00101d50325401a01a40c8081c11034046002684070400d03e80001c1100c070180c001d0a5040c10481e0610300e4090281d401c0e2010140001c006070f00100e07000640076420000c0c00e00620300091604d26241403922180b001c107504042c0030f001c0c40101c4c4a00c01c0d0395841002294000c0200071000ca0302c81080751301050203544802c8410f400038008014039045440c0380c207000c40c0d00000e00401058807507d10340d14100513007040d4141c1d6000d55039550001c003c5455070110b41d86454800c101030b126042c2140740240c4200e4010144031695084004248140c410029001210500410740508140c2d030300c0d0000758902621042104861080c40500410088840e410400703030707a001440c1e0040002440a044103c1c001d4407242d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 638134496 1250 638133246 638133253
    0x5100f0302060f4302010c020f0307081204180c0c0f03020115090b0420041a1308010203070206150307061206030507180c0207060c121808031b010905 66
    0x1080107141041c010f000100207030140500f807544003129691072255004030070382070090041640021403000082c4010290040e502500700d0741054000800171502c980d0004d0085181040c0c48084d940c0400014008249800854401041c24220030341c04e0b4000d03105010000810b01070765503d150050040c2c02a80000d5500c10710704c1c2080d900c51000480ca000001d4055543e0303420a81111543c02508070040c113030320b480c0030904d060b0f8032040c0007c45c1c840301003c0c070712102a4454a619640e0010448086408800c1e0080141640f000c0c880d4640c4501c01b026008080d06000000f070104064020714801c100700d4003a110a90754070842010500b000300403080e4550400e050500c1154050005c60b590343e00d105000044098403a80c0741c030b00e070403807580041c900000002c035289130b4482ca07401031031100000c51019049035440c10001529009800e1401004120701c5160350410900c44e0202c8880d62004281034500c0580d29480342e40c4070b521108166094000701001e144d540d00050003604000c0d644030005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 638135746 1250 638134496 638134499
    0x30607170a060503030a0e0111060609241003051515041a0d0903020f19050606010e0607060912020f03041a0a020703080705100501051801050609120a0b04050105100f 73
    0x440d0540002401e103182560749503004100b5403804c00c060540b80c042e90311004000c2c620b074400900480c801c1041c103112039108500700501c5440e198451508180700ea0b410159031381014040300c410200c010681e0b134100032170320b915424003541a040940101c00d00c408180c41c10710070790b042c400c041c0740440060104c904204010447c2005c64100c2d543e811b03a60712107940c01d2080e6000f181040e62035042d000d9005038003055059444d42014012165034410404165015000b0350ba1850349400d00180380f10306200f00b5011100054582c3d20440704011b512400c1040048000e02d058900240d101b0481c04c014450001c0c0c1a042c0d03a400030440b01681c030204c000300007200d400282410302da80042561011801030700350000006050001410304c1074030400c003030134003681c50301d000204072403051f80554483d00c0300780c180d004614003440000c0d064550a42e00b003a60781e24403002059085c0310002100b000d6100c1c0c2203604d000e004e00c2c28407081c01507200b28028021a16074114010144090b4001d050204007681b40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 638136996 1250 638135746 638135777
    0x1e13080d0e13020c250f030b1e07021f020417070e011703070b070e0303030108031c0b130c140c100b04090506012c130201030b01050c070509040f0c08100506030607 72
    0x402c1d402d030000e5a40c017130b440c1d00c030b20350f400403100f00c0d500c02c035084001a02800710591811011100a051044229200c0e02d0030a80081d5508040840011003170002040c042d0301400e035404503400b40c000c03101c441000008448807030341d4450061086410403030b04c1c040007086200107035042e0301c4940121402942040c080b0b886080c100740000d031a20043c071103418400c0c40c032a282440514000c06a2801540c1c40d00240003026103000541800c0c40d10a515080340701300903aa0b4030a04801d600080c0341c000447c000c0d0644140d03800341507100c400904503408550070105410024003c0a28075400b041400221001c4003480180c0301c00d0070004003143c0040700180b20750030a0b4900250a10321809209102240b003241c400d020345410745100003100703941c6c07004405658050050541049080ca0700c0f601d0300c076000403002d0300c0b113017640642031040c1d40e004085414451000050444190000300110a05650341440c6035100380d084204900c2c2820800000c04510300481c402d44200156103a02c480c508100e407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 638138246 1250 638136996 638137033
    0x70503070b0601020105190b0a091b0f141b0109172208210f040f0501080618070c0314040b04051e06030424090308010504111e13080d0e13020c 63
    0xa00c0d034204427a0310000500c80082d00900354200c02c0c400610460380c5074124001e060039441a040000d010881c90350302002030340d280c01c44110355200c0d04c0b035028100e1445103190142000c5a0040d00111480c5d910800040541005048419901c01c400400301c200048050012040b4455102c09401aa00c110000300d5282c500200c1946003500291400b404101c04100540246d041106040e9070a0020300095811120868201e40b00f10340c0c0c440780402d07041d184000041c2c018200300411180d4604a0200350007002d009071004401081c4d1607c0341c1d1215040c640315085840b8091040d070040800d078440c110000e0100c0400b4201609151955442c0d887d19079000030304240d1121a4040c03c0000c07103400c8120321402c0002032190317441c860154134000420042e11800f50080b80b00440c20071000010300d15010001d41d00300d01c210001c6440d010240303003c001000c2658020f03211406014280d41c005944146584515117045409100791480fa183d1001240241e5811824640c09015000c080740d403c803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 638139496 1250 638138246 638138261
    0x20c0d030c24020403230d2f0d02070b0f0a0305070507050d080f0c090a17031b030903120a02060708062403040606142112070503070b060102010519 65
    0x140c0b07989108a2140300e1480c0403203440400800741c0e590218052040011548110803580c0c0c005034040f80b13101d110301015817039520f4064001c0c14000807040784200c20080000b564200c616004054005880d0b02e00b11949a8803000904c00060040c85404580d10130300c070040d1820250302800d514203040c0c0d490010307402024050700384d20034800103026074000a007003001040c0e10310386141d8501640c1e090801d0304000e10140602031080c1c0a6042c00340c8061500ca0307862000071681000509058411488609403c61084030b85d100540141c0c202c4600350400000010082034800b94111603020480c5c2c0118000e40c0030b010700d01c1005822680103e883d03180b081ca04540c12130b40081c034011688506101c1c01c1a2103100f5000c08200e000d01204000078000c06128141c0200301c207030100320500b0080d000140100300d10000052072126850725104002408215012000c007901200b141c0c1c03403855003010f99403034100c07040c11102c44609400162032548180116801000012202800d04000c02d03c3d640c040e0040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 638140746 1250 638139496 638139503
    0x7021f02240105100c20010309020622270504080c0f0703120302040e241e0f0406120f030224010e0702070503060c070203010e0111030115050a021005130f06020c0706020c0d030c 78
    0x22079603080c02583e22800140510300331140d807481170411907980c81c5002165a13201380d4100980b148168202880e640139015449443d14000400d41c1d91440c00380303139078048d025194075940724503100c186000030b0000f901000e80b0300945030840c140c05401c00441c141d03c0340f03004d0700c0032042201000c1080e88003007081c6c401d5201c14503401c2c800d0a130381d59404200200030845214860402d0b241c01c0004c58244030302c201c04000001d440c240801d50401e04048081003000f80000c095012641402040c18401e0120141e06801d1008051440e0380c2261450354518003800358400a140b8400800c2c100ca00014140040f6040903020b000250b45840c01c42000307401c8140c0698155480c3c0d60f600008040070302c600e000c0e00d464040042e0f00d03541401804c0c9440e03c040310950003440030400004400c00e03000181003064034010301c4c0225803036641c04202c1c4001c10130341000612200583d0640010421a03030054160031104008586000395204001c0780d03035014210490360030008051040c40072900c1981c3c8051000e01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 638141996 1250 638140746 638140751
    0x809010f0507021503010f0504061a0a1107060f0e180f090304090510090c170406110d020712081608010515091011060a0207021f02240105100c200103 66
    0x2d03243c001ca4080264a13a6404000300c0c0000184034040b46041603901404d42a034040014a007800245810340d0020041c0e0404441c000c40d400c050705120300c130300403402d88a010a9400d1280d80380700c0038150701d20703160500000c00c5030841005080c1c10040000c0e694540350045010058848040115001801030003118481c0000c00011411038031500926002e622142c0180d100380c2d18140e040030460300303007202160030059180c0c2d00c10580442c403050250450741000000070440c2403546465454030803243c580c0001c5001154150074403005443d803d0000046445800343c0765510304451030303400c0c5151188400b080007200140a01d00b402c03034810844c00700312841c442c50403207010001250a180c2c00012400240b81c15400c00554405021441c1c101d1440706082d0305110103940094160b40b16000610402a501250f84c9020340c400c10090450380340c000455002070201c110480c02c40f070024084e01c0e0085643d0f003210808075200716100110103802030300080c0c86000c0c480d084000d000c1c0141070a410143c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 638143246 1250 638141996 638142007
    0x3150310020c070e011a0414010e040608010c181505030c0c0708070f091b1805040507030902040b030601031a040302011121060a06020d1202070606120302070e040809010f05 76
    0x21018030040c0b20a05841004184061403d00c44160080058005609810a98102a00e24028041544d06030385a2002055050303200c02d004842041103031a401e940716040220008000c10103602502d4144402e80c2c420340c0100504480110740486031040c035840c5010144800705640c842d5000c1d6400c00b4002514926041107000a94640480d54215404a400c840e208014550358904800000c003c040000d00c2801e209620b16000d512403005001c06102840d0454041c1015000c1654081e04008004201f141820700c8002c008040c000804c900803171511042948510b000105281201c3c0d02600030f00304400386481c4420503020281040b401d40d0348640c01f01c01c80c180c408002d0902c680c000486404840016812412281d2000e801280a030700c42e1401808080c0c1d010407001c20406940c1446501c000141c43c00b40c00070b03c80e8840107404140350010108040d40320f14072403001c660080d07085818154849904003c0071100b500c005005440400011019500800d01144101da1500785242881c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 638144496 1250 638143246 638143273
    0xc06070c05090106032307090501051b1e010f02041202061c090f021305090705041e0207050d0e061815040305060f010504151211120f070905010b0708031503 69
    0x910070313001a40440c1c1c951144402c5540c0e1600c003181000d04607400740400382001540504482080e00804d81045000903408403186404610245c0f1000310804581040001164000100101e1241c4000c90b5003031021880054029009031015115620300600c1040901e030308101d025405101c4012a10103040744140d03000c0018490f299100c3e0240d8694090070320300744100031040d003034000d00b030710b01c0361070300050103640300c030016046c000d45900392000191801d010001c6a085103001e903440c18010b000188610800c4400f045401c0c036442c030f9840f01103c009a540c201700050040d15400025000a06185069440e207440409070500c42d000d88035261a80382c0e00c074903040010031202030a08600325401040242494820588000424841e01483d54280f0302c80d41c840309180c80300900b005007800501d00241e0364510500b44030ba5007500c1110721340c259010706542ca810052044c4c0306207030300cae04000040d1000b01c4001c6400a55020310700074615500e00d040d040700641100c01154041c841e41e4031641d020b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 638145746 1250 638144496 638144509
    0x7180218130603110a1512061502030d0e120a2d0806093d05060c06090105010b07020a0501300915140601080702150403050d1a030c06070c05 62
    0x418421100101c2c0c0181141030180c044240c000119009580c0c004d002c101e0303824070440c8041448950300d450090002d080c41e000002d03011a8010104e10142e0140403041703950004000c115480502c40c05100196980185640311515410100c1d602c0600f00410070510384100402000b500071410000e0454034214107003507001807411400000700e0280350901200b458442490f0340e0085c1c0b0712482d0000c004000e207940c1d60500b015a10402304a240007a001c4406100c0e19529002c0e2001a14403502c90348041035140d0385d0030040d1404801c039407070140086a16000c0b6012106050b40184c00c0c20082c51800d00111842e49004103110401000c102c000a1a007105d083c2d0f209005028030008241200c460400c0d400e100c4200c1c443c2d1342910b1600c0d50b2203400c080000c00007903100b23009007400c02c40795940c0e190507400c0488003512482038500120400c010960014046c000c034115014003008140548a0341d0303080308440c03070446989a0b00200070180f00d8030b4400020300c0d00078810317200b040000d0307030307074008542d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 638146996 1250 638145746 638145769
    0x421030609021306021515130b18070906020c310c03020901030c0203130311060403050313060e0d0b1b041a0712140a0806040b0306130b070207180218 66
    0x10910141c14080204517410010300c00e4264604243c2440ca0030980401039a902c0209205801203c280200403954000c50307122264040300600840b0714070300643c10b000038241e8102d0780b003c00700380c111a01207501440001c082c41125005029160f000c546a008424a40c01048004200d550401c60b2850482d03079a008060300301c00c45440c05a10340704550009000e588011b140442154400d01c0700c803509984840c0d24000300c0f41c0020002c070f03600b0a039201003005442190405040c0b4800014804034403640d031b1310040f040350b08940c1d03002102184a020445074908156028182e0300031302001c26070084074694510080f892040d5054617150b9207888412240241c01481425024086219005c1c44a00b100000c1d07617a041b89071103418608a5441100c0c103015404c0c4034801c1007441800a207054a55a114003203c1c1d40040490700d25207000ea00403081442402012100601a0000b04140c1f41c00003500205075a10202e100b4a54110a88a68002d40014602d102112100d8218403140e49a2400510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 638148246 1250 638146996 638147017
    0x30b040b100c0501051602030f090d0c060e0312030402091f1502100c0206010305120d090b130611130e1003080a0f11070b0708130e0c0912010203042103060902 70
    0x40b031080032424010f0844d00e0040950040d01c00801c3c282c00455030100c1191071024152180544030850075011800342c2c04c5a01008003001c2c0000004034044e90058a040364981b0100c0482d000c1c074141d00d403402d500e404151030081d08141c055021074050a4258808030404001c1034400a107a691403280388001084040d2004c050703040640d100206094070701600702101d806000800c3e00b54910b41e80d15076981c2484010054188008c180c9940318180c03034001c8005140c00c04004920b50408400900c40032001c0d038011201c40d85071003445035405016809a0740c1c6100e60502800307030b141c902104400c1c400b400900c00800c104d06650040002407122000e44100e09645d5120100c141040c80003508107440450759120b154407402081203546011021100f003182c2c08020103844610300a0100c07101c1e24142c010701c48044100041100c02224480a042081400c85142c15000c0b0703680342d902c2c06c034401a90b0150500070f6200f806c040761600015040f90311380c01842c000640381d0745c9200790012a0019000078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 638149496 1250 638148246 638148257
    0x321804110603131a090a020d0302030f0414090f04030e0f01140d020705071a040620151b0f090d02060f040f030b0c1908130b04050d1e020d030b040b10 66
    0xfa8140007102e4444400b001e01d030030b84819641041050255105003d400c028483c104120100c0704143c0300f4010740d8a00740030310750300940300c1d511404210882800441d965000d0002c0303600040000c3e2609410307600aa8158480b4a40304442d1780501c0707119206414400e06120324048600c00e4130004400500d0350a88500c0d0060310340540341f60039814139130b00380d020382148041d10003030a00f21040c1c5800c4404458440c107050f6065841669030201c40441540205801d0150260341500c0504040744140302d40c13200032205551103211003000c0003a005a0f1841c415207034050060a4031070801401884c00340d4002010503040c00c0440b20b00740103a501c1a0050314944502030f6040040010a16001b0740100c4056801c40c20499000700441c208111140032004001403203003c86d180c102d98100e503101135034004100f545245401e05149603076060440c1c21000284160321a002205010f800521801400c0d0380a0110703020b0141c4100c0203800c28403d5164029515241144240d560300c2824030f0400307960722076 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 638150746 1250 638149496 638149531
    0xf140708070209250318021309150908040302041a0603090109030f0c0206160c08030706060806060312120601030b090901360f0813321804110603 64
    0x140202d004010300300c1e803c3e100d02c02000380505241c0041c1e000481c0c019180011b100c180001665000d5200000040d401c500c2c0c040b0a03600c00d054030f4200c400c0090040d01482c88a44030200080e0441d01d07185009010707540f05020620051900b90007200030012075100020001c000c100016125a00035500380c003160395915084001c02d50040c41c00584c1ca46075040c4440440c601c1d8005c00d59900c42d44020001c0c644c10038901c5070400103000d042c0d502030010b201c01c40c3d0b1a07000601e0b186006045602901e1250700c01d06000030b000e4a000505904064000038115040002c3c00200c0c5049a002a190f2070525848201100c6151070342c0601d81d1040021400115101001500900e074940841c003c2c444001c41a144404044400007060038040b07901800e07040007140e040c20034a0080c007031002515040f20b02d2034000542d4100d00c03041030500b10402044800400304a901000c0030f03810002a4507080000e1202c0d40f615080c20f801c0c900d078018000c0c03800d00d06010940c0b000032820b5104455400080442516 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 638151996 1250 638150746 638150749
    0x3040e09031803010908040b07020109090c0e041b09180209030307080a0f0e060f22030302010e150f010b0912060405010606140702150a09080d020601050108160c02010f1407080702 79
    0x2503640380088183c0082101c8111906c8800440c40703030f8002d0000c62240080c00200b1644910100e200a148505080200c4404a40d00a21a0341c1100042c2d206900300600c54910b9500c02420013003641f107a444004101d80f03841d9250b49080144452800b8180c0c4c240078050039070702d0030301c01049190b00c20507031540c1d5840511400f82c54003031085010410071500c00050030700c5468040445480d00e501c50702460301c540041e90704145441c0c2c00c0b1814414a4a032507800001c041e015080b0086680020b016502c11080c0c1c80c01120022004480303500368032409800400c83c0b00c100200500302d00c0c0c80038044103950300c0d20804507880c000003a01d040b60f0980d5036800400c0381540c88440c1d01400070540141500e49465900000c022400c8030200b0255401e0004400342100e000310303051070080c040d007810f484080c0756000000e51203c6c001d12404e4003044044001031508204011a454002129100c8034150750140e001103500d01a07140c004410f01c0500240d01ea101c40000010b4403e0601c281c4000e560b451080c070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 638153246 1250 638151996 638152027
    0x30203011505031605030a021303111f12110d050f09010e011104090209060403050f03181c0f05030d1118100813060609050403050a02011b09050105030903040e0903 72
    0x40c000700030040c06006221076022840c1104010760054501551a902d61154000c028426100203d4103c000c19400100700300c41c1100d480e079080012101e0f1091003150f0b024052440702c90a800000160b0500f01490351106160300100a0030078081d9180d05080e40c100c68401251401c0d90014a001907510400903440424000d00700c40b000360000920258903031813007107c407900031805187c1d205600803490a80e541c882c00241c0740155000421146020540c40c0c03c00d4580d844032040034000f214280100295042019007100b00f40560700c0f03000b074440c0140d140d0306880f59500e0700440b45400200010400c00d8554000c81400b6800708007440e41c0c604a0340d030320505004200004500514407040b640e1091a0010100343e0f101810301502035609450b842e0000040c681d582200708945d2400d130600c07050640c000e0280117405245d4000300004910141d440ea00140c18000b035900040c1c20381c00501c119482100910382103081407044034241070703c1e000c410810b0601111031816561020400c90701c00c40440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 638154496 1250 638153246 638153279
    0xb0f190c05010c0e01050f1602030106030b0f071701090b13061511060906070c140111090f0405010e01090e0705030f0f0d080609180a020a09050123030d11190303020301 74
    0x1410524089146100042c2547c050a019112080c034007150300264550b04d031b2209a02c45900030000c0000ea61a850583c03140307034080e40c504001d85840c500080c421402a010488452013440c2c00b01c9050303203040054805011074842290f0800105c03002c0c100c0c0100180580c3c006800300046144e594000c4290080c071451001003880342d41e50080b0103210340a41d0103e459600110305140c12400d0801c50f05000b07400c15545160b0404941c80c0440f0100700b018514041c10002100321951221114032034100802d503031081c003400000c100b500700100402d20562780001d01c00f18400b0300b620f02250f981d00000b0305203460000c44a0464120303202c10304001800340704d051210b40c40f504200d10342d41001c2010903090903004007840244050404c1305440c2d03000c100310420744035a0041004080795220180300001d81300a1164040303e204644840600b04400c41d02c50100420290003032040260541080307c00042006400c80303203000e08004280481c00341c4545408103170080d2809031381c95240031414010403049 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 638155746 1250 638154496 638154521
    0x30d0e070513140711030c07061d0409050d0e15130306111801050703032a140f0909040204090534030809040c111006030c06050403030503010b0f190c0501 68
    0x201583c59806030862040c031508810b83c1e144c0031414865900c850f61440c8a580d5044c882131107280d400180c03036940300150300d401c41c40d603601c4a40f08003442000e00040d98105100100540c008020780717240d1511443d003140b07501c0300041c4030109001d0b030055413000583c0081408941c441c5c51510520a00813980101c400c00260030f1403031460710641501020032134640300c2d075003410400002560014144650480ca91001940301d040c034070700c20b091006005480003001c9034000300302e2350341c1410181c9403213000b0f4941c000c2d049a001441e0030354090400c2016180100104e9005a940790700c2d802281c020001c440194060300f9544d0000305c0360f00c5000600a15034640c2c614001503200044c00007640290940315040030039a001716040300200400d0340c5500d003c007d28032061203407600d40720303c1e501c0c50740190046a0241d0410f00c840d41e11400d080700c451140d800007501141381040100014001d040040041a21681a09003440000001012041c006c018944000740d54000e011003401020703c11000c1300c811 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 638156996 1250 638155746 638155751
    0x603051b03070308160819020c100f051c050f010f0f15030209030c0301050721020301140105070f0f110315090d1b050a03050a1e050d020309030d0e070513 68
    0x151600041d50b038207010302006140c5100850b89000d403005140c6503c0a03a03034084007054071107201038510703409400c0c2001d041c401880f440a0002c424141043c020000d07023565628200b6140d40d68500fa1a5603010541000f134901428500e4046031100d0310900b8005c03000c40041288030b51424441c2e000d4094640c121040d1038401d0007042103c100c1c03200d01441c2610580c00d0260300e4003100c4002905092001410380c1d015402c220401824036130100800186000e200b01244200058400c15812400240503848031840c1500400f102580258064000c851085501000030b45d84d5507102d80e52901c1286040b01c08040340b100c100c2c001e140a0000701c00d8444e0881c111580392070310650031368ac0c03018039078043e400f0300c0001506c01342e6901105141e00011500001102c000d000b4902d4020229400100000c001546d071030760f4100030700079204622143c0300a80e555541000c600884600081d0300145c50007100d880308102e42e900101d498010072282601704000b0380b44543c0b0348800d200d901060114091400d43c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 638158246 1250 638156996 638157043
    0x110d08070606150207080c03030d0f0b0a142b02010e030f01020c0a02040e0c010806060c01060f300807020405151f0e27040215070f0c33031e060305 65
    0x202d000050751202b0424500215158124254000080c0f54880703109401540d8003038080b60040761142184000d040c00d45070b0102020104449551400a0150f40d60507400a564900c0256120b03140d02d41407118010180d800b5900320b000b0395801c80c0d0104621000a4004074524410b5140500c9030484030180203021f0800810100c000034400038004064501c02c44000c204080343d80f03000d42c0468041c04101e9004400d9513146d00400b41c0c11500b1030242140741c5043d445103a600000301c03642241156000d4072141c2403c815600b004050200246050200c0740b08010304080b9581e00040b504042c0000e0500740000c01c884800180b40010031447c0c03900070717200c001c11551800503081c140040d14650f90100700301925540300041500c400c2e211020341124000c1510001c1c840f100d00e0241003a88600607071102c403959108080c075021194002005240801c08090345105c00d44e8190b000072249500c0c001503800880700354031703041d18415554216203d95030708003402007003410010820310a034007031481c41c00c05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 638159496 1250 638158246 638158249
    0xc19080610030908220b0d0207060f02070510020c010213120c14151b010c0809190b13020f03250f0305070510090f0b0705010b010c110d08070606150207080c 69
    0x600c924900e4040f05d0121030070034089081281d585038050906000a01e0b501c0c10317040a0750010350800e00b025074209241041c10303d200e903071510032a51a1580035002d00a078501c03001040000390480c8284411554080210140e20100201d44401502191650000440f2141000110042550450301160200e032505504c00d941c0d4104103003080c02d260040720396908000b50b001244200780c8e83c1c461840d40c00d0840d411074a6410031003c03403041d02001d0031a02c607403d00c00c00b6002c800e0310000020b483c088411001c2100307070007050460602039001500b80ba0300e80003003070080b91820080302d4014450b49403000c2d400440e40144000324004101c1290307052112401c40e00e40035207941e0548100f42c0314142c3d906209400601500070040200400c040740b0040650b6210384000710f034081041144c01d540b90280240b000d40c000d050b08001c6a4100520114451740e01042c003d2000d83e44000f42c66a15051001380001021401100080c09541d5a00150385c1011100a40360580c0c1380c01003002030b0800b00ca580101d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 638160746 1250 638159496 638159513
    0x103050106090b07030201110c07060f02120301030f11100e03010f110d02031803030c13051c1203020f07050d0207080d050304110a0513060807060c0b0f0c190806100309 74
    0x3d07104a0311559a95100d50314081e40140340c1640181c042c4500400c0303120380d80c4408207402c4202c3d00241c030346951a48024000301e07100d04040352143c100324024001030021032403001f50b0162842c4641d10114521075540005050348860004890000e80e060310707841010306081c01b501004c030101040c248081002c49103030000c1400350180280754180c1c0400020041010240307041c000040c940d0940c0e642e820005100758007070380141c1c80c0784c2c0104101c0000084908200310510b00d00d0240a160031a0a4440e5581c1d40d400e6031018401c20426400388800e6080d100d414000b005110310400003000340780751210b000303424201c05a1142001d50414280528255000011650f01a910000302c07480701e031054002810704041a0021600140000150800c42a2961010003651064002c90b000c02d80d940d001142c0842281000520305005100820a46c40100c0703800350b041413600e00803d051a909a604003020401000b64000094224090268609003800603810464040c40c06004000d10b5843d00c100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 638161996 1250 638160746 638160749
    0x120a0f030e06071a06011b080403120509062706041202040b0108160e03210a030b1c03030b040f02030915010e040b0f090a02040203070e0310090f02150405101d010305010609 76
    0x4c070940c010300018040c1e88203000078101003481092115200c081407c03d9003840d042800215808442d01c1110f2807500d0107007050b07030001840100074501e0306008609840004e0b25070764040d81640301010303083c1500c0d5116000340010349603101d200a1f6007000d5004110584042c0b5140702e043c00384410a00003070b0805c1b0003000c81850b403a41045140d0034446800700346495002110100740e084820940b10904a881c0c005241052035035800303026641c120f10810440141644a0704c2c4002110705507440028000c0c0c0100003420402000096042c1401d00d01200341d034012120380034a40c00000e40561030052030025180504400020144149050b5480704040f03032000d01076036408501140080c1c002c203000c101d450aaa40d026209544904010300c000d0450a1080066482801402841a564002c0744100410550420b08c1ca4080d0310072502400380c0402c00d0595804500010840404c01e0b4903240c1c1d41078000e8080f0395074032680461002201c250620341422241c101410035004201c160790084c41c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 638163246 1250 638161996 638162033
    0x30405011107050301050c0703030528090c21020306100b0d0b1c0804080d1103190203040f030f0209010617151305090c09010e040507060e120a0f030e0607 68
    0x125810003101518040156110f291300d582000308110f40074030480c01504030780d4401d45080c48181c88900302c142000e212248076010b800d24550011000b00d016822164000d402220f41422050306c0340549260955103090110002c4c3c00780c0d08801c2142002c200041d808444000864040c6040a001511a10030068403410039030322510415a41d984050b2121480200c0600a200d4541031749040d4085400c5803140c1d000c607010381c00700d0304020390181c400765101c03401e1000998038020080b500511a00b241e80484001c5100501000c20301000c554882005140a10441800306400f803040000001d01600304004001c0344885182c40004045140b6401030402801010010f0041d000300700181348020080021600f00003c1c0902104041824002c00d500bc2e078152480707a88800310a00c296005890003007580c0c1c042d01040225611a0840208001d030051400107a610b110340810310b03010407124244e03600883c11004038105500505954a100320541d0407074101161a15a40300e420390100f00755 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 638164496 1250 638163246 638163257
    0x509030a35031501050408031605010c140f070f0b070306081b0d0204051906030b09060609060307090b0102070510020309010806030d1407170f070b0a090b2e1206061703040501 77
    0x61030f07a8010340644020f04181c00c03c4070b407101c80d212600980b8450040081d0b419519000e00c401c00b5034411101182c009004807051032a000c010000380910b81c1c00040190345a0203500850000500c403148800e02135140c50307401007071081c10081541d0a0a0704200d074210b488008010540711901d8265409031895011a00040c0700d588070b0b0403003180315807a0b5404445031880c1003800f104001503903040c213014007040c84c22500c040c0c2c0d80c6070130b108184005480703c13541540031040c1000001d2107908200f10320841841079400700383ea10b07c080340c0b1019400650801580020590110300d590001e1401d522007011401461004039504014028074188100440c04200010b80300040c0018841d240307040d5281c550310550740e0308130a81e49030440d8006000c02c98900640c1800b00740c565246009070b800442d00312070030004075150810f840550080715202110058400346840c0d00001030241300740300070040740c190b02007000c900c2d16149040b2000c6400c00c4203090008084984401c0002046d241a2407080c00c01c1f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 638165746 1250 638164496 638164531
    0x7230c01080115030b0a09090b011d040b0a0603150204031407260a38040b070503070c050f1e01090503090f06040e100306050901020c15070509030a3503 67
    0xc801501d944038590741c01101b070410020b00328080740c0c021040719016080d9000b807641c03140c2004050460411030005c03001c00300004100801c080b0205190815601c402c001b650650340c3c1d4a52400440250359001401c2d40803030200188601da198540300d01070002c02900246040201c4401018160f515052034003c0e000c0c0046113501082015103500d80d00441c0318111011904030440c140500e983e201e4460010b141503a82c0c00f0b84280e03c0c41c0340620340c03040c041b00007030341d60b032208030346c240c0008114504010304961080f02255003841040410b20300d0402600100601d114001000707a41c0c40143d2070940e140100f0709001c61000f00a030f45200c5012600d040c1400e03200400128039000c0c0380c020103a0342581c102400310710501ca80c480030450b0b1241e0b505001a0f40c0351340e079960807406a0000d640b12a0802e61800f451801e8890784298004107a09040f030800c00581d0102e0b24100707001004507001c0350500001c070b0034541540000c0d048408484150030707003804020080c00d03840c0409000c40b640710404414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 638166996 1250 638165746 638165789
    0x70f0b1003050f010207060c02030f040504020a1209061b0f05121e24010518100302040b120117010603030c15020d0f0f0b1e150903010207230c010801 66
    0x11500045402c407040301c3c4412241c609442c001d5000c21412501f00c0e2400e18000000ba00100a880305040c46407900c0f801d15140c03401f400040d50259509004021240c100411500c400f480307002c3c19140108000900506910046030768144112a05402d001181460036032052f0320070100d03070b412104010748a0580d00c40d0540c6200202d4182d1101a0701003500c0108050460342d0540e1282c1110849404605401c01c00015945881580b042484424840702c1d11411403c21b0b40b5201c20b6642149401072800f56104540984d54000f42c0049080c5484000104003421404040c0c801802254000b044154503642e4041d00148010380e008104001e584024041e50b8050380c1501c1000e42c4591051244d0303000d00f604480101114600101228540003030f42d00d15040ca050101a4200484481c207060108081089034048030741142c0700d40d00c0300410019500c4d88003800038182207442a0b0f592510b0301d4141136103511322509140300b500290b103c04000c9041c0e80e070180116046070520340010070001560300303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 638168246 1250 638166996 638167021
    0xb0c011a0616150c0c0512070803073204030201020709060f12081c1e0920061905120a090f0b04140109081b1c0e01050c010f050a05010803070f0b 64
    0xf050b076400c07640303801c072841005900182140c100e00c1c0300d0003d4810701040d00e00800f43d2401821009440310005100040806025400f441840540302c192012282304124000ca82540900d0000031240c40201e010011035030104081405018561000d201d42030030224220103000251140d4040c42c60b4400300300e010b1040040031656800042e030f07080015114907420034009815000c1d641030000d142590510039005040c40340841c42a400800b0f42820752001d01d040d194459100c80d65130744600d04020000b549018240400d402900c291203160300c6919560264420b4100180131602031360411143c0c9002601d943d403507100d070395408550254661140d08044002841002000b00035610340008041407280442c0036000d4925904119a00c035504155825102e0121660307050300e8618840c5248405400f848851400e0007040c541390b8180350100b80a142980c40200700d12426a0362401400b01341980d41c082c540c050258500114545071241e51000010001c0400c003a102c29070080c0868124804c41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 638169496 1250 638168246 638168273
    0xf090705040905010801021c090f02121002030f150604240324030203010c030e070e0c0c03030106090614030403050a11010209060f030f060d020913030302040f0b0c011a0616 76
    0x2100403c8190b031070342d20150003076000d5454140001e412015131030540d015070103011611613000ca9002070211b41603080c400c1d8984051305070b410301d005180009a02c01000e10196100d4401800111200e0425494110810344400c0f1594000c11003088288000c42922006200c600c04180c00340b0072030310300c1000031401007071400d0040b00004c0d42c20300d800142d05034000108055034001c40007045000130483c3d05030b003110640e10810100760480d560400c0f01c84071081041d90310a0036030201a01c4d06406080e65030540c2d01c00d8000d0000310300406405d00c599a440b040390030881003100d1806140d4101901d014085004886000301005404081c1e107030010403e4050b03401e5180081d09060715403018004043d59034000321001c26484c1640780004030289001e490b09090280c018045072400d8071800e0002c026807035000001da041c0342d003c10000580c2496451362a00074802544556102e40314800306a007996443d0004491403040100c000e0069034511084400684507400f0288801806191007803104a10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 638170746 1250 638169496 638169509
    0xe01030b01060e0f18040c09021e0d020705070608041106120f06012a0215040f03031416080702011e050d0b01021212041b18020705010e060403050d110304020f09070504 74
    0x390380300c00c41e1000c900744030034040d0b4811f001040d5129103481462040f401000181c0c401007898184040d0780040103001080c102c1e1044002615208807520b42c6032400c034040e4000000501000c0070482070120400c2e40c1103000004542d814580710b4401107011a80b02e0240042e407a4807410800310704183e004210407102556290704414040065030a00c843d603080001c4207030b000307010750090b01e10755030b4810080700c05076201020b0000260741540c40c00c0758048100d211b00c243c04030007000490101c42d0403855902203584501d40030780c0d46a000384001008203080812815030008070845204013a84c020007521500c41d503103d00060070003e6440100c1c60b000403203166640055000031600c0001c10000d0500c0c4c461070192603811004024880c40d65a201c045205103402d00c0114814002100c2c041e0300103210f580d00900011600d405c0700e00010341080c4050b10100d000c580009100101c00605000b2921141c001c45070040c114036040e008a5000314000301c0c00c521a01a020015141c18003842c00d86019010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 638171996 1250 638170746 638170759
    0x1002130b21010b031311012f0106080703020913020112140105011205250507150903030c08010b030a09080f030a1d0f101508060a150b160b06010e10080a060e01030b01060e0f 76
    0x230840142c0664040b600d00c5c200550a040001c100c1540006e414030446e035024100e001d039943c078074244185110b0840c0d000c9040100c074203003521102019000e04c00c0c03200a4100d418900d545880d00160908408101400301c0d241041c0c104070703000f50300c618100440b484910034488101d0a0301e000719524807650340001c2c0b400c2d071610f107054172404450f48440308051003511308128139030300703100142d4004200348940384007010200b00148005582d5044010410710070051a403d009128007803541ca030304101d03a446240e40c2d42d0084240501210b404007440d21401c04060119003014490f03881d2115204810020081d807501c00b051600100c04c0c18080080c00741d00252512424200d010320050840d43d407002140c1d00a201d004260415068100c400c800008201c0750322640e61507441c601c2a075030040c0303880c0c14803c0c0b094010402e83c880c042101c84030085582d40c2510ba10340900850101e5003550410720000302135400600015800800c2c81303040d50b42504081c0c20800c0b40c10005002a4082e01e9501d40200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 638173246 1250 638171996 638172047
    0x305090123010e071403130f020a0e0a1a03030a05091f110d05090d020f01210906060807060503060904060e19060f0e1002130b21010b03131101 63
    0x3001c4400440c1a6031400c40020382da5141c500f4211050340c12501031894028040001c6601000c0d005100102184240000c1300680055000211003808960164a42c0000c1c8010414503225511442e1840001880b40c00b0300e160001c80402d03901c1c050038607018280140020065015030311001ca041d41210714120b510000a10b00000504812882c0b812403101e101d80c10119603000e010f881a12446075014207000b100d0780c103503020080441b4a05030b0050600080e0f00c8051201e01036107003e900e404042d400003040e0103400e4034050003110303019032015007035810012041c000c940e0700c801180d401500c110f41501883c3c8542c1090001041c062700021858420002d81e0a040311820003085100c0e80988001c2001c2441c21481c842511048907011200c0c0c0c2000c1d0b60446011074660113011401c054042070400b080e11800419035a9020100c6001a20414100c00d100642886c0090703024004880ba0380b800c40c20484103842c0c1c2495240002440700d2840c51b400c1e5220b9104522020030801e1001c185840e10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 638174496 1250 638173246 638173301
    0xe0f0904060b0306160f080c0706050c03150d02060301030b1f08010914010507080f2205010f0b06041404020d091b0f050f18131506050907080606090103050901 70
    0x2c0c8410040d050083c061480020080440c4000000710450592100320307861000301012201d44000030036050031940180301c00030218045100b1544141d80c2e400e00d0035070b070f8140080d20940e041e6011044500c00c031507409481c00180c48120690341100e034003001500007504c0d01043e460034210020307144601881c03c4040010038680540000d0b074403034060141594041c0d07240807240c0c00d076041150100042820640881c034210707403d00005500050018501070342a4404a03210440b28036100182c800e691203c05480c030401240c861900da110046444030f2900e8030703260002400e2425258260700c1582c1c041110305d02c00718160004200543d0240d080381b0429142c0d83c0301d042d011258000c8610101c1e40c1d44000c14079080004490f02039600003031140b02d007005441d40b107190030750006041c030342071a60f24803071500050042e0040300d01ca0f02c0440350108080d4200800e00440c500020641c0040210903c00d0103120b40383d00080301c1900300b080c6004100c503510020814058003803e1030342c2038000441d00034030601 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 638175746 1250 638174496 638174501
    0x4020c0f030d14070206240a060c06050c12010303030c232a0a06090606080307051b0121022a0109051506010e011808060103081216020d0e0f090406 65
    0x2d0741a001040200d0081e000201c44802c00071900c1402590211010620101c0e00c42072205100c035150703510f0114004800003050f41e031002c036400a0081091051031a0802403d40586903111408805480c02d0001c55146030020500c10305c006070605a490314042001172103001c0180c3e17442800c980d00d40c242d042d561052412544500c034015100c609005403c1313101848071003103c138802030501c01061255503e8440340005d2100800071550f940c0d650500050010341400a040440d014401800c0c0000402641002d805000d5400074100445480100c0000010028200310080340d280c0042c1c9440350002544010b0801154130322a42e0b000d802d14100104d01504840d10003842442991a1080d070303001e0100c00303840141c49003400316405041054055100c0c00020500f4111100c0011b1655541c1100c141001030030307001907900010002d0030141c00f40d0711103191a0801951a95504040e0306480f00030b4035800006091010004118100821607445110480c042c3c1002888600346040c5031500c10300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 638176996 1250 638175746 638175757
    0x5030307051909080309011103070606090b1305061521011502070806010b0301031e080729072c0613030203160305030405090a1b0215010801020a0203090d0204020c0f03 74
    0x142800e10042c00d4102442422000c0844130010000e50800700c1a2006580840d0341c189240c0151000b070064002088007030243e18000c2c80e1200300000e01c06900020710134080003800e1042d24070390401c414400140c0701c4020441c50003146424182d15080462550095011080012604004048001300b60407075800f900ca92030400d50f8085a100c280d03901c1289454120174401c10080031014070040001c2030100000b200c1210021200c0361070380c00143d0f610300080d00710160a55641006140210140c2d50154503900d51050b000c5080312a85868480103000480030100e00400c100002c0d100748000000c03041c4030062480c000c080b29151203805101c0c0100c0d040b24881a0301c41e2280c508000100756036a2000c0b401e4981110145191500345000c2c01510b0340041c0840e10340b15612000d00545103020609005a0305280d03000d401100080001c1c840480c4040c4c008450b26481007100604580d00042100c0d0241c0060f1810742042003140001002802003040030b4016000341d181c07440a06030040010b00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 638178246 1250 638176996 638177017
    0xb0a030f1d0d020c0303091512041b050901080c0409210804060f0b06160f150e0f06130201030e030c0106150f030b0105091e040609020901020c0d050c010503130503030705 75
    0x70714210b505281280c0c1c1e030241a0000d5010b800c2004614620b09100e002172200c84269080c00e407800c0700503421000302074030444041e201c0c010f80c0c481e114106a1021b1502c002403d003110702805650410000f640c580480c040054400e030760744d0762984200100da0003d1001c00030166400404584000d01c00f03003030030104a404a8a130380c90f090100001004510400d2120800581094100600c0040a29044a0444050b142d06400d5400c42c00007a0031400c01d00b044100444010584032107a01c011032912012950310241030f0460420000c10201043c5051350b130781c1c0c092a0109601c180140310341d0540c407551b81030030629400c2100206409020074401004503c0680c2c5e40c000d00315051008600f00c0301c0140d00c0b01e000800802c0070b038102d0710300031010404040c5001d180c04a0000e1040000c0d0449095500c802416a000b0400006542c0c041c0019201c407001941c001c8640d407074981e02d4589824004260606202c004008540b107199203008420042d9408000c0b241d403400c01c10700181881e00200d2046 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 638179496 1250 638178246 638178253
    0xb0a0314220809030a230109031b030509060a0201020c12070302150c0c0d12110405030c040905030d060f0e06011806030c05090a0306150803130b0a030f1d 68
    0x40e00680144103690720841c1804050300203156410640003441c0100c05003607421660520160183c0d950600100095520455515100c80500000e080520203415140d400036454980340002081c1c000c400e040c1c40c0c4c0c0b01c00124121140407846e05850310b00134800081c0d0405000300e01245065015401421071213041422500d160711009003124803480381b580002c005030482c0b5980241c90241284030340d0059030392070445041807290034420b0715041c082d44090002400d02c012004d81c090840c41181c0380030480c40411883c01d030400380480d03aa040da9944072401603076580700700c4003805001c5c015a621038900f550103001c1290756200600c0c0a0003140199801e0600703401c08a80e4660058400400c0824000301c810b42c075a1900c41d00360001c0c1001c1d001e4209200301085201810380d5280020800b45d0b1040c8000105140d443c880603040d09840d42151a0a40c010459070f25070884007100c1004851814403029030316840030b82c040f40640491100c40540500b008845004022155603000301c149040044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 638180746 1250 638179496 638179511
    0x130605100602030906090d050f0a0309080d05070f020409020a0803040513140411011103120a0510080a110a12030509191d0402280f0605040f180b0603010b0a03 70
    0x210308220624441d110150303004000032955402c040c1c0c0582803100d40109415000032841d1241801c0080d41040c9003d190005400301c01050f400c031503104081c018000003000d1000a101000d0841d104070240641004140c140500455075641c0040441c2a40900303c0e290407540c1d082015a01c0e04540561407003110f0556400364803080c0c620801208411404040c8900c0d152611585480da0000300084d040018954101340c24131b0042000702034407110100509042e1616103040e800700c55000d04507102d101041402001100c0c03000807010038082c0c00c4141511262180d00c0040d14003000c503844004449124400e82041c9900710002d0030704c1c69401c0d520703009144003503002c5200d09240b901901781404c00b800910401c400da15914a5401403000d04012240011014650a4102c08041e03010300b80c1d8115800b408600710005131030700105614140141440d041040c40c801000160041c0c00020341c0d0001c2801d0364480d20341020000d00005440f07503941e544c44600d460b8455120703e444c200401c0c03c0885 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 638181996 1250 638180746 638180761
    0xc030721020c01090306050a0902040c05180904170a0e03070b030a1a0a0902070f080c07050a08011b030209310b09010b160309081203162102091503130605 68
    0x4444440781d42c165240c808182c01c5580c2c0700c0003080c001d0f103c0402903aa4020000c010388483c41101c00102d42c03a1103d6403030f11414948841d040300480580c60150300140103100c001407040c1804070480300d5810481d92650071010b001c0f51007c200b11520b5a052003104000104c9642d0780000314024a250038007804010019881d408000c4c00c0031091a40101740d810f82000707441c2d1146d0141c29424418804029208010b44a03000550041e01050080fa0405901048689400013010f401082c1160082c00009040e1103103070004400718035403900b03054000a060705969039414503a255141c1705441c40001540c40b5400709a403501c020b600001d03c0d4a030064501c158584800700c031b4100c408041c21189000111035103401c8051201c001102031082503030004c42c00c18400d000500040c521480e0007522840c0c41c4440e01c41002c008401201031003000198a021001c5c48842c81d01c0d004078010002d0707a16050700380807442c2114203140c8599150404000d101c212540c668034010350a002c2c500c14045d0741c54800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 638183246 1250 638181996 638182003
    0x307120f0321021b0d0e041a12151806150a050405100f09140a0f060305060f07020c010e031905030d0e030304060b03061303030b030106030807060b0901060306050d03080c0c03072102 80
    0xb0204040b8140d11b45101c0c4038a0190052900c107112403951223400d050190210708948032402d40c4400a8001107085020320546207005548080c0280d01c02d0030a402c0040d002d43c6442000c1c011403c21650148607440d20785801d00c4000042030041c1081142d854510b0440b4200b480902800904079030341440050400c00c81d000340c924040c8940c54000a50320382c03000810041041c40e007689082038a6241c0000030420a200940c4120001e034003600c00303807030000d4000b4103088130128514184903140c4080f17681034a0010750901c0c0007400200c0c4d41c0b444c0d9032904105142d402404e40940b47d40d420714201207150788011001c2c501403403045006018100d440e400300744c0c544200721120f036407190300f2444d0320020921907049410300d85c002030000170300d07692603031212242035001100c2503401d161210414903a40c00e00c0b44680c0d004000c030f854200315a50170a80001d0550120b84806010007100710085a0303d0b5440d681103a000300706c84030482c1da81b110145003028090030003109125040400c0b2054220045c00030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 638184496 1250 638183246 638183263
    0x3010e060f10110111090a1e030c081b060f190c0501050a06031104060b0f13030606030f110d05030f0c010605040903090609060801150c1103010908180307120f0321021b 74
    0xa00c4410440c1c00c1c5210400c0c00418a6070521000d0400307823001000c159142e83d00b2019200c040054909030030307142e00c2d074000c10301a6241a400b6020400441030f01c1d140103c1611000d4402d4103151200322401c0390110383d00c42c690303a000783c595440d040a2010285a9600ca84200c0c0d00c00c01100c040003c40e5420441150320b140300307000343c04104000c010b222810900003032400928140c01500c1090710380e21042c0403030380285c100f201d4180b1820810350a020201c0098200410201e401e200311080c1551100d442c0d019028200c2c0b4001c1002c12040361428007034200501600d4042c00c100102c0080c5d04004040f40014441c042c04110783c51400304026120700c0311513042c2c03180382100c052900729481040310f0040104006032a02042814081d610780e4003030080f0307100d050152040c15190000b4240080c00a2444040240309610040f010440741c44040950f000c920b030401300300c0400000c03a00303083d10450080c04c00507490ad0400d88210740405030030b501900103070030320341c1c0070002c60341c0094106c61307444110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 638185746 1250 638184496 638184499
    0x71b050a17070e0709120c051e0a09021c0f0b0918120304061e0f060501180b09060909240901030f0b1017010e0f070b03010e060f1011011109 62
    0x1003801070241c0d00180546540021407850120700480c0c0e241007041c003811117004200c43c0b043d40c1f140100001d01e4070058006819103207a13202403d00003420001800e040c12481024003198010441d11240b00340c004141c0700342500c809080c0410b0007441010401070086140442c0b06151040c0821454048140001c3c0c2103818000208090404d041903a40140c10060003212010b4a5042e1421458001070718002100d990010110f24007684254200c01c2e071701c090304240d04105c0d180905803601546e500b0f02404884d50404203c0d900d078811408200d1a11072001080d4201000030180950018003280d05140407201503040d200038001e0100b0402074404c2844003400c500c6004014101282295507050341000306020100c000d6035690f040c4004901c100d8003a202165910124012214410700c480c003a05003c400140800745d0501806060324041800f800a210100c64000b41d0180c03a1440354203510a4000d108010304d43c8880703030040c6440500100c1000301d5081034808121b841a200a0304c0d0300ca0b10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 638186996 1250 638185746 638185753
    0x50a050112150203190603030c023a060b0424080703150e010b04062c070903030518041d0d020111030601120b060304080415020c030307060e03071b050a17 68
    0x200b4560800103500040e1400d0400900401000502e404a214080046200b503d8411003c103180c0104000050f2a007025107401079040d0094103100341140034204da08207040324005411026040071001062207022440d00186410007072a4046c02080d45c0d4400e0200c5004501600c64070351468640321405440f008000c800c41d2210751507aa1604d400c10800c0c410762500000c0d00021900004054032080d605c03080c00401c51080c282c00ca102c2e2300303848400c0017080c01d0040d481c6d400c116400515940080c403000d4108400802c102c1e1421f2110407190110342002001800f00e50340b00030304e0041611410042d501503100c0c035400890b03440d0041c05541480406104814111342c0d07010010b5030114060014240310554947c1550071079620b00b03010354080c0b03024022440e141c50074400c0e49141518071030f2100040d98081c1e002440140c1c2c002003181e400346e80c070050104060441501c01481d500941c000148403018481c022a900c4842c5409482101d0f001c4800f001e000d65990114100c409138600000354540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 638188246 1250 638186996 638187023
    0x30a051b150408210a020406120e071e0902041e080109020a050402090d0c0311030c0d0506040204090309120312050a06050109090504050a020306040302070e180a15061503050a050112 80
    0x1102600901304003e8a0120a14041003010813407911030400c0382d0b0076104e10740c081828040d4950020602c2c2c6200c04d0890200030113200a00d419079100b9080c07141740c40b0512030054111424804000f2007000b0103a6503020744d07c4a0300d8445c80b8410100845000845a036100e50001da100414041c541140f034010702410f613403e0510050101175801041c0c1c803030308907101134511070001d52400c18620080d0b0090b051f055444071204100350502c102c0c2641c00e841607400d1040c1311b0209601242964100754101c03800039144072a03280a681411865110403039001000160400341900002c1d52a184500c8100c204225618080c0d10310403075090740241c9001408541091022003290352120360810302a1003159541a030a500007803030203104a40440041e0007180302040405255143e0325040310714510303013003100c4030403030142c0c0c0c0e64015041d0060300740c0080608880740c03004181c0c80b8001034911024040800c91802c000a005003070242d601da0301481c0b42900029030300001804640190ba4001208007010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 638189496 1250 638188246 638188253
    0x60108060a08030a032a050a030c02012909070f020309010c0c0f1205010501090501060c060518032d0301060e010c050c09040606141012110408030a051b1504 69
    0x4400415407604861241c00105103484100b000d041c92484035035010604043c0d4001d10b900301a01d403041030301103008107000c038403a5581120aa68002c07016240008800c101108102d002d840c40d810009a039000c07003206e1490002c0c404004d022195801c2d1120301481d10b4584d800c070307000111203081c178005810501050f481c96220b120300001c03040c021080314202a445001d110b513a00340d02d0f03100d0401c040c00039071003404002c000e0081e24010529003004004940c503148001d0040250b2240083c0850359500000da86881801103040c4008111402c0b80d440d50040c00d0028440c21403030803203100f40f801c15800383d2007911f050030840703040e00c42954840207140c10103001590041e80c080001c9400307000c1c94805d81200d44a4090192040f409403d010401a150518a4080c0606020b4603800f81f842e80c20381704480750f0044a041c0400c3c00e000310000d144c054900c03860b00310340115001050315010001d10140d0166208010300071001c0701d140c4404260200d0054a9503d420b0000c0d4480030a604c1030005022 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 638190746 1250 638189496 638189507
    0x405070f0f0c0606081504031d090c070807060e2812050703051204111206040f0213060803031e1f030335040b06060c060a090609080a0c02010f0c08030601 68
    0xb00d48224008541203131115140c0b41059180c840410405108100300070a041c2d01a0103481c1d0f400900303500920524103a4003140b40740f04000e0034120600d1000803800108800841164001500301d5000c000c5548003240c40c40d20360745290b4003121960260340c59240b010380070b040903405031a40208846460b54451405540e5500844026010b100d0184010000780d01081f1816100d1889003405048801c4d01c0810040d0003c6d462181c6400c03607208808100004131881441c0103001c0c1c04940d0a0008654124503202508103900800214000881030040154482d04120b02503000d944454003c0c1d6104103a0309121420010760465805601c02c04001082c014010b01c20301c504d105880c00c1b0620900d503460041c09946003012003600346d46000700003e105190300d82c540c11000494002d8a480000c0c00300c02e581c0c5001400b105005a654050344040003819444000c001d0340c00301d1501e0700d0b003502c4c08028018032003d09061340460b00315035000462500c15410300203480c1c1c3c000303540c90443e201c10004646 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 638191996 1250 638190746 638190767
    0x31501020703050f0a05120c03181c030503090d111005091203180106060203040b0a050f041a0406080603010506090a0902011106090f01061508160302040302100e0405070f0f 76
    0x19070003001d10200101d44288024505852502e00070410b03260f030341c90941c6c030304900c50030269030504080c40b0030341e014600841190b0000034000780c4010005000b60000701240c035035105010514480301e40c08420275030410080c2d4420000701082e00d403079040300301043d11407100d0b000c1c0c40c40203038101c441c154a40341003950003141c000c483c0004031002603800c411190071a5000b550403440c0412003140703a2000040901420f0301800251000d513051620f48850a41c0a006000514090010100744031030000030190949000b00b0329a039005542005000c1d2086027503126001d2140025421700000c0e50300c1c00e050103260b005240c050000e50540d5100b818180040c104100100d041080c0000b150b03002350070030403219000729100b9000e052005505604a42100e10720f60100f4085052280c0d280450f64010102079405a41942103803038426040200320000c7c881c0e03400c000e6000a204018001155104515821000c400d035400c10644d1150001981c200090b14900b60014450142240005205040b0b010707 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 638193246 1250 638191996 638191999
    0xd1a04060207060903200f120f090307030807050d0e010507170903100b010e0f06040608100f0e010f05061602040b010302120406091a0106080703020702120303040b04030e0a0b0315 79
    0x1810566a650f0b0803050325030218041d4002a40405c0340081c500e51111500303402a07091004222040b505c44e50561900c1c0c07403101900b03003964080b442901480e4038804841c400c0200900303a0364625141d26004800d034001c8801a125445101080c61400703018003417031795140304140c480e03506098442e9603500c4030040e44008030310500e0091081c0c5d481c5c0c0c3c46c100281e2902c060409408a584c1d940074000400c400b541c41d4450780700c3d0b0002110398100c1d44031541168299102490000700740d80d03442c0141c0c015444103501c05a00140400c60001b41d0307812003160b0a0582e40003c88501c005c0e81c1d1541049407901400c0240880d20100c0c400c14401458241e012a016007410b040160604074144001c0c83c0c00f4030211400d98460303440f1100c52080004900d649075030780e4480202c8000650503c4c1d002003032880000e01c079005156001035414207664600000507605100502120b5591815140c0b200c80c266094030101c011840580110303030940f602e116400107450b1082032076829030303540011100c1680501c46525 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 638194496 1250 638193246 638193251
    0x325020c130920190e06130e0f2404021309021c0503070c05010302071a090307020d080d0506040b030d051b03040b0307110102160f020103060e100f050d1a0406 70
    0x340300003403c065916180324200302c48210711481d54010b00000740710050b4a40f00c00c4030a914240302d200200300c41290040d0080d200c50443c1308465103101e0050034100701c138130b0322407007680012103100d240080c03144d008121101200c00013501d68208130740140429540294003030b400490300320502455503c0b060036580001d02980500c1c070881e0005210280c41c1c0019030f4140c100288200a208010070000700600081c6030452400225807100249400c4402c0a80e48400041003c1080743c003040007070701c903ca50004c018643e4542945031220055020800d14482c45040c0400202c0b21714162144200e1002c029001d84040d041c1c1c0d4108032061b41c031807000c05164a60010540d040c9690800141000d000344c50440c5a403802e1402c0081c0103054442205641a0700402060720b4a40070403001800741a030001c1800b034545268801a00981324540082418070f0041080068405c1c4501750841283c02d1140b105030529100c5040c40b802e4156044007910400e60f03803400c0703448030005604035036010b40101c400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 638195746 1250 638194496 638194511
    0x5090c0a02100c090e06030703021f0e0312030601030510080d110703120906021005040809120309190609050102120909070908030a050a0908150403050c010e0708030325020c13 77
    0x1803100f111a4800c50f00d0000d010000140000c5542c07810380c540050b8118010044030b4515400503c1441d40b00840e10080304040c5242011580909185588194000c0546200303070b040700c8001807203070011648223002a0501c7c0109141d070300340078200e00603901184040d01c001402c2d1441500c0800200c4041d2055204100d0004003080307468036642c00820306a92008402e5251890003450701e111191503040d414a410b051000081c00e00d001c88114140955001d82803c0444040c1411406845141d0b6004444684051181048540c85405448031a165914002d07100d00c01280d48440d1810804000c071030030031a100192400c02c91041d480801450b082c1c5030f1035100e00301e0394150f07007010040c0d4010400c08600d0024154002175020b02518900c4000d080000c1c000400301074403480500301400b44500092110ba01010a402410007030000000b1242c1495681c10165600d5000301c80101522004c422041080031550700540e22920b55036004000c02444401085034405c40c0300b5208402550704c112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 638196996 1250 638195746 638195773
    0x80c09010215010f09050121020f06090d0c06030e0f1506060f19030501141003051b120103020f04020910080915160228080319090807030207060905090c0a02 69
    0x900d004e0301c0580e4004040614111096040c0c40b01a00422900c1380407103424601c030b01e00c000424030703e5901201e01d80440c2942a0100c1c44600c54448402d800c96942e0f5618020b0005031040f050491394242d0b4100001002441d8450b180e90524004007916006551821500d0042b041c006400650082c2890b00c0c26805840031903403940404004801000070500f1039460f1034044c45481c1c014020a1900c0118054020011f42810514443c01080c5641d40380442c1140343c403840b09503c0442c0c0307110120b6442d802e1800c5031000d01c100344002c0348280d0f4407a02800d03460415000361482000064000d2551041369401a581a080140622031510418454101d00c40d01c202c070682c0909480715400010704104000203080403c808040081170030003000240000000c0ea83c05500e041e00402c000f906d9803141c44c002a0f03054003004038910314905040804050040810003022194030075001c0f1401c19950304d10a4404055621445912100b40380005002503da10024030300d900d251302c16241202c54106 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 638198246 1250 638196996 638197033
    0x1216120b031e0703050c010c080406051602040f2004080712031725020706020c100e06040305030310080a0b012705010f060215060d0f0807080409200a080c090102 71
    0x8076102c002c1d4441e81c01042131040900031509444001c0c6020001080d1980341d4008900ca0b40c0300b43c40800200007648a000e0a5000000d808258000d10510144641c6c810748006081e07040b61400f08210040060307554090a001190212800d0380090b150703040c500000340c03814842d0882c1c01d600b40450048501424100454441d01c1045d40c4c0d5405920a40c014095041c6050000700314015580141028002c076030700001c6040c2c217000100c1d52252030012002c4116000c2603110b00c050382000002c02c01004101c8084040e6108207141c8509103442986c07100c4013a80c80000290103881517880a00520040d07103030780800301c0c00c0807800b95400040c00b1030000300011204268000700034008400d1043c000203605211446a108a04403150150f0803c1c10000d0b030742d1205510002c254003003d054100c00c00041c40207581d0200d0b00b0880c207540b15a03031403a0040c00f0385600380703204003211140caa000c1c110030114410b9031030b0717040155a214010341d2801400101507004180c06070540c494080481c0e2100c0014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 638199496 1250 638198246 638198293
    0xc1e0513091107060c11061b0906030f010e0903070f080a050f120f0a02070b062e030b01020114010e07080a02090d0f021c031e1b05031216120b03 64
    0xb0010981d4421075400e180040340c3c0101904402c103c0e900508094600d000110b080c1c1240344001c21720510300a04201808a00c60f054200d40c10150100820403118941c200030780c101d8081e0302c9090819581c40d00560340740d20a04800405003010540d0b024085405038000d0950700310071b400d0251804060701854040346d00030194450320500a00c04224070350030002c0d01d1a8200341e01c09010f6042c40c80c140c2d40d90803281c42c010221806010844c00c1d1035198415605001040600107a96824007c0800c00081c058405140303098050b6080c44001103039441c0000b00326049540d0a81c2146650315a500d0481d030608000e844483c0d02502032000200a0382c50300309440c05540304109032500401c0d580b060000b5502e211041034a8140803415150200303411803a600340142e011100318100d012a404192a04400d07035980689251015410000b00440040241654000140e1004840e07485480c143c26151160042000003a0b0030060442840d041d50403c41c54400e0060988200c1c203071500803142c0d20310380f2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 638200746 1250 638199496 638199521
    0xa0803060621060414100315020904051f063b100c0326010303050d091e051b0102121b0d090f080a02010804080702220f0c1e051309 58
    0x181d0060103e189058410100700211300f407600300d050310700728442c10094001d501c000742582d04c0e0480740701002903569040b02c2d80c10300010001c21160504500c04034810381104091340310fa14202501064160040038003403100032000800b04482c071101075104c124510311018100c548000c0206040c0300d582d40e016000a11050340e82d6000007582d90b402d000700003004101a500c04443c1c0c07001c0031031000c20400400f50540b500b606065076958611400f000081030003500142c50308244004101e00d41950040c003141039030141086502201d400d4450b03d0400c208455464050b030320690115800d00c41c150b024103802c1100c502e52402d1900d440c07004606101400c4241000180d2005042c000700f1403a8510202038000203004145c003c040d070340040c0803040c0107040500b401c54045901c008550f07600e098040c03128440b2040303289482c1340c000036201401c0f2511304602d015040c034024642680c840c41d07004040b49910f201d040c1d98a80702c01015184c2c0c5d400140c440c010081c207031001040ca00303410300074900442d14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 638201996 1250 638200746 638200807
    0x6082103010302151b0d0207090905060103331a1234090213060207080304120609140d0207051804060203070e0904030c020a0509010e061207080109050618030901020a08030606 77
    0x51b0351100078201032407a0090b04460703207012603000c04143c000820343e0640c0e074044802c00080007520b2004110b041402921000c0501d0301024880400b40d40e0410040d520102800341c2040c40c2900411254851030010340c86903505c00b5001980094002c400c0c447c0c0800c082401526000c0182c110382040d91b1143c00c44a00503400280c0444410344002e0324000809007031003e091140d0034660720b2a264402c40c420042e800c40004420010300c401d940c44200000e5210381c6055031100d070b0a03c61900c50400c02a010054000c1c2880045c0600b80724840301c0010642e030380d4031815661a42e880340029000a4404400c00415080c680ca690b101c0c0d03810540524000e84131700f080c203103c0381304001e4004510f410031070080424100401820030780c0a54290812000c4625807210300220889601c0c00840c0d81c0312295660800030b446050000101d00340b030044202002e103904880d114071105599100d52030340b26006038400c0b8080720129a00c0d030081d60b0045401491903141400c56600d021885402e54040b5044e0b11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 638203246 1250 638201996 638202013
    0x2a1413050307050904230c0901080a0201080903090d021507020904150501090c090902160c0902180307030506130f0b07123b030d020c0106082103010302151b 69
    0x81e0400c5608002e04040f02c2d0040c1c5031900e17556003000c00c3d00201119241c41414600c044110340107100c035528003440600241165a541c100c11a51a4042c2d031003a80422914001300d24895400300440f41c0454004c0c01514443c0001c2e42400304e110f0880b603507085170020038001078005941c1d200140380254040c40c4044c5821306107050540445070180e119100c640c2c50190102c60968200c45028110f60404000684a0003400300b00494010301c0e0000815000341e5100114000380ca03940070340a9512000007140f05a048038080c540d5400f00d80c0009007941c2c1c40400044c0561034400040004c1d40e2191602c013074461000d50702c0140812060b6080c0c4042100c2d20300c0002203039114451441c41000c20111450100102900040413200301c0d05050002003480e1007081080401308100c2d180340603c484119a2006400e031454002e000f24000d40045018003503940c03131200c800111030a01a200f80c180c00e4a16403035035082000e044504481d04202c500c051080250b0b0601c080d0b59072092501241c044c0c00c094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 638204496 1250 638203246 638203249
    0x5100806070e01020d0507060e01050a0501062003070230150601080618072304030606061701120303060302060a09050907090e010b180613182a141305 66
    0xd9401010a01004405080c1c14070503a4005205d2002d40e180d400c082d982c031081070415074050101d62264100d25820302c018003c050305a030b4012412034800d6611900c0100e001c11842103200700c01551400240c1c0140883d00c003524080fa120504010415442103440c2503003000002e03c0c081d466240c1c10690000314a59a00c5840c08241c260b111000f4a0080000e242400019181000f08120403d000319048006107000340102008105c0024290526005801c3e0389510800caa0080c00200c0e001b60400d080086e205008100c10704c04200c140640d41c86070f070b090000400c4d05400c0c0c03030300940816454030400405070300c070900289a00b1401d0b035580641142048140407044034003601c10002c00074500010082e94038108804c6040d00c1c0c42c0c401084da42c204510700d120313401200c4182d541d481203001401c60420014205000c2c00c41e29110088160143c02d07e1002084590908480200c001c8004038034848a9414005a01c112594200342c40401d00320300c03c1480e1900000084c014914151200b0b00c5107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 638205746 1250 638204496 638204503
    0x403080106091706040303050916030b0910050c041a07081215010e031b0307050907111606050f16150902090c0a230d02030f071107030c0519050301051008 68
    0xa48507080d60210f08a400c200540c2e80d4100003407002d0700300740e0b452010a0301c00300d051001c140e1403980000960705454072410b055024160907108010148180c50740300f515a400c40c00f90a1040807540c801ca03061034684159424440c05141800111042c100200c0000031162806030160f1012412019000e107018140048074440008119040c80511418a400e554001407004000da800e180310340c0c0c10404910101c1e10308407a5070056075202d0191000c000c015607010b000c3c0e07111100b209080394111003981003003000718921402940000b91703003080000503200050000742a2030030060b100c410860915111402c0c450454280c04a550307440c3c0c1c50000551920821268000420749010361400c080010050010044210910b0b041000307443c0c2c40074400040010341c3c0b66210030400940d40c0f80341803692079049000c100d6501000c207103581c16003400803000240c40e800f030b642d0180c8600e91407030424040001d40d80c1289100301f4000600c00c008906624207015483c060744101101c05400c1e03040c580c00504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 638206996 1250 638205746 638205749
    0xd09080d031a1c050a0b04120305010302010c023102300f040201111c03060e040b0705160212060105030c0108040b131119061103121803070209040308010609 69
    0x4160070220764422208180007600d80142c030407110030038402c035040310084070010442d00280041c050171400106101500c41103503c9148180581d86030078408881c281e040324000e01001c0c0c0090610461390f801030900d01d280c24030451945102400462481c0b100c64480320219807901c2c0d995402050b01e14021440c41d04c1c0000f80c50802c40600000443c00040c0b40394900010485014008044003140540e4040e482c982c5805001c0401d40d1003c0002201158034140c80c10b00c9100003d00c1e202002031805c0c4400b40143c0520342c810130601843c0c549034000c8695400c401c02a48070414101e0300c150059541c5645040d1912401c0060400356151408040c200b0324000300160501585038200400158002100f41d4444000e42000318501d40908020b051802d000c81c00c02d420146403502007854a0109542c18100c525598410012100c1d40079140d84a0046800c960b4203a0250703400b10b84520402d2100d0701b0007054031001c81c2c0c00d010180e00045c21040082d142038010602020051012030f60101004c030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 638208246 1250 638206996 638207023
    0x20408010e2d1c27080c04020909060d03020f0a0f11041e0213050a0e0a0509010c09030b1b0a0801080d03060f09180206130602010e0c010c14010e0d0908 67
    0x1401003070780c00c155141c008088141c6140c1e85102c20900303455024544d035030421480c030b0740d068502c42c0d810001c10012007014003030140c15100d1504402280c0c5050300032035407002405481c0790210b0322004140311603070001800442c02c1d4040d4448610389000208200c100817030003401103d00401e4641040c900201076400c060b809a030a0045101c4c13080030001008040b1141040b00594640703107040c880c0810311058100c1a40041c60550002d01b01141504980c01420080400c0143c0c2d111503a840c0e013212190071401d00420440f0f8401c20115040c90750302ca03445041d82050a4000603644640310b2540d210600f4070003c60307001c100501c15140b041184149181c0c0340d04040000900385200d400300449240b044c444041e0301c900280070750b8108030b0304038401c031607010700100e0312500a20a26501b0001c94050000150b282c002503003400311001420080302d000603100c00074034003201c0d110440d40310294a81440250340b00c525004034601c00b00a04841c0144540c1da49484a0804400700d050281400b0b020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 638209496 1250 638208246 638208313
    0x607030c260c030a0b041802030f150a0b0117091510030308340305060312090a26060a1407020303092d0307060f06050d081804020408010e 61
    0x1100381d14040682240c0100300c1d0b038401c035100e940b09048840500400c2d094160890b0034010040e110001551901c241b01c0d00c00c9040d43c42598402682c141e503035540c82c0100800c1c180c4400840c00820255014400010f0185805001c0d00c0004084d0034000751b041e109038420303a204800e041003040da8145840d4100c050000b004040c00c0c40c2d0b4400400e1500081d241090300b2240404950800700022540c1e028113582c2c5c80d50550350459030304090010a02164914082d010303070403948400d0b5042c101200d2010800400c103401c0e050030310301d844a0b10b001d000c274551312001021202409099040204520a00c034800c00401c4003640643c2803c40900d0150090040d940148140149114041001440c0c0e100381c0030303910940120b9541e9014036003054440000f00f408005200024065103070000c010f039540da18400d0200d6030790340c001e00182e681071000c05082810f00340301c1c1c1e0528018a601025600100810150a103500c485213035007156818030111307c0f1a40030741c01a982c40685013a000c007180c04001400d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 638210746 1250 638209496 638209547
    0x20d0821011d0a0e06090f061513020702031f0b1806060703081009060b0318030418090f021203072a050d050307060204060503011a0403150515030607030c 68
    0x4541c208601000b803400d14484180000f0999500c0c1e42c802101071841800b26082c604102d00c1ca070b40c1307800362041c80c40f50074014000020000001401181d250f0300002e450b0300320f00d001d42c00c0041d0003900701460890b818020740401d80d9035420040184911000040000913000c0001010851010030b010003100314465810200911a541da1003951046a010b08041c40d003503407240012190110240c01024404d450000c0c046a0400c40e58041c0d48070310781c0502c0070340f08100000d00c803030341ea405640700340741003203a60303140d50342000d46140c00204c10706100d8101380190300300380c1d07002450394a0b8100d000b108690011070700c001446610f164028589031003031698000c50a00410b01505a0818081d2902507081d040031001001b02c1001162542074000701e0031901e072a1201801400d03a4402c1c41020340040c80d031050134088000c0ca0f0101d034100d0768081c1d281039a0262074440c403c0a480006e001200b891044550f02a09480030b0100901c200b84540d000241c8591540014040c907014040b910041c4020002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 638211996 1250 638210746 638210759
    0x110a09060e090112020109080f030901030e060103170f0f1b0c0a0302030c1002030705010203130b070809030a1407050601090c030e010b0d0311072301110f0c100c020d082101 76
    0x11081c19108188503840d02d40c6214001039400c7c1c05241e010300a28824500c40c03003260a00400a082401c3c801d076000c2c810105005020340d5154404c0c04054006018010350540200780d0034010a003111802440500303100c045100102c154221007161001904c8121040e21138440031b00c4010b2901404607210340d617560031a00440e40c0c0c1d04039101c07190b01030900e001505445500030170030f445a60b6031090095690789020b40d4941c8048541d6007044407401c581802141d6100d000383d0340644901b104400842c01e207800e40c0c1081318202e51100d0302c5510344500f0010000030520a1000d680a09491200816056801c10005088a05540e4000c0c403603490710204100c00d5a40c040104926034240c5030944a1450620040e414100c1c42c1d400b042540b20314040d10342292004074808030714014242c86502100012007291522080710082841c0603410401c0e0148542c0740144106415681c94a003c00e0358401c640d000c0b60096211040a440c00c410203d034454150700410000e0000042d010a906019450702a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 638213246 1250 638211996 638212009
    0x111101e052406040e10051228021f080f07020102090a0b09060f0703020a15050f072f011b050a020307060e0a0807120908011b05070501060504110a09060e 68
    0x3071a010b94094450002c4010f6580c00054401034070f9641c030441107030700303202900000103059071003514001e44408c660300c10300a0000c564514910480700b1806010341d06003056294510807031908a0303000002c002000000303c1d09000b20002d848541d04c440740c00b42071883d105d00b800341004047c4801c41e03004020701d11540c0c4890884204498041e101c203031b00ea00d11000007641c6402410a01041458082152024958001101940722740241c002150345001455040d0685800f12580f40d400c0007000085140203103e05005142c1c0d4118030721400b106004014050f04280340001c043c1c910340c5d100d00c00c1000c8101c000040048050703d42c00c21501d0305191010107501c9019500015002a41d5000045500300c428040b0f61121613004c060166503d01d140382c03201e080c5030b1030f03c0c10344001155074602140b1328005204000307400300320807038500005003000340c11900b17640280400ca40c9952900070010b80c588580c019006140c0c40040c50300d8880304d6031100204100300682c00442002440140e442c40d9407280c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 638214496 1250 638213246 638213281
    0x10e03042d1203020a0b06010e090c0a030b06040602070311030f060612070305060c070605090105071209031101065d05070e0a0605040908090105090111101e05 70
    0x18010703620560200110741000e00942c0d01010b0010a00c9101c8000c259010036034448061207507a00906a4030390380011501100d15000305034210702c10750301140b810343c0001c0c040d21510140346004288184c126001c0b43d4586c02075030080c809a44007103000c1c01001002d1410304d204000613001484481100a05150741d01000f0740102e00668414224412030340060089101a5402c28116049820300d086011015130150200b03640da14034140101d4944107040c06200c0c0240e0044e40ca0807c0b404c1101e01c0440109840710080b000c0c800d061003e08180e2200380117402c000c11110340182c414618000840340c02200d403030b49074114246001000402c124014003000c541013075000d01940d8594646030403c8066900e172001901510900d10000b0b0300c00c080925940c82004080000e1290320b542d00700340804e441038558010308100c000d00652400303520070400b412582c4014504485c1c0740341e181112904000c2110038441040d0748951080d007803208448101541004180410400d40c5420304075400c0d4100c55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 638215746 1250 638214496 638214539
    0x102070c030b070c0602210702030a12270807111f0c1505090a030306050406060203030a02070809090405011401170303070c080c0d12050106030603030903110a0306050a0b03010e0304 80
    0x805010950b03007131048030144007081d40441c0031599955220100110394114076422420714500e440020343d003610200030344001d000e41ea1203204240c40d605d2400c1c006031a0807042c03034845088440090f4654071039402c054203894010344141d50356143c1d50402d421180f400741850350142119882c1500040c00c041055210b000c40c1e0320309501c030ac0380c0e146820036074840202c10070702401e4200380500840b0701010558600b0540b00c0c4c1c40c01c0008a5584040c04203a540b5841000d02680082c400a0000c0400303800a084142c4100780003407500842d100000c0603060141c9003034840b40e540749180d12884039000415400b41c03e40003c1c002c110582c40e098140e8a1000402c08010803422144490400102c13a09071184181410b0941e0800881070030001c09022152415182150034039000040e914041d12480c000d40e03803d1b940c0c4001903411038607030702441c12103031030116009000e881b170000200d0410710580d4041c0003000350100740300300d540003010300755a414420740b00150410481045103440c2903d00441c000c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 638216996 1250 638215746 638215763
    0xb270f0f070e01120c110d03111b030903060127020412020f0f0907122415020a05072310120906060b070c0e0c0310051516050f0f0102070c03 62
    0x9002e0040350380310b1001d03400444250030500149400c079004024103a20b4252401207030008400840f086007170300c03869105118a42c10420090002034011200884000890011246440d00c1d040100340742113000da0000201142454003810200b425050002c80c485080c1d0040d8200b5040c4540e01c03a03100e2160780028807807104225000e05d5622040c80c01502408014040c201600e01140042c08890065a2000c800c40c17400f02001c83c2c200c4982844e0840314a902c0c14024420704200d101548001e400c1c1c04101940704841030701001510400101d406400ca03c009004004050b0240085400b01a10010310a40b0002c00b0070030000e50003400541c01007088040030513410441c1c200840107000c203400c079680307a0000040132402d202c401c0c0380c5001100c00142910b07100d556410381e4241c05000036641103102c1c880340101009541341c5440142000a070400b035681c40e0040c0c48050b000810780d200003c5a01ea0031400e180c64807014144034424016250100941c9407418695444225020b0360100401010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 638218246 1250 638216996 638217017
    0x120309031205160e1f05070804090f020d0c0206160e04020f0c06041101140301050103050403050f16110102210a20100605010903120806040b270f0f07 66
    0x14440c031920440a141c00300304001609010500c038010078500340031800803074400c107990754040c20405052150f41d4102d041404010026010884044e030080e0002c5e03c0d040402c0c000880c000c5000d1081000c407141050340182e0301c203074190b4840283c400c80800e03034041d50444010849007815004442040c403440b0700d803030911000d003a00010f009006107102075985072004240300d941420000785190080c0e00604840c50380841610044900c0504040d003544c40f03201c1070004014950080c1c01c600d410500c40d003802400c200d10426110f0f12070300819240b6100341c0030240b400050020190040a18440c01e102924050050701c500380f010700443c0100500c80d035000074825054a00c9041001e104540400c121205000d640010550f9a0030080241095070b283c1000080c9540c000c081d803c04583d401a9110030315040e204095592000c0280580d4015494110b40d20007591100300d1100701040b1100301e0714288800c851610003901c0010505460345444a0134010608422092a64031182030b103480103044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 638219496 1250 638218246 638218253
    0x90115121e11132c070c29010f0807050d29090d0e1003020307090803030108240c16080f030a06140102010902130b060702102a120309 59
    0xe10030120030040792500411820180108000300214584072a81c0c450a80c0c5074001e030418034408580000000c00c4a004520600b040070a0715988003104d401d1840c6030759029214400500c1c5030501103a85507000b40c094170200c05152915601619041c505038940e80d0034000c0c06551003909000d5540f140348004992800c0085080d681508106001c1c91154900003101d14100c05c16029a40004140120380407810480e100301007407401390000810b8480c440041040c1134000f9803000c0d00c910104000000c0c041603007a4204001c1d4020541c0000401c003107099102400611101801c2445010444805102c80c26401d0030950b003190000001c1900c40340154078100380c02c1d100b600c0641c4500c070008401c10103440103e90102084a001e5406903e1100382c40004a00700c0d1040c8100950100211281151201c80361303109610003003025200d640740603a00c1e00060614241110300d1070010705000f03402c1c03900d4034120031000400761407022808480c000c03d40d02c3c0c250a02c200c2111008050341c424200090 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 638220746 1250 638219496 638219531
    0x30a0b12062a071b0314060601050405010c0503131715010f0b0a1b0c091406130f06030609060b03010b1005070b130f030e011b020303030a020c011b03050609011512 72
    0x80f5035000c03d040c0305104411a400703035408164803056072180a1400025401100440d40ca442803105070340c2c283c64542081c00540b404404cc00e000d8500b07200a02848a01801100c48400500001e1040d003143c1031030504140d107400700c1c2c00e104220040b400c500400c03030000e070318008000341e8200c00c000030348996018108450f40b01d00f450780340b00f050040c626034070203001d2028400d2064406a01007030000d040d203a914410840000c0d1140c1e60401642c1140750221a0740b603000c0c5400c40c402040105040d540c03900c0745000e4400b440f200340c0d0700301c2d641e000ba44c0b0140303401d00c2000446a810750b09400e000103140c1c00501103000e22400075000741ca1650000e4402545c041040c00ba00340e002000d807400c41d0341810000e00d400010b088035804101140d0401402c8412820943d40c503690040056203117590b101c90704030203504409102c80f00342d9211b110120b100c1c80c101d00c181d8404a1a55000200ca01e402800c0007070500c01a0320641c050100d080c0800c40803940450031038060b861410004c81e103440307101c121001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 638221996 1250 638220746 638220757
    0x50607020f2e050301150c061b200703020d03111e010e010e01020c070306020d02070212060405010612030f1d0a0b0409110f120a060b030a0b12062a 65
    0xe01007144002d60380340140c0402c01e010b07074004080c4a0000040c0304035050326548800e00806443e0781012088000251286154643d443d00ca684c0224040e070211f040035489075003881c0d01c1804508e00070510b1a2190411100c004401c96580c010800b8030702d19000310340780241101d00a010840e0741e090744070000740100903481c05001200030384003494040d1101c8500070f2840d680141080c0d4244884605010014025501504052409040f2007451a0b4810009501010301010755640078003150016070340d200925000f444082020346030a150500e0110700f1900b403500800c8142c08501c001002103540180745070248007080c20960071310002c4c80044036603280b0170f00e40294007482c0d120010900c1c0000c840604200d0f0450f001c14400500c45404600f101e02403410105440c0c58240408008030101500940d08880c15132800a072580d210300c415101395004031454003106449021103078050416108102c80c0b000c0c0c41000c0d11143c203103400d44900c080911200301c181c80b2444050309250001c0d0404966 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 638223246 1250 638221996 638221999
    0x705100809070e1806060a03080306010c05120a0e0a06030c080c160209090102090a06020a0b0c03060a080304030803040309050117240d1209050303030415050a060902030f040c140307050607020f 85
    0x54903100c203081180c04070b13482c1c0b003641a000700c002090783da00f8420044016a03034001c0340103095035100c0004560344c0c124802e0030381d40c910481d11481306a01c116070040c55001215540e80c8209038020041c4104c8140e99070006040520305816840403641c808081504007241594081e80c4014480300e151903d5036038800690701441c01c1e01030040000056008005501c0d00390384030540b00307070746910581c2c5904035210041d0103880c080000035001e02101000303503403021005007a05061780d00c0e105000d242d9013003600100d4107000000309100500d0742043c0303800c0081c002440c01c200c54080c0d4200c81551028041e00d10000500743d8091910f1038442542030070303100d00c0c0141901d18a1951820101c101c3d82d8503046801c00328150355030210351070a012003201d119a8100f48400701d43c10324851248000d0400601080a00d60b03119004038001ca0940010340c003d904c901c0d0711a565042c5403d0802101c0314039802205104c15010391040c003600c011443c0402ca89040751015140c503018000724801060300404203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 638224496 1250 638223246 638223269
    0x1050d020405040f0501091d151305030a1d1509010c0302070504020d06030c062f1005190c210f061208120c090d0206030601140f0a11070510080907 65
    0x4042d0244e0340d07019604840b00c02c1d40500a4480042000030051001c22145106801495840c42022074054000b0723001800803c00c10765000c0c59454007421a0031417031005000a443d026200b42045500195006030030040300c2500444101030402e202520403c21000e0500c1041007126017031500a01000700200000b81c000d642c4c4a446417a054010300c0c00780800c0341c520b2540790f03000c24081e101c0c602e0844003040142039100c2c8042246e00c6032441031024420326442c6d1103610030340703618080700d40122030294503403044804041007000020801c0d115404210742c108201c0600c201c15500761080c1e41c1e03415564111001071028841452000034090b030b9000401d0040110680c0420044400010440400d440e044403510743c503a41c243d1b4045209070102c0316070010484074100c0c05031406074005d5410220505040c1c502003802c081c90081c5400c91104012001008111460b100c0d403c032504042e03404009010b004c155040c600014110320039200168100450080050290b5000b00200005007901d074001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 638225746 1250 638224496 638224511
    0x1d0a052d12010f05010807050d1e021302070303180222020f0a0f08150f060d0207020a140112051b03060105040f03110a050d0507140303130e0703110f0901050d02040504 74
    0x502d020709410351a100500349403c00000d0700c688045515002d03100d0060424048850a484280ca0720010340034481c10803892142d907100683d40c041da8054001241c101c0546c60360b01c241009401c0350305003032040c00c1400c14410078100507911001c0c5182c08220901101c0c102c1c40c01c091800009000c0c015020411400c00125505525000784090150301000d82d04e0b000569940502402e483c2c1c0c80f41c0c4040d03041000350803022942e280800c003620684600720b00050402401b034000520790030317040d4032103442e10f03074105154038003540d00034003034034108607094400d200c141031880400882d134400b11050418440088040b0315541c0c07091341101d004102c0c0420510314691030341000c0c00945000900c55105d803040d042d000840e414080e000e20768281d0010f014240300c3c1d03d05064036440c0001e0840160b4503020400c103205034100c0e09a1030034090300c0821284112480c1050015080303c0418083d04000e0b002401310442400040707080310084002841e1040d15469082156000b07130082e50041c2ea48a410884e2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 638226996 1250 638225746 638225779
    0x60e090303090d0f050909040f0206030f04060c0f05090909031204061e0e0d0c15090b04020f0d024009030207060302040b0d0207050703020904031d0a052d 68
    0x6035001d21248820381e54205a40e40c8284e9440b00091504000300700280208810340c600750000c0f550090191401110030400c641c00a10030303920894026a0403d2440c0a000901c08144150030340300302c0a043c0000c01111041d40503040d80500120302d44247c00d01c000003401e82e81d091003074403200022070900fa03400d8141441c040c80070300312003003900d0300300701080046821014007402a00c01140c0303a4005020301006a070412101b4072002c660940720009017800e43d03032980c00240300f9040c54601030440612681403910400501c040c030500e41c6403040c464000300f400542e5522081c00461441848a201c440413001c0b040810000940540380b2004016074246044072003503045040d085200742d09443e00c0c43d4640b9010381c100d0144c0d000b1010000760034044040f040794642c0c01800402d01510844030034950b41e500003944100e0888080740090b40e40842c020005d00340700856160b545c800c5990800035410840803842d400600582500b482d03690b1404102e40f00154080602c1080c80589100c1c1c4c000405030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 638228246 1250 638226996 638227003
    0x80f070c062027030c10030b011e0201140c0309060106050c1006060e1311040b070609080a051308010606080a230103080901320f040e040303151403060a0f060e09 71
    0x300410091103e840d245070310720300415011820f9000074108042c100403500210010840f10304100d060100c2c007501004040e00c803a0a002c81c40c0495400841c410b1810040982c10405c00f034203283c9110404e20501c82d0224010805905441103450940d403206500607480d403500d4410500350881c6450081d000c0380ca581e02040c80d40468405480c0c3c808100510120003080350700c130007110303078900b1760500081c4401002000101040c0c4c1c05028042046c1405440e4980700da800001c149005c44c42c0003600507074041d9071804010060101800802945207414009840040f0003828454007070703030340ca00c980d140715846c4051010048040f07400360319643e100e00c0d0203801b50f40000c1205010a4054601c410507581c00344d07040080c51080400045000d1150358450303d070b90425101d0308000b2100f4000072031814030090030207110340d0090380d02064868a1041c500000d050070b82040030041d40d141c05188403910009801900000f454400050b0380c000c540303202d0000e26054008044181001c03052144245001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 638229496 1250 638228246 638228287
    0x405131403090f01080f0601030c091a09040b030706050a0f030204032f101b060e15101211130f060303020a050c0a0510080a110a02010c080f070c0620 66
    0x42d20f0700140c1c003407004019605100100c03466000749102c400082d100f54400d4011035200b00b03842c207040d850151600d50488074040400c1c00c4051042010456207111315050040503072240302a00076002c82803c08074018420700c5030300c0340030703085c4410035040e0304895221340c2c1150002c60300100321002c0b0b200d40e1a030b0003503180520b0b18801180184500c8800321480c0528100d510601941c88020048a030040c80d5151044064001d8804c165641c1400310212030a00c0020183d01c40c0c4440e2800741d20b80071480201c40c003a1130304206011900613140d540011020204107c07a003404842030500300c2d6490f1100c4000e03003ea071a24081003030401a0000c10145c00060740c2d04180c1c070510070755036050b000000381b00541000b480b41c2a0b10030b1850305486800d50050b80d01541081c0c101c06c011848428000d0340491540c4900350034001070b0355400004540755030180306150400203080d6003070b00c030341002d44009003015524000640b5440d82d800354010010b50140754450642403071003e80b81c940c0c12a050800307151856 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 638230746 1250 638229496 638229499
    0x10618052e0306080a02040e010207080723160603090203010f0c020c04050f0c03070c030c060525030e1e2a0306011401021504021c0507090c03020711040513140309 72
    0x20031090340214040c0c040c0304151382c00070000b048108410740811011380781003a003002455500300b01101c00310b982d03074004080035800b40908454000750b506003001640c88101da0400302d604002d500c1030582c0701030795001040b15142e15020030300d00100e0001900506601e200040407030316001020420540125203003111036821101001070faa541c00100741c0c6a182244d84040a100400009101034010f0300c0344c0c84824042d18000101c115107076225400c95a06941c1c00c4c01100c0f40540f03840302200c41b188400d030740d12102e1409100701c00700000e10070355400700e10340e035061003020040d5030001070541001503501004000803010f000c0004403214220789601000c03420300030700a5800104c0c2c0ea1032803940c124940c00045e402080c80c1c8842e40204100c400e0041e1049910222650980ca10002e603507008031241030092014240540c0380c08500741c119050503154a084c9401030000201003854509801100c500540d004183d0f03076180b001a1401903500300000340000c143d03400740200c1d000000054148000d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 638231996 1250 638230746 638230819
    0x1021c08090118080403060c0c050102041d06040c020705090702030c12040911160605040f080a1d0a24020715050d110f16140f062202030601061805 65
    0xb03c40e042d40d43c0c50720040c101070152081003104100180480e400f0080030381c064a40004041c025030f1341d16080e0781c0940d00840c1094807440d00348080034140321a264110b07034100e504210f020405080a5106c0407a8400c1c544030352810b4002402c1a8024403c0791542c01000d400d031890040ca455441d171070b41d006401481485031614001e0007003400c03140e04480d0808000c942010900d401640c8640251100620480e06500ae28010707100182c8200c020b012011100c0d00d0794054414081c0c007603078504560000892040b45046c004100d07a24080d106682c0385800301990b0309110400070307400e03407a0202c1c036400550006803100c904101c8940c8036014200441005200340005605000d07010058010b0742041b030b100020400603d00e140e01c08048a149091094030440c5c0748900000b0b00b2420400c0c10460380340a50026810403c0e06041a1402d1035060010300884003103154a03008281d03145014050503040c09010500740141c07a0070000414000e0a0040064000e6080050b0300b1904240141405a43d2907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 638233246 1250 638231996 638232011
    0x28060914031f05100e0106120e214f05010e01030c09181d010c32030408040311030a081c06030209010305010605011101050c040303080601021c080901 66
    0x30380070a450580d440c62082000d10104050501c0c1c2c010500540f0f801c8684e0721003d000103800c41c486500c0d50082001c0d0b103400c0300100e10118140141c0e03503035881800c880e800c00c00c8544064648400c00b682c04400c1403512540310340c2e10090024070041e04807282d80244504000340d070310041d80c0d6000024040f03c542a020b10302e44000302003811900c2030340511804100d2980b405e40302948254000c0e213040450349400c251860b680c82214001c50007401c00c14602035101c00e84480742032f42c42e840341171031020084000c202180b010307080203084c16140380b402010b14108403401504440d2a51b56804600c00404070103a41c0e0905290000c3d0f9640b0610003110715803802c0200c070350303e843c0c0854118443c54104003003034070f0101030208440c400e2490143e580300055803960040b016031078000034280a0340c403c00000805609240000d03168a01681c10203030580c0c140760030004980c40c0981641d04030303070740340c1012180d13600ca210050303042c286003180020100d04080d12440141d030b8006112030042d86240000c10498 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 638234496 1250 638233246 638233249
    0x70b0712021614041401060201020307020d0912140a050d030218030105040c05060d110d020c061b040513020d05040507050405011401090b030a15030317010504061428060914 76
    0x1160034030310b4007044000301141000a0b440302c110b0f1121916000b4000120141250b045001820081e002000180c2d800b03c100414103404100c6602419080d09040a000c0d19191250480c48008900140090100c1450003203030300341080640c06840d408415100c44807190240200203401555210000b084440b0600d03c150506228550003190407014a041603400c0009101166000680240700280d96861104a807c0214050702134540800e00242c1d171200c040765a90300d0010003903c144500b5507100303510144041d10701e040340d0840340150340a001c411140703c5000000e002e08020500903505110800040050109206060b04c00c00c9034100b0140c1d8a521102c40100301810109000c90380080c001d2040c035000d034018551010500001040c5002c11151005045561754002c0300400e4101d568011604405010680980400c1c4c90400c100c600c2c000318103a2009900003428028003a401c04240e040e031017621103c241d0011098140c8006548100043c00e003485482142070748243c1103202c0055 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 638235746 1250 638234496 638234503
    0x80616091502150903040f0e0f070e131806021b1002040605070b04290106140a0c080715061202030f06040308160e0d11090a0c091a0c070b071202 64
    0x603680c564010b000c40f00408403d810301030000f40407408140700038000000c0740501094144058000b42030920414201800e0711404990b02401a4040c001ea0b8100344449450b099010201d5480003103020442d90f80d510380802018007251005001c0302d00000e4041403c01124074001d20754240b54080f21201040c42814408034090360040750700081041000c240881c1c0c005286540040c010401e1000d040100306102e4114080c0490700040078665600400c02e6542101c4040c100034807902c0080e2a00110134001481d0a40c1024010064500410580c007400444040c0f0822040b0500c01001841c1c2c6882e000c506451a110b8100d100e440381f61018501200c000c215940180d070306032102c15090b01d96100d00086143e80608410400420810083c80d035500c1c1100b0000041c011903c00114241c602c05001c01004020007400700700e8100b6003c034240b0759216500608440d40020b10003030700500105400880e102d00301c181d41541c40341c0c10021415000c400002c2114a01c00c1c05500203210740304005a84 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 638236996 1250 638235746 638235779
    0xe071e020624032e05010501021518012a0329180c0a0905010c03020a03030f0b060f0309010b011b02010f11151f0803090607050708061609 61
    0x10303041070300801d2542501c40b803402c04440248508111212401010078a8904142e901c4c000b20a048032811401c9806419a44080101800306010b10360400001035921005900101c100100c60b03000a800001d00c01c4845145501c0240240b0038850020b0b504000301c1c0000307400c01519044c080813421006d00038840c1e05003040001c0580c0303108003400300b000d0081259000791039402040c40511400110039880d0607501c034081c2508991703151200b01c0701c014008407554110764113202c40307803600e00c0219400190710308820b545460041030440c2c01b0300948024280c0c0d901901d40105010076502e5a030703010b00001d035104242400003040f60518000c0111021440522a217031000b87c0a4240c20140d44514620540c1080303d0411102075070310622464508103800b911005140c4011040c002400c8120003040307400881c0641c4103c00300d0924010039124400e0749900e51107001e0000b82d1004008040c4601c40040c20050141e43c2c0c40d280c44110941c140e01c1b0701c4800400203071107600100d40d41c00d03121940e01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 638238246 1250 638236996 638237057
    0xe162d0810060c060213080712170c190c0b0d02040e07090335070b07080106030e0705040e12030903040e100b1c110d1d0703120c031403010e07 63
    0x100b440e0f250340c8440c1d009510400c1d100b501c0d220035000c042041c18003000010010711b15200380c42420007190810012805030800e1807003140c40c041044540070f8100280c020380403941d030442c003c0c0704a00b031326081d1400f1546e83c0c42a10144000f003601040780300300398090011221281c0000c40d160351070300750880d07400000b408020000021540c01c00a4406885140c24110700d60303000200d400c01d15019108034942040700308540c3c0040310401c0241c0b285d8403c80060043c131031401c0c20700010242079041368071284a400340030701a0356a0000701d00405030401c0040700f0780e0b1424046907a41e051582901d9220b038001d004a0340c00b4204400800c0c01402e41d40d202100304c6648001e11414078907180415240d0303420403040e0b126030035100d864044c9010708100080c4080303451014000b600360014600c04e10201100207115405400c1420100081503c229030079041c49500d10304014040c101f481e069034180d08629401880e100003000225101c1c003d845a1400303034105807030f00650b0051054881095040020501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 638239496 1250 638238246 638238257
    0x420e060906090a08030703020d0f061805011a0906120403080f0f040b01090e011e0506040606080402030c01230a08040212030c0c0906010e1e0108060a0e162d081006 72
    0x2400844e4511000d142c002032a1300d0050320340b08001d003141c0c003070340c1103400404000d555409041000001a18642502d11f100074400e101e198076100c5980b20007454061068001c05000803811400d41d14071086030302c4002074405d5170240b4100750070000c02c0c001d822666031340c200480002040f01c05451401e100d00c83c07a44080c00240316030030451140c02800e807045102000790b480d0314408110fa034121181c1d841d40d0320030030710000b41840c20310104410b481e4140c1c8900280540c030300a110260310080740800300c00c4000c2c2804002005264000410040042d0925001d4840410402289030f0b0080226018500882d54402c5600300c0341482510ba10a071032001540b0790082910046905003144648d038400030505040b41c1d10a050004101c2002c40024820600d14000c038642103d9a00401a183c0188041c0c036602111414040b106230412006000b0b803150100c420301c40d216103442182c0c4520039440720130f1031004409580480b03501d001da500d0000d45c00700e50240300003106628549108002c8a1165454 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 638240746 1250 638239496 638239513
    0xf03010e1320010c02121b01050403030c0204020307230d1a03100e100905070f06020f030a050d06090e1507050a23070b0c0d0e0307420e06090609 64
    0x20001c00e02d0700398900364180b1000c0444040560b8030107000710707910202d80c0041d021a111401d00802c5600d02a02683c3c1489802d120910200b60f0080d14680e515030b041d81d005a903500e4406e015640031030754903c0d000b82c21000c240c10316001c040407000f60144009803001400210b502140d1903500c000c031a03009640503800b4a0101610b40f20a82000308560800030075505400c00001408040d54805401a41ca661011001b041900d0880f4907400040a45101a16410030485104c94481c4107160f03c1c3c100700480810b159025100b6580240010688054200400e900032907101c0c0d140d041003508404190000000100300074001c80480d545040250703180000c90010000d11001c41e0030554440c2403449080c40a80001824511494003545880c40c1c46603c13880070b201250241c0d01110450655500b050001c900080e0340f1a407084841d40418807103030707143d10321681c00c0a03e4030520030000030030385d0804c011092140060350000d005036511009440c400d5590646050f6075400c141d6403d503655100a10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 638241996 1250 638240746 638240783
    0x3040c140a12061505060a0203040e160f080c0910080105090f061012090b040302010b030706020307051b0102100f051504060311360f1f060e03070b0f03010e13 70
    0x1c03104c0c00104044401c40c060b5100c1021405a410902c4010f016910005052040b580342480071644101100c82c0704081c02003c610007007000e078246041005001c50381e80031440d500802c20030341e42003a03800750000c0889580c03104e0003070000c502840303094042c017a40780c04140c1d07803501103922a03ca508082c00401e070b000c0190104440d0450000b440c04403666403983caa10006580e034000c507004030b020740c0c0082440314100c0d0406082207081c2e40f0a1085d50300410040d40040c3c40401c02c40401c40c0e01650003010080282c00603410003050620f625041c40c44d0460540d45040301e81d101034008c10581060107400c0010380c09100c12540325010140c140761103000c078859240340407400124110442d40e198421010004504012000700354810185002504100001e24a0504289600401e02c00172030aaa440005801d032100f0154002d803002c20001d00c4004000c1c1c2c0f81003042030010300310200c040d0742e54140c1150833070385130b0001e02440702d0020944011070102603401c11225030007600019905d042459014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 638243246 1250 638241996 638242001
    0x10171311040e1509033108061312050f031905090c061602040b030f06010302100807080f0615040f081b0303040b07061b11010c0f0c0213020d0203040c140a1206 70
    0x2401080039202c10411b074070164682d00f40b1b103042142c80c0341c0465611002a4014036a0b4241078120810a80c4450f00300248172010742403100c45076070004099030140c030800204032810b20942400c7c65551200105000c0c5101004a04802c0c01c4c04440c0c4c200b01e181c45014911380c4890a006529a0100050240602a001200c84903151038402000040c000b403100d03002c642400ba03401c0100342c0d6a04140010001d41c141704100f0781861030b851814604a10b88414054040800034103903100d0700b090f040000700d580d102c004c1c40c18009406545010348075079a5441c2d003140359020b4042c18030355000d49003d10310240211038200d9a400700041c0a5800c20307082c450941c40c2030308219000d84925840d400c01c151080591a40301441b660706659011400102c0c00381c05003500c440c40040c1c030801c16100340c4e415945a01019070394006604030780e0314803041450a41007003e0300511b20300c0440a440081030004101500110404a8000d00540c450780020710b402c10418400130b20401eaa500c0701044090001007059 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 638244496 1250 638243246 638243251
    0xe0a030312150605040f0e1b07110418020f060a0219150915150e061203040f0e010609080c03061b13030602040515041410171311040e15 60
    0x1508000382d03001c888541d80c0d41e200e04551090010030341c009014480540072113540c070007030f10140e1f0fa074030030780e0400da054408608100c4030034011211020484904000b040b080041b0f0344003008200b80100903401848000380304060000728030603007084540450340e0401c0401d880120704940c000d040411503c4800382107040c1100c400319182c200c010300d402c1e0004a140305051186000f180c0c41128149102410000c442107c06042030050b85400c040003103001610b86594403440548005401a042119052440c0119040355500040000340401d2280350700c203480d812140c0990356144a544d890040c00e4450002000c801d4054102600103a43c100c2001803101d521181c1504043c545055584082d200d0709298008035441d0f0740000701040140740c800380001c07d148440359050700d440e19144490300c0404050100c10700803002030302c04107140341c0140e41c0c100c1014101c001e032342542d1804a0381401a085121801c6940d180c0f40b00010005040904c210400f09480e0b1005040c00c2841566551050000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 638245746 1250 638244496 638244527
    0x7020307050604050c011d0a0515041d0402210d0c022e0f1403040b060427021c0503030415020c07030c080705150417011103041a070e0a0303 62
    0x10410000041c00030801d40340700302c0c02003000d8640b0b04a244001080702441102018076202c5204403440c403035072441c44100c2254022102c284010120309442e01c200d014541c400004d15841c40580368540080c0005103106a100305c1d120713007204010b11125802c59006a10441d01648259030740740c42203008403000d1449900003040705c05101181c0350b100e005000b110001007030101da121010015160411308084000a490501e00d41070f5903001d92651035404002c1001d40b0407110403000c180c40d500d407540b010907400704d55002d81181c7e030784918034848070104107034040340203503d0300340241e0142c44c01000440545603c03002441c510340321901e403c070000308140450501507034204201c00c0c0b10b040822401c40214402d002d1f01c442c8a00c0e059805040c855180d03c80c0c1d000b0340c071500113600c1c10380303220049405650b0002c02c00b1040401001280740180b0f1507240b03618400c1c2e80041400240420b00340740718400890650a503000341c0d1000400c032140701d00b0741035058000074011000d100103800780500d001404903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 638246996 1250 638245746 638245753
    0x21012108091c030206010501110c041503050d020717010501150309061d0c12070e0c0a030608060f22030e01030903030b03061e0108030903070501030207020418060614090907030b0702 80
    0x1422800c80c0641010081d1400b6004608143d014000c050060500342811004000d00c5910305446084050b0450320a9a40e0003106481c000d00d405100051354101e8200e0b03000280c4c0e9070019507103004d1402414001070302020040042001406014141c1d512021094114020b20f0030030b4010300a201000c03151951610580180d00403d03000e0f208800d0415030041c01300c44110700501408003084080040c0903048100140260880315040301c0e0403402a1103020b6440d80e800c10210014138240e042910f060140e20709105c000051101035a026030b019501c0c5140307903011640c2e02029907a41703000c000c0c0401c10355214600258001d510400d202c901904012450003007010000e410100215102c00d441ea1803c007090702c054440400940c090300d0400006d61410140900282d0389007031074070a2170f04041d0005070100440d01c0d26000551904c0c81d611440c0219001441c2c0807024140c00d0140802c00361190003052010f1030710300c0c059405014240003400405003503443e00750001750001c0040c0103500c0f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 638248246 1250 638246996 638247007
    0x70509190c0206160801050f09041a0c030106090605030702060c1c0905030705010b0d0302060a05041718030c1e040e070335030c0a0e010219060221012108 68
    0x10001e004140c41d07800c06030b014004070b15191100440424040c49484104002000144040d865a403540d01500c07100703c03071150186c2c1c1c0b945000b41804030380f82c504091904103c000e002047c0340c1034020b103060740c0d440d44030020700c07503141c80c0c0888041c041200c820005a010002003480d0800440007891b5282c00c8003c00081e002125128a041c3d810f00e00702201c055000080c5071061140a208501d03400c00215156130003600e01d514020f43c3c1e034802a081c4a0b801e503541c004502001840818a90305400504000c3e88440150a5051a41d0303806050300303001c2d00454107616414a0b00724204a2114454880300c0c40c2d544003503007400001c2444143c64030740c901c2800710100c0803a9030703031034600c45180c0e028200d0380041c0494951a2501226040300301d82420091003480004403000c016140709180d940342c01c0c41554403800040b0315006840c0001004054507003484c100f484115002413104d4580c480840d0780d00a5040340b0401c910038240b00300803894603495542821013000503100f006a0780582d03030050a14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 638249496 1250 638248246 638248291
    0x30c030b0a0e0a0e0307020d0602030702150c030402041413060902060702061c290108100317040305010b0603010521070b040e010503010c0e03060109110f0408010c021e070509 77
    0x11880b500300d007444580120822000001501840d16040c08000c040d40c03c00b005940860482d04101c0360050403190080001070740750303108004a50501d02d91144d807150360704000c1d040654550041c2e4099003c3c034200f6072075081300c55090b00c100d4018800000707030303603400d000580742c1e10018030801c0700403030340540c04000e400c0150380c400300600304908800007004002200090303440d08540680d444164a0601d4013116400044005c80701103413040c0c203080078102c0b0b07920415603901204583c0c1008000079140100c65035041141ca01502c141c0388540d00800070361003818100031040c0424851942d204030105404040c02c040c6101e1151159501000c40320210f4481c059109940c01c00e4004c103103440c28600041147e440c013409441080c528608003402c0c070a1954000c00d448020500641ca907640d00c40c1c005071440135240c0100c0e0009510f440d025901da0b030312105e10902920040c000400144140308240004105a041081890708408010701542d031610042c0f0851020041c00000e50389090701452448 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 638250746 1250 638249496 638249509
    0x60a09091419060b03070318170a020705030a02240c0109030c030923040213050301020d06060e1f030b0d021009030209130c050d020607050d03090209071d01030c030b 73
    0x1c491059010341c18914040610242c4101100881255103040c8401006889000c41c11a5000311251a010900040880180c0d0b40d0b094403032401401c110300c00b043c00c0c0d14400160701900a014595090b00c55440ea14000c2550358145600e001c0d44c0000d5903503400c0c2001d2200d240d191000c030700400d0f006080141a000fa582141c04100c01030700030076010b003107007010180d000101ca0090031340c00c40220701c100030403102d02400810207000140200e070300080000348100303d050114020310307000b0029556890940c0b810000740141e0b2244030003060201800d80035a24150f24500c622503600790740050404482c44007200904154501309070091b5207a40a4800f58a4003120101105180e4544440452851040c4080014001d0584214590f13410400c000520324841c0c00007104c3c4216610513480031311b8000141d452040c10b074018558442c2c1d140f00320909426401510a450084815030910369840c5025a0400d24120382d4001c07410700ca4104520710340c007039480701504030f1803031400103058003850303010a80c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 638251996 1250 638250746 638250761
    0x30d051e07050415031b0c05280501110304020d0609020f1f020f06070f08040c1d090f01051026030c010e070512030406050f0c07030b09060604050402030606060a0909 73
    0x24a00240c1131004c00070140d4882200f0003245400c0140000081ca403283c02c5090040d284200904201d0364010b006041103110300180c04c0040c2d20741d0608208100102015520000b19400e500f06911040711502c4542a24070071500504001041c0c0e8440d40c404008201c02c2408376808030400034288105d8440c44204800d07050b20030b904007400d0030081400783c5001c256240503049a032243c2d082160442e4004a04481030011741400e207a59251032805401b03101c4140c00180400303c410a80700b50440b494a4082d004507413043c15134040b48101034400b400e0306ea0446440344501b89038001044807840d40c048042c0461140000c0d40b000c00360412695046902c00450f56409a4550450140c021803d0200c88020b03d030131070354071810b4410014510307160f0203540b141d0b2081c041e01041c0c3c020800e00c0307401143d030f12483c4481550b55140c2c403460005031005090b562a61148030700e0000981d141080d124460040350010010440c540d900e0303081080c1d652114505600b000815070b0000b5102040d03004010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 638253246 1250 638251996 638252011
    0xc0f030f0702030105090c01050a03020d1d070302090f01120b0703020d0903120b030601050a06030c0c0c0e1b160206030c13080105041221020d06050915010917030d051e 74
    0x707684a0080c0101070a440c00608050845d40180300850220b030b03000b000f22882103200707040144c2c69100f01c900741c8000305200225800d10002100c9040d5840002196041c00e9a108607591a55a141c442144084001c00d0085a4101c0100c071355000101c8d6411020319800003142c900075250218a40c00d1006581d181c090440128840c1d804003241c42e040f901548000768015001451310b513240400040c2c0d0744d2145d1150405041c1c0d10f02d050780000b441011409110350b000003003180080e03030711400142075041c11262050030403030095208400d0780b60707102142c201d40107140502801d00c0d5540c003004520b92000d0300e201340680d010498011801c042d81d840c0c000a01e91007000181da031605081c4500d40e4408031295404215040c0210303034402c04543c211019010012900507104d2951058882c0100845d401c01a4065049130400154900c2d0041240340d80380c081c2e80b054056580d901e4a010004a181003070081d41d08188031041900074540c2c000d03030340303c4070302c1c0c00404082296281c1c508041d0429215003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 638254496 1250 638253246 638253277
    0x480305031803010605030d020c12011d1f020f1c150b04081c090306050910090615050a23040207060213060305060604060f080a14100503070e04020906060c0f03 70
    0x700545020b1285400906096018008104c0820002501c1d0f11112000718401c201c024000300c0202e100b54000d40d601e0b0850800078041c000c0720076205603500c0c0e03000300c0e031002184800d00e0106075290500980d64280d4510b0344103400e007141e031018850310019070172030150706035925519825890b01138540d0100502280e041c4a40e194188100103040000803283e034989984840c0c4d041c131109601c0b00340d0104581c0c00040c0012140c4035080414100b140c0d401e120500603041c815030f101844415440000c44901200700c048c000c81e40c600078070180007400e04c184581c5990010400404540002c4076241910300200010b01e0603007a0364a810880e00000c04030400280310a0062220540502c9810b42201c001c840840c14946008001070880c103903200701208121503240031482d00e54035130b004903c680508a00120191070440b10100200c0311900c5040d00c00e01c00c40307000140d03004c1f490307140c0d40c0143d0300030384890050344d11081800425072082514980da031245408000030800c0030310103404c0e603459520300d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 638255746 1250 638254496 638254537
    0x5040806060a0f170a060903030203150f010906050d06030606240c05030706020906070f11180f130219030302030a030b03010e07050906010507020909030748030503 72
    0x2094503002000700310310702030780624006000300d101d902d21481c11100300c00da201280390b0101d400c503400c0c2207070381d0700080407282020000c500300358051b0082d511800349688148240e01c00d94080050030907410040f9030115403010010b1050034450781c010f1540711001000818080e5070380d51290221076607a4406145000b0381c01440d60181601c42040c80d446100b850007080443c0e890701c50f15140d101e07203800100f0315540014002405e445002c11341c0c241d15003082c20001c1ca260141484085110940c42d1a44141c1d0740e03c610719040410740030510700407207440202e038506540342c929004041b37800d440c059900105400d284144042452402c4020354880d60242d601d13031a10500c05410b9462020700c00d44a641000c48100b601680080c1b48411a0340407180d0300d1198845000686661088250281d0071024440401842c0718002000303003480e81c0f103000480103800407054a07100c030342ca40f110b003095084c00b00901e80301100824050712550003000ea2800004503525a81d19242d90310003400100319030402c481 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 638256996 1250 638255746 638255759
    0x30f030306050904031b020f1801090e0f07031b051f140901120906021303050a051b0a031b0f0909031716350a05130b0406020d0f06060504 61
    0x20703203000308019035003004a0304103640c000c2c24514040a50500b802c141c005c1400540d42c0703100051290f00409425420305603141140c25402e17020900030341c0e1145041031091140b0b003500090000b001ca100b40081c0040310300b0755840d50003148080d030000c079000307015007000726081e5100d0001c0c0684421140101c0c0840d50100d0001d0000303c02c070603103400310841c11b0081d00c0ea05e98200320a4003607880b00c1c2c1d174001442226442d110f4001d004d03138042881d00d440884c10210800100180030540c0e02e0251080340e600741200b1072501c2200e10000b4030f01e50801804d030300c2003001403082000f001080d4900c034100e080450b10303519036100f0010240e0140e4045a1284c0702601415081108588440c204054182062904804983d0981c0c1c1c0400c142c010080c4460350320b43c10048001083c1d034038044400281020714000000c1c034100100985401c245685010301155908042c40c0d2071400310742e804581e080d01565561903240007908040c040c044c00329200c204980301101c16104500141c01140c40791910b0390305002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 638258246 1250 638256996 638257001
    0x2190b09041107062a050703171f080a02090f09120318060411010e031506011d0603090102120a1b0804030507141c031e0b12100204090e210901020a020604030f0303 72
    0x1001c45c05010041110b100865030012500340207030080102d0310f54a44031080101e0000c0980c0d80b014054500784040815225004288104000c1c02200c00c4c40b8140c403800341000c0d8280702900c1c0040340350b01c84034400c54143ea0603c055684601c0c001070b101000e04030041c00340c4c1081e4089604580d105031000b101051580c001120900401090300206030007984408425007442015240d2030504c0501c500401c0114a40300c01803442c528050304c2c80c0d40ba07003400c107221382c042e42200d4000b14489a040300011031b046018411440d0307200514a49400700f0b10301c140280c4007858040c0080c2d04000c4c082042c60003140c80d00f51100c80d9190303100020031101c0856400c880781001c40c446142c08041c03c0048012032007010b842c1784c0303d403a000301100003000c405030000a5022000981140f1342800344500355a81c001e00395029204560311480d081c0400d0070982241602c1ba41e01d01d0840c4c60441901d142c4500119006014058014042c0100c80c1070442980019501d0f07045607104a8440e0204c10240c400c02d80e050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 638259496 1250 638258246 638258321
    0xf0c080319030504030e04050c0d060e0105031e0a0b060109081509190c1401180806040210030b010c1b050303070510060807030c0b03041e080702190b0904110706 71
    0xd02d010055400e00b6a030040a100450105501c241d803030f0310203d0f80320070040c012a101d034205460308020040e074074103511100700024403c2e20b110f4015125030310703940a807079650000c44581d80e00c064014884269550728220b10040c21940c1000320491300414072410402203212002110111a038180c548880c00a2902c03a07032649201100c03000c644c1c140c00080c001100d400c151400790400c080003990f030f100101c40ca01481004541d403006400000200c541740419402d0044e8000e035103450702044502c00a4040e2030099140740d00145060000901152100392080c83c1c031103000c1042e00c2841c2e41c80000910f15006040280c60507002a920102e100a0700d2107098020651400904105491a01d0342e204448051080e000829400030025040010050300e820030140102040e594501981c20005090f0700900c0b4200e020702c0c044000502401ea0902903034007100e1249207010310b040c05e410144000782c00e1404030401e00030b0041c840303100056600d0168a0000200d0000003803000c507140070070304180c80720 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 638260746 1250 638259496 638259547
    0x10501050c0307080f09060703080f09061b09030a2405130f030507030e0415080d0e150a030b0904060b03100507080403080603340f0b0909040f0c0803 66
    0x100000301e412074010050300c5085070000d080c15211080c1c00510541840343d040780a5001100245050030036401160850082c0d03a14200c000300c0c1d603581c8440c82e60742c1c02c0070b58040c1034104080e00f44400f000070340f00087c2407408000d410748400304155903500200d40d0140c1d94000e80c1c1c2c1d146440c12000c0c200300303208803544010341d82c03003081c824015501c030b035150b00b51080e00140030010000b40201c00c4c98012001c6050b1010007400070401800d4010001500115074040c0340c02c00d02503407a01d460542d1140d1816181914014401940c401100c039160200f940480c844000385515012004072564070a03041074800c900598011941c2c0743d002e010942070000c40ca0004e94140c0c60034061120f555401496140d200b0b074141021002034440b0800a4a003105003403a0303400b01400030000d100d81c6207002e40c2258800060101600300180c8600755480040300500600b09851418400c0e4205c40c41e0440b4011703002030140408030312050240d00e80e294603012580054074280d0000411881d406411000c01a0040d070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 638261996 1250 638260746 638260757
    0x103060b030d03090206040b0708040803070302010b0103110c150a091a0a0c091220060d0c08100b0910030624080f010e0a050423011a0102210f070f1109010501 70
    0x2a40e00007406c601071402400d02c9040081040010010041c0460703000c0e110701d030200c82d2526218070300240601010b42c0e84a000030308150042031b00340c103036000381c23801a00400054405400d0b041a0110704642c024005860b85880307504040c003040005441000c4415506183c48940c40c003030b01010180d070200300940003048900c0b6030403c100c4140f0f08040d440725610030301c0080d134103061800c62481d4115124420b9841240000ca40b10080721a41c0f24625000c49511046583c1c0c3d110a500f2115040c148a0300d0504142044141c02514158501c1400c0581c04e0500150258a940030090721801c20041032101314000380f00c6c2c01c41ca0f40c0001c10164003500c8902c07680e80c00e40c1849010070700541c01806043e08244c0f500041004c00c0f900c4103100e4189820130302c401302d0710517008420340e0103001c10f40f8180d00d00207074102c2404115440030403002c0401030680c5c40703000401e4036421008101d5005c000d40002102d0140b10302e00c00540d14010a440c0c042c080d00c0c0c801907021203c010400c0b0400c1c180c0c0f2140c14841d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 638263246 1250 638261996 638262011
    0x91305091203040b131a010620060105010c0f0206040e0403091a18040f0603080a051308190b09240916060906050a030b04060b030f1b190c02090103060b030d03 70
    0x1078809150301d43c07180401ca9a01042100b91829004110170310305d0410588081b02c00200d8101e501280d01400030421075880d2009e010786044080d21010f00b8001c035030010f40d0f03110715040410000e81001910b148040c10282c0383c81d039607800040c1d514000392021000690744a4040054030302d800107030050810024800f52402c0b8506030360a618200800005000f1604c54022540400340707940020015130b00084a0780c0d0342c0c0130811004025500c0010b49141a2141e0900868074510009040e0418000301503800d40c0310711a9111001d81d420021b10390981c074414802da404100c1301c44465038481050000ba842141c0c10110402410301b6203811000d401d00b000c10030304001075a80189031208403a030b181043c9a0380d22500c64128081c0c41100078150700701d401c000e00060300090410045124040c0e0182e07249607615050b1009543e200d03c800c40840c0b4070030034444c18030124464507100007003982d2070500507240016a40410b40e0810242d20070b640305d640c0d40035501450700b0180071440000e040ca01c0d080040e003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 638264496 1250 638263246 638263253
    0x10909111902010e251203170705130611030a0503090f030c0c040b04150905181b0a0e1005060d14040302100e1f02030c0f0c030c0111070210030e0309130509120304 72
    0x401e03201c4c8151b4280c9400014040c1401066440f071488405a0389407540d250482001e086a030000c041d103c090701080340001a02c07849101602c0e1402c3c3e130312000d1440d2a1030940b00329544e07000a05a000b0500400d0395074070f00b0103c100014400c0302c0b098000303450682c81c800301300000c50301e40640c076501880c14521964600010000c0400940300c4a07180010075807103158001c003c2d2a40581c01d001781d0322640c0311403600c040a80315000f0a140302280c140c0036507a00c3e813040340b0b5002c005840d40c030181e84c0311043c01e10071490400054400e00c0080f60000440054184161001c2d0704103480c15400360300804d410090300203280c010f01f45110710140042264080b00240d00e400303d10702200b8210a1540403001c103100e000000121855410300b9108503488810042e6850340700d40c400030300110507601e00b4400c42d03400070022099a109a400a008034448040904203070003500c0c030852082141e0004015070001542ca4410f640760b01d040040700020a0302e0071001c064504902000d02e000550018810030000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 638265746 1250 638264496 638264563
    0x50108010f0e0f09010b040608031b0118120512040602030405010606030506060a1d060a02160e131202100f02070308180a0f050f03030106171005010909111902010e 72
    0xf0a40c941c590001c1d0383c1e001c0303c0c2d03006200900c1c1c490760145c100040015070641c00000340c40326603150500b43c01a0446001007030700302d690b00041c410300294140390481c0400d05800e055107201e145818214031b0106802c04003030410100319801c03540d2550203c24041407000911403800a80024181008503081c100002110350241098004c02c005641c0c0e82035040c201024070fa80350518028210a40315100181c003c1d40380d0844500d00100070381c145000250640386403820f01d02a6140116089001c682600c554503140311800b032500a5108410703601810410700d220b400044019070400503101c403c5880c006103410005440c0404038200b086081824400c04180149165070080c005541c02ca02460041d04000c03020303464495600000c400010044c3d00548082006440416595442e80d220300c1c0840102e01640030301030024042c00c2060003294580e601c11141e0000c0c400856080422048100310482001c4484000603511000343d034140c0341c000c10003182040068011215a64203e103e080700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 638266996 1250 638265746 638265751
    0x103051606140c0c0d0501140703090336030c05130605090f04020a0308070f030e18010e06010302040801060306021210030f0b06060d0c03061404060803092e09050108010f0e 76
    0xc03038020000310811a80001c01900c0c44d0790b5005081c44076160550b0404c0d074024402000c0942c01041c044000809e0581f1910490007507039455110f4400c004481215110721944a192044403c40a81003c000f0301b903140000303070015807064005062480c240020300801c003a403541180107041c18020140840d641d105142c40d408001d405c00092507690341c1c00007952600640c1e2000e0124140011a14144140001082d01c401d0082d00c401400b4140003051000354100344918104501d4413130010301103080421092504410149400340c201a02c031440d583c2112650b510485840ba40080c0078844888240c0d00c02c2c0d44803020040038200689503031103807608503c42210040442c1060000102e0a03030303426007a50111725901c0400c01650120310005401028107000f102441d5812202406480c94640504002d0300e44d00c001850034055000c091191045041084071050b8142c015003041c20b0004e020380f000f40c5080381e51085800380c501070000d406000180c216410b12100c0c1034080c418080f08010503074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 638268246 1250 638266996 638267027
    0x5060703330816050d02040905071e0807060924031d0a0b0a0203241518031002090102032203020301140708060d020d1104140c07030e0a080618100c0302030103051606 73
    0x40c0b0a05902d401410408d032b54100300c0801c00c004880340e00603140c0501001c01e4540c0d0500701d8112a032100801e840404161061140d00c40b00e03a0240c01e1103285407550300500c421503090100d1082c001c809614014084d020200140307034020081e0b80180320300b20180c075401000041045180d81010815003072901c0015200507000c0141c01514804c40c1c6a8100c0600b010440801c41b40c3c4510340c040101d0210030850001610030300c640c600b16010400a4800c8a04081050f002545030140407a00c02e00841d08120b51840410b031482c20010150301d00f1700666070441164030071a4014506500094444400506814095204e01c3c0210b00103031a09814490038a801c40e0701041c80480e00d8000a0103407a000741d0390401d201e4404c0600c0010a100000303000c16910079187e010801c5095004c1c05061750580c401c00b4019400f1070042028540d02c03406945210301c002043d624030100c00010441991400a091000203030b000004005005080c0601013074407046002000746c0524012004100900b104c0504 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 638269496 1250 638268246 638268251
    0x509070f1805030a060c03150b04050d050f0114070206090a0506041722090c033e0a090f0b0a120c050702120d03150305060703330816050d0204 63
    0x5080207101e2080c0000144001000c80305114150301e00400500210303004080401c1c20800380c0002a43c3c070410705030070313a88a0448541001d00c1e11003006040b81d4151025103060007032a40314a8902400e00034410344150202da0130340b4509004000130710b007480042031030a09070003903014100021070114000d40c00039007100c0845018004000600528454030002d469810707400b03401440c80110350b00542e0211403080404010310b0710340000035000e5030f9020310f50001100c2c495401c905184ca21050030075000d01d46030701d8808031000410301070078207a01050001006c10030b0048100440d000d030041143c060700c940c0c0c10312400c110700d482c405011004907001d004880b548808c81ca80c07085110b2001c0d520800d40040164600010340080292502260301c60480017900700040c04a2a50026148204807a4004018820b80d034418030301310010601c80c2520b84075900b4441e41591480c0e50701140502080b00c140301900300500e0a40c05a2400400b5010b00318861401501080540d4508441001164041d14003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 638270746 1250 638269496 638269517
    0x250224150303030a05091903091a0418060e01050d151a040f0f18080304060213030f03050324150306060d15060e030a0b18011401140a0509070f 63
    0x9100c0400300d91555014880442049130074421608030501400c1d6140955121280640101c1c40c0c80120074005404501115005c00441c210310b094003581244580189040c95114140c10200343c490150000d0f10039240c15043c00b5000d014100780f401844226101c0740c4601284c2e03100d08004900101d0320f40309aa8400c142d90080380c1170300c10310b2405400200100301150592a0042c010720060080c0c400803443c02c46103203d034500c407011400b506900710655078295607039a51008042e6100c038401c036a0090b9540740002c00541e111084210284c8252203e41e01c03440c2c407074544d1004141c0d42c10400c04603010744051f0b202a0f00c0c1d03403000802000000c00c1041d030360703901d000109000303104c1d513810100414076220002c0c45103a0802400c40584d07200e0390350001e9200d00c50041507030341e10880c1c502900d000300c03110100d126140301520003101382e80c4403000456042c40c40da100406066091b0b001d07102c005009080e15800349441c1022034003400003180c242207607040551000340501c581c50103d00a2181c0f04a2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 638271996 1250 638270746 638270761
    0x80706032d021e0a02070602010614010503011a0706021206130614060d0e0709140703050712020304020111060109053108070f05010c09030308150f0f01090509250224 73
    0xc20190100c840f6000b1992440802d200a40d2403d4610404005510300140821040310440b50100b401c4416980d0f207066909000d0f0020f41d00a08400703801040e0410000c1100048090015000560705a14200082e1803c9014406002607405280722514903110f4140081014040b403d550395200b642c0e9592a1000000400d0007450048203061f45403240d001c00081c4101e180d04204010611085d40b400c65448135142030301540c101741c40705d00120f08982840d0b02200c045038080d40d44075005240001500340040c40d454100002a005141c180c0d485000700040d0105018905100724100c1d035250a601c0c6005503201ba0110348000c004016000c00a0a01d061040414242038480c2e00200200162081c5610140c00c1211078401140818910400256100078950550b0905000500f00c040c5603101d200412101004654181c1d050010003a0041190380b078400d0090b00c504000ca8181c08100042e0642850204507941440c007190f00c0803002442454040301010040024103055000ca84c65092 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 638273246 1250 638271996 638272027
    0x108090a1704050405010e0103022e0e0a15020c030106060f050702060a110f0102090f0f011d01140a0c1109072c0409151406011710050307080706032d02 67
    0x83c8a5640b060030f00b400800c0403602c0c440e5240c102c070310031991100e001650b01001070005020440344004c40124020b14920380d40505c1001230b444500800c5420707400d840c3e80503150804502100003005a00900c2d445106003001d00c5030740003900e440d0402c40502043d40c04028410700c00d85000900890340132901c0c04400e4050070090b94401c81c0e41c0182d032000301c0c4110340c590007504902c0c0c2443c851281c007920420344ac100803040c00592001039641e202e0340c628882d84541d005407650366a07410031400702c000072030640c001005800c1205031641d40b0480b154250404800f150480b9020b140705103811030600042c25006848140400b503080021500b4006103511031000d41d403001e012940142c200103d41d01007180c000c8105c252042c80403010031004002c4402c1540d00c210031a1041c2c00711300742c0c04244244c0600a0011940482d80540062340d064890780801e060000d69404014284c1c0500424010380e41c26000c0d05100e0980307032500c650030f400406144910e04080792101d000c41a40000c0b07004044441c070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 638274496 1250 638273246 638273249
    0x201005090a0801020c100501050f130c1707110705030105010b0910021c0504031511030a020f04050418021005030601050702040b270a060611250e070201060f050108090a1704 76
    0x2d000031512101840e80041e2203c917601820350000b841c1074004151442c01c003207051158400500100c0c8040900c00c28200200450b140990030f0001d4500c040c100300e000c42c04000c4c40b494466030392443c040344564000340740000f590821403081e4140303001840b44001d20010b035481103a040310b000c140404043d0b401c1e4242044210708030114203290b210602c80b070707400c000100b046904c180640035007048140710140844412003603c0135030b0360341040411180c94654000d020007540000e4004e203440d6888000800715803103075007507003001d500b800e45c6003082d49401d1100511074482400d215265180010009201d8811413000a10035552540b46420648458401088619407100400322001c0c0040c20088070324130864240381c12500b0001e011401764400c42454495890400041052882400300c0140c04940d0362001000d015804000086040407006114007602c00c0da00009101403c100c0c00c1e00205403180c02950500400109100c0080d0380041d01c605200d030000500002c80b03c0482041c100b42c4100e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 638275746 1250 638274496 638274509
    0x33a11010905030a090b0a090902091234150804080f12010f060215040b13080703030c170c0d110f0d1e11070b10050913201005090a 58
    0x3440340790810004004000c1921040907141c00c608a035483d402c1a815100d503400b400001a80b0141c100001c0320f0540151003180c4004080440e260301c002541c500d49040701d0b03d012038030740d0502c0c030b20003101c1d4140c501d400c010702102c03025440d81030a00790710741c01c400d0004440508020403440002c041c00f00b0b11050b112000d06c41001d96690301220000f40540380004c0c0900100f20710340480024003d80009031001c100203015044210f0703030b5240e07161b00824039401000e00211004001c2c1102c0091071050040c2040c2d4070a0310001344aa0902034000c00c10000d030040c103411607050000b0720035090418000d880842d40803400c08104e00048554808490041300e0035100641004201400341c0342071a006130a000f55440400c916607030b0f000d8410380a9510300200c3c4031000c0750070411200070400208150764448800f0040b00b00e100e607100045280c2c19011107c8044070808028510100441c1c0285c04504800090b05540000000000201e200281d150001c05100000412032000d48031404280c3c020310a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 638276996 1250 638275746 638275751
    0x30b15031c0c0201020606090717040614040c0e010b07032c1009050102010e01110406110f03040b07060b0f09130c0e0408031602030307020709090f0b15033a1101 71
    0x780403805400504851400c070b02500545000407924104141c50511070007296841c17103152b940996944e0b817141da0207401507402a440d07040a010142c0c1c4000340ca405544a499491607080ca40f10314280524010380003000c0b22042000000c3c00b0a43c0600001c41c0d4510301c0703e000540c0d01042005c0692040200322043e00a07020070300c1c0718105504184c00c141158030030713002846030384000e000040c02c0f24600000805000824801405600e220341089450304100c84112103d00a1003480b19186400550100010031000940042009100d0065100c00f200503213a1448148030600011200c1c1030040ca042d20a081d4064a50140045500000010450064141c015051a003030068403944111800600c1d4500c14240138a0244004100c9220310072540c06030203407900702443d000c081c00c80c2800c155114907020b11064081500000e00381e015220b1001c1540c1d4042e0407009140c20080281c80c0190380100303041000f290300300391841e80f1a801c644190f0014441840501c10b5800f01ca61500c00300b000d61 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 638278246 1250 638276996 638277043
    0x80d0311030105060a030b0d060f0e03090d14030408010e0102041d090703150207080c0c0a050a0e0a0903031d010b04180b0c21070203090f120a1b180515010306030b1503 74
    0x555000d8ada58071400002441344108100d15540d4a00c990161303241c0100e440e6080c1e00100b0101c1e0100d204101800d403e42c2c0c036043e91482220300f550034206041740c40c3c0c1d500003410001f0b0002c51241c00c06441c0b444a5007191480e1200986444141d02d21000c0c0a101203001c01901031004c540c11180455406400e40c0d40780e4032402e07151540e03400d519800b94005d0140340404511840d016407801c084400a10b017009040c1d48410300d4030301800154a0032000c0c180c440201d002c0340400404031044200103000006a2000c580b0100001d4034040c0e03081d40a2034040081140105541544141c0d001924080d0b142e50b07482400d4070b41d00300068482c42d020702d442c03601c0c05101d001c59011000340040b01007190780701410f0041d90100800307001c500108841301d038080c01d2140f0002d22008e00108007610b00000004200e40da60700401c005501c01d489560003655154100700004d4109502c12003190002e02e405c10090703003075541780080744201514040700c4603200400b810170b907907040203050710518100e002e103035102 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 638279496 1250 638278246 638278253
    0x80d0518031c05060409020d170403200a0609211403040e01170d080402040c090509270105040f03180302150a031b02031803030f04030c080d0311030105060a030b0d 72
    0x201c2c40001040314540c1040041286880c050040c0c0100d181c00400001c803001040e07a5982c00c1e40c02c840c1c2c014000c0351040c80000003003070202c00c80c480243d11004030026100c2a403810001482015000a818001884400c0c0140d16100b000d01c085101c0c020900902010a414004400350303081d07c601c4918480050701141111041d10224125001d03080111204080002000d032960b84143c00c0c0800904454009000351400780c00c0790b191080d003400c0468030756850740049005034800311010528103038074083c580e600006082038981c414607000020011800c1586da07402061005010203403c000c4030b060304090700d0041e01c0c2408001e5074000c1c061041708100010900c000e0304401d0030b041c0400d10304502840000c0300c00340620b07000c0d540396001d5403031b05694044c8913001b0203654040a4242c4000c0c8041c00c0c03014010030090001e10700403040c3d114021301c0d20142724901a407203401c3c2001c250030a0090240c1803402400e070b03030540f482250002d458040ca0f41c0124010000d6506441e4880f940c05441401d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 638280746 1250 638279496 638279527
    0x5130521120a2405060703030b040906060323010b030304030201050c0f01090c0f050105090d1401021b0f1c0512190c0f030f090203030405100302130f0602100603080d051803 76
    0x41a403008521001612110f81140d8042d0b188621600020100308040000c4c0c031941c00680744840003080007032465416201c6004a41164004031031210310240302001c2c5000d0402c80d1209101e19500030300000b01071902094803400703180b10080c1480408501001c0003e0140000f1010049540081149030410308100c0d414400c103215081071410758507004503155126a00b11610300301d000d0040f809251065444c3c071f4808020800d8611595402e20200b4120364000003200c07030b1600c40a000380442c0502d02007150030680c0090303041c460a206a2040b4030741d01d4200041c0c88515044500c443d8a5607207001722103071503b0380401202201c91420010318900d54000203c501301d41f07495076080010103d26481d103000c0b2003000002a50550040c04100f04520f8585130000e843c0c10140380c050f00700446131201c04d070b807030703501c0d030042580c5d451606000d00100d40d0400c82842d20a04086042c0030952854481400764801c00c1c0c84421003070788030302c00603040908a001d80d020080b0701e10212592044904041d81c0d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 638281996 1250 638280746 638280761
    0xf031504170306010203030712020f0a120f0605130b18070c03030b010206100509090109081209010e030322020d1415180c09070c1704080105130521120a 67
    0x3003001c4080506001c4005501c10380c0e20450068004504c0c503111150184c508030080b03c1c6c0f50308016000c0115100d40c0d500e10b009000300f90b515441d420380c04407400d0fa004094840101c4402d020750310346034080010303a0701c0308455050580c0301ca03800180d043c0f8a001050000941d2080c0c4000030b5401030074404110360104001c004580a6501080024004001242c9544017913508245440c00070b41d0600c07152500c0f1198036000000000009400110b83c0c0e0307220244d82080810b9044400030300c0401643c240c00b802001e10029181e0091407135842c040704580e01c28403c0121510030700751800419000c5440301140302007134030340140500041a92844542e9035821100c05034001d00381080000c02e00380801c2803902d400d02c5482e00090310301c01c0141e034288a0703a0680100003804100c412402030300854480d043d01904004e1098a040c1d80307078140010030b402d5920140819001e030072940b16540c04100049207601a2034142011000004003119062000740a081e103c2c562650800040c45141c07801507101c2031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 638283246 1250 638281996 638282003
    0x903231222151d030105011403120301031709060904151415030406020901050d020d060e011e1401020a020913050c01090b0306040f0e061e01050f1309020f031504 71
    0x600ca031104000070007003601c01e10400d01010481c182c1c5200c128014100ea4800000d0502440003200e401c80020b400e4410a078843c0c4070f4080c5000750740710711b410107120101006100d81c40e007a143d0f501d19a1a40c0d00d00604140100140744041141c045587d600012280078190040c8148644c440400318001000246d208801d204035001c6034000c181c3c2405800111020903106509065558503281d260203541f18186150400c81c003000606000b107600d101034000d4100300d403400034095007080300c06010100d068000d0041300e0040300140c01011107010010040d00c41101000400454080c01030307107005540c0100943c04488507082090340c0400107050b000850003001180c01549007600150740d0035206020300e00d0309040400c00191103003455045210368070310305440002d0158440306035504160313050342c1400b030800c1480283d2161039404e2035824054101240c0010800d01200d0008203850311007500a0351098480040c4000d665802e50407014681c400f0341610751450340320307120b00340030801110100c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 638284496 1250 638283246 638283277
    0x60c1e1709070303021015050604030303150f032003030f0c010219080906041e021809100c051c0e03030c1207020304030b04020d140304060f030f0c09032312 69
    0xa4000d8000041800481c0e1305500904014407040e04c0c101c02600a00100e0300d4102c003030380c50003c1c16031501402000154003036035001411548500040c0c14a50b00e40e4040e0407444107400e01400420041000001031503084161040c00e08069004a4154000c105101c14408800310381c0d903004c15019002482522080808040d06224510060303c00c04815600d07000c0d1540040001800100d85c00511028001100342030b4004041c40d50000724001402213452008020b04018400124800c07c0180500c00140500b885000e00a110040042c011601d90b440d2510080c0012604520180d02074a800301c140000e40795030b86010707204d80c00ac1764001d0200031001c800c03150010706440d01c04070a0318284e80c0d1040b4152001d4403907408220003810104001e46142c4d84914141c0c5500404100500007001c184d158800f21546081001e0103c0d0b84d107074541e4450a00b80000b1a076090b038403451174400d0380e91040d03600c000007412030b0b2220310401d08840d020415201d0240c2010b00102d890000e000368002c40d6282 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 638285746 1250 638284496 638284501
    0xc1c1506090314120403120309050d0c0b070e03030d020d020906070804080607030504050309010f02011d0c010f2a170408010f050105060a080f0a020c0a211b060c1e17 73
    0x1c2d544100c1180702d0301c500c031130901061000503440703611540064024a404500401c482d1145800c2101d003a03044e101140a80c40c0c80030802c888245c5041c3d001110b400d10308161708520300400e03140d10400507421840c5034002003850b1220b0841c0d0503140391001c098100717911a044c1345045651540079001d800071610031680042d0156109000c2e0354440c81d444405941811405401074400800400d003e83c155500d843d48200701d20500c40c915450015104020080090701e600054100415102010704110000717006210401030340e17007a0034000140301000321085800c1d0a00c2100e01012590202400c54006000618404150407800e46000407a0040200740da0700c5040088612440d141440032854140015442c000740d0050f25501104070307003001d032070021a41d40703440c01c01441d040304503075104224602504542d2150f010301c2001109052042e103602d1000d0345005649541c1c4070082ca040e444035000d941c030910408074802c080110001039800c0c12204036010344950004081e004200400000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 638286996 1250 638285746 638285783
    0x160605010b0307050711040f020c0a060605030a05030313110a0305030301050103110a02060402090c04050d060204031e03090b070c09050a09140c0d0f0f0b0c0c150c1c15060903 77
    0x2203c1c040c0e00c2a442e004c0c078205859840050000170601159841070361030f0504403c1031745030b000411207a80d210010b44504240e519003442180c9158101d0380c080e90000c1641000034400008494003c246458050100700080c036254807003103150398040b5000036980c400041000800400307035042e18001d8a0074092003c01c80d80b0280305000c0c042d040c0005074072850204000d41072540701f2940000c104a9450320f0b00d0b44070b034007090f08490180c90850b1810b41c009010024002920540c20720000c1310184410701c19030b1610f00800035202c0b4001c03d076070f007200010654100030071100c102d001071500348003e000600e0081400c200415002e00c081c0c072500024441151881000300d1200b4074694010804c810440309500c8882d81054951400c452048030b01d05014003044c840f0300d60078070609851000302e41c2c8506441001d400c04020000030b042000c05c2209200102002c030b410f944030145d480d10880381d003103004c3c0f45a801820798421800103101c0d084d200400d0300c59120030143d0507a13000d04884004080e000341e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 638288246 1250 638286996 638287019
    0x50607030c03080612162d0b030a090204140603100903020616050c03181e03030f0c030d0e06061503011a07150203070503100e0f04230316060501 64
    0x94004002601248040d00028000e00f0819007215000d000c0c4030076014000030452030403c03000e0600440c00c2c0d06c0e20007002131040c40548014030450030744c0d0504119106c0d038150941c40a16000b0310305070f440040005440c0d00403591029802d0340d00100b0a200c041600182000d295005540160080c0510180d16203c2502d074003072400c01d02e50560040140740d0301c49201d42d4007080b4910742a020014100074a003080c500802c0030700352444120041020181503541040282c030089810410607160b00c12100d801070764003009965000151031015642e44815464403130641c030590400301b0b456803030200f0b003440d2080c0c00113031180b10b520182c07100203951000d5070302c42d40780e40024852a100c034000300e0b000089851800c409044540c1c0728118045035500d00c050104140e8000300c07203200002300084100040030004415500060542400f400340e08e00309a0f400c1c1c500390000800182140304941001060700490f0000400c1d212090016641c03200802d0b441c400c20140c903035505480d018141000402e8050941 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 638289496 1250 638288246 638288257
    0x106030b031005070207050d050102040821070f0f050d0c0227040807050123090c090705072303040602060a0e07080a060c050f04060c0302011a0d08030408090d08070c0506 75
    0x80051880460341c0b031100c0c02070304000f801071045004031000020592a61860f03800381e00c1c80341002680311703420308900e24a0840c84c401c01412580d18004100910b81c90601205d8403d900942c0b0105000c005040144002d40030780c000501c0c5110300034511801a40c0f04912120b000e100b2207800d1000b144000d80749a12080b2000c0034507422404501140c0058550070040044d20308c2003002103500c1800f0240100e807416480c04091075a004001000640b020a000e0008214400c45008900b4141040b00070004c0c040c0c04002003010000c0d00c2d220030320090310742520360390914150840b0707039407074031004003d444400903a295681d10b0300f001c4000c1070400d400302c0d165050390b00b02070003807054a5913611407a02505113070b000d404c207202c01080b00121008583c4000e0001c3c0c54292030b02c0b20010018074000f401c5030081c1e200c3c81c00d01030054940f10100c1c1e4804001740103003900510f01c25102c0d182c90409219030b10a00c08240d920036250b1555108000b100c4000e41a8070340910725000e80182e89605200c170a1040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 638290746 1250 638289496 638289499
    0x14070605090a050108041b080604050f03030c0f0901210b150405030303160c020a0e0f150f0f0103060e010e0412030516050c1609150801020906091012090b0f0106030b 73
    0xc0a02403544690320040e4002d000c0c0c1e24014401c00f50009082d107005c1940c0008e034460300600100014000100150b49034450754000461461604d4400302565009415a001c403030000018204c1a81e0b1007507080a4596003c0b000c8242140c0d0511603180c0100500f251042c041d40c020a075802d0401c02c1c4400741d4040b9032016014510b540d880c4001c03000c103130034010000400e00c5408590b41004d62135042140000c1c20019040b850076040c18141b20540b8070307000300005440301240310341003041e8695001000d49600291541001c1420880058001d0202c5811140d1741c1d00c4864000a0152002e1800038015406041001e2000e116004110706643e000c80d08240e4480600b0100c1c28250b106800038400391030450160749480c1103400840c5640700749070348400c1e9100e49841880c0c101c3e1440c00d042000610542008600d000c1c001d00c0410414020040d00340d209840c90845008543c0c00b41c540781c074541442003001c126050251600ad44100d0095440200d2814000f0002c507041f8000e118202c02c0900 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 638291996 1250 638290746 638290759
    0x31006051309020d1202031c1b0e062106010e01110c06071127010504090201020709020f0c0303010902211306090c050d0302031e04060f03020d15031407060509 70
    0x61520300070740080d00080303070080b1920101d0008030300101e50a072206406580915500c0c081c4140c1d68410000060000e030107240303025100710900d05500e001d0302e001e400314181502b90021a000054140c010600d2207103100b0340c0030b626907002e080034602141c0304100c241c0700d14200112010045840030100798542550341d0080c882c0c00040e18018000d040c031240302d81d04009400306400c0101e1001188483d5803a00d81031074000f038170f4840c45004211400740c41d00383c3d010481041a500000d544400e188207810300c0990010700c040452600004507034081401208495803541d40c7d500c6031000358801c0212050f0b1143c0052a210071440c500213690061a084440c0c0c1601c05058507048000c20049d0700440c1c020320b0703200b80080d00d074a50207520300c13003d0b0094000e1030712025505a031454005411072810025001088240280c54111a403408e500089240060721000310041007402081040e20b000e0002211110000c1040000c610048002c5a15020344000d02e0799150300362100d000d56248981d0180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 638293246 1250 638291996 638292019
    0x603021312051014040c05120d080405030d0e0d14190e03011b0e030606030f03070b09120d1d010903090b0a030213090e0f0606130e0312100503100605 66
    0x54160110034641c40c01581030724042e2503800c002008882581030040c8521030040100002e201610144030002e00702524100c0f910440c0b4a03400d921103044400c0e42d010310420354045000c2c40001c0043d281c0342d401c0008100281c0c9406491190740ba05590503400000d1200100c10034446042404e460146542e01072480300d800301400c040d98102c0c04506056015962101041c2c8400c1c001d00c5c004002941640383c41c01c8007600072050506100000b05441d0190b4400e0307144000d800d01c00011980c42c681c22150020550f140d1200150501d400150302c04a20400824400550411b03a4003824401c4240175880081c0800316401509950750541d000c0c02040f06c031b06080141c01e4000c00208245410780c640146400c211000c5200d01640980008460542d180281d082203001000900c14440140b00105006c0c0342100000b0740c07618a54030040c034080e4a175040c501000000300259410007010026107034130380ca0301c40f00e06911100e6501ca070030b00c207118071409071990a0103407080f83d040d83c00203028a03d041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 638294496 1250 638293246 638293259
    0xc03050607091d06011107091e1b051605010905030a0305090d08042603040c0f0509040b0c0f040b190f0c1a07020a0203030705011a010908030304031d061201030c06030213 75
    0x110000b0441c4d81404141e48048100100911041b00501109000011040346004041032075010750201c1c41d141901e40704201102e440358180307050000d411841c0240e500c00c400460340d25000c414420041c40c942c20860030b030303003001004800303401c06910940c0c04110556880351000d43d03403e4014405800303d0503040114020400c07100004040c00440c41ea03031020548014031a07142d50748121010b60303101c0050300b01881000da55102d0003005110450310a001420241c0300c5d1200c0c0c01c400307000a2154640019011410a482c070180c0b801040950141c075115010f000d2a600c41c000e1b0760030b1090001d501c1c90031550803140070721034464031160851403402485a0609110040460160a030400d510a140303501c001a9030800c010320b0b41501c00d0001165880a402d88111a01ca50b41d40341410b00401442c24810034800105a941c403d0b01840c0074900c020550100038401c500418040b40c10110002e094402c02d000449924100c078440c4480700c0c0c0c1e40f80d84110803422030140010700c2c00751010b06031080004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 638295746 1250 638294496 638294549
    0xa060603112a190b0f1b190e1e0307081b010804050703210e09041a040f08030c120c0f030117030f120105090604110d180f0c0305060709 60
    0xb25422a000c039000f100c01221400000088900708440040f032031000c20000d010000c00490704a03401404a5a1000c042600c90165005038202c0a01c24141c480c054600d080c407030b140c650310058000d0100411148200b50340e100c0719001210082c0684030306100011400000034000d00147c044980c0c402100c010b86004484901c40170340306880e00d1041c01c90200c0400d4012841c07856005003164042e0000402c2040602040303051080603114805010800011130340d402803111544030700420342583c41e5114a0f00128214103400f0151000d80040100103800b00c020004041b10103001d0b89101d42940c4017807000d00306210703c40b41041c0c0030302d091004100342211407030b405280031440030030340341402654601245541c003c40f5540035511010801000b80c4e0030070342d02e060380004040c1c60500441000d083c03030710f405102e00f103c5a03854681d9180f040d644804d0703054001e00792940c0301c920030846460740d0406542d542c1142c001035405000304004503120318045c40411f130449409940c03c0e1000010304007132855 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 638296996 1250 638295746 638295817
    0x3020114070f0209010e071e3e031b01110910020712050c10050c1c110f0604050c0d11010f03020c0604060516090f0e0601020c090a06060311 62
    0xc46003000562800180ea076240d00e98007030400702004131014906100001c2c011140b2152209001315072034401c08c0c0303850b4480f00d00c02400000030070340003201d03244005040f0602c25404814281c20501805100e1801020000f4a00740c8800306c00c0c07009140800c1c5c1e0160880312000d204004104042140f4085400e108403009040109070041c2c50000760354641d610f4203074501c01c0040b80c81d6000b01d0800500d610300481048045a010310344181000b10105110307640d60b03464a00c02004c06100202001e007140310704203036211001d264050300e00300f1404030390482e624402654101c50078000c0d401c801260707042010364015801d4120071401ca1802c0f10f100151420034040d07513407004040d020410420300740700070003400307003d18400c5e00005440d182c8480b14180d4960074509140801010f81002c020100500809806580c070081d018003141d294003006034075109507044010b40204404003084045000b1f940704004a4405807000c0c000b02c0c1c0c107500344448a100d454a0b20350079030450240704000f00010601e214 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 638298246 1250 638296996 638297003
    0x2f0f0d0807021003090204051005060d0504210216080a12080901180f030921110f0d0308070905010309080a0c0c0305030315040b04050610540302011407 67
    0x5291004070b40116051800112240c1d02003600c030742e550340842c2400e00c1070170f07070005003902c1110410342000c0015404d80b1035030380c03903040c03072601c1e0800314080c400c25119034069141019105804a51340742406520351501d2000d2441e009200c0328006440e1401203168030015038401c0d6121590742107041e098890520260500840f50f60711410300c0c078160100100900c075507000e640714240c071003003610f402072072010280c022000500e40080300c8842408401c2e032510300c096011000c11040f81652000c01e06180b0320440c140d82c840f19120314682415002188103000d680789950f08000c0f561124019401d48070310300c00c024a0480100100d088036071080e42c40c03103a410311a00f5100076256032910352503c3e40c3c10903907803141400d200440c00143c40c5000e1050312003005040d10103000e1403030410001a8680c20b0011042d090142d82480400e8808003070340c004010350f0400c015080c603131400221100301350052008941008050080c0b40b1036856940f800308044a50503992040791a89060202449070000700c0100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 638299496 1250 638298246 638298263
    0x70e2119151e0c320702090a021209030a050409020a120615030609091203091a0708191506052203320c15070f2f0f0d 52
    0x40ea0318040c0780c000e9440d880e14065180e0b0002c4100010303042243c041c0d20100003800861209103410310882d04891141c401541c4040282800750300c15442c151050882c001c1d4084655400c100b0164401d901070310380820240f007408815550180303a60b60320301c070360710120012400a000800241e0b00716001070000c3e000f20300e0319408050940310800d0507141d441d00051344d01103003d505684e1041c0d05210b01801050204010701001c051506c55200c801d00503800f03c1c0070191522690801e20010404525402084c4140f40c46580f5240c80010603030300c4180c64840e15004580d049504488a5014a22a82c3c075101d0365002c02074a8400300361881c0c0c0c0b00c3e1040c81e004002100e840200c2c2100b80100000079401400389138a0303c9a4200c40c13001c041450707112424072000d40200034246400018100c000c005082c0d912b0700d105002000200510700036014024900c80b60750a003941000030341411800380e45242c0c0c2500d266281d41c4500400c90045810302580c002c200442405181d00d00402c555280b1401f80c003030b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 638300746 1250 638299496 638299523
    0x140315011116090c03060b04140a030b0115120b0f01031e0903050c0c1203070b06040b0a060302090f0105160f0c0e070f0f05090108040b060a0e070e2119 67
    0x1c9040101c000c0c09001540c444480800181200e03000d00c8000c00b9291030208851350400d100341c000c6d4007075406454000300480030000c0143d11080e610101940e044100b208496a482d50000d040007000c40c07441001641400140191308030500546008942c01010741e08560450b0b00110001c1c80034100f42c0440d50001c07440002040c22511604810f41d019a41d00c3c1d17954103004650f1464106807085c100d00811800303941d0f0362144070200940d00303501d40c1b010002013140c503660001030140180d281803642c8416515030001d030258041d80100000f180a54244400d094080015030f06070080780d0140c0143c05822018200240d001c424205d444c81c03041d41e000c0150740e1640c1254280300001c807841d0300424581c05444400b01d0300048941c103c0b25040ca0414540f1144800007025000d024200500c0c0040a00204041e0b0782d540c090b020140520142e5101c1900c1d0513900117010008601d2214050f40e4009007038140700050465843c040c80e4444000e12190300052a00c801c3c48032080415604903141858 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 638301996 1250 638300746 638300777
    0x70b06091e0c041d07020a150b03011a0301050a0506090126010606090e0a361401290d020603130507060509130c020d12090c0b040906050114031501 65
    0x440350140c42c490b50750030b454038209908007248070140d2451100d264005000c015990380e00080d00820194041d034070b00001c4038510b00d01c002a00c030b07030800c184e0300d075007828080002600580b840d642031780c50031070082c44642c90310350310712080340c905541c0c0c15040321291006014140c05c20f200040e1240e1148a83c94150303080d00402c0d802c45001d42c00500000d4040c91042003080915000b49401039441d003000c00400c00384400e004100c10f050407400e600c41881d030201001201075040300540311a0000c04012030300301e080611700c0c001c190305a2208103000b40d042060004107245441100100409403c103070044d50540c00700300307682c1c000030814044043c80381c0480000030001e0001200802c0952201900ea8486c1010010307603ea104001849041c5030072a0521906c0d40002c1d030305500009402d140305604440a00d410203850840c20281220010035800100e41c44d00c18000c01c125003104408021440d00c840045405440d1100207505c41c0e1814400f16241042014040000f40390504218051345000744 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 638303246 1250 638301996 638302051
    0x8060c070302190b0f01052e0e2106280506010e22060b0703090302041a030a05030c010b06070308070e04020c01020a02070807060c030212030c040909150b220f1503081e070b0609 78
    0x2880b010301c001c0c42b024412001c010421800e9001032102a800903143c500031084d904030a024039200b21490307140c0c008101103901072034a81143d00e80107000f11880c0320400400101161101003c80c80300d91404400160b0f09070320101703581d6800d51580c0e40044082c5550200030281c0702a000b0b012640d400c5186480300f654040004241d5107100d030019645545041e00700608540041c5001c9004440401803140041e611503500c0c0e03441801c0d030914442010203480803c4c024044c080c5414810740c400a000007007190002600803c94043c001120000c03912204112107a500c0c00074000c000d0b82c4001c0c603182c100540e24001d5a802500044818201595180c2003000d68001d100259164008081d114800b8003407405907d41800e82540d9140c446000c07480344141e010041d042d900c00c2d0301d075601d0061080c8000c0350013801d802c1c2d155007030f54030b003854603420130001c554002100e0350103c91240c0c00c0d01000c1c14440c0e00340c590482c0c12220b40c0c45207035a08020311061810040500001c0c0080350840712000d041e40c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 638304496 1250 638303246 638303269
    0xe12070c14041a040203070c0203010204260304081c110102130315291804050c09070801080c061620130608060c070302190b0f01052e0e 60
    0x444025900920300030000e00d04045032400705004038144008a07204901c003140e5004007900980380141e40c0c0d5101142200e0850360a64000d6042d400000c00152030b58400820941000d24a10035144d0020420021a502e1146203e01182a0410412030034202882c0c411002c62a00e141400219802c506030003900f240e001004108510340042d0090052000c0c9034883ea46115441d0400c01940041a04200c072203101c1c500d940c01c00304040880c801e0203483c4c1e03415000040d440e50742e5005490070035140c01c2d03880300e80345481c0c0380c0603646440004007414401e0300c40c207040f03a40a0703004d071042098990038002c555000400c4a901d081031590102c0c00070785c609050b0700c0038000031150f44a502882d08200030f604622409000041820311000f0701c80c0b25004204250407040c55100036540307030709c9468180e0a03c1001102010298190304001007070002e1840c10324480c1c6402c25a012440e85c1f01d9003007000a5188034000003070340030b00038200340d00d44001000400c10240c443c18000c13014040d10002408030000ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 638305746 1250 638304496 638304503
    0x12070b0703031506020f0a0b06131506081f06120204080d0c020f010504080c06070c0b0a0e040c03061d070e04060b090f09070c120c08120612060106120e1207 69
    0x80d800c0f00c240403403c40c07919a02904061000e003e4050941505940e00c1c0d4101720007501d05403000002c2051651032011802400881d01014002140f03242e0560b18900311520690020a011200150490540000140103680000c12214916060007403c441184500d003010820582c01c00c40415a42010000007007620919134400030000d4030352045c400004040c009a0f81480028441841408400f04010650450030348009890301458100301521040e02c0e80714006c2d0b4100014900f040070360060901000c00b0041d0b80070b01012952580807000c075141782c0706e0383d5400500c50521040f1a030030300244c1030b00040d19207060b5690700d4052000070200c1c1c0403a400381c600e04030000f031402c440d402d040c2d18000d480d800c00c950f45e07070345480c05400c040e254242a000041140880041950030742d405180841c148a811480c0981c448110b0003c8030031014007681c646100b0b40c0d00c0c010307207001c0080004140e41a65590b44e14240c24660000e1007402502150f035600b001c41c0150800c0c070301003441e00400b5001c00c034003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 638306996 1250 638305746 638305751
    0x2a0806040312020a05040614090405310314090a0e01060e0301150f060c03030f18021f05160309120b180624031905031804140612070b070303 62
    0x2040d18020306801442d1090118490052002c0b520944e000f0301030f90115201c609007140c400c090b404010342240300b03c140041c2c2c05450302c02448107540c14101006aa6504920302c0003d80102180e0200e14501040009000582800a00058005c66400f510b0f0a50300501001d10680d01c0780c441c44031490098010030b00042079203120b0407581c5001d0151708440c8090200313440020b0b0520641d003003084064059041070001280d0000c0c2054425802001d51607001d050400090140c0c05005420345055202603108003004c4602c150440740402c241e2080404070b032955480c01880600350211041ca00c6070a42c20700211020002e840c01e03200d82c1d01051984240008203407842e020505418480300c03148100220340c0b00c0010020801c5100d60404d000c6d51031004d0041c0b4285814001030326080822200044011703003d0401003c0020001c054240310360000d081010650700071050108450240b1180b002c0e0081e56008211542003515101d0001441c40c13042d95201a19031400d20a540d0180c80c2c1200000e5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 638308246 1250 638306996 638307001
    0x9080c010603260403020f0105131d040303060602010c02100b0a0504090503070b2224020a020708060a09111e03030f0306150301081506060d0c051809090304032a0806 73
    0x707030310051985001c2c620310f4485040074155004900007203600c070002e60510200042c0ba0454220421030f80d001046c045040004d6042d840351040c24800003030701c00701c0219007841d0b800315200e401030161660740486035004052003016141210302610f1510041a00b01145c0d5101150303945590040880e0240a04005c5039610300318030b080e20904400501442e1000c1c0803200c001925410319508800300da400040101a1406000306d00c48000074150750350080c2c034400141584e406230040740000c02c64008070166901075907070355203040640d000000d0060402d01d885d855601c140c0b600c1b07800e140c5160010240030341d1140109e4086861540155640318001801204103e201e00d40007440844141c48800c5060540d490003e01607600d8903100c0e01c04014608500004019440340c0c0b0079649803400442c1c0911400020309005000b0768050f015203002c0b40c0341d0018007000790411040b100d00030035014009600d080d1441d10303020b9111f03d600c01400104c2c041682109804100c8903041e00c082c00d240c6001d8003860 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 638309352 1106 638308246 638308283
    0x1e010804151b170c0c3a1d010f0e0d02010c0b0a060315020301030819020313090608010e0f0c10020a02090405061603060f050409080c010603 62
    0x241d8140c507040501a072248524011a8202c3c000116a072101442000c0303a1154030308249042d44a40e4070201658444c0c07501010038200b544800b0080319898aa202620611217602e06c00a00c402103003031000d40710a070800342044001d0030001e0558849140c05800748083d0138220b44601000408041075901a001840b0925403103101c8603000c2c40c0911903e40104407a000964155101d10000c44030b603211171003108c0c1a86c1e0490300c640c2c14105c1c4404d81442d00e2075480b481c60110b00007400b001182060001d110300140008a10100c2c28a060003d66421100c20640444699000590102c81c40c2400320b200443d0341d40659200050010800b02039280040b400301c000c2d00041c072041044148100840c203d8014040c0c002d13009440c0184043c01c409407001d41c0298030601c24a01030400491410342d101003c0540300300075003401c1c855440300705421100e10398000d8640c030a01c050503c400 = true := by decide +kernel

theorem cover : BRFrame.Cov 638129496 638309352 := by
  have h0 := BRFrame.cov_init 638129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 638129496 ≤ n) (h2 : n < 638309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
