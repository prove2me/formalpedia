-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5411
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:46:57.996982+00:00
-- url     : https://prove2.me/submissions/6898c939-8959-4250-b55c-44d76a244516

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 973021582 ≤ n < 973201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 973022832 1250 973021582 973021613
    0x10c080708040b09031c0906030902040b04090803060f0a0f1502030c0f0c0114032703070c0801141e0601032a020d030f0c0c020f03030f120919021305060111010603 72
    0x74461b9003010b007200000d070314410b461a03020303880e820780c640c0c1003903c104c02400c120001030344c210791039001803580360310707030b44500e001460060040e00d499040079401c02c03828000002c401d61055228400030710118100690380700444001040410340c1241c070010980c19805100b802d0507140c06030385840380c0c110001058441119009a80c2c240102d8030340403482380f0b280425101010308040c40d0000110318482d00d8001c006004c64402228100b903d41d95030b04200102980214805944030110013820940005825801220300280301e000d03104030300c100164480b001008617042603103c0d8129226400c4c5501c10f01d0aa078270078044846100600380c7c002c3d5540c00d805107010300080c074000c4881910401c9206050981c1b18541d1011a81a4140c003000344146a2100c0c9641c107020810202c6034034480d010051882c3e0004c1c09103039440749000040141400e482c0383c0b03906410390040c40b558006a8510a070b042840018140028403903c910700101e50100c02e548a650326980b80c43c03004800d000541c40400c4e1b42c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 973024082 1250 973022832 973022839
    0x50a05070504020711130204080313050406140112020d1d0313090b011d0f09040b04050d0201110a030203130b24060a0912080f072915010c080708040b09 67
    0x40a9541041c48120311400c1300280c0798140b2041600344c0b0b03142c002943c40d92008014030160a00da22100110300f1540412903003841403540f940100a241014020300d001800425201011907500c03000113000134201c2c40c100c4c0c40345540024164039500055000c40d03400c1d01c44200815030100300c0b8121344e40d08d5104010404120522080c002000004d602848114040695600c02e004040d507114080c0d4180c01078099900080440e485030003901c503103500f03a1241c1e01070000e031891418142001410983ca8030705200c21641015001d03100450b1103c1212400090f6290040e600d0f0b4403401d0400d4205051000206051001024014500800c100e020070b00a85074200c40d220141d00d07400c120107031042c40301450200c3e4180d4070400c40442c200003000401400703502c480d4907280ca01040c804e1380790f000c0c1800b12914500d5071b548042c1403119104441c68400c07001d80c554814200403986401c4e910304009850704000448904400b0880484140c50405502c04100c546560315a8400900c517040400300318007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 973025332 1250 973024082 973024093
    0x6030406240311030705150901170901020a1806020705010503060d140c0a0e1009020a0207120515070c0b01140a03063207090306050703020f130302041d070b25050a05 73
    0x3d146030100b01041113940090240301072130702c1e948003000310b0340200194605206d040058108008420300c001d51090f03c08400040c0e80e02170003030001e400429024103d02600301c005505000c05a000078200c4240c4109080194881d03403400c000641301106460020460079510303402d42c3c1c1c50100000c1b00e03202c407a401c41c0c50946042d121505904581c1085514120820305030004000300d03000d55005209440c080d1050710402e40d2a40316500450888090482e11b66201c050b0a40c4040807281025070000f010f440d000c0d032008129120080310304418010305002d0401c51400b03244030b544000411006550011003401008410020000a40113120090b882420444840c40e000d480500c40d0038401c070031503103509440d582075886060003848003c06020030305a08102e21400081900d01502020070341c0003610740d4150440c410300050b9502c0000054010346680c08050307000d400890a4015075038100080d0380c0300c0002200404c89910702240c4200d91150300c4601e0000c0c450702041c1c1000d06070080d003c994 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 973026582 1250 973025332 973025363
    0xa06050a0e0d09030b09010b0901030b1603061412030c1b0406050a150c11120d0908030a0c030c051207081201060212071b030606060f031b02060402060304062403 71
    0x42d1901030021040e000941040803d0001030810308007960007202800000501c2d810403004070300b060070b0030b0b00180d400305168010440c0c5240301100c11091542c1c0e42c6800d120b4a441c040a036440c0c3c10038542807600c2408040415000408100181d4400110540895100c106641c0003c0d2840960341c884034061810f00e000460316040240d0310804135060f0001d84480c0c8040d84600300e941c0e108800b801c40d00da52000241006980d40c003103421890304012006040c0112900002a011000319402150302d42c0050040e1940d90740c201c102505441d806003007a10143d0703a2854494101405101005c10172040400e0301018840000064240701c0903140c0c1607001c6907200e0320240d0355140d006200000c40c6004010201c001107070100700700d1880d600c802d5011034864895580c1c00503a01c264000e0700c0020004209001c4183d414000d203a0f10062009590141e001c50030f030020745030b0714010030190046400101150402402da80030005241d07000c56013400c6c00e15842d640060411403444155681b103807408109 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 973027832 1250 973026582 973026611
    0xa0e0709060503040602090a06080f15030c04090c350109170c0a021003051608061011030c03190e09060306010302040e100203011e0e07090e0a0e0a06050a 68
    0x154018149500ca080105141c2581241c15501c01801240c0c095000d200c0f0111b01d071211004c400281005440d0a800b0b85080c0c2c0042d000404000c000c580e46690b44003005881d1b13100400c03492200d02d4107490124071002e560601030782110701d5510000602d503010f001f06150603000060741881400420b48056015815820b103826141070703c2000d80008515001c030b40d070700d010b00f40040103070580311000d980c0c07540c00c1c80e000a5000c507000c520b1040800c0c0c850080004d2143e84014a184007503c6007010402070501e1008030383c003104001c0c840300c00d115050a00030303401d40040050714402d200e0401213036034420306c1850207482c03c440100c4007000b01d010a41d2102882c601104500d03c15100070703004200d141e2171a005c02010380100d030404155401518150003000300e69000a6010305a01c0c1c04900d040650200f140145036080e41c412503040c003000081c03040640d0b200042c2002ca0b4a00c483d8000701ea11401000c0c0000d000924010301c451003428960401c1000907000070344102c280c55030400c001030f5407003e40c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 973029082 1250 973027832 973027859
    0xb18090c12060106020c130f05040303141803090f0102150709060e120a0609032006060925080c0409090303050a0c030605010f0810080601180e0c0f061c05150a 70
    0x186000350304a0301c01d2019a04086001402003801f40101180c14904610f010049610a0358150000f030703122a04a04078240c0c003807609805c0440ea00c0026000140298071546070300800207801d2148509000001c0341303030310030801c60504a92009519165080c02c2e41c0c0503002007514441c960110300c1280b9052094900114000c24560652001e400910440d94611005041b030a50031800c3c0078603030414202c1010307141c041d10f680d000c002008142508120f0100400700c580104014201c61400d07600600d09400900001807004082c2822245615185041c0000d40900d4001030300892070020345130281981604902d000342008101004190080f500c210142c4842e0b00035240400d02c50b10061108900c251061944280d4110b5500810780d1070b8602141020020b0303000d580164444166400c1100b041e100d001070403101400102105125203012030681c5171041c3c40e0070311546010035000c0c1040e4000b0000c5000c034803010780811181c50004148048500040a198041c845c0e4240104107650400007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 973030332 1250 973029082 973029089
    0x30a0f0f08010e010e1f09060e0112022b060c030c08090f0d050a03020408011406031603020f0913020a0e071101060b09040c11011b110607120b18090c120601 69
    0x343d01c02c0b40c0c2420701c8110140c4010b0090500850b9800c0c0d0b4254155031250010017510542e000401c0c194900420680200380603040041d2480c90200c420005a480251400f0300c1c4198080c2c004603254900380321039401c40e43d8503002e00201c0c00d00101f079003a15859803207070400c01425121030400c2e403280c2001c40d540300302c414058001640300089007180c41c0d00036000361410340742034a00585491b4840300c065080d51401c0104a060906000901c00c0a14061040042e00703801542e0007414185190002120320400b640001e002c1c214510100c1e01e154010140d0104654014004a020b41e503242814000c0700000c4481c20300143c114240110b10b20410301521080b9900c40d041942044000e03001c1000500e42d0022690503c03074a40c4116107007032000e0040c0258060810500c0280b480b5108010705008002e4000840d160030400c10801c84a400c6429001280d8a62a000801d02c254401261500318a1219007598120350710801c2440d090000b07031102038040503079110400d000c101c0191583ea84c0c0230301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 973031582 1250 973030332 973030349
    0x40611120411040b0a12050d110c09040f140a03020c1509040c1b0c18060602030a180503120c010c0807020d120207060c030203100b0c07030f05070305030a0f0f0801 72
    0x2240104400300240b80309104001c0000031412107410015402c07100c264041d14034503c04003660f00031702105001780d00c0206840c1c140800c2c03e05002921075202c0782c0094409108040260115003070102d10030036a14203a41c045c41d949a00100003000343d540b108007810842c01827044200089490500703400369464031000302046400e054600e000c11020300b004024800c10440040303e00e0700c0700046c440d000250355016040007040603040c10714540a484a103004040341d1402c00404000031070b4004112180c804441c64a164800d0300201e034030149881561200380c8c14440c0441c51030320218490000e000340c4070548000c10401640240c20703103c018003219038030056000025600b00e01740c0515a4001d0381c2c40003000040c9403a4641d078400b82103405640079040021b03804420806440d041b042c441c80a040098501c60820460450f0160350b160503000080c0851741e81d8907071008110040048101459100d000d907501c8421044d07004040c6074540c2c146400091890303146a00c454015945281602d0700030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 973032832 1250 973031582 973031617
    0x1c030f0318080712030c05071103150c03010608090a020108010b0315040c0f1b0c032a0f030b131e0f02060d02130f060e0103111e0910050f030105190b030f040611 71
    0x1034990031107200410180c940c150041902f9400800b034181140e034440c110300d86145407254102100104051402455401984d128a80141c00340c1e800c952060b0444021056081d641c2d035074958001c408040211142d03400904108500e000c16401c40d02d00f5942c1051340e81c40c0d10080251145101707612242c40c401030002d10302040180041109041c0c2c01280004640d295007a0b040b4400402d41440196404000000c1e180ca80600801c841300220a4001c2ca5002c0c050070004602c0d00c620081520304031141d84200480c00d030b00e00c02c01022940a8030015001868561555a01a84030f0040c2d40481102c40000c401c4100100303000000c0b04074441a2100c0d03075601118928400700540040c9254400c40c0d00340300e000d0042102e4503a03a501504920f6a079038030529118028001845400130851222100388102403089241d5001e2000980e811600202c030050300d41e40ea2003c0c111030b400c1642d042894250b0001041055225020209500a61048800300410380c200c0c00d013401c1c0d134010b05102e401c20040e00d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 973034082 1250 973032832 973032847
    0x703061521111b010b090106020312220209041506170c040209010903050307030921170a0908120703020c060a0f08040204020903010c0e040b1c030f0318080712030c05 73
    0xd9121241d880c444116483c607042d80000c641c2407403000718800e89041e039121801c0c0c62150504052840c01840c2c8d030300045040200105043d078034403000402c5c001754181c3e11300742c92840b03403100cc40c04110b1035005007554200c1d0419040c110b0705413520803015240d086c2400780014600000e1404145500c00c42c101800c0c07049903100400019503c50b80d20700781013103002003012020942c140300400d803842c4a6180c1c4442180340282c04040c0922804499041c036150b01e0801c80401d051b6030810340000780c0c41c51100c0eaa01c003d07140546441e13501da0484903841c800c00041e0381800740250001d0591078080c0d000c489030018840c0420074148180c480e80c40002c0d0790125020f1569024440290f00248010005814860410302081c00c6411a806600008401400c2c004d9642410301c11005103580680301d90f06514102c0c03070008058800140010f00308820030901c903074420300ca41e0280d030b21000314a1480c443c41e861810400c601c0d030840d10050b1180840c1c503464103c1c040c0a4800c030b20a800c020f40300c807805c2c00c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 973035332 1250 973034082 973034147
    0x915030a11270d060f090b0601050f040315020d0501030f03230a0809010f0e1e0105010803071e0b04080912060709060507060603020a0b070c0e09030d09020f0907030615 74
    0xc2c040c5445820054088003000010b945005600402450040001e4070590030300b05103010000c003400d06410b0001c01c0044140084c6940100c80503a600000301601240c984140500244103815401c6034552404001200300403c15105a4001d800799944c0c0c0d5420406250540e00622260900d440c510010440e80100f58042e0b08055071003000300d000040d12511003c2400c0588480003800002030f04003030b40100c2c03030701e0402510170003508800008000310342c100761202d0b5491103216005000301540701045007003184800c03820f0303241ca90f0007803a0a42d1410305107801440c03070300655000c1c0e114692140c442c15040600003459440f40c04941c2e24014258600081038510707078044001590500c2e00c0c1d07400440944c941c0c1003680001e0034810803007a1303554054108201d0508180e00400c100c005108107200103183c0000544585410f80c1340c000400c00003520000d055150000315540c0c00a80d504100074004d03400d82d0220048401d610709020541c0b151640442d02103a01082c8089480750342c5030305124150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 973036582 1250 973035332 973035397
    0x30f0313050309030a0b06130603110d15180b0a0209150f040b0c0304031103071419080a120912020114071e060f11090607060e030915030a11 62
    0x140944150b919003650308003c00d040c4070503140300742d403500351880a200740d5042c01c1c00c0000a98000200400010f8115928900680b0480507404d00c9170a89506100c18000b60785030320010030b050b0316010031114598510049040841e0a0282c07049050b120004224a5a50003151071486004218600420300200c1d04946500201094641e60005000129402c0400700080c021108880e00860304c5510714544044403800108030035000380c000c464100044003000c0001c94055000310b655000f0031512100e80c1812a00e40e5000604a02c5450003c0703003886940c0300c0003010754100ea56000001600d03400250748070b0740e00850090008205000886080c0e07000300c09801040d106030800071406018019901041e60303080c07400c1c0c0340c0031303600c00025840310200d109020300d0388a0058020b0820b08038000151440c00798100151926440d400c803076182074010b20451b5107003100105455107046d401e225070311150704203d818000c02d030700e0718490b0b5105407242e00c180d5000c001801a50740c107a0059006162604 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 973037832 1250 973036582 973036621
    0x71a0f03070c03032322080d0209010e060720040605100e060c0a0506010f08060c030103240c0306180204080a150e030a030c1e092108030c0a11030f03 66
    0x16035203150a02c00c400e150400741c186031901c0040c1074001d05103401502c5200d01c06c600c0c1150500d2028010301c3c0014084020b039451014041030060f2500e000c5001a90701c2c07100d4661456102400150600810210309140700380c9a01001014451601d020107020131242c840c01041e510000640846039100d228422080c510310018068900f0001d64000f103504d0954440f0046560b40c0011006020b5a4090205c1c01e0080061100904040c02c0091304d809052006020160102c010540e54000d00300c01c00f4041803000500703d0b0304003d03c800010008000b071807a4042c0b0580503039640c850301d50001d0b60b8025907050741c0c9801c020340403043d581d549070412103403e41b400d104a103407100b061210741130060014240750710300c50b00c003c507a428003504c2c000c0c484106800302e8450152000d80811159520524600681d000181100004080743c01d0303500111043c2180100320010000070095440c840102515040c0f480e500c87c0805504180c96068a03401a4183e0b21310546050001404000241e00e2113840c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 973039082 1250 973037832 973037837
    0x101a040b09011505040e0f090d0f09050108130b090c10110c28030b071b15020a02010605061801030b0a0b030411040b06130608060f010804080c070512071a0f03070c03 73
    0x1050b6440e40104031b80c03201143e0302000c07410f503003040040303e803000e000e040386022091034541820600d020005c0c2444045002e0a03042083c800b0005079206480b4007068403454020346030190516100c1070072540e03400d282203c913000307001d4081e9441016014521580c200610b04001e840082da001d028860903903802e02c030741d04c0f000304030702d601441c42400b40580300e0195028001c1564203242c00344001e00031040c100c07501d11120900406d024041000201038140e2604410005a038401510302e040307001d4041c541045070301031700006403c282c56000c2c02188040c15000e0304c051000078540000c000c030350300b03480c400d400415104000041c00a418940380203001d104c02400000c441840314042074260300882c40048100c0240c00727092000b9500901100d5210004648810001c2a2000000c01041000d40007c100c0031340400e5a0b10340581c10301c1850090607000e031106144160740c2c141c07150b0300c444500c124810b40e0200d45a03402030918190803250100c0d00380e200c0c1407450301c4003801114078001c401c005404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 973040332 1250 973039082 973039087
    0xd0207020a0612140609070c050c03010c020f060a06080d030933110f071104061703040306150b040605030601090308031303091401081b040503101a040b09011505 71
    0x595400700c21101410a82d55420007400001442c041203800d000b13000001d440414040001035603994903640c5d844142883e010030400010720740b09241c24210000302d80c0c10f500f044d50f0000c00310b500050505514104904a80268842408020480d001401664616001186081d031503a00030382000751043d1040410345202c002d104106100110703900d10720440035204020740702c42c0300824041c80c541801c0d00f00386140f401114415a4007680301b016001451080151682070304c03591250710000090119a40c070310704d000d6002c03200c1c80c2c4030f50103400304550052074591114042001055a00251510700101e5440c06040c941d05507001e40004020706e04002001001200041150000d18000d4146c4034000036221402d01d009002c0180540000c4001c0d1140d4120b00045d0b03900c01c0641d0b0304483c03110400020007101f101541011320a036040660180304003451350f5a074100c41d44c03013031881806003d208901000e42000300403e440440401d00d80c0b1007601c000501c004010308442d030b20301103850305080d0b1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 973041582 1250 973040332 973040347
    0x304031e030201230117071526011404020319090804090f0b060d0203131b03110d0209010306020a03091b06092c06061605010605100207030312020d02 66
    0x2180d8841003012100003030300010502055024010124183d812010200d1420040c1c1c04041035000148180707600298034a940c0101c0c140c09200c43c401810103441415004580e41901034510100450103030803001825001444a018100d003083c162001d40c0440120342d0305480070400a0741000e8000c80c0c0c050116607213104500d940313116880841e80303d82030940e280c9203080d145508490030121885511424261810490740e61001121a0b070003505e40c0050f04d0ba240c00e03030340e013803100f11400c00141640894014810900d4035000e6480490f407040071140700250b41041804030314007140380003c0d0032101d000014000a5020b8001c1c00d8134280e5881c0c00200c2080030f0f00c6007a01c02c10100101c20362041071034028001607078805044409000c090852100560b0503400c9440901e40251140d0981071610700450f0487d50351600300c2d58041404002c07581c0703921550a2850080129100b018864103004000f040c0036400424801c00301d82c9c054440c2c42d81c007041107120b240658810142c101ca025400c1101c907 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 973042832 1250 973041582 973041593
    0x1015120f05040309051e0306041e1a240102031b01110a121104051c0f080324010e03030d110904020417010c05041a0a090e09012301050d03050a02030403 67
    0x80b0300c6540240d40d0000100e14110078171a000d141d003201018003103400c6034810215100060f21a811691180070304000c04221001e85154a5000750010040d6402a0b4010561880c02e4680c6003c1c10420300805905848542030045801c200d07107203640580c0003400003102208078150400d60300b000300d000200f8108a01c0080750616071280a481c404584001000106100c082c841c155000d51511111032510342002c001941040119071b80d40f12421003440314104009002c0c0041e842d4990003410f8503124209549426000300702c81c0014611800f03100c40c02d035115807140111410220300a80554604070030303002540c0c050008a07a400c000a20200301c410295201d5200038070003040007506960744028801400c9081d42c12a09202c003c110003400184804405d00d20340c0c00812a020780e040e950f811900d03900381c0d0521141d5204509244d446c0007000f044240c1900312921012407040d40000c43c0c8400004060b40c2c040038041c25402c2503a4004440009024000800828001c1d00440e81040c1e942d40e540d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 973044082 1250 973042832 973042841
    0x80702180c250b01031202010e03160201020c030a0b06060f0c030706062402030a0e130e0705040b0d2d06050103054206040905060103050d081015120f 66
    0x103951603800d00080d0003000070102d407082000c02d10076403880568184140c070b64030725001e03060101919802e89640d1001c2518002d40c400d000141c1000d040e66140c0c0181d18820582c040f40d42810307405805107140e0b40d0010302d0046071611840340d100d1900c441c1d9440c1c00341400a00e0300403c000c0c65450a0802c04406c80c01c008001401c040d13031140402040807810b165000034400d9080c00c0e04800d480002b100050480c0c1c002c800d4500f80e00c420701d8039002c81426080010300c0083d0000c0d10045440c070740b0540d16040c0001091000c20344006440078482c0c000258240101c089003010050310200d140544242d1001c00c44910440980c0382ca81440342211841c1c8510088070350a03801180c166000301140005040504203041d03650f400d010000c10780d000101c40a00c2003050040c8503030584904140001c18130759032a0310100300c298000d003c03a401c41d0b0316440d22566400d024483e2360701154040e8009200200a00901d90660350003c1030804124015801541c031750828409001c501c644841c000d020840f02c900c078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 973045332 1250 973044082 973044091
    0x3070902071b0806221208090c0307060507060e1e0706020105010918030311040f06021e010e07030b070c15140c3405032d070f08070218 60
    0x1aa036154a00d01691049644240c000c250402c9050402000b43d01042c21a40240c1240c100345503a03295564000c440508510014401014881c160716103030741c0940224829550740044038962105102096554010781c0320300c10000742c00700405000115180c101c0203140b01ea03441250b9003031100492440c8060380c001c0b5000a0396005020070402294240182401012007607001c0005140c0d100001c81e0014000402400b45a1242c5034801c10b2000c600458004000da03008070078405407070b02002034650b00403200042d8007087d6000c0c0304154480600c01c020220316000c00410140c1d180d66240b0003903000061905084c0700048800601041c42030030b41150f451030640700090b40d4900c1c540c0c8505905806010060380040c00d018090f04c106003a008514031914003444403010025200f9500c8000700c1102d40102140030110f0b0001c10360110800f8600b404203400814080f8008108015916009402001d4000c1036000389400c041184a0000d10100e40050600f4081541010291000840644 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 973046582 1250 973045332 973045349
    0x9110904420504050606033904050405011421030c0d0f0305070c0203191e0b1009090507140f031518060903040b0f0d0507080601030c0e1005090303090307 68
    0x6400388920361a05a000382c203080300d040096040180c0420f050b030000800030854a00c49901d09203a40f00ca0441d2000c2d1049010400e90304440310540d83c1034950458410a8015801c00002040d052420002100c04140c040c0c4007014a40212040c501c61a0500008142500040141e24003407030003405072070b1081480b6166601e103480140781c000c0864000514003400c10503103000007401a034011800882502c44080e20200c800d040b801c00c0028070b030b0701001100800f440c0302420000c00c820340c884140306407150010f00c03107051707503c492007419280184c0707009011f600b00c11020b016140c0d50a8000c0d0300fa02010300f48021030b40c403c8000c83d00e80b91411841e0759a840c603100c100055550883d40c541c810b41849000743c605030400b2020700d50f0f280254025400284004220803a140d8002e03400c0e83d0211403502411f101ca0f0070507000150140c0000d5940c3d50000c0d080821690f0071030702a07000c44010b4400581005001c0005420446058015401440d0f2501007001460150742c0c08202c00d4020740f0307121 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 973047832 1250 973046582 973046681
    0x1091505030411040e07050105180a181b2f100b090606040f05040b0103020915090f0108130b042405011410020a080d060512030702040609110904 64
    0x381800b1594094261160384113034140181400b000320040307081c400300c0300c1c01e080c01d81d1030300c00f08590469400d08910001c1e81000c01007000141c5520000200114003034101020003040100e070407034a0b18101c8501d803400c0030410240280001c0e0075645003004034000740300307c003042c5910352481d01404d1501c08004448603585070442607101e03142c00500705402000c2107480914040c03900c09020880045031241e0391103242c0d59940c0b0702050340280c04070f07100d940f002000300c20105406c810507100e58201000d400d014506409040d602940600c4960380248451901140e8840250351100080700008204441040d031207040300c1003002c200c4405050142901c08045210342c1800340c045140c4400c4c911244c80f4103000c2c401d1440c60703600458200b0f091900862090b07034840b007110120001d0322840e407185400078841c1200c44038084010010b024604d20841d03051103200d035203007801400e0700d030140200e00c00c0799010400121540b4003a4050100000d4042c41d420640300360314103c0d403294100090001d44110300c2d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 973049082 1250 973047832 973047841
    0x1e07020108130c030f051b090105100e0a0819031205060d060f09140a0314041d09071d011d0105152203081201080715030902013b06070506060607020109150503 70
    0xc800c09808411f00a0f6000d00c0035600d00750006140400310781002c130034040c0015600b00c0c191150707003401e8041c003000c0045562414070705103585c026000d91402900020a44005501c04207598007809009d002c0091013400d000c121074032810003c040d254280c01c00581d4409070600001c404900d0903d11685141c0907088941150034091b02810014404050b40c4a017004180500c907606080c05c14051041e000c141215a900b805841c80e240703598101a081031703100d1000810b1400700c0b259803070603503100300f00384281c0c42d101d80e40c400040034003030042692155080d1000d44e000c5510304003500d000306102c03540002c0300d14a0714102e4a44066500141d410f403a000442c0d10500204084807030050030050f008000d203034501a01d95082a400c2c2d9040340802d615038031703505c00b9a84194841d252500450125a03030290b050b80c032032501c190784645443c400d002500f0034030300c191601005603181190800090615540d4447c10070a40b0750103440c0c1281401403c903008034a0048441d11012051701c5503e80654070f080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 973050332 1250 973049082 973049113
    0x9090c130b0a17030307080c0408060906011401171f031505060f0105040e010e0402060c0d030f1a0a0b0903010e060a090516050d0b0403050c0d03021e07020108130c030f05 75
    0x120343c1c000071043c01e16071030700c40194103001080381c2d8025810300e8000001e0b11000071022151040344e1208409110360400d000300c90f500800c06a0488480208803241110b0907001900c4918003440ea04d0a01503120001038843c4c40d01d0f415461708144041c510329034a50300c9079500001c0550080903026120303030300c074100005410045084090417009080c030034101403400002d840051014065546c403150f520b0049007c41d1a448180d40100e01602c00303680164200d244014000c1a10903900e900740d6003804001341d003402e16002c0300e1040b075501a02e0710720118101309003142158030800c01d2170340540d40c40c40c00d080440d03002c5c44054000d100c00840480d1012b03480c1003071450314051680704400807000c80c1c01000300e076403150030750281141d104c01d0109080d9524201645c1c540265600b01c41180286004a040d16a25600424040340b21920702003800384010140b20450041e010000d000c1a014004502c2d60007080e580c0015140c0300301e00c200300031902c0c0d60b80c1d00302c94070044000f11965400120342c00b42c1c111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 973051582 1250 973050332 973050349
    0x12110403050a052b0e010507020a230a06020c010c14010c08100b130302130b090108031314102703060204030203010c0201050c0a030e0c0319031701060e09090c130b 72
    0x43c4500304c18044806043c8001c8201808540c000c0d00744800303200021066400f9000745c0e801e65030014040e500d041d070b903030f12899101450548068641c04049036409850301d0520001001d8840303590003050440d24200055403a44d012050035107200006507c1040030305424040d5203555040c950b40c459041c1000210b14405034503503080010308d01c20a101d90142010100f10b079904480e0101c4c4d5480010707001c00352080080c80600c00f065001440d40c4008030f403101000000700050030b414200c2c0111140e82e1040c51404ca0a05500700b94031443c1e1829034022103100b010118441e4404003a082c2150983c803400c0e80341003019a004540071500800c04205500c1d0078461915142d55500081c4a03924003034a00718000e105080450040c5980c1e51070280010404015903006000043c0c00c590181e0310810002e100f0782e03000030b01180019000300d038400030009111003050407148592508170186050f4020440c100600624943c80c40c4101d2158040300c1d9183d40d1441c0302c0300712040c170018119500d40203028054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 973052832 1250 973051582 973051603
    0x1a0915150903152211030f010509060c13170c011b0f080f0f04240c052e090f0302070b0403230f06181b0105070312110403050a05 57
    0x202442904070540340403401d4241541c00d000001c190f591680c0040300c508010461418452100190300300801803913401581c0c03940002c80899842c1d8280740300306421785108452000441c2c211a01041050fa64100500040d5618107042000180c41c0c82c40c1c507401084e011500d410300e600003214000340d0351700924030074a4042c2c000d2102849800e50f448a8810040d02400102034a40000c0c00c1005e04042d2819585249030117400c5980c1e0301e031384040d00760b0341080c11001d49039001081c0500c1d21826000e0701d940c2450710341c880050f0020401d440c2c2e254040403224444a0146d10603100c0c4140c10520302d20a480205108504280040d24103040082c50582e2541044003443c004020074404921154400060503e080058182c561078915840341402c0c001e40401b101442000c05100c089102168140170070b0286504982c5090b10b540384400d043d468401030640854410041207000c2441100f03808040c080300d0401244110b45c00c20400600d912a620607541178111000c1c101c2007003024001031511 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 973054082 1250 973052832 973052869
    0x220f051e281109190f0b0f040c080408091c1406010806060a03080d060f0617070f080604020310031721090309090a0b040f1d060f0a1a0915 61
    0x4254081da81d828480d07031210005441800300c0da00054012215600d05589500320a81c1170016000c030300354485c00741c019400441d1007003400e0085c15446040510a10b50f1001c3c246e505c098050326075446014503540540700164020803410500d1b52220340c4148010320780e0744581840308800080d001c0f02810190103030800082030b0000130234004aa41d9680907842581d8116000a9803440c1d0322400764020117041d80500b41041c0b10020020341180c0003002e60817244550000d60105a907507031011141407502200d0b10022030205400300b41682019070103190f07c61480c424140080f0303125202c45a11074034207090b141c0518000100c101410650b82c0c150b019120346100500b0960910003001a01e178040e110b40d840c007984c000000914241c0c4513800c80e4841ca54083c104109400300c206800d00a0302c24000c80d8a01c40c468102c8e0202e200340f001031940e01c50040c1d000b440b0440e86404d450a40507040440c00f0200b00e009000285080360394104c55240184220401c800543d03244400740002c0b603800d11544101d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 973055332 1250 973054082 973054153
    0x20310081b030d0516050d0305070909050c0328052d1302060c03041211040b0613030b070201110c0106030201030b031c03020307030603050f0c010305220f051e 70
    0x10280c5000070340a040700058101a170701e680d0b00041415643d02080c201402903c900c81c40d42e82c8154041e4020b41c0a98001e0f601c1d036103000c0e210100072050300c07403e0741c0106164a0400c0000d02e40501c2401036000c400c1c42020000605d8030240740c0700300f80e400c10f851144e4003000080749054071100041c03281465198458107000149030040500c0341c00480d1610182c001d8400150b007400d410b00c1442120040c2022050b102603d600c2401c000080350031403041d841c090340c50809162024070300301040e40c00c5e040b2800c0a180c0200e0031940e0f801c0380a040a0050b00c199901ca41044041100c0d5001030109080030b2000050380318a51300005080d2403502c1149802600030721503052a900d40c0c2019022204214200580d0343e0315040c104074000c0001d980041c11502643d40141040c140114070541c9894007641c0070f10054850703d00c0c1100c0c44081c0c240ca5801c02c81d844081c1c0c0300145070b10441c142078a00175001d49002c481d00340000040851000040c519a41090204001400e411411354803a44440420440c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 973056582 1250 973055332 973055383
    0x308250c080919060e180136020f07120c0308070c0507030c09050a060f08030a11030f0f0717030606070308060a030203010e072c070804031202031008 66
    0x81100004090140c00c00318005007052080d251840f01001c021031803a0a2500b0350303580d06004003209120130009120700804418141d00403401c81c8070720305071070303ca100c80301ca51424007035074800000c0d460b049891120030480c540e0001c0c0c0502d00c09400c1c4081d1180078199504141d160920301090311220003030501c940704c0010000b00e03a00241040c4c0c01051030401452100035800c1240c0f801c0380c0c0ba403009080707480040000c030303148200750040c5000784010300c001e1080b50b4441e040b09110403601d01908085501c240080c040081c42011180e4403501300c181541e00e45002c0104111141d802040015415840001d41200b00008918000c241443c4c1c0c034601811810107000098440c4600d0704080d0400103a00045070241d907400e640d00c0003c65008008003c041d1710600c00e03980702c4107170744078043c00c10801d02c03520400da607480500381076601c040d4484481d19540303c2e2b100703503012130780a80294100400d00d10030000c0480d0038030085001d030118112240e0018035015405140101d01c010107071140403c0032180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 973057832 1250 973056582 973056587
    0x90f0b0a021212010e0c070606060e0301051302010f05210103050703150b01120c110f070f0602160314071d01030c1706010506030702010e010f060503060c070b270109030825 76
    0x5038190307052140c00440548031986c07038a10ba0700400f0005010a40380c03510014406804c02c5c07280502401c00e42c000d100c03e03620110b81c5150840d0840c8003901180312480c0802c1d00c644100c00030b0601001d00000d490f585000103048082a14007604216425813040e2010703c2800102c01002107159000c0006201c00480d15000030403102c00700085220050b240c1820303e60746405001c0c40764058031240211540c002e848012580d03034603118401d503050344c031038031002207280c03480480da000280024003000c251051950f52080d12040d810740700c4807058094407a000c1500b6102c0c159225140b1000c40205030254114105004544040c0c0c0c001d0092888018242c4000c2e100810380074112381c0e04888013600c942d65220207a002d41420481d600c03065180070400d0817242c0d107a600940036107806404407001e03980e81d9220040180305001e4040d149100c0d40001030103810b0b0b400c540303003140e4001c00e0408840c0e06410504500703540034010200c000ca40b02c2d4041180074140082c400d00603000c031411100c10300c999081c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 973059082 1250 973057832 973057867
    0x50714060916181d0d1e020304050d0b04110a120b151003270804140402360d061409070510080402060c03030f04051005010e0c030601090f0b0a0212 65
    0x2410b80d510750700201c005000050402c4070101e0104107842036100c003035000400030404244c0b150001446e0250444413103100205076070903917002426034003c80c400d50b04e820004c1e98009000b1103812401c1c0b0a07080f015214032407840000c252807a540c500c0c1e0b80440c9024150904010078116a0454404034501c4a0b80d60302804240e0900360f040006858174084803046907406d2565061180120004450f000c0015440080c005c681000d0454980815042c0800c000d0748144401441c1d202084441200490b182d030500104404014815110f80c1441a002c01c81c1401303007190660f0090382d00e5040111151012010562024588010f00b80680c108400a2403011181c0a800104a000c000290464846070308546042e80708000b2251a841c010300803000841e02120116014010621549040502c0d4040d90b0305843c03809170340c5119a41c858082c8141500b00410f02410843c400c0d00004408a400980c40040d10b4ac4d400701564440580c00064500401c00c040030202c1c02040260428084d00c2806 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 973060332 1250 973059082 973059119
    0xf30070c0b04050c1509031006120803071b060f0e1f0e190b010302010f08090c150d061509060801081b06130b0432090601050714060916 60
    0x1c0d40308060302c6604280d45041501088142c0150700c1c4005034210540190242000400031412142c5000c01ca04460090b0b0700b09225007441444481d404100003600b103c003855200740c862030040c0d000f0342032200e1101c1c4068290025140d1554070001490388003094016100d0800d040d5004041003070a05e0748550060443c880d4540c0195030340d10840ca4502014402121245101040345014075200d0401e20700280c42880203e0206101c08901d081a90081400d1482211100c018240c082c2d0060140100030100840c80b02e084a81080b901c01001c039280b040c14080d08140300210a12400f2080180014600da0130802c144008603004100f41c400005261031503022403ca0180c90700400000714429015046608821031700c408008100880c034100500116a03020019410f8001c100b4441e41c11a00003a07600d4030a4003100220000908010301d056800c580185800751409004c1d03200d42c00e02c020188243c682540100061229100f81006551842010120990301984c981410024540d15085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 973061582 1250 973060332 973060343
    0x9051b030712020a03110403150e07080a080f09041b0806010c0c03020d05070b0a0e03010c050a12052805011d160c020d0803010b190806060706050c0f30070c 69
    0x84d891030103500c00d03040381d05003410b54622180c5a0f6140e02e03100228041c015544120f1030f14058012150100000701f0004640c2c480f000f40c1401c401c1c9849861180d88041c1400700100802c02c2005c07401d8665102e080034155440303c6a07020a4501c4100820410002c0c02c603138104143d4203840408103503800b541c4021078be0f044401c0d10414080389072442c203000542e40030810a05011800e00c5445070490003c003180f1208070001c000b50070030484241c555000f1000004000b0380b8a03c5114200c4426600a94001e10fa0b01d44045c0c503503c03a42001302c8000340b038039843c2c4c40e4940c858004008440b1031040702200c180224260f20410310b0680404401c2001d503d80110402c40f04083c0002036448220055510700d401883d0203a8960f150b100401d04c661181d904400e201003d1a81c003420707644164909805040e0041416141040c99203d01d0080e003405080c501031001c0030005a42c5940101e0001c04d21000c01440700044250100d03c1100c441c52540c074010100c0c16484100b014803a813000a9000959014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 973062832 1250 973061582 973061587
    0x230c24150909010908130f060206160e19060903060605060306090c03130b0a1d1b0f040b100c020a12030e0409051006080c031608071205030d0609051b03071202 70
    0xb601a1800750070340c4ea1029006000004610500c21a920071807415586100d03c03001c1d600b41d079410101d80c2c40a00325409000485a02500340b8294414400d12842d100e00401c0c104d4020724003420b0384001281a8031002c0414071a240070010040d03d801098010001240c20a0562520002103544954000c0000122140c0080001c03c41c1c10700c031000b40241c64009444e1541882d0040703400c1c00620103601001c020003801c0e45510030869000031940015600e4540b40581c000d803101c1030105100302560490741c0640c40d024510496152100314100408031a0341e240e12084050040c881d4642a40c0c000c0380010011219680129406c00b89041c002c036010b56002911b480c032824100d0911002c640d0030742070a410710380002600b007000070301410049003c40503103801c04022040342c0ea21604d107203e21080e0f0381080b07a080000e51021141408424040c0342903901e44403052030030748121000c07504558940e9a8030710500c2003090618000c070701d4509610405501d94102140040c04080b541c40d41e1100c2c05400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 973064082 1250 973062832 973062841
    0x1805090903040e100e010e180313050f0307050303030a0212060102030c1902060d0e070314011a090a02040b0f03221e02040e0a0501140a0603020603010303230c241509 73
    0x2000c40c0c08010100c0e541c5c403035070558644000340940c41d021354800300003920070030000b02440004030403104004260940c1002d22403400c402d100b005102c0404081d4140034001d00003800340ca041c03000b944102041341d4016070340c60440f42c04030308480001e404281158000d201600c0c010000190a4800c03101c00400d058003600c05200050b010b100c0c0d580c02203a00b82c20700d140a031140c540005c1b07050640c0c0c070544080c9520400882d905080303502c2e0105011910080d120682c030a811701007401c58000c0c40c0d071440989020b8980c410079811380d000811107201c00d24000200190182d128032080304428060781648003220041c0c50b44070120400c2003036405442c500c440e00d01e0071543c807584035100d148107450949400010078140380740203001c0c80824003484400100061046580c62055034240e0f03600410b5a8116401e40e18220b480203050309071943c20800e00100c200d524841030020b03202114500008042002c051441a00b01040350612111500701e59000e029000c900304170440d1541406a4401400350754 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 973065332 1250 973064082 973064101
    0xc190e030a080a0201050f1f090203040501110403030207060e15090103021602030607031e0c020d080a0212040f0201110c28030c06030b0a06080906040b0403020a050d1805090903040e 80
    0x200d0100c002c0081900140c920b5a154064106074070442c41981c0462442d40d03640001c0603111810148031522440451050000d0041035028507001401540001001c840000c3c1c004a290f2040d001a80540c2c4071031010410141e0102070303510403150544008034007000c50744003003005000d007608540c10705030003094480c402c03041a20f9004031503400500f00c5a060419560103402010440d000036007100300d1345000340100a2600515880e60302c5030340203140000f00710a040b15110005840001c1c11a000c200c1103001c1c10a07070341030364080c078059010f00196403103610000d41721220103000048030b1380203902d80c41c20a42c0da01c0300034101074100100c0380801380e0004980c2101c04230705400c02071026445600214002d0f034994071400312240291340c0301000649a00e42610346241c22940c3c440c0d280e2000000500003407000044030b4100303110780112220060035680707590901c0907040b5079000092801409600314001c01c0130810003441c05440140d500d08011080580300d00c19402240e0518480d100480d0880070b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 973066582 1250 973065332 973065343
    0x4090503070b07090603150b0403020907050c1f0c0e090c0c01020403060e010606030e12071b03020907030906050105150f0a0203040f14040b0103051e06010905180901050c190e03 78
    0xda00c00002d48051078010b01c0504807100038014200080d203480c90f0360704001d560007422415103807000c5615041610f03680c2005000e000041c0201c0c02c2040904c100c002da400c003004000c00e0705400002402810712400400070854600c4e622510400202c1c601e110030300d8403018a1a9006803144c9051030345c2e51541c05404d4007902c500e07400241080c3c60428400c080c1e01040d0b21041c02e07182c0c0d41c4c3d001d01c601ba180252999844e0170010700d41d90342071010032580d0009150f03101240c1c960101148421405560798000810b8480c0803140e000c0465180c02c0300d1400c1100510841d40540030480d5400e49000c0865000c880034014101d000d0941040091703039401c028000c00c150380c01010820a1600419269003048502000325807240b8000c600b4a01c0b0b01d01c6c07640c040c0c06201e220390611407600603a1201c1440c1c42c000202d0141255041c40100c80010640b5100c2c2d0306480d481d42d07030f130700801c0c0c0c6c203030510100180c2114001031120391821002e0041160900c0052009056948035203008500c0c000f41100013030520 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 973067832 1250 973066582 973066597
    0x81608090d1a0604090308070f090e0103060519110f0d090c08030d0c23090406051e0a090603080a05130f0e0f090d020d050c0304051203091c020f04090503 68
    0x1061040520080154411450402c80140e442030b040c00c1e02c03a0030a01054840182c0b008011807541030000342024030508039550458214038113400c0250f0f8541c01c00e09280400e030410f42e209501c0d40100616250302103095070180ca6480307001c000f0030100403045e10740340c0503100d6100c00390320001514a50166081c2c20074100b07141c2150100b0701c0c1954801895541c1d44c031182030900071605060340a00110b0141c00c05d1301c0c008501e07281c44094a41c44184490f001d078488060190b200d6500d08000c03a407a19071074055005081000008900740011000300308511149901111006051000500001e0722a80c2518144890b07401c149803944468000d007059191240c104c006c0c02114540c0006a03603c0b50703c6950b00529107151030801545030078240c1a21401c0750740d505005a4030140741360641034481e0005000110b50441503909064850b400200c4c0c0030300500c04401264404119800c00b032416005492600c100030181c008021056400f0426442da18818036208554405429060050a00454040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 973069082 1250 973067832 973067839
    0x4032d050d0302181002010b010f020706090b03060d14030301050301150f060804210c03110d1e120603051507020303040f26030a06080f1f0203060102160b0405011b08160809 76
    0x10751702c5584020b000f0668882a1030008021044d1180003a00104100b0141c1d009070343c540603024200644240e080d0703c098002da4002020940d844041602e00703210100c2040c0101c091562949030a08150079070326203c1c442c1c8124504004100882a162002481100c580781044803651766203040c244c0c40300110000c184041c10a1041208030240d10203103100b5000d2003621490020780100e525956548040d09000c0e010680e102c000d4442d0821360202002d8210399481c2804c0000e0000200209607003095108480c154410180c0c4401c55a84c0640030b903209009100035801d501e416144c45228420700040540700e40c8480501e1403500e0816190410384081040409a6a05040501400510f0700e8400c3c042e9500684a03030710944a00072520305000b140c0c11440354481880090040f0081d40081d000d40e065101d20804198014040c907807010007812803401080d10303146001c001401c0a000303012160035510a40392260000350000007030f90220520019004443c0341945420f444a1150041c5541d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 973070332 1250 973069082 973069099
    0x160201150807092735030a0e011803140f030c03040209070219150e0708070f090216030f0201140a061d06090106081b04032d050d030218 60
    0x1c81500c00520a400c0341c416940401181000071580c0d00a04004c0c01d101c03c1c000720b09088500030601240c0d10b0107240140d54185000c580800c40e0085941e07101c880075002d1440e0203c02c100940d6054465076a0503c020340c002d2016401c2c02c100e000a2032841c40300101070000d90b501040381042039109803101c0c60140e92200f50b40f030916401c0071000740c208542c220720030b4001d000021003c43c800b08600041d00389007030f20403401100c2996054145907000d922150440c0e43c0e0311710031300c4040c0104100c40c02403d400000e0b203900c0d41014921039048495410420750240108220517813183c0e01895940595090b1504031808682e80302c08a001d0035a9140e00d5450300d5000040c0030480e4551b074041400c48100800307010b00300100d4a800050f900c400ca549a41c07000c0e88500400c8030314061543c0640c880703000356040000842c03030355102c21550055007080d03a0a100d03020401000f05030703800c050046031780b62500b12a0110f9950b5501035441240b45441c200701500030070b01e1020302200c45a10141954024560714 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 973071582 1250 973070332 973070339
    0xc270305030f0301051002011e0e0f100b1c0b070c031704150f060e0609060d05030315013b0a1701020c011d06070c080f07201816020115 60
    0x31501c0c3c1003806180d10070784032200d0780ca061600501c40d407640c1e111100300c004038600da80703034090000b8540c1c40d40ca184580107003080380d89a240180aa08030009203160b0005815066000340002040c880c1040045403011a01d4800810b008281c426440100341c5000c866031101031804903100300aa00908903480000b20030300007005140007900c0036202100b40204403000b0300c10310701030a4554911880c2945221000400c0c2c00e81080d1001c280c1c806800b500d58604844542c0d01c652443d8002c4801c1c1074030041d045200e211030740e846039044c02094a070007a0a81c6220389641c3d241003003900ea42d981a400390889403400040d8490402c400000c00381042c2400c3c074145c40c0203045010307500005150559500c1d050740d00b003c0010702207405407190074040042101d981ca2100c166070000c04182c05480110b410311488040845d00c8008201403807203000451480c02c54100c0003d2500440c0c0c041520030303010b803800b80f6a044d40b4070b00c40f2a030001b2500171000030384d2001541640140220040030f044c440b00b901010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 973072832 1250 973071582 973071607
    0x100306031a010602062a22030c0905010b030114120f03040308030f011212080405012007020108060111101104030c061d030c0a09022b0f0b040c27030503 67
    0x214102d8a8640a6417800e65800542074500650040c4d020440000c2605034070000d000d19014065001c40d010707401800c03000c00e41d402d181022407584101d66281c2c09000a100c01c104c0c502030b4500410424180e1402e6504121a00c00860894804180100c00c1e03038401c0f0990440802100d030074682141b0a0341e540302e8880c20448006d602c202c68014034014518000540311106452508180f508150300c404036041082c0200c03015000a80203840c0b56491f000c0da200060041c840c441140202c50700c05070303901c01c040d2001401300c100050401341401840500a661418085002c444540c651000000c40e04ca00800741141e03402207800c041d04503c105200800c046401c040b0002a012400c0d0420001090703070b07020166504880203845410040791042049152003940140c2001518000840051411250700802c031221040f003a011058039418804170305880b502c50303414070500a03202484001302d001c0e070140202080f503803000614480c50742480303800c154070010b2401940d842000c0c4c03a40c0e110a400c45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 973074082 1250 973072832 973072883
    0x406090b0711071208072a0b04090b04060b090d080705010507050c15042609181b070f030503040311190c0501020f0607140909043504030210030603 65
    0xa2801070f105010340429502010400318010135445501c5a240110b40d58602080c0c200040c0c100e4000489160180000300c802d9070700101034000c00e40d486840743d24060b800010b0b0f5024002c0f07980145e150443c01c0c00404154412119444400e0701c4c0b04409203954506141da5114500b80501103502c0c00c4240245a5802030091105001100483e80f07484411080325081031020388005180221990f84084040090300302c40c9101200303421041c1c200103507076010600341080e410300110400103500400401c0b2031140240c0d49419120190542484400d0791016080c0c514024040c0c2403100c00310000d03041510070361000c00300d201c0d04826104d5440400040038045d241d1200111842d20f000c1074042225440003c001464014000083c6941d8403444425a014044405280340004080222200b680c680308031403809030380308100c040c81400050603131011041404440381504422001c248803a41011400c2d141501d0b0110340c964654106408294000d10442d407004002081406511061601600c82c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 973075332 1250 973074082 973074107
    0x130314040e01090506030706090b0306090717041209090b0109050f1909091e08070b150a0803090909071508070e1509090901022d0f0c03071103031305090406090b07 72
    0x1203507901502c8c0c00c0c0565203e103035401007103280e103130910024100d843d0600e034054200d87e0b14109841d0050800d5000c0103200011030f820748607841880c901503103082e0701400c12401080c8880e02007203540b9032240002c00c607000911a26100e407003002082c20322035641c4551121a030480000a5040039529648840036140000782680d190072081446181d01559245024810360b014102c140392000c42e83c7c0e20303c841c0030081c2a10303003c8030301684007212580302c034075140015000c580015a103680c585810030504400040c4901d074190440102000341c0300b42c0120107910700c5c85a040103d01552040b00840319203012000c40765001c05442070102d1017154201c010515514280c8074000c680d03079045072641c244d2003842c89114142020302484d034961500070303016882c9481d0b00c0c0c511505d0301503450303002ca0076074000194880c1340340c1001501d031007040204800c07030043c2c0f201540a103041c03042241c0c0c01842240d5610505006125140010702003250780d07803068003601c0e4007945260880c20f0090b00200001e0b00c440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 973076582 1250 973075332 973075339
    0xc120c06030b030604030e04090302121b0c120a080f090d0308040501153204050103050705091b030a0c030f060f06030608281b1418130314040e01090506 67
    0x12082ca41504010030300c184500e400d611400d260450f40000d001c001c0800480a508600030700384400d8414031504000c103902000c41c0500b103525040c1828080c20004030f0750001707104410f0303003148801c0494041000b6400541185c0015210300300191300e0111842500c0010754005500c228003000c2640001c40b06001d14055002048000344000440c40c03040b00500515040040300c02178000d0400071b24903101241d13590000e506001c10400800308042d10b80c01e0708100c8054000f43c0c401c0c81a400e041c500317140c0c0010b103140b0303003020540c190701d28040130b100c0607101340d00d566243d2003903580304ca000390017103002084200380c01c018242c0d50f5104100031034480d00600c0c00280c14140000782403200015101260207180803a20100d0081a8114804180b0301408840003c0c0308642a04010040e12151000305410b911044100300003404221034035800c040080e83c8103e4140a0240c1d40c1600040080215230604021001a411051319038080c040c9130307c840b402d074081c0000420f22443d250440c902801c4242d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 973077832 1250 973076582 973076591
    0x1e0923010203070e040e070513060b282d0c140106051011060c130302060307080406050f0405060708061f021c030b030d05180d030e0108150109120c120c0603 69
    0x20713400c0106880d14070000804a5214030800d014034500080c042e810410311480c006103450780c0f0b451060164124445c1c03194013500d591200e800002c407a0503060201001450464402c3c0d0314500641080049402c11980180300040951583d5010381d254a041d40d40000088003803a5641c503001c0d010b80b506e03010302d9004e0385501d4440101c85029481056580c140c0340080c0482da5122032030131950b500311000c14040c40c4500840040940ca4101c02107000300440c5c2c1d40c205662400e801e084056071400f4050421840d8180c0402000c202d0209415800080d246000115602e5050000c1c28081c02c11081030a0703503161403000b00c500d0b50006845c0c1c80215a06140082c06080d000003a4222216492555010b800c214501000e00348030b9002404150489401c10007141c82c1400071444100c03400104802249030450b40c1c440302d682000c036159002100346070030300c401c62210000904600f041d2185c000c07080382c884404010440d0110100014011a0154100c0b0200c1410820444600ea10603a070110340340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 973079082 1250 973077832 973077857
    0x9110406080a15090e060a2708030604090816030801050a03020a090231080705041104060c0501110d020721020304060f030905060f01051806030a030c020f04140a0608011e092301020307 81
    0x23115170081d0540b2903a80c0c582e0400f00ea141c854440d44000c0c100d81d400703581c0f4020000020002e201409007541081c030381800040e043e282c040c0c05004180c01c00ca214030600341c41040103a80304030400c41501c01c1c218002d610b440c0c45100041704d9075443c40f528481604034818982c0d2a22980010f4800c94003013008842015503924140403c071002101200e46900040005200080c010005490302d01d104e0307000040d0300d04244121020035003000d030b40560090b4001030340c40180b01c0c1680b50319a052210800042e070540c2c3d5100080c0d5603108a106460600424041d24501c1d14003d0340f1103140d0581000a842e00c524084c2080f02c0310150034042c4d64403e00031032405280442482000c24821500034000701240b0015032005c2e91101052081281c0c0400c090340d00305850380302c5000d16200d070f0004a450b06801d0908640c40e00c20740b01c8a40114038a40e01d40100401d41b81c2061240c8404840043d0000803e02050b040031280c0060003086014500c40c0e40081644c2d88074154003d602c540e8269030352002c014034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 973080332 1250 973079082 973079111
    0x70213060b0a1d090106080402060f0307120e030a0206070315091b080c07031d0a0b0d0f0b030c03280f141603020f09090f10020409110406080a15090e060a 68
    0x3e02c00016040854180103104440c01038075816080390000300406e05046a031026202c0320b034801c584003000100700300040c084100c40b900032840042206400366080405402c0001d54844000b00128201600d4900840c44c0100b031680c118090050100c081c0301c0081c401510001076101c0111840c00a0030840004504a00d00402d48240980c140d030b81102c1220349403010880f181d07002121950260f4040b6002a900030104001c005c0341082c4900410f4503002490a001160b4030019024040d801c24840c583e20f0350340114808010005c000007a030780c4c2404101c80c00864107241d01d801003141031089910800e001c800c0c01c441204120040444000b444d01041419195075940b0009400000c0c0c462070001c0d610f09900c01b180c1c030991b041e0884120340c01942c0d041c0d280601056403107202aa002800b841208000d005900302a10040c002601d0286418001010032800921051041d641d903844001c0080b9101d52040c0108115401404840c01c180003071915614240d450a10b240c1c42c3c10640180c804 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 973081582 1250 973080332 973080377
    0x10608060604030b0601030f0e060702100203010609062d020304030b0c0f0f1803121309060503060606070312020d1410030302060a0b01090305030a09180905070b070213060b0a 77
    0x100078110908040c5156501c5480d10005042c6605040d02d44601808545a41c810642e0034803444000b081e444c03c1400000e81441080d070702544c14140100700511800d900309400000711042403500d907100702d844400450103001494410070a88030803107100142d0990000180081d40d00500300301d0555210701c1d40d03060052154841000b00501d040c800c0621080030342d00640071950880382290664410703e00068144116117607a000c1c01e08000c24a04401c400c105200400352990f8141008450b08100000c0e59030741c401494180311380000220502014800e400103051084162025519200001c8000c000b030002400a101c41e68007000015021807650003280703003241d8041d0050304158541c902c06c0701c0540006021141070007011240080026070400080c14003881c43d40e00c003200303c1d040542c24801009002d402001c15800c00d68000c02150f8042030030700490340b901100726910f58191012401c2000d0610300c0d00c10310352402c1030010f610440d0800030002a6607603075031111034400b0010f1012a00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 973082832 1250 973081582 973081591
    0xf060f0a0206071b1707020a08031c060305062a0301062c090103030305090f03030901141e0606181002010b030601120f02131b0e040c05041215110a05030609010608 72
    0x45120242c000491040f0114040d0300005d043e07400d19050041e0046520310705103901907095540002150070032200500c0040180782c1d00c3d42d009021107860342d210b0304e5880202800b010740740e18110129010740b00c0c02d131000c1500d80c0006e40200b9180d6039555009400081c1a44441c040c2468150290308007002c42c00500c0c0b070481d0007c1540c092a400e6840803401800010300b03c0402e0322442600b0705607840b04001542c42840400000f0400400303510803000c007408040e01d1501141001d45a0b034012441c2107100c19448841030710007503101c0f59039105000152f0340001c0c0f856000019801d0900c202035040d00040fa051800ba000c60300c17241d907904081f0b42601c44000d000b81202112040c44001403501020b6400001001d91001c1910b041c24043e0001030510089214040380b14856513a45605050150f210944007030b0904a0034246404003e110807080c000c0020710309910410691601e207400e44c0b007460100c1074104281d07103a4001000281c00b9602c242e40591050303044400001d900c40c8a130001c50310a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 973084082 1250 973082832 973082867
    0x515040510052214030408210408120901030605180a05090d09090908040e01060818070b07030c021206090307110a060e01110c131a030115140f060f0a020607 69
    0x142015000308140c0d05030070202c2212109200b00ca013002d00c181c100080c0001c0e0080202500d11484003c580c0404502d120141d0700b0126001d000400141d8404205560402540100241e6032600080100d00038821a00500d85c4200a00307842c8040e0300321403842d58481c529a4074204480c1e1592001d466031844540109000100700003000c3c480d00b000358011580d0705105103101400c09032545220790070306400360480b2000442c0300040041e940c1090081071042e040000141a0b07079424aa80940144140e100240511400c61a07030411501c48182d864505140e0005803003440c1041600c141c0c80f43d001107020b5035a00040342240c81c1510b004500c0800302c5450344c80d04c00c505e5a000780152400000301d44540110302a0752290034a984075a403034401c2c0070f03121b40d60005040044d82004014001075809a500030fa15004560160314003000c00c005c01da80505066065024400000810855082036056003250010523081408819000505005101c075000da0352640d0750010226803c4103600c518101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 973085332 1250 973084082 973084111
    0x30a0c03141512011401090e120f031b0702040c05090a24181e06090e060d080306240909060105070305030103080a1e1d010306080721051504051005 65
    0x442c1d18003480140102030401001140030300780d8217140040e4482c01d078000300500b5100e03500c0700c81045003070140c1e002803400e02c0001801c0c829000c004042501000b440041c0000c81d0158104868862000342c5405642c02001809a015201d00c010040e411081505d40100c00c0c0c1400883c0104520030304480312040000400c40c0d45403003403001c0b54400c444031180302c240042c0450106800b855035040c0740c0903200c500c05400290f468118028003001032a030140c102c01c44800700b40100c982d03400b0030416801340c102d905103403251035100011751641c62035110502ca108440706461030441401c0050641c848080f104040310390b94060044d40c0324400c621006000440800040c0b0006810002802420f000c1d403829140a00000a04440400e4803485140124900c200c0348103200702f0719a24016001030030320b0203200c0e003842c0007400e03941d883d01340c01800612102101a440e00f0300310211007607040d40c1c000003250382c124048000a0030491090394240d17414010301921040245090054900a4007243c00040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 973086582 1250 973085332 973085371
    0x40510181a0a02130b0304030f140a0c1e060e33040507151116080a170d110310080a120e21101a0a050105030a02040308030a0c0314 58
    0x441c0c60400902c0e44040a40c00e0011450043c00d03e0440f0014041701c4a00ca5a80c2c101400c0240020402e07034644810040c4004803c0002c54020b0140e8802d03490b0f50812025001a40c90300c0204002040940c8038071036800c85400d01400269041000b4940140c0152801d00d405807005c106a950841c4804d0320823208503050400d03d01c80341d820369500c54000c9003030f40d9403280c40701d44110a8580c0f001008000949829240c5003400341800021901da070b48201c9019924070305543e2584441d003080018000c0c2c2e2108040540b0301d040306d4201c4402e40401d2004201c0c1840e00c0307101181507001680d29078860440d0420104001c0c0b000104400440d4000305500c8070003c08041c1124000513141101e5044034046608000000e0710040c60100d0040c0ca001030003800c06c95a00e01c07400c4406c041000203240e040c001001000752224900070069650a2900036580d68480d018203000e88150381c8010020580041084984580e80d40a404004032a55061000700801e540c07940564206403820b01c4112075820514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 973087832 1250 973086582 973086623
    0x190b1f120e0304091a011b050c090406020306100201051b0f0d11040f0608010f090e010b1305070f02030f03010b0a1b0605100915180b2112250206090904051018 70
    0xd003a0340300d10308032840c0c0e281c0b27180071400340c0005803030484440b0340100038400a490580d203000400007152000300524504609040144050f640c98614209800569038030202648003c44107a82111380c01840980007180c000c03102c0b98841d200b5000c008250031400b00d200783c400c0444504950003030280d00311682c100304008c0010020100c0c0488250758543e2041c826807507080040b411f0f1100b062000406203071400024007a10030f4440300900315081084061480c14a0105481c1501e480c1e0344c6c120303110340b4900e400b5610110706000200340f03030741e2503c045c0c01040f649400640c401c240b214035008000c0e903078140c000e055501005a44803c41c039120402e1019401e5054040c0c00c0700c800c80404200c001d4402c000c24a061041c840c3c100c03600421106034040000c04100c29403d0f41918001c092511070001802910004000c40402c64003c1c0340c2c02d400c0542d43d0b6501643c1044030010650920340c1440e207407880e59044800034441146007841505243c2400301c000b004040e5401c4015040c10200c0034022 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 973089082 1250 973087832 973087877
    0x91227010504050306040b0117120313020a0b0c0a032a0f03031808090406060f0818070b0a080f07230d020c0105040803190b1f120e0304091a01 63
    0x50504210042c0400100e640e001c2100500507805074011003042c2d4100030f0615204040c3c800c403400654088441005001c40031800c5950110800c0900703100b0000c42e00c0051203181260784004094040412a2000c200020800341d103030a200745c4501213176602780e068140c0104c0b143c91040e402a011040484c0124940807000e41204d48286800261001605416002040c550009445151003c14248450708203440b650b4081d210750b0529041c100b120350402420a0f5004142140309030500085812000040100038003900b0b09492a0341c4940401a00030043c520445401d1f036404c01807000b041c1440d005261400c100d00010100706005103040e03443d004240d002d01d07051440503500300302d02ea913080c000380710f00c074021889a42482d0340ca05103008003c506000e0041864140c17494100c918941d59100c42c4003c441d001c04005c0c15854040d441d03011740d0303c00c1d168071010381c07614201424000101c6010004100ba1244908200000c440d88041c0c00d4250422001450220720412803411b1100c551044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 973090332 1250 973089082 973089157
    0x106120614091815010b070b090601050603011e180203090d080c03070e010c020d1a0c0f041703070b04061b030e070b1b1c081f03060e010f050f0912 65
    0x46030140d40e04ca420302c00000d142640300c041c6590300460180c040002c80381205402101850013041d140d411f10001642074801071058020384c255034a40c007034100f1180d00768400101180c00f0444100051401c0000103513004403480a0725015006040a460f40203880c00341c05a065135082d40d0a42c0d48001007600c03a1319640071680e042c00841c1050100594a1481380d5a11612070142440022114042d64010302c00280082033f00c60750038080c1460f501c1084080d5000c9a0010903d00368807a031885031542148114107029007003036030300020007041c0314458122400b00e26904500c10321854440b03008604680c1800035082c9641c00c9a00204000c030744000260020031540b07601e0703104c400c4094180e42d14088110b000c452400c3c28038a845901c0036000b94100e980070501d5030010b1010310b200c01c040403030700c00b80380401004940d135035680030f06e1810250700c00d071000381f070320350040201d4201020304004154084514001d01d116051488140007e40000e44424582c0080031440d08140160030307003402d8800c0308 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 973091582 1250 973090332 973090381
    0x11707030b0117180708030a02030d0906060e100f0902090603011502034509040605070e0607030e100309020904170715150902090f090c0f03010612061409 68
    0x3a03e94842982d2070425034001c040755540c0908494401003603a081c02120f41c4030381100d8005000703505540d50003004441e001c0c0800710000805c1d0f5801d1034040000c203229007040c0d000300816030400c110f01d24a4413840054907454200c078110543c1c0c40040320141c0c410f180455801000503c010000f2110164542c004202c0070b00540f401e002a8010303001040440d01000c10208141014010384181d14000303900c60114041015082e003400e003004a4007051010300001c00312582e400c00156554440c50302d4032450310004002540e00c012904004213824898840544078003520f0611141c154046e201d2504001e0740a45444215aa10344038000d08100422070314125200410603900000c410061000d81091020000140d0451601c244101d1800303035045180c005204002184165540c1c088503808a04100c4000c078042c0d8900b0444015400780c4503000c80310241c040004940b040c0c0183c04c040c07a110480d00108165039640824113503840d4408006900069032501003506880d82240310141e441144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 973092832 1250 973091582 973091597
    0xe0d06060503030a18050640060203040801060909050604140f240708010303140a0306050901030c03150209150f0702030a141b060a110f0709021206011707030b01 71
    0x1100800d085600210440e000101034483c56031817032180706180405060282c91050425090074601a489281241e15a08210360820340748401a10207070504403041005450f009680e9885d03c01a650783c2041c0616400c650030400042801d0f50640301e58016260071000408550b21140c480c11400e050415650003d8064020102440141006900d07856101c280311a24116840300f40c3e001c4c17a00001d800342c4200b0503c0401080071a601510040840740003a60b8141e4038030f5501310580007040030f640041d41004c05c0e640000184000d410030142101e00070700303101400503880c040601c00c0b03205078200203910110100884184101e080068282000c00d100710038580201500000d01e442d11002c0c2c03c440c44030b00d01c0c444203004807003405911131081d45040180000d00d00500040c3c4103018130046d41c410000b42c005080500041000b1a05883c000341e401e4030380d22611000c80d80040d50250580d488148801c00c045596544140d0090700d9125011040e8442a102c9800450141078404409410000407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 973094082 1250 973092832 973092839
    0x703031e02030903250f06050c0909040b0f06030a030c080304020f03010213030516081527100c0908060601030b130e030c0f150106050c070f09020c0f0705010e0d0606 73
    0x3144011406140484001e545811400c1c00c9040d070070101002c0c1d400c1e1001c40701c16184c006000c000c1003401c45a4412408111550341c164410310b01d000300074000303911100300030501045c8a03040b0a001e015000c29001000765544043c00d150b0b868003c01d1004001a070001c96240124000b00080c42e00544001d00219040b030160b000a4207a8105e2503042c18004102802001000001c21178004880c0c407103900d0000b4145041a06602c0301078052012603420a000c0015800d0706184215001140b0380b035aa8845128440e602c1170f95a03804051065905d500d40312050441500401c200411079100c10010b0000c0e5458000441c00340412340c6c41c0c107401138039484200c9825040d6000394142c1d280f08900030f50300d40c01c2c1909041d01c2c3c5414030900700c00c00d801c0b03034114180a1480003003050540d12542401c50341c03040c1d0701c01014582041c56001c1605184481b101003545440d54004050081201c411501903800c400a000c2e1981183c3c45280d0218400350800c3d5082d0400c080070f8412140035120010b540b81c0e5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 973095332 1250 973094082 973094141
    0x20315040e0d0e0f1e030102071a09070828140303131109060a1a090433060801060c14030301030b011d0603030f03132307060c08070303 60
    0x85105506000e80c202c0e0082403a00790f40005403141c0881e049540341201444180810080c10084265018041c84200300d040c0940b004d4049500c0f41d9448a10003900240400302d86100c401e068a03001344034000c0000000d030310308002414105641c0078259055800001c14060640c010950800300d130444085e4160041d40e40040c03010314401c26005441d11b04141e8580b40000c0040c80c40505180715101c100140042d0b40c5510344400c0c00d035241c9030f82400748000c5025846005001300c4c1d18581d4440e00709220701102d031410003210244c12136140700c0480c900a0100064418014038060f44001603200001080842c0c8600260504140542142d070480401a015182950720980043d01c00400d41001000309040e2840c6040342009100c11041990900d100025128401c1000140346c0120100204400c2d0026071000c080c01c541c440e1442d10b5242c0e012a41881803500c0180303260582c0a882c800003015030241000c1c9011940c45902280303060b0700d40d58103800500300c5007004005500204400d4283c5030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 973096582 1250 973095332 973095341
    0xc06010e07170708181b04240303052503020a020f0409050102030a020c0d020303010b160c0e0a05042d06020f09060403050307050c010e06030609180a1a0708060603070302031504 78
    0x203016690344e1007600c0c203e60701c41a007081210f4201d010303078402890007070341030074100707031214042d008507030100301c00030b8082500003001c0344101c0c400c2d1581050240041090f030054000d001314054540c01e462402400890320b84200b801000140c05a080002c1020040c581566140740080c0e00401c001b589101075220f903402c90b0403c50f41c101c0929800192106120f00800170490380e510984025403643d0b05140d4440c040380078170400c0e0600705800610b00300421424580103805045070280301001494410021070140c4030540e815941e03045000b4402c41d5400c0030f80200c00805500101d050300c03807803060792010b0007527010001030b4140c00780500c480c500c1d03943ea21005100441c0107000540d00c850043c184503007800c0306802407a0501c02d044042014584625042c2e9a003c11b00721141d2034031703170380b206005040b41c0c6021903800082e000710188042004500310f4844606031410b82003100c1c0eaa9080426900240b081c1d488550041c02840000d101e58400c0c1c00860b8002c8566511480d11040c0901160544 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 973097832 1250 973096582 973096591
    0x309020118090617072301020309040c0507110306060d1103190302060405250605131832180a12030504050c01031a01052a0606150c06010e0717 63
    0x441d241c1008020381e0301070740004d480d02c0388a034025020191801560b0036440c80b014250b045000c44d01070350000668000c1c0141d448500c00038006000e1100018401803503a486800101c510342e41d0200f456032607040c0080c50138410040a001d407101c5a105448000c1e00c000908003440e0305200c1d1603024890100c03105050200030b4480d40080c0303503508003481d20030704002c6248003034201c00d019828240981d030520b4445504898050030443e94407441d08180040001032500403140050b1800040388489025920200c0101c4000302040c11041d0220b1007800c01302902410311012031400c001007a02100c48444d5246211100e40440300c0c1c0001303c6e0b50340c01c1030301c01000c01840400d40d15000c20050010910880701b1601d02441c04009036010400c50030038444c0d0195100e070402402080079000b2100c000101d0403554080800381c5201180e048840e50b9491084640381c0c0254000506007002525840a80d41d0003083c1e400035206da42e0a1404020400340300030118810800310000c0d580401d11410481c2d40074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 973099082 1250 973097832 973097849
    0x70615060203121302150a050c0106081c0206010305030904020f040f0b130509090601261204031205120415021c1b141801140c0c0315160309020118 65
    0x200d08451400f00c40f003590081064806280010803240183d0b2100107030110988140312203074807607800180031180c43c040c4403150324880d17280c54400725460400050703030010380040b402001501786c071842040741c80303401c02e02c0010020b038801d00c16012a807070650050541c01c110581c2d51410140d540d200350b415540c00b80d002c40194400080c3c0051148001194003010344010766071445c2c94188002d815549200500ca54480c5180d403034040c02e148151a101002403424110486903801390190782190310f82d10620080758401621411190254010303805d5490500490303014414503036503501d820610041d60a59107801c1c541c201300c00c230b0304800e0420360400d40c50541030000561490940151141d8420721600c101804050300d080d64050700ea00040300d43c6481e954203014824001480180e89440e00d9034461500450b010840f05400e030f0700050158060300048040f640c000e401c2e103601c50204a000d40c0c2c07026042c00b1480740300075128003071b4002c140403910600d8449200030504582110740e00d82c1d900706548 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 973100332 1250 973099082 973099087
    0x207091a061305010306140f150d093203160302070b0f3402040905162c060a1520030915120f04030903020a1511010b090606070615060203 61
    0x3d156030510a0501502a203010340c142c1088910008407148021000d092241035105242c0f1601a00310069400103c100c0400384114445c2d450440c03010840c012024603c682e2240d100d0800700d1030742009650100c6480e01840c60401c040c010700b00300c0200e9180070760651050030f800180005410008000c1d4040e4101c03800d40b0780d140420b10004c81a159030a03150b0204c640b68108450750440e0b2005401d555040710005018002450400e007400c4420281210706030440ea00040d22a06660320710500c5c0a0310b034481d42c406a180f01952030b030740009880e0075801045500040c414030541c4600322400b108103042c241c0064040740b00385003002160445142d50b941001c04d604a550810b40224031410006e02001d81c1000d07400d0001d084107820042c00f0100455400d0007003028540641484d02c0036680191003103041684562071012100c420003c41e01c002590180d103410112810310409004910003061140e01e5200c000800440e40c00a02042e07070f043d40d40d10100d20300401d4044401c80182669009983c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 973101582 1250 973100332 973100339
    0x709050414162d030e0f0703120305251206053f03030703020a090b0306010c11030c040e0a0c050108010e010509130b041406070207060207091a0613 65
    0x5459031100081859400c20060149944110344050300780b82c4640781c0f025038801d1000105001060709044400c01c0001c2d0440510303000c0e8580c006010801117003048400303d01d07048403002d5440e82641f0000d403080301c64410b095030040c4a030300b060b500620110700340880210010103900000c440f080c5040003040c416002d000107030665024100c024034045900ba00b400100344000761241d58003500118014079080c1c8184c190244000c203072050448214220303500c0740b80400024000350b0011001da40802d2001320b0000304840b02108072485418181d41d0300f000d608556480c0075110342810002c60303150041d805580c010380c0345c501c22410b15201c903100508040a0a04001580511542145042044010051140e90745407104941158025902a003050f551401a5045802c568100820980002d42808103204901c010400c440d201081034448903160a84281c1c1d542159201e40000b58021401c1004801001d600842d40d0603d020801d40c03a0300b42c03050004c2d5140d03004004141200b0503504003031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 973102832 1250 973101582 973101589
    0x30902040c08041416170304030503070305040509061e0108061c08030a05090604050a14010212010806040c05040213050904080c0105090601090b0d020f2812021f09030f0c0b03070905 80
    0x1000b60126130340941034440b0041d00019002109010b0710190160f69000a0039101e010030888000b99000710950b92150694540208180d01600c0364600c02c5070070101140c9142b40c040900a020804c4544041c0c4a072403120042d01d00ca10014480e035802842e0100d07030b0504540e184014286213101d422007a40d00e00e03002044500300c0c1d13009801454254851000c00000900000e110800c1c00d40228402c40803880c942c12135806442800401c2c045818840c00011b400342001607003600861164401c141860780760310a0000300e0141c0304040304c211071200404c101d9418020040b40d001402550140d1410034021000f501b0340b541a00c050400e136010720010808080148035400781103000300c4080d1029406500001d4034907144401951140d1200001e01280301b5841318100e407006008824450f0003692400806911201d0110903802803a0006107400440385160b07075001c501a4a444048030a81103444a8035180b42d1850112540810351001091800c005406144242180da44840100341031a091 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 973104082 1250 973102832 973102853
    0x60a08010c0c0213091a0c1306120f1a12030408061006021b010215180d110d0503010803160f0f060605150c120a0903060609091403040e16030902040c0804 68
    0x1510000d5141026820014034841200c04a13640c0b010906c81b00e0b030300c0c0c0344050f20705841152011040c070009050000f40b05500002130000c001c0050300108001d0700700141c03141c25900511443c0070702c0c0441c0c15100c82540341c403020b18410b800c060011641025101c00c9101d2902406a555440d0742022042c1049030a40c104074900000d0240b0442c14092071030500007035603e1100d04508404020042d000503401e81e011080461805170300011205442e410070f074058a5480601c2d200f0700940103c1c5843d4040034003c104480c122003810004518208903441c10481d40030515104944800c410030007140400d095881c2c0b960010b01071a03000680ca80780c84100060300040c4d448401d0440c406010504032380d0800f0608800340450040003540d100d1444104840700c692541008001c02d1078850042803554071503000010f601d110303900080c4600c1c0030401e82030766805640b14076410361001d0000682c1400644600b88265400c0e810003049107681c60b400501070f541d0092100d4000340c00c40c4100000c0c440f000c4c09 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 973105332 1250 973104082 973104109
    0x4090617030f0a0518091906050d0206250c14040605011d0f031e1501060513030305070609060c0e0f0f150306130e0f0c030321060a08010c0c02 63
    0xd5107011820000c160043c0201c1e02c0103818440042400a110001031041201941005210313420b103280c01c00c003410001d0920b18440d81c11130f1a00354003098a0400160b1a100c882c0c004201e81d0070501119540c4a00c0c2e1000000a0205030090001000240011512901500c4000c11f2840b00310754000a00c0201c500c55807010f410440711040d4410400c059003607040501c4415603902a481d0a410003192400e800e5014049040410300c20066400c0c00108000071100150040c10200b84d90781c1c00211968000c0001d01018012a500d00704006400b400043c02a10b05c07031719001c1000c103019202c01c02280d240e10904000300340e4903018050f03945045100c90000e00c50441e100e0f07001e640d5800c085180484d08266103007000d200040411115070300c601d111840c1907100c200a106903511b0140c1c07142c480c0c00300114900303940705180d6009500d28000c03043d540510710904149081c000700c1041c00407a580d000d4001500603c070307003c002c02c00f4502800303081076403441500e07810703514400362044c428051003c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 973106582 1250 973105332 973105379
    0x7150c0305150405070309052a0a0b0f030a090f1203290112091506031a04030509040b04091a011703120708061305040308010e0903090a06050c0c06040906 68
    0x8003001002d079a4500c515001d4042910b000505544960b010b034014050b181c0c1c054910311503080306007003a15003d041c804601100a0720a071014075510180441c040c400c1c0141460200e042c400341807044c1c00e8034050343d44061143e4002c00e05101c540c403605070f440803032281074a0003000e8604107140b850705801007501140c1c0030200c0b04128451240301450b400c8840c0a003504010b040101c004000b9806d401c064052908141c561500f100f003031a841c00104a01d101c120396903c1107039540300c0184010f4000300d01c142c5d09520b45c1480c24528104000007000c01d403501d40e42c40f13039032609550041641c85150a4201840c0200340c050342d4140412052445c4c0d00c3c01622480d44c0c400c221003841ca41c4d2404856400017000e04101c1066182c90000481014140445a01c81442d2104102c00d00d075101c40322030704841c945a0301d6480d40d114a0714294491180400b41504844158070411500d071007403006103e42040d01c0242c0c1c000120080004100e94090781c406070031035485220902c4030311000903440003000d0248 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 973107832 1250 973106582 973106591
    0x609170a030531030f051b030403060c0c03052d0712030501140f06090d1a061e031b01020115060804020a060e01080406090215070b100608070509060c010b0607150c03 73
    0x1507020740120400d0401410804e00d8100e65001c140a030b8140c2d4071108507c42c0d80c4001e0340c4001d02e0350741e4a400911007074036150b043ca2400280ba90149204040e01905503846520b07003c551214103400420350b5164000c0c03a40c0d01542c03401d80c0705c0c0706130181c40e00a105076038031600d80700400d60040030f44a060f0040b0700c8000d903840c1d000040b030790b804913603842841d030503a01c1e541c4a441c41d00024a28024070880540011300040071243d2007a0058517080c411501103800c071480c0c64220b611040d0341400305d0032564155011060f01a8450801008003044910500c004600310710103503c40074111450394001c070040390030001030004610b405161000640070a19044403020364550008082010103080030341503e03511000507084d912003040c054201c0c2400c482e4035070795a0032440c01c680c41c03000803205480540b541706c01c0490840c2c0308803042e6010f0001691414200258502002104c4e03000c508480615941e6000b6040541c9800b000b40402d40c0c0280c055054150f4105158401c0d030300303081380700b00415203030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 973109082 1250 973107832 973107901
    0xd0b04031419030b03010b030304120302071a07031101091209030209010b0a050f0f12040807060509060603071a04080a260c060103240f060801150308070609170a0305 73
    0x52125400740909603e40892000c0018003c0780c01040608810ba0305400000390203c0c0340003d090241100d28030076400c887d08242c1d9424486401c2a40710803012010808000f1039000c2845144100041010100009001d2410781d9403c0f03250300c99804513401044010b0400c205502c0d00c800400d0040c80b100040e580380540382e42e0018054841d440e800340d0420f10100d000b010701c01d04e66080d2881580083c0d803214060901b410302da03480381c10118003102e11901301800902c0c0440d02140f628001c490107401003405c103043c00c0100c10100c1c004c0b881400904000c1c803000442070340030080e600565001b0100701000324079403103c0e9a0050b010355840c5030024403c215403484140001170441c1101d402c203808054010280d84210000c00c0280402400181065002403c0d0200c56000504940307106000f0041d80d4000020001c0805480c44082c0c01803c050003000c0110f112a0010403425100d47c2210a1000c41c156412003140c2100f02c120000a556078100170420b0200036550000541c03080c000f507144c00301f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 973110332 1250 973109082 973109107
    0xb0603010e041e1b1205060c0315150301140109060e011209060c0206090c1e0607080715051609081f060504060611060a05040c1703090d0b040314 64
    0x10622844003492a241c0004040c0701a89101903645580c1da108807411000a040c42c0d0002080c0d002c0700016140e80c2200000c01e2000c51040d6400d480d40b04000d000b007550f8520101c86a904001c02c50801900105903820a0ba90f030407080d445005581c1003219120350400341c44000000301525410b0500c4002c2c0024090180c0002480e80c440409190800801e0344503442c00c0f0190284c44001031440c0d090500c000000c0b500441e2492254102038111480600ca41c2c0803c0b40d4002500d6050200d0743e03c0e070702d21403054105070000f084e4880c000c1d0000740c5048a65a102d0480b4802c01396030315002c90341c0d4400d0010380d448418071952003000916040600710309144125407103e4480d040580070788004002e016000204e03410642c020036009000300b0407940da84030060012510700310120814001c1900144110102d072068034002d51b040b04480c0c3d036290500c1001c0021022001208015100500512001da901d540c0c032070010f140320f540c8100a034107140c90b01601812070901910400c4009009207814243e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 973111582 1250 973110332 973110337
    0xc0b03130f060207023706091e0e010b04090e1f090203070f260111030726010f030203100603050d0e0f0d03091a09130c020c0d120f030b06 61
    0x980050001d0010192031820400074820040f000b500120f80e11641448a030504140700001140c02040310504881e400c104441c1e04014000d52000c200e4006040c00702000b4140d580e0304114017107210205203511101d00d1124994240e000d500b2050700050103011105880c05000c0000e1105001440c60032542c120007c400c04c0791050410301c0960700e02a100a65400300098001043c110100400c0662900b051444032900030f503000030302408590100c001100d05210b017030b103103103c1070440c1c07429601d6044003150340c154502c011000d40300c9807422a00414070050901d500a0282201c102d00785841c0d807042c075040c28840418007280382c2c1303082c5003000850404222004072150f00d10b880610441c500d400200100700c2100d00316002032098649508240e000410707942642d21407501e0040f405039454000c1914072803095000e400c04200c0c000c008404080342c200320003034021401500c10380b006490205600700442c0d4001d50340141092600ca9000c0c0e0440356181c0c451845140a01a4040c00c10201d000303407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 973112832 1250 973111582 973111621
    0x7021c0c0609061d010f0b0d02100f090807121502030601080f0a090821010e04030c020d0c080d0c02090108030702181b0c06041a09100b011e05070c0b03 67
    0x70b840341800010460b20b548a210b007245089652180c0ca00c010700641c0c024041101017035102440c0c501408081e24000107105031183d4010000c030b07291420b42c0c0c0304540c2c004106a400e02885145000422481010300004014081090401207034025034181055188030384000500d9091040083c0700c081c2c2d0340001c825500c008066158038090b00c40c0b140207030007440b125601505120021918050300c04460601c1c134030040f807100c4070030102d0740c03584501045c1400c15035008002ca05410103403801801c0002c44121218018000619140e641e5034506007061303986c40300034000644072400c140440c5060300070607000d0180ca500940c24604180d010400340d490300e010750a46210300400180303040c1c0c4155142030424510440d019111103881d00038640e2132106803000c03070346080c8035141c020200b440007607081c0c89402c0c540002c100290703610394010f0080581812940c1004200c02c40002c1c1c50110400e0103100c0c0c1c2d031395620103070340765100e00344080030b6031049d04031102c010010414031020a500c0c0f885c20204 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 973114082 1250 973112832 973112843
    0x150108010320010e040c0e040e0705012a0b0112120318020f04020702150c070e15040c1119060e120a050a120513111009060c2907021c0c 60
    0x159107220060b03800003c0c0c040030a1740030b410040b41c5043c00e41c2c01003904104040548051000b2082c2c444426110100343c025580090180056044040f086800302e6040902d00901c8840004490306e49403200f10782608440301c421818140201041101c00900361080468a020054000c1c8201401300c0100c00043c06031140450040b503221554599048402c0b0540c010a20b45143c1d0019803000201d40150850354214002ca0700c00044107109001900d20819110a0482c0c09421540c01c200040c507080046c0d104200700398084042c0001d0401481d2007032003c2c42001180124146040d0064a06a1090004941000b4440180e0720849400c2d10f441492038141355407900d900d58811a07141822001440020703042ca004d001c1010f20b240e0030040c100c2e0080038100b450440940034044a030000910103400942c1d44042000407a200e2801400706601c0b9402c0909174110480320a00c81c400f81c800c1c4007901c800d8010500c5540e07501040050411001c0003d1410748011511001d0031030280842c01800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 973115332 1250 973114082 973114133
    0x70818120706020f12060102240105090a0b040f02031501021c08090f070603060e0901140105041a0603040804060e1203030411120a060501140406050310090305070c0e1501080103 78
    0x2c00c0450b4041c0c5505411120480e030b19520001c0400e035245c04180d501d140580140b000e40c409030806006243c5440f51080d0f0310810703503460242401703c450001400030480ba0b83c1c405d120f4581c0d1b600c900503118400800344003da240d0038030101e000c001418042c806810f41d07020001c012420304100f6500c5c5141c400360300307160304160340d0090003c4c01c0440b0082e00ca1041c3c00b6082000c1368590b0140e02810079249940403194943ea29490036030302320758040205055103002c81004010500d0a41c02c2440550b10a03800c00c0140825080400c1c290341044e602152880800b0030144502036000d1603c1079081e6044428212901e48554403d03128072028001400501410702500000c1d114200c03071074610310005086a0400020f42041e00c0104401e008450364549000c0d0014458a0540650000d5401c000c000d089809912000362009043c0103104509200c400d00410000c25500e00d80e0030000e00d01800d0000c014500b1400700d00032010144010303418000c0e60001800811180385401e01101c2c2d02215203c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 973116582 1250 973115332 973115347
    0x9020f060901050c1903031104060c060b221a03191e0804170c0109050a0b0702032d0f12190e03032d2b06090504080307081812 56
    0x3c4461140d07180b1850a4840c031803400900b4919142105045406940e00b0012281140700d070311403e04c80c030711807200040c118a002401003207059000b805c85240003000004a200d2104041f108952001b511800041e682d00d500e20340c0d20000d07511411318250403405014048103503220007031039589048014020015040891410074507580001c43d01940005405817030b00e03078410203e10180202060a80903001f001d040307803415409107002c10b0560b40c0090483c00340604105800744560040c0c08240c0e40340c840d01214404044040c059002d142c8101c0c9036251000106800c80c070325105107800201c1551b406a540012180803140542d042c0c0382c0405001c0c5003c0107444030494a490301d81c40800d61602002400810410048800c0601c1c80d05a0300005241c110700340c068640750080c292581d203001c804010b0003151034040ba004000c4000e5121000504a480c0e8582004a44007103c04030386d0414004103200c070964002040642c0f0020304c00b0141801045141e0860300d90121400385622002e02080c080d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 973117832 1250 973116582 973116587
    0x60907080c120406092913050102040504020403050f1b0d020f03010b1807020f030c0a08030709121506121101110c040e1e0d1b170309100b0409020f060901 68
    0x20750100010050000440c101400c009000706803c910407034680c001c05600340d61801c0380c6d841144400100d003114000300d548040c01c00700e00c540c184a08540d90355003008046801c0e03595201801c05940180000d02140364402c5101d890104031105050382000480c0601001c1e0b540e0240401d00d0541c165040e12101c0a9a800b103405007015110b6a82d1040c0507040c840220501c40c0f030302034447d000c00ea0031200310700e4550100f43d0f00c900c0342181644031a00041d0840c80401d10b00c000441e04108107103400c090740c41d81c8411075410384a000c20101c1d2090b100102c0105800494082c5401420000050440e0841c82d0b60790040c1d41c090344025941402410704440c00203c90a001c141c5031007001400c18400c070103200600c1c1d5240e0390b40b10361130040038039812008601c0000000f0314110f81740c500e0719005501e110701c074070b0a00d079130700800001c6605095100100824185110103140110a0100242032420041c070307410007690500040580078074074001ca900c004d82d403450032201d02400240d44059988183c0c4004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 973119082 1250 973117832 973117837
    0x180d050903070905010b04450605041d011b0e060304030e030d050c07090b010e220905032d120903130806150402130909110621090a0c0e0901060f15090e060907080c 72
    0xc1c0e520513308851002c002c0c0d10b4100360f00200324010000c20800c502002c02d880c80c5101c451401c1e0008641100040c0e26080810085800c04e0290504640000f12100000c0c901010200058005100458110000c4004002c0035002d003000c51414000310100d100000c1c020a200712103240b0500c504020042d0302041c400c0703944980d2108030400e00007408a410b10325642d60246103410400c125001c10302c903020340d8040905144003151461381380381c40362240400846040150442100303010811242c0101007040d40c5280c02021300c0c40c040d008a1a0600c820041c824100805d04d00550042012038980080050301a050315140040050808910f041c0004007140d151030366500140c0005180196803c250b542e040394100c103003201c05e410350710b103001e40d519200b280d03100a2103c001403000f401840b852000956101c0c4000c07000007000c0382e40c1d40583d0401c502d10351090505910a02d64450000c0c1d000c034452028088030454204281000c1d00401e500720801012442046801c0c000703c2d8880c03244204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 973120332 1250 973119082 973119089
    0xf07050c0f010c120e0a0b09120303131502210a05090a022b02060a02011509150302010c15050a060f0503060c04060e0105130602060609180d050903070905010b044506 73
    0x41b80c2042d0301c42004164540c418000148242404e550110700041c000003100d11032043c4202d07445003040a540c43c104085402c80fa500542d503024420f032522070040242140011007919071906c00c90800907030940842d200541311013400d0704448100c1340035071592030100c1c81d420514544541d09150011001d0028805038900035488140020080d5010341d05404c034808406100c0e2404069075500c134101c108aa180007003000d500f201903002000558058681183c0751405040c030000924804508601110b000315201d482050b91070b241408850790007003a003000b43c2400e4000709401d003400043c1e94441c0c003d502c1840204200034072014801c1c0d101c1c0056078041410020810080d60321070348080d44621007100c240d4041c004082c00a46003014064403103c8181c0b10001a00325580340181c00c491551081052903010b11030850b00040724591403084c14000c25219103226121410719078140380c1010b00e51000300700720b0b85030044414035807000c1c0102c00800b505002c0c04000780211600c41c42c050101a030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 973121582 1250 973120332 973120339
    0xa020603071403130b060a0305070306020f0f0c010f05162f0d0201020d180807231b030d023708030f06030c040c12050c040b0f07050c0f010c120e 64
    0x3091081c0a070b1030040107130420b07204514400050342c03080140180c00f0030920019120768050740c01000400c049030300400381c028217811715600d00700307400184c002c40fa400081d400c0d001307039510b00d51030340c0e20000c500c03600303401260300c486410600c071440e28001d103984940394002c414a42c44012228a08425040302d103c03400c1d4a4003503440803d03c44401034003d401003a800c1e014581020200c98020700c0b0f07850040b00e0309500088440c10690b03141c48050b00c40f21904000390034143c80c0714031071821140800014403941c4068001030018141c1c00c080c1400c049444140c4805c1d075000041e100303100f068550560400346588040792680079040b091101a246800740c0c05403072404004203200c610981181518401c0c9001c0c1d0071269210451000d1004036400c0d1044a000605601e5101007980360315007106401403c1104041d06194460844d00f14139071010100d1042e42c2e00c0002c10204000003804920082d031000c039070f40a0f81c40704a00000c0e220110292004003180d160518001c90640140d022400160019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 973122832 1250 973121582 973121587
    0xd02160204230903040506040308180a09060323060f070c060f0504030e030a0b0a020a031e061e0323030c0f0726101e05040c150507050a0206030714 65
    0x40019440d000c44045a04030b00d0b500000c0040c4084500100301c404a03200508074a103018919210b441082e0000c00e40d9951048010000e81071070b40d51407285001404442c51f0018802d8a9864564900c600b054080554101111013190880078081030199110b10130351265003181e500e0107411103091007403c6000f03000a150454007020195180d00040c80f0718440c8e12120301c9030158108250743c40c860203000500c258800d2001410080c410303000740c01d080d802402e001c52602901c5054003805102502071102d826a600d0003000a009560040300158001500101c1c0b2541941c40380e0104d410005c244605003e030890b0b1041080c90101f0880d01e501030703004143c03402e00c001c0002c1503894904904c20400d802c81860b0721210f6036280031881122071070300c0ca80282028207183c925403014000041d03060020304024080149407400c1801458401d6115070b0f40d401c045801c0c0a81135840014000507981000030900c6583d0006000150f40f412031038049640a0b1a41c0e05c0c06401c441c0300d03890f94881020071101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 973124082 1250 973122832 973122851
    0x21608030f04020406080a020907180810020a0e0d031209111201050106030e1b090612060f01030c143106080a050d030c050a0305040503190c0204061a0d02160204 71
    0x403840d01ca0150780300729000d100c01070760b6890090b030304d8840d050040c2d440b42402010900150040c4a41843c0c041003100004603140e41c0c1401d2420301c075441d00c0d4590600e80015440408640c040011240440d04541c0a1304100c0b0a8800030302a00149008070310941e52402c0070001c4c022042d0302030a451030b000b0409844280340d60300560107003000388642d2010030305111400014040101d01400040d404496500d042e81114081182150029246030382000302c0303104403400301c030701030020610400701084000200d5241d07261980010320142d125980405401000200300d95800700384450b011896091078240c0040100d1020401c210060f6000c0c0907484c1220008800354082007071648140201d040e070700345444401e41a420390b01000c50410003d0350800c0a0403425000e0351240360072031300a80c1100d00300118400400d0460303215001c0310000c99290305040045180a0183c88041e10410821808061298200d00b03498020407a954400d542c0105482084141d140400c40040741c0003401404071460 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 973125332 1250 973124082 973124101
    0x1218060d0e01050c0414010320040305062509090f0608060109200301240201060e07270e19091721070507020d020d050a032106140402160803 62
    0x1584290706415401d02c00001e0901e510003060354111401c81c240171a208500c0d10044004221440d04140c5185540ea0311400c0b071001075000c3c0c800b66100b400140401d09202600e44a004400e03000f00c011041120783c80391850303500c40342010031108007000110306c005c01021003001500094005c41250310407000005620050382d00112603048075030700c00c41400b00c0c2043c0c1c191420720003401002800c0031240b64000c01ca0b2150b0485510404841c4000a81240c948404029941045c0c60190006d58450b0803441c58583c1a43c13400004041d25041110f002d2801c0f43d444410380000340358540c801d40c6408140a00300d041d4108448050344a8003007007440080200c0c241083d0060526458410aa2000214801c0c540328010307025521a803121410100342e6420030038688a80e46040360011079005500780013600410483c282d1911a4941d030906030110120101c2c1c007904441422441c40c1403d508001e05403000206084000058038050ba1b11050b0640c12000d10800c1c9000800921001003002402e10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 973126582 1250 973125332 973125341
    0xc08061009110c2b03021314010c0807030306060e0108060a06142116110615060702060a020105040620090603041b0b040609060f081f1d010914091218060d 68
    0x40464a40341d5880c51340c0300c0031800c0380a0060600c0070325611000030302000011014401c042d0405252180b02c85d9029560b4548540203118100d011035212242807142c0d9801210b01640340c8803e10b800d18451404000059207610107101700414458403c01c0394103134104a504440540c50303050b4100d810100e41d14401c0141040440c1c400a0344c1c0030080c4018000c9102d1300c440e24048107024010000c540724450301c0123f188440080c40d81c040e904004c0c0b440141c4030741002c2c00d010900c640000030b02c1d2605003807110075250305501440505900f203240039510b09400042c2c502e0b090040d03400700e40300c0e5654640a0076140c451081e41c041044400360015411001ca0010010703580295940716000d03a540c5801c2d01c0080202c1c500310041040ca01c000303009004050501081c404031217918006071036558181548950340b240c0c4428102170b6400041c4000b80346c90250340015040f104408040c2d11701004d4064843c04500c0114045e1900010601041d00b030450440b045041c0040170903945020b10a0328100a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 973127832 1250 973126582 973126633
    0x411011b0f05100c09151704050606150c151003061103010f06020d05030c160623010803071a15090c0705010b09060f041107080301120c08061009110c 66
    0x70300c601682540e043c030060040350b000421540f151040b445c18660388400101208010100b04a90074480d5800b500b0301c012841c1c040c9028074058070203400c1c81010f0201c4122a44421540514100074108141d040000e000034469510007000040d40c82d009481021002e155001400083c149540d0380707054140c2c84011812103c105a407001c03250f580328010ba0300d4038090109080481c105100048076500c03007000412180310301810080901e0115a0303400c084031061b0381d65104005180f00560440180402154050321419000b941000c4c540d07030707030f2034a015031a1072202a40704040b00402c0c110301c100004004000742c000c08400c41460007100b20002900800401c0c0e420390b081114000150501c000c0f60760282c10040e1015000c42842c2c024800504100d40c041c0b1920724042001d10f0104000802542c00b8107808c048001e001c10503401d10010541d81d0f500501d220350014401d01040f01640d141100c102d605400020a50080040460300240a18041781900740241448560807441c400e030b17020300c0c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 973129082 1250 973127832 973127843
    0x30c060306061106060a051c0b070908010c140708210c1201050d050a0222090503091503071205060a05040f0e071202031b030109051b04110c060411011b0f 68
    0xf280e2030220031036451805075040c60700101c3c4140144094100226180b406031007841030051580c5090380c030400001d004070b540c000043e5203480b09000060007800380000d450900d03d04505104000b19180c0068490300200408640c000100304400b06a1055158403000f021102c184c25850031240101c556407090302c0e41454400003000101e045c0c98000d04070b03000d540d005001404200c1041d42480100d1110136880081800c4129568815660380d002c1d2004841c410700245444000d0f200c2400320052038200200100d000074002c1100315544107050032803e0118400204032521070a01160b0a08000e0300101d4210741040c81c020940b420769000501c8802ca68411a4a01aa1980700c2144ae4482c024000e5054100b046000803d207018500003c3c03001c002000000d50141c0740da80d041c500503400e08100300744d500441c0503900c1e034917261241a848152240702030349848240a802600d0301c200901c028540404545050711991180082604402c500d10845064210701c1c145540f01c00105a8120351 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 973130332 1250 973129082 973129097
    0xd02010c080604180b370509011820060a030902090702060613150b1603030b032b1202040b09120c010e150c010204090b120a0308070315030c06030606 66
    0x500b411301c038040400c18540c60703806502085136038580d103205018006a07403100080302002d030040c8048010024500010345c10110001c0b000c0701200c16528005c05046440e4906071110103000c02c0c0303c04c90407500f944032000030804a080309407051040d90b03c4440b5500200040340e2104400e80584c80030340c13803a0080302c0580d9642c0d506541240c1e82c41d0100c82d16a0004a940d034034040c80440754114100b00188407079150340311a294a00d0207038981085490281c420060880007044c503030140b203a04081801070f00078000b2150107415528907505c400403401041d04c00b0720b12607440d0340e20405201168255100c020740d0342d80d07501c4126400b240c2104521a120b20501c3ca075920103000c000903944001c1c0410385808102c541d019041140070b0a03000c4000d00504d0003000b44c02c84c0020300784000c10241450010028009180c0f8040c01141500074454400f19844804200b0110f03800c20f25260b4030810628000c035040020b02c1000b00c00d882e03642c2c0010070000c00c000c004240e403500741e00702c2e82c140c800d103903680c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 973131582 1250 973130332 973130341
    0x709050405011803020304050d0f02060a030c200c062101030c0f0506070b0f04020d0b0c070b15210309361306050402120f0d02240f07020f0d02010c08 66
    0x2a42c0c1e000f410300040c0540d02c100010050342c05e0003200160f0182c0a0b1010402e400c8164012520b01c2c0e01c44604400002d9841514850303407500100a502d41082042041210300031074060603580d522840b02e854800e03100420b04194502500d080300341d203401c0169044c7c24070350356031a00504c03800d414011302c0d003190034045001ca403900b0888255113100d070f0000345041140d21400454866040c012b0010b90b000800f1561480105e015030b002d69000b400709102c0140e40d50424102408040f0010f071407894141045c1d0701a10480e5039010400501e80c0211111007120040400380c1840c42c45240d1400e60061040b21261a6400901507880d0b03a0551724002c40780e44004071801c00803a2141100c00ba141260ba0a01c40400300e85950700a41c5c0c010b04c09800c445000e10003c0303001c0c2c030700f1042c0490a8403d522030072607291900d60600c002c4511040d58410441e0b80350340540c4800c0d003890020704555004a20500182ca80e43c401c004034003000c0030034010ba0b1b46401400d0340090113001c20349480c401040c03112001c00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 973132832 1250 973131582 973131611
    0x130921051804020a0c0f0c03020f06041503050603012705160f0b1e0403110f011b17070f15050c0f0403030320030903120a0606020717010e070905040501 67
    0x2100040359161462280000c070038100002900090301c0d08080040184410000070791004660112a0058060050040c40d41c070403c451071180c0903219000304424001000081403240305500103207407509000c107099030780300c000c039004000c1042c1c1001c0c1c080100d142c003591104400c0c17450403032a0046003503d289080e0700181104240544c03041c0b680b0300b14072a01c01c0000d007044070080d2080103100c01e1102903095084c0714403c07490700076400035078015500040c1d55000d0316003943c0c068075603142824004c1401c0510f0b04271300c540701210300d005400011443e0a5205c0d100c5144116611795501039074411201d01541030145d802085018581c004529180108041c0103884c03040c0c441920105024a00d0107056503812070180c551180301184030380000070000c90b00013500b00a503225088080044d80c94411801124803100d0025143c48005490a4810700c0344643c0030505205981020510342c0342240001501401400c1c0da4408035001d01075241d000c00c0c0c800c040c2c0c01c07090003180940000e201c0c0b5903144209 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 973134082 1250 973132832 973132837
    0x32806030506010620010f0623090c16080a0c02010206130b22021008090c0603010f0302060903030f0c1c18090519020705060f100608011413092105 65
    0x50402c1e40b1550040100604c1081c542e51900880c40b0703100700761151150b0481c04d68618002d6450304988420061141d942d04405501c081800200041040c0d424580840e080440140c68040300351800a8241a040001c900e03a09100e035000007440d9403011000002406541d421400301d0046c00b4842c042840180c0d000611500c03941c00403042c00050311118010140d158050341007a10405002d030b0030501580c1c4503450000c2c0b5018a886050052404e00e070500e0810100d10412071245805000611201c4804020307402503942c103950165580101d800000c0c81d501804800c4035000c900092035a5002c01c005c10603c2e4401c04480031000189080181542c000d40300000c060251400030b80100208202c540150741c0009210081030814882e0036580802c0e81d00c0b010003542ca503070251003402050040310725005d60081c03460810210746c83c10090010f02c24001072240c04028184581e03d280b4330340e10700d02d0b100300c81e5103204d204000c0503003107141100c103004148030120000441c02450042d0720b03018004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 973135332 1250 973134082 973134089
    0xd02030a0509100c1a10120c1404150b07060b0105030408030a150504060602031e160803040804121a0906390f132408090f03032806 58
    0x11440c2c2000395680a0101042c00d5411241c20025000090b5002c20800000b0805e0021100141407152411a500c0c00c901040d5501c0315828500c52100d800c0450b400541003002e40e0008810311170380c03914120000380500010080c0c084200d80f54840010850b80002c02448a984200014000304a652005680d24041154054900d01040001079040215580008201020b90882142064070740d00810b0445c1d04682012025a00020b048440c2005601d010b1078600c40c44070140d403420301c003a1001032551a2010000b002100003202040420000c2c1043d0b90150150346001d0181804a003041044282c600d41ca800c054115140411801400462550310403101e596904042150301204845c07201c88400492070b409400095001880c020680108042e0f03040412590300c6d0b2607a06d0b081800b034141d07503010040c0c9007124495111344244a1116841c1d0058071b040070b2110f0b69580d00090f081c1140e07503036403108500002041006201540068403155400b2444114480d40c2e030311903500c11a80c2600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 973136582 1250 973135332 973135337
    0xf0c0411030a0c020f03130501020c0907050f250c06170906152b1437060c0807120e120903071205060417090f04020a030905030315030d02030a 63
    0x20b40300d480036421000440407944100c1d107015214007003090454000403950010003504440810056170f040088408180d03084541002a040640010309144140e98a0055802011444d040b24003101c0c0031110f4501c106908500481401d0701e8078500310107403805103c012840c81006410005510340540d032258000c2c1c001042641c5070358a4102400400483c29603101040c4400d071a13030900360003800c0510818000b64412440400d2414001c0b28041c0007001000d41d01c1a50184180c08615140a041c605c3e602d541c41500c1c09070b0030218052100c0c440000c0d200500f01480401030300d0307010285a10403035003592000c03c80040d007480700041d01d03000d0900b100c06030311001ca299090007910005182c4000001c04030703088166103090010640740300c108140d810f40c000344200818026000c0c1d001003480d108c501a689000c01c6100040d9210000c0c00b007050140e58040f1b99910b4090003036101045c1c00b0307002422662a0300d0305c2c12078601c1840032414824024000c9403420300c0c0076030001003503440080c0282c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 973137832 1250 973136582 973136587
    0x120f041212020405040207150501080f0319090e070905030706020708150606070c300f0b0a02040803220806130b190203070c0615060c030c14030c0f0c0411 68
    0x66049071806054058480115820003000919940c3c520050020b107218414822120014007070403011241c0580c0302e003045d900042d1248115090206c2150480e0884078980c8101941140003140c0910715604540700e0a0004400e221206810071403001c1241d00441c00c40750300d40d494071000c903100c0901d44a02001c96001404020044070080c01107a40220050302403030030210280c440800d108540c1c1c0c011005032192400c0d001c2080f002011340550b100c80784090200402d06940c2e0840030554501000d07000501100c08540840415011680246007400c05c8035200c5405071840d1124104000f160f1002a504880020380504042109807080b12004400c00310780c00b69460303255491030024506140010070501000f841c44a92001d0b40c0212401e035a85030080303a15103400d5048070f440c11080704191072160b00c00c0000b5039000740d15100706a4944cc0c00b06600b00d05282410343e04061034110840c40c00045481800e1450004020540c500040102c40c1c1d601000801d000c111000c0c00d030004030f041c504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 973139082 1250 973137832 973137863
    0x110901120203090307211b0c120302011409012c06010b03180726062503020c0a0524060f060f0922111635120f04 50
    0x1907409194400060019a458119542c3d070f80416110003207214405074034034482a1122503030100c0c0750506200e102c051078004a6094403003104420040c82500d80d0000039103581401c140c403c0d01f160301142451480400f42d0304204540d603020700040c200c20b5030900740001074141291002c0c00340743c020003485e1010305040c3e400e041001c441544010608200700d9401c40c9550169482003000c000244042c8503043c2d40c0300342160613031440d1601e60703060421545c0108244504400012402002d685101e400745003030044250041e00a03020f80b440000243c024844001c1c1400030208510380f000c1c0c0d07c80c50850000700d00c80641e66100b08103030b90f07441d041260380c4491070b09030802d14010b15811134a40b5070b40e82010488800107945200c0e03256580c0e203602c4450b081c21602180b03401010001403007151401d08098944110589100701220301070082a603040594400c11401000e841e00d18046200800401c0381d5041181416880460fa0181811b91140000ea5142c0310407421400b0f180c0c00200346030745041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 973140332 1250 973139082 973139117
    0x1e06130c1b030203031504090c0504050601030b0307030b040302060606040602070e0402060d0e010603020f06041202151b01050f151f140d1b02010c050301030807050a1410110901 78
    0xc06005400c24000c20940110001c041e4030381424100744658004e5660f443c2032000081c5036540b1001c0140254100002c41001030010f01717502c3d080c0da1064400040541e5050012405080d9410041e40c05025136032000c024000c10000c614403881c066000c0714142e0b10b0700001d0142c548110700c070300c50050f00000814008004400b0383c164001c0d00081101c0d080a58184c3c11504454403030794641201c1e9034564003003046003032411000403030010072a5980e00b00b510b05901d0306181c00708003a009100700100308008454103101300941f1041c42c03540e1324403423402d440381043d01d00910701502d101e00005010b40c00035480c01c0c2900516042d020010b04210003034807040c61010b51401c4007001d000c1c14401c0c2810b02e070a000f04a107000d02000360b10355001103401604800120400b0000c030340040c0869052801e4040c1c0160854220780c112988151a180e460300c060610600701902040018a17020640a40c608007210001e01d24101100442e02040384400e1200314658510861500302e0225503150b000180c0c0d4130 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 973141582 1250 973140332 973140341
    0x130f061e0c03020114010603051008031309050621070e062407020f0405070f080114010507030c0302030702030604150b030c1e0420030739081b061e0613 67
    0x51190002060080d52401094400741c5c01b41c0004000959900c104410080180487d00040444101031850f22020480c1c842c514411805803551164032031000c140c00d51101c0040000c1c0c01d60300003491421a807004c1e001038407030039140721300da43d9a02c500c4003080091030b201903900c085051181101c00c510b804580c095031150000e0030f003a80d024010301c821140944841c01640d01c649490b6441c9090b2021106020b812500180c109000c0e0101c1700c0500781507642c11000320303140183c250800c00310464031407604a00c0c501c1502002500f50181c0030501040003e001e0b00f0305460782c10000d003448204900d00906940703448482c0800e9022940104042441100013200b00c10b4000142c40031841c1c0c81500700c1d115420017540502c1040c441c000003003000e900d03440b03001d001c0d14145014a0806400400d00c0d8408a903d000c3c01051010202409081c00c00c03060004441880580820041620b0081c600c0c076916100202c41407451041c0f80c400c108500c111803034800d03100c0c4600401c001555240c5440f80070060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 973142832 1250 973141582 973141607
    0x10b0a061418011107030c080d030506090f1018020418021801120e070b090a0807060804120e191703120c0a2d0f09080a1103070902130f061e 62
    0x102420002c20a040c0030f210010256014070187c1010a280c56102c0d45040c1d400c0d107440c020540b0742818064640d84103051640c00801c421518113603519161031500796444207500c0131113038110f5901c150b503c82c0c0c119000341c41200c05810f48a4a0600528080300a0f88110149141d51070391014000840b90b0080b4100a40fa80e84004005451410726100b545042820f03080344000d1030000c0f500107040d2800218410140140b803000d400e140745050380140a60b000548028464120b0b101c1c2c10003001d00c211400c0a003490000c1090155180040481e640c91030640602e80440c1c0700e40c100c040a1580000c129406400031111140b6070b40d48050700380c40c540e080000000200004948202d02006200303051801044203017005c4d032600b61090b0405001903210700b02d10030507c03801070810440140f003c19076400d0190814038038094900c803100003a041c00c2c880e81110801c60310201c0d18100e0034103a981e41c4001c0c0e520032402c8649042c0c5030350045e900c0300c20044240b81c1c1ca0b8414540c80000d24400c40075495903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 973144082 1250 973142832 973142837
    0xc210405061303060510080607030c0539030307090317040b04062613020103050711061e0a05010b1e160f050607141801020a05010e010b0a06141801 65
    0x415848200180c01c90340400c00708114400700d404144140500342c8109a00410042c840c070801500c0c2c000d11940361680240f040781890744d40d07074204000070b0096007150300240c8824040c52180441c004481425912100b050b01f40b40200b8290001d02c203400011a4000c080c4c1d62100f0034128619135808000c01503403142072968050911000402d00c031440040c002130310103901c660085e8181e18405481d114444044840c000c0318190a201078840661a0300c0c040c0c0740c0a18000c54030399500542610300c0d1103a400d010f00144600c0e0b0400c190b401140d20003054002001254000703035140e04070720b6415100d0a0013800350000007004408100d00c00303c45052a04900810303080d0410601c03500c90641e4043c070420540308081111030f468200070062240c4c1da400b188030300708848421003007601101e4078002c2c04404c5009400c502d6010000368000c1008214080d03128009105802140800d00c2c081d107103490340e85000b003150110100758540203040f1039000501d124011820100890301101d100d19a00911606 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 973145332 1250 973144082 973144087
    0x2010e121e1201050117010b071e0213020307020d020a0c1205190302030406121e1d0f0102090103050c041a0a050f1210090b0f0d080f07060c080c0c21 66
    0x15200c03800340c0b000c0502c281461002e50325000000d0802e214450a120032483c180300140116807501c82a81c0c00984c10100007240f40c42c042d0800c4040c40106000070b58020f8107024192044a00e6800440c450800c0f83d00382c2d0007234401900144da82c0c2c48402030003024005512400d0220440c42c4138024038041c0078034107c501c07050074140382006145001c00305a0050700001014010240c0100c41c07000d1a0382114420000c042c00d031588041c02800c003081d81c120198441903854042c249041e983d50011400b102924441041003403414001c1d444582301a012908100000700c0c00020101650100e40e90058041010f4076101022041d645c00a440710061042c00d102d140702020584010f800c041d20b41018502e141d041001c410b41900500754011491642000203941e40750b02c03102415821f090054401c90039805940c41e00f031030715024440301c0070702c441070214906041c013480d500320b42030082c00b80d220f80b0a591140e505a030414070403800410480d03480303140001400c500e0321485d0f04940401d91000790 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 973146582 1250 973145332 973145377
    0xd0807060b06041502030406200307060e010f14100f1827050f010e010e030f0c01091a07122a09090f0f0b06121b070204020a0512060102010e12 63
    0x340d002040c18244c0c3c016800400e0922850350010605609001101100403602000e50549641c80c454100028800c07a11054030342c01181c025000f20703034111080c0300c0074004c0c00310f26050030b224110704a40c0000014071005000a8240d00c000160302640d4829010060f003109140c56400501441c04c018542c42114841c0c138048005101024100e0a108801803c16800401c0c02e0f42e0a50716030030304506407030f49081e8445080e82000000c0780c09288445850f55221107018941500511005034050594200207102d1001041c0c140035031445044141c4039169036400304070709202202c01c2d100480c0d901100780890701d01c40f4409002268580d140f146000b081b515146d05d030341410340b00f400c40388441a40c1c49050410305150f86002e400324030303081528030a04120401144010040d806090880c8442d00ca881492050800d00c0c00c40b20515000b80040d0741d140c0f04035600501c607034080c0030004065420040861807640c418011488244074100003480704000c4075161a003d5804140c510004040020080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 973147832 1250 973146582 973146599
    0x503150612040204050f0105010e010c060204090c031b0512011a0d0e070611061e0c0d021603090518060603061c0b090f0a12080a1107200d0807060b0604 67
    0x70112001d0440d0081000c0c100741c0705202c20340380058000720b90100c03420014003890760b1001441c00008401d00c0c000c5554202410420000d120f65044440c0300303401d01c601c0891481d0135801c05948024000344542c8407554080b011101801040d8400719070841c075500400800307681615003282d43d1039008009190000309242d040803031b0b5007040c100310660418001040306941080028690300a40405801d9a1602d40009640100100110100d8410389408604038019000945209a003641c0c0304560f41d40314070400707841c012940081200011107640707010803075041c01e0341c1d00401d0000f40400013200d5115003040009941009081c40d81003a411040070300308082d49408282014010154640c02e800c105022a041003a040f46042d060f81c03002d840c2c030000866889440100c1c01481c500300e00d00e5150123a810001d0320481d0245140048041440c00c10b0000004010707480d0200e808416800100c00003d02800c62402580640b03000002d0003402d012458681280114000041c5400e2415483d8000d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 973149082 1250 973147832 973147837
    0x160620100f0605031f0c0e0306041202070b0c0619111606200301030b060607020603040605040515090f0f070b07060b04060b280203040e0705091f030e120f04030305031506 75
    0x4072034540b05c0c0310f42000e61001203105071140b10f5074a2500c03c207030300d142102103941c9100c058030080030342036403500909015200340140e00c040c0c04032151495541800f40d400c65558001510ba0030801e0f40d40342015113000440784140040c03440c0c00030203981810346242601480c40d4a0405c19100300c4e44500301003040040015100406210076600c0a0300c1e9410f5040000c40d100c0b000344407a000b401d08102190150b5140130030f40f07900a62203000403e0f00d5446161590510f80003c07000c6d121040544140078501c031000c80c0a002c00c0949004070788240c01120030b0669075084920900003c44000c200610201e0755a41103805100340203403000c54829500e4440340d40681c01600100701c01e03c240020440018408581020f0303450281c8003c40c182418122400001c083c080c1400041c0a0b0008800840e61580c40042084c00e00d021044000644d200c54007401402d40b96650202038000d06000c0301c00b1214003800d442c181004055040e0903e03086903016140da6002070b000341d103120300d0103000f5031041e80c0f413000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 973150332 1250 973149082 973149103
    0xc050d1b030309410d090b031018020304050f060606030a020a02010605031005040c141309030c060516021504121803060618060e15060f070203160620100f060503 71
    0x2c0c0342191301d0f080c15884102d40d83c099032410150021030564404543c0007003084280c400c01460340d43c0d680c1322030140e071948110300d80c40180d015101c2d1a816a4290059000d544120301640a0700c5c6a0501c4041554943c1011a030013903200c041840403132030101c80355000c5d03c80fa590500000a500f600d1f01c5c0002d142480c02c01016645c151a00d0402042044543c14400141440140c0c0f41048001e080013841042e6081000040d0690303c0b00d50ba418148126240803c43c1d0301303c00304203d6410002c0d00307100392110810418000d440f42070401c4601c0d00d11000704600c0b652b0401070349452910040021621000c1070350f503801407150b043e04040003003121840303641c00409c0e111446a0741880ea143d401420790710b85a00420311009400108444c010a08445a003940411103e0756514001b888910312103004000d0040d405100d02c02c01c610f040c4032440102e078142e41540c0c492600f200c128041c04030300402c0d141c912901d160042141080541440d802108400003207100115900340c030307040030910340f030000351 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 973151582 1250 973150332 973150403
    0x30228121a1f020d0f0f0e0a051c0606062a1115030f06122e06080303060f030706091203030609140414011a0f030f0d0c050d1b030309 59
    0xc855050303690100704c0c045141d030f001e0a24012501c100034001d0400c04a0110540170b1020705121440107070356446e0f0841c041d003001040d1300404007120b1041030702198449001ca4965241c281d01240f034a004003071800284441c04c07040344014840c24905500301c03021000441c0c0b0a03441c51001c80c040c1d51000c40c11840c00c0394201e096a220f24205600e0000c4c110003034040c90007146043d244903180803004ca4880c04440c1c2180e0340c0381007070700703000d03c452003d501d006450705155140540c040f6100c400840294041c3c46d044540756000c0000008164485c2c24a01c1442c010503181041004240c54100e42620243e0081c20005000381e82c80e00a07101761450040c1080c078412008082108200340400c404a00000c180000c00200d5103c000340015407640e2a10640705100e0100760820344c1e0b17400c100e084d148001301c400362402c1d0400014040c04000103030404641c24041e0098000c002882070300340383d940002c003d6145a901c60700b501e0650040102160644403409400d00540180700803913804000c604032030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 973152832 1250 973151582 973151629
    0x16060c080a1103013002120c091b0714010f15030201120507080a0b03101407080c1201030b04051903050406030e030c03040b0c1c030228121a 62
    0x4031080742202d10801c940b2541c1d40e0140014466840c00003504485074031041200c00044000c20749030a8076055444000f503106c16401000c201d09940070503074000b2984151600c5525440e0710f02c0402081d404908a403003071402c02d1003801c000c01c4411504c0c403c01103099000140441c084049202501c0050500e100d0108141c0c2c1e0800c1156030004940701d0303113140001c0412482c00e005000510040000c2c02d030f2051303141c032007000409030b5900303104000c41c2d58490441045520242c20000381e034000e00300c4420011074035a9001034030005641c5c08440d603103c10490802e50781c0e0300750746d5400600900517100f5207861042c1a1965980007524900702c44482c041e458654855243c44070081c259501a106034245401c01d11185050941c0041983c003a1450f41c0f04e507540b03500801072941d14001500e54440034200d40f15103400c03145900343d0b00034034a50700341401302c103d03850408082c003d0a172203003034003140050143d8145051008880d441680282d0590400101c19124000024124404000c10b540d00c4503c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 973154082 1250 973152832 973152841
    0xb0901181a03010311030312071d040204231002030d0c09090903020105040b06040e150a0e0313050a060807021f0f0c0e090f0705370201020c010b01051c0216060c08 72
    0x19030340d200c0076610302100258589238203000381040d000d201408100c140f000c4186005d190104c0140c0050a4101c080d0045440365a11400180c1c50702a10b01c248121600c80b4041c00000c1c00c20503035210454070765400a501d4100080f500400808030003941908119032042e020842c95554003400743da0300d0190780046220f00b09414136007078041e405042c1500c2945841400074800c0350100c2c50b0001c0341e8840b55410003075954003503440041d0465031000b03405404000307811601441080c00c20310a503003054803a03011164440c0c03025030303424400760b40740300250b4084041c01c1c55000120303100d00c441c984030010201e000c00d84203003103006072002c0300340d00d2000c03500090300d110150410100280d4003d000241c1910326040c0410050310310f1080030400d00102103004841d40300d01102c0a2020b0040c802210804603510094800900030341040401003429400c0508900b203540c403600903680240100e480c50990000000000070003540071004500804a1f40f051a030003090441c854043d8408183d12500034a240c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 973155332 1250 973154082 973154093
    0x3050a030902060c0d030f2c0c19061b0b0c030901090b0106030903030e0705060403021905030a0809010206100501140c10060b070c080307030f30061503060b0901181a030103 76
    0x4584031150800c1d4900180000d10758005905281c0c0360b4600008040282c035050312227030902d201009440d4000000340a124108110355980d04100c5516540d081004201101c8080c0c00300e4070f40c01d020740324609200101d499000710800554002406070000102405260740d60304083c00e00740c0c04500465566440c0500349905402000c9000c0a1130010384415030900c0300142543c02240006030060b05045150351511022001c003c0103070800030308459840c1854a480a210b40c4021a0540180a4540400d840707202c481e113680c055440c1610f410706404811f003e0200301c0d030031541d40080544942030205400501901c10031000c0c01d070340c00b080c4e0355440d154201210031201d10340c0250301603402001b0800c0417a81c050108401290640740410000d0b030245502e503821140c010b0614210b4290114454078102c10b80e0100c82103a00040284481e04508407080c0c040b14014400c4240c1c0103c01c0002d103409600c240c0d000c800c1628000041001607480d90540d800009202c42e012001201c0040107006005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 973156582 1250 973155332 973155341
    0xe0c030c01030905060f060111030415030b0d03091701111201060f020303040308060f0d08030a09020109090e07030f03050415020f01150302010e0d0606051e0f090c0703050a030902060c0d03 83
    0x6400b0b007401d019424140d960240c4d1801d00a01c200040412040401e600c2c3c0e1040300d05d408600110000c0765240c0d61100040e2060009a160000201c2d10b0504940c155013000d503080d44200d40c05880352031407035140102c1070003a00c80c0b0302141501556a80c0c00c188152102d08040c2448150f403000d1100341e50304140340a0305849142c022075003503620501c10000000c0d440044103901c800f080c0c030100e5008507000003140601c0d01d640360007050144084100404400300c0e038081c50b02d0714001d87c0d0300314a42d540c4100703643c11942c03400300d1007aa5411180017132021403000c1c64001030281c07103464a40d10b02580c8520801ca6660603208540040c1c00001c0c185451000c24001e00ca1071448200400c0c400d21700d1907001030082502400420f02594540010805102d0706900920040c5801380c100d00c10610004c041c0b880d40d030343d00300c1c0c036511442c02e50403c074140381001c0e035642d84140f46128490b880d0500300e85003a185034000881c038404060700c903544880181c41c3d950242900c021000020500c0f4401440d0250589 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 973157832 1250 973156582 973156603
    0x7090b0a1d0a0c0e040f0b01031d030702010503100e1e0c092803151d0a0b0f09160e011d160c020f0a0b0405031c0203071e05010e0c03 59
    0x84901c81e0700001040351150140c0c201041d550001071441c50701d5010f07240c2d40000591a64028a008443c60f0300514070b40081c941200d0990702001191424046019010700285030b14110f5031080c030002005500400040d82c110b40000c50f5034400700d5403028084604070b01200d10212091803074a010000035103038031110f40c10403407511210707040100d00004a5618103064600070507e0f070450460304240902c101103074020307603080800e041c01070142c200d00700c0143c0060501486005401622040020804a008600a54496119481c41c3c0f680b10358102451400342440c0310303501402c80e09002c071414130300704807004042c0255070700d101e5031400c1c01c0b01065591240c4000160340d0f010b0104000f035400e103e2180300d03030215070074076900d206d04500108801074080800c1030707080044114046141c4103618050070888404608032243d041e840f07040361442a5a100c40030000d6842030000c800050079120344c1e008228000c0241c6d05804d801e98648900355950203a00034016040180c2d00e107101c0c1418404815003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 973159082 1250 973157832 973157849
    0x904050a09050f010b1806010309050601061808010b060a0509060c0a0528030c02120106091118031216061e0c080907120b0a09021302030108071a070204051807090b0a 73
    0x181480302c0806c00104840c0000c400c840c201d1000146640e000c1c0d80040449608001202c51642c2c503110040c00349005196240f1828450640028100c001400b502503040c0c0040d14083c10310007401e8081e5181d401170401d295011606108200f000c801c04c0015603446030045006194002c0150201c0301040740758601011040e01c10030018010a42050180580d641c1c141c84054211b0459005607004100039041240c0312402d00d0303280d911042c0058054011404038004038544400360108044d6105500046c0c11061076062052001003020700200d604d07854012a030101300408000304d0880000f00382c0d138042c01150f0382c0d01c05415680741c0c403407406a03200c0210380c01416000e082002e86000100c00e08802440f000e013400014041000682180184a0380070303241c07003450070040960001035002409445c4440c441e400c0002080100721000003071300b180385922a80b6001d1503409101c06004001d05070303482c0400c1d0710110320005d03c0402144006200c480e90010f6950884030070004035240c0ca504c01c440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 973160332 1250 973159082 973159091
    0xc02100504081b15010e090a0b36060c040614130b0d0912020304060525020901030503031b0a0f03090303060b030a02091503060a2304050c0a0201181212020904050a09050f01 76
    0x160f00d134002030004230007604000030841680e03480706d00f9102c03086e801c1c0c070301172452605c0302e90030020b0000c0608410354101740c002a11007503a14082280c0300d1340260311542001600d22004e4954512030380d40200240b12081c90990f03c003648520070038080e40d20000b02102003550b200110002c2c440f400121143c25966440954a40b51030130400410600a00c0101e644403400101d140c43e00b035828003581001141d019201401b25030392414020340b44d400c02c440114149822006010740c0e0f51a42003103500300d03000c81d01c3d04142540e1010b030840092540660840c1032603910075001c20031201c0000603501c00d041e01207000d6550030703001007401510304130b841e18009251418010300c86165280609003040d1010400611440414048a01c0da41c0c101c461211350410f14110034040d60018010042c80c00c0c1000783c00070f00449130003c0113007020a05071500508900100034540800510401900020001480e00035003003081c4200020115503082d00e103802020b645003001b400b084003e0180c0c401c2001000000c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 973161582 1250 973160332 973160341
    0x60e0904030509012015100906080a140c1e10050702090c070c0b071a06010c0f141f091101080124110313050901090c02100504081b15010e 61
    0x144a030180001a0b4180001c0c0c00c08945c2d60115101001d910b06a81c404032803034040c1e43d00c5003401012080e030f000281c03c801d4003000b2440308101d0155504803951382c00104003a45894840030183c5903848046038660003018151441560385200300e214800d001c50301d0a92217803410701041090786002424100303200c005d000d041c0240c0e44503404558020844418565680c40900c0e00300c24006480e0092081260041240d0081c041e2003d248a00170b1240c00c06204070740c5600006407103280000c6401020242c807521040c00007546408542c40c0341040000f04c600c0710007200e040c42003004202c204203940716900c2c8880414014260010000320f4000e0810301c00b103505091000c041410400e03047e6007501d401d2900b01002c18820103844110811010540752034415039124881c0240042c46070300c1c440c031041c0001240c1e5444601c00c95a83e41e203150001c044d031014060032103020303100050080e034040c4020b000c2c9135044118401c0c6000d4400c0140c1c00f81104444880da2102d0025041c0c0014048041810810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 973162832 1250 973161582 973161587
    0x1f0206070912060e0c06030a150504180609170a02031918120503090603150a08120a08130c0b030115021b0f040e010f060501080f06030c150f13060e090403 68
    0x1c980036500b0140101350003001c0200f680c6001449180160049800810460701000d140e101c60070f1003002d00c5001e42c1042d541c508000a071241612000051040410030600007103040c1c1c07108201038451000941910201d40120000d600940c200d000035070400610b8200440118004c210b020300c007820b00081402544003e0784415829000710320000b5102c0e80d80c8400d0280070800d9801d1060300500341d0380c2d20f15254002e00000c04a11031018000e02d404100450181c1000c1000780885010108090a0214818085902a1019106072146100c00c1515004240c80d10410000384ca40b20144170341d80c0d454100c60b00c2074034083e030f000c0b01d0440d0003400d60201d0340508100031002440040300c0340080c0281040000d0300800a01d45000519881c1042c10700c5502602d03001903044680c00d8844200c0c60b6030f4040c40c0c3c582c4580c210741260341038004a18545c10b515015203803900740f600a02d500390600c40301c40c1c3d1001c07a952140e0b0300c000340b4280f58001008090707403104142042c0c0b102540c40580c2e508055401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 973164082 1250 973162832 973162859
    0xa17070512010b0a1d190f051017010504080f09010905040c02031b0a0c1a09030d0e03070509060a0608042a05091e06040507030e011806050907080616050403021f02060709 75
    0xe446e8135080d0402c640302040d41ca40080122440044081015040c03072210b202241d941803081c400c008c51099429001c1e92018418241b00c3d5400c10802c2d4540100310b003c500c0345504c0340b501130381803007407110010500b0b45551150445603132040d001190b40300300c030b52844034003100e8119260105610000e1f504d0006280f695550007107980b59280400c1600881e00c6140d42405140d45d143d401d480b40320500d1680d281c2c41041f8140441d03094056410b400d40303510603c0300001c01110030b00d801c040d0088003000704ca482010102d50041c0501c070795404074002d515110101c02d1070807105800307441140d0b00900947c9010b0088580104603c280e00b0910140b03940d0400241c80010b095501c00d680d19000140d0303982c00703508050100c043d03243c02044206c0680b504e2624008920000351a2145000b0014021003c001010400d4610b010f004054643d24440007100c1c00c1c0130200b0f01010800c0c24000000182c42d000b10310005d40003010901d0040c0c040001e8000c0c5000c10040c00c207420400d000800700120b44101d00c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 973165332 1250 973164082 973164091
    0x3020a03030c0309051006030b0c040f0e060406030c090522050d030c05040f080318030d021f110c030306010f0e0d1403040314070303021005060a17070512010b0a1d 72
    0xa0215102e128160158003c00d84004040c0046c0107450854030301054585c050781c19030744180d00010241c0c880f07407034280c901d0190b80074002d8600183e64040c0f15419080907140d5000d04010404103a69499640c2c50341600d190364041c2c15141d0b00d400900c1344440c1c0d940c240204515109602081081d21a1186030340d61668031103040915640e801690303025807046c021900942034940d003100c4991341d1030062a59035031096000145106c15454544254600440c0d102446175565004040308080c0c280082090700120207048101c0384c1c1d40107a8080d002c40c0d41c001c3c111001c080409107849140a000160100007540b0380e220400240f1112904540d648003049040070fa0468003220441c0d0b92501c20900e58807840d00040d000c0c801c001c01c43c903044000040d000f01502d00c81e50075103940c0308000d40d0f03100030b80b60705aa205901c05154103003401100c00001840b004a146081207031903050340e400119044079054500700306240d440342e11700080c2d0b0401d6070080d0700910160b6100c140c0e849a11008440e203032030190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 973166582 1250 973165332 973165337
    0xc0b070218070c17040303022d010903170f040804151103030a0608122104062301170a0b040204111e04091b021c050c0304180b060703020a03 62
    0x96058150344414010014031140124201c0c52400e000501502d5441d40322000c540c080d100c4c0c0003131068556110240c1c0c04503540343d001410740c01002900300303c0d010015208014680c0202c1c85594000c038003405030840090117901da0f5030341460389503007110040c1d03002441c104170350307602109010004401c1e20844040311a81e9444a140001c4014211340c45082166240c044d07100100c20320074010440d80c0304404581e0a6400c60704e10942440d4a85482d004100e8085c016441041c0c0e00c14000d9601c40c9070961140c0315450005456240200416466a03040c208500c04600140180504a03041100300602d03ca003000405402108d40e80702205039400510090080b40c0361508102d60f5500f00b0150391050b612404121050b200d940006241078200d0b21a80e600c080c14940040300554000002c00482e409980c05800b1480248031400303a20b2b24001003110400804001c808034001c0240040c00103042400801d180220b02001100191854488645e2184800308001c0d03000139000100f4100301603260 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 973167832 1250 973166582 973166587
    0x3030209030c0414010503190809040b1f020d0306061805060912061306051005012f160f0602070e0a05040614090d080901180201050309160803040e070302070c0b 71
    0x101c2d0520300003482d8a034000e814030004542c581c21011150341078890503003c4407111201e045a00590b051a41d001501c68141048084440d0400d40c100044c0342c04003801d450110300c00c45103514800d084008a6000580101e504202c0169040c0a02d200601c400e19182c040500c0146202520700201d20440d8480d42c800500440140c442c4c40d8408402c544501c1a40c80a2800900003120841610400c80c2c81900d410700007071010211b0021607040d41e0b4103035907007854111840071002018002c0c80d942c6643e01c125400601c2910300c10054840040c44200364000c10345e142c0b21081c0402030306a00800255009050107104070f84d0041495580440707110004074a607261401d02070001d001c440d00c0c03104a000400f041140164000810030070b00405a515010280c1c3c504448038225180791701401c00c03140c07200f40a00050342c0f09902654100c000f25003034804840d80910b0403946d1483c650b00000842d04042001c1050b81103e1091039441502402d0030b5151058566421207581454001c0e11903810f0003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 973169082 1250 973167832 973167847
    0x30b09070519231306020c01090f0504050a0b0a14131b0c11061207120e0709091506081f02030606040b180a030803060328031b0804062a0f030302 64
    0x1c1094071000031001c0d0100c1d6076981c1c890b03001d0311359030708900a06016105030b00c81c0001c03e5220340030032400c84948508501d00c16090000708005440d01800c0d4420346900c0344175030b02940d940c070040200101300115078451400e00013002d000b80c800c44500d900d00c1951606010020460f84440183e8411040323181a20382c80e4110328107030800704007010a61f904004082980c0784507080b0740c81041d0040c9115150700c060b2240401800c0300361260640f5002c40ca0304110420001c910a0342c108071a000e11a00c0c0d41c1e8083c52001c0d407e481116400d5000081701d0340264040b85008028804c05c081044150400b5880c1d450228003041c0248034a1240e0514003000041c800a40c9058003102494440d000301001d003242c0ea2802e00e0f03829078109544407440790151600b0602001d908002d0b40100e0b244a40c0810900d071040e840940794500250881d10a591000603001c00044960004201400c819210207007030035809028000e00c900808201b4401241004404011030a10442c4506413a81480d0142c1d0301c0e0b51 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 973170332 1250 973169082 973169117
    0x90504062d060801091a06030a140d0806030309030a0813210b07050c0a030f0512070c050f0c090606180d06090b010e010b16050f1e1513110102150403030b09070519 72
    0x2d89c0001d003520510703682d0700b101608041116581100982e407680b400f5100c58040607142e1041190155040d40511070303e000003001c0304060112800c207020342c010b903665180c4050602c1c8882c094045041c1c0742e11a00c190410504901940e040026458050305002201d0b0801d5a20300325200081d0030701003004690300c1072900c100704840f20301c3d04080c0c01074020f0030402000791013450380b07083c122907600071100500400c10340066039a54522004028030304d00d444400520a40e5405610035507040c0300c039444840b6660b214405a80541d900c158030002e03480c200c42c1080d1134115810780040c54414480070040000541602c20744002c1d68006202c01d004030202d1420f03518101d01c5855070080ea0285030415403600c01202115805a0028000e464030310300c8142c242c45440000b01d858550410f1085d0914010550312006180b001d10113004035224035030b0703002c8130b04982e5500b01d504600003520381c1c442d0b2126041142c41d041e0802c585007003d604091089800442031458000e11400304180ca038120b40d540d05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 973171582 1250 973170332 973170343
    0x30c17011d0d0e010810092a05031b120103081803073b0c0a02010902090408091201050601120b0a0b070803180d0504090504062d060801091a0603 64
    0x200501c0c091108620000015454840301c81542c404070f102d28a600005502812200b44640e584010a81d982e60804201c84001c0a9000d4095145050710f00909810710070b0043e4034004110545405840b4544501076100b034880c6890076000600040c81864031004180c254a8190707075000e01310300d4441b11801d5204044207100410b41c1c0c0e151080c1400014090805014418010010110350700010303da00c0d2602102c0d840c02c1c600000a5010301e000801e9668888050414100a0710005c0350018441d0009084890252410b403140113002803008107601e0302000964800a85000074019032603e00c0004c0d20701219102865460341e01c8540f2405690f8a4cd00300b070f03014000da80c00703a548902c0315040800701e5800c211000c0e130a0203003610080c3ca406c01c3c000f940300712001040ea02c46203070504026a0201502020b0300441e038041d00d940c0e05014402c60f070100e400088850586046900188040050607074140f13501c00c0e186a4500417602e07000c6455001401c13541c08608001c4d0803561210b00c0802d00c0d11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 973172832 1250 973171582 973171601
    0x21506060319090b1f080703030804022d010306060e0a0501080603030705011a0306010f030c15030b04091208010f030b0105041104030b0c031611101a040c110115030c1701 75
    0x380f03400900d10070002107156444c064000000080c80481c3c0507207088800941500902840d07178001c210800001307110f4500b0b1940705201a01c00321403185545581c5041c209021400c0006040e0110341c100700d0b5a04d0321805000b00020b141c0060102c80304008075550000b2401400e040050711400918151000c2048610480e4090001c03c456115030040000c2c08142407a903130310034007440c1d00000311032032000440019240c00000451300245006003400724410044210801d1545403151030411350b90b05e00c603140120317025400c00100848800d0000b05100c1c0140c1200f11f17907040c40c44007800420400303a10070b4191901900d00056000c5c15054071040783c0140d50004041d00000c50810484107498000356005462850062982c4803030088140e5242d0800244268030b903101c0403c6d920399849a40000c80300c082286480c040101140011909603410291804007040451307200c4404000244200703000d541992002821345400c4d507407490131100c041c3c484c2c00101c042d01c8948101c803110a60059005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 973174082 1250 973172832 973172881
    0x1318051f0c05030615220905010b120a090c0e090312070822050102040e070c0b090303070806011214130b060d0f02060a03020f0d1b02062a0705070807150215060603 72
    0x2030f0803c000c2c4030440c806c40c020700c5005030920000241220021046d0340c00c2d0244c40c00d88400564650b10054010219000d05841000d0391580c001420260080b105e401459000043c40e41c030180c90543c01001040a055001000901c104200462a9081545e56141d414030458040750846003841401b900458004002e940050b500b802030854100c8640c4a0440c41f03001c039009642d40d011100c644902007200c400010034040d80004440350b01c11382403a080442201c0740002c50070400c074451980607408482400480d00140c051400b44608000302560000e001c44d05d608943c605540c03507238607400712201c00034012400841d40c0000700b8025015516a00108404203884103440076405000d4001c8100000c2c5103510504400381e40c42c8045400e80c410201500340901100050407040c101c50b04204a1440d080010702c800c0c0006082031110314000d003240401040c8903030804a405d0380030602c1e90450b20030365116007503001902e843da0820661003002290010b03100e58800c002c022080141c0165200d5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 973175332 1250 973174082 973174117
    0x709120204140705032401050f090d050105010305033a050907090504290f0402090c043c030507030803060a0801020a2307020f1318051f0c05030615 65
    0x14400c1d401300186108074448110290360340e00820101400e814480b0200e4000f031020008140c0c22508540141110100541001003c00d01d41c0c895030b0840d902a0801c48150304002080507100c0c60301401140e2100c54101d0390300744031f034048040c038922035181003290203035640b5072000840c5450103100c200300a1040d0340c018000b83c5410b181100100b010030781c0780c11905814404102e9442c14580e205842401101490100b5840d0b81d000c018009400804209210004100110349904010761100d010392800140070020030b40ca8501811b04040005440001c0140100c1000840c400042d090110b90f042562641c0d00d48540d40441e8500c5501c0e04948401c1d8000030302180340c0350b4450030418091040d4a14128406016845581c41e80709903000654800c1e20000b50640310b1401005220000c80f018900260555141c0d040c01480c03004d00a003a14030b600843c0d0301200c42a800030040c003000d4030445003002100c0001d000a0218080070304a680505000464140000024030840700d501d00010989032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 973176582 1250 973175332 973175341
    0x100b0117071e141b1603080316030915050a060b07030f0809030a0f05210c180301110a0305060a03150b01031529190f08060108070912020414 62
    0x500b0650210a5005141e51040c40c0d40c00041c4100d403161a6000d0700750301d052500518400d01113901c0090152a00580190f00d201c1080007800c0c01050001c52042811603141d01d809480056030500301e480c810103150801c03ca02d000650902d00018a8010307000001403e030703c411500d200140815081422581d2000841e24103042d0030050f06250703608243d40344100342e5030341c0000710703241c0c01144074202c08036403090342101100c1d01801c00792075803101070050b02d0701a08c01c40c007200020120589120b90040c10000d009010080401c05400304c03508190000e20020141a080803c1f500c00c60b50341d80105960b80c0c001c10b1181d41d07100410001160000101d00303161480301d441c0301c0103040d00610395001c40e180550301210410f42030501011952045a05005a00c40c280700e60000c0401440700f1444034410088400e8922641c2c0300e003280502180c0e5411f50b0482c012a0190500324050041814400c4a2003003000b011390109001c016110100c00c006014412440440c1c044d194124401d40400001d60402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 973177832 1250 973176582 973176587
    0x103200301050f180d020d030903020102130b0405010f050304030c080a03021b1b0306011206020a050c030c1f02070b011a12041202070e0108072102040509010906150503100b011707 79
    0x354010213250320002e80050384056141c0d035a01e0076400700c4000d43c0004188150003130003070340001d24450280c000940707008190212440344a44641003000400303030204040c041c0796808407030240d1104090a0143c40c502b000d49000d00841d940700001020880d001503006034443c0f0030340513100141c160b410040740e581004824191200440d070440301c0c110082001b42601c2d86400660a030480c0d911074580c401c0405241c8410020303500202d078000030310600b008140c2080004000074819142000064920820012645908900c46040c0300741501d00602c03600c1c0200740981002c0d41160300c0d40540003032001c000c4045040324011a140c0101060b05041040b0502090815071140c0080560903610350b42e45545d8100e50200003030203601c809510998060200303c43d400c0454907008015075066007101006e90010b4252442100c17500016511010700300704200380b034082d102070161300c0d590f104200ea0034900829955000b54444859054403451940d0040c1d020f098408021036085500c03141615001030301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 973179082 1250 973177832 973177861
    0x110703380402090a0b1c110d060c03060909020f040e0106180204081c050d09020d150b040f0e03090103050a0905240c0405010f050703110d021f05040506010320030105 73
    0x50303010310f80c003200103202c030304041c42441c4c5c0c0d00000800707107502c1d45c543c0b841001e0320b0009200d045440c08040007130314501c0e5940360a01040d840c440c3e00c4c081103024625030014180c607440c0d88110300c100c0c1040b0080d401692400380c07505498406442c001424a030340311000303001d494698441102d00d0305050003c2e048030b07007980041058412440484e503001c62990780b008010040d4110040026405201a800901194020392604c40c0010a6102054410303203522180704281000b40e1106070341d8121500c59400c280c0603908031380c00e000d1f800304815060603401d03d0f16442000e84050400da5980300094820045130320440c6002d400100321403660313190903000440f00402c401070407441c402103070021b40c941c1c00c448226801c0d0388040c0d5608a0200c2c09001c00d0321075411a42d0120240041c81d401280c084c2d400300071100d50b50130325130b0081528405807440602c000310141d084d0b490090a03c410030012038030000c0c400d81160b81c0984168004c0c040b00c1c1c80482c0101082c166513626500701414460b00e1007000e5038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 973180332 1250 973179082 973179091
    0xd0504050715023f1303080d0c020f061018020d060b04030b0a0b0607060e0f06161b0b0105210d0302090f0409151a0414040b0711070338 60
    0x44c1d102150103402441c1c07139600510100690340c15058115002c00f000044040e10003c1001c1c0d07100540d25441c1e1303441d00743c11340011a00b240c50070b541e01011400341e82d0400c20021041c0058018004900b0060f22800800c00725009032400d02d0306511b40100c140c0b0b441d50448140100b0940308004154032200400c81d0340d4454801540c0030b0a00d10003081c1246428400c1c3c81101d80028a02d51500d0482e64821016010603d11004a4001d003400503504040620400740700706882c00c0c131f604951201581c041c020100c2190f03158151410308a01c0c00c0000e0b08581518155402121040d0b284141800400314040f1412054042402040d80c0c5a8005406030050031070b03500b085564503000f40c090b030203200c1101e040d41c2016007156000d031660122400c3c603501c09101c9406002c0001d60305224140420182c1d54103441d0b904a8038a00c504100600c09180a0590004078619040300c024061400b0150340c0d03401404003516848040c54500744c50001013112040c401400c0d035031080f052104148400120380c0456 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 973181582 1250 973180332 973180363
    0x8030109050a050912041401200105040c090c2003090d0c0e070507050a06090309050402070c0e06030f0d1b15020a110c0a180605030307120f03050c0d050405071502 72
    0x8000c00c0604d00041000c40750040317810601d0b801c05141c0f0098041c0440311a02803410303c00019401c0400d8880c81c2200c403c083c0907040003045031705007494080c22180c5540d100d074004605c0d0a0b0418200b035448440e1000d61341e00550070380358100106c05510708510034540c00551103585010510f040040c2c81803944216001c2c0701810005640c1e41000383c60038030940c20010300302e42090141c03100160b40c51340103200860103841c003203400940b41e00c0407400726400404141c49040b0800c1e002c04c42c041007500e015501c1601500540b08542d410740d40036503100b24446200092110450303803000508280d150403002c06411041e2414104d40f100340180007940300340ca403907000400c0c645003503c410707000141700000b03410068518406603140480b000b01e50760303c105080358040d8945100252a641c1000035018640c054007207604c09401e02c0d4006000040044400c0c03051504140c10000c200e245074040d034615a40d490804141580d41c0e2030300a0420589400c6191141681196031100550001b10b00c055030341e410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 973182832 1250 973181582 973181591
    0x40b1e0c1c0e01050a2a0c120b0606090d0308150604090e190506070f1106010605120f010e06090c07020a08101a060306040c020a0818132309070308030109050a 70
    0x1100c04e4425211800080746203c1303459100c8000c801c2c14141101c0c0700990000300f8001550703034003d10340c0e02e40c0d000c2410001c04106100504c0803d40d4401d82044080703a4951038030032940301013801cac10900b04d4042d00740b00144000034001e803c100c2c6007241c2c04034020400b035903454540e101c400080610000f001800d11800f10710052000e044c1404c6030b00140c2101c01450103540b9814101d8148503003000d84d1003048410700e504002c1040030004d0354040c000a0715042c0e1a820b2581d60310344102e070014010f21016509000400111040f14030b1150800d030140c40c07202482e960304040c05158800c2110081d0019502c5034000f6030010046208914000142c900740202c084c500003405a03510900012a4042806c1020900924156010956500f400e00507203d0840703468446000e6900714040e1400c0c140c4420300710000a2034440c0082d158040d00450411120984100014820520040003080c0007a440c0c00704540060412941c0020355100c40300581c0c3c2d60b1109030b0b100240409031128198203090 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 973184082 1250 973182832 973182857
    0x61410050405092508030d0b010201050907150c020d021009260606100306081605040f0c02030a0806060c01060329040b040f060209040207061a06040b1e0c1c 69
    0x94058140189000f030010f2940c000d854448114180b440112411030001e50100040c24001c2400640900b8504980c0000c0404130300d0006070070740d00000c10b5051940c01081c018080c2c881401c203a90014507040c6003402c03441400b032003c00c035100e0201c0340c0a035024080c0c0c0c100120503035000f02d451041c3e6403031840190800d5800c2465030151101042d201502c0e8016400003051800c195004005e656460b00c0c02140680d510010716040c50304009131015000583c101c02c1c031035030629025074130380c1907000e400811107100442c10084d04c070b015041807802001006c0300410025541c1b86c040d03c0380f404021307008014007581d034039004000186c1c03c1d0004c0550516810f04d6546248a00c1c0785602c81c0340c1003010801141d8696882480407040c200d42259072550038019030318162140d20142803814410b0300c00044d400c2080d180680c0c0c65080600340c51080c8403c000a201e0020000b090390b244040c00d2041c1e64014144400800c080e010b0001010300501c034100000a40401d6010891503140c0740303451780c9861464 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 973185332 1250 973184082 973184089
    0x20c010f150509190234030801150e031606090f14060d06080d0f110d020309120703020303070c180c050906160b0f071418090702070306141005 63
    0x108180d04000c030101000200014200f5100d415480380d54092840d0300b4079030243d140c5003283c10040ca0182d95803d01a005038040e60707054000c500b41e1401c06c0091031100d0107950b00030000c8405004042c0406071100102041c0c07401802d4030740b08581c00905560421081c050a03c46044c0c3c248103140000f00d8004000500c400c070360f9200e00907a181300300b54401c0c00310040180500c0d580005480c0ca070080d6504400075803d201804020884151030352186a0007107411002040c01107490071111268100c0010f110f516a000812566105803d40d244c401c0d40c0e0b50f11070b1840c01c0c844a50b0020707405000014006c0704000c0002601026034400c06090306100440c00c002c00100d545c410b1010010030010048145d40f4500840600340010418202c030301000301c669284440c1420550707407500300548a00500c60815004088a45118103503582d590078224441c0c00d41c152200c00e0119140501e0902005c52401442841240080d5030403503824002e032080c41c0c2c1202147d41d0211449619003000080106040c075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 973186582 1250 973185332 973185341
    0xf0604060b032406370612050709170a0501060b09040c0504080a0f0f0807030206041e020901030206130f0611161d0601050d0f060e130812150d0501020c010f 69
    0x701602c840070303c40e40c0d801c0140042e202101d28030b081102c48401841520b00c188024046403030300300c0c107648035020b0f00e080c1300580143d800e0810500c50909120403c09001e610440280446401c000d4a044a00c0003890700340c00d040c2c0c1c20380058081e500380540454440340c00d800824030340c44182d600f00011443d14000301c0d020b0190707020780b10072500000000c02c0031607200c1d218030001d24001c80c0c1e22019a00141d480308250b50102d0f41c00c0340541c00103030803c0140007040c00840c0c41e147c52400381d011203030199800541e550f1814040280f0810740170482004505007128404003902c805403840f40010b0f180c04001d0314076251981488560300c41e0144112403011904400fa049a0884c40c8110000e40b02c802214505280140443e04100302403000c1041106117010340c01541070f4001c4c00107400c90405645404101c0010a003100080100340c0755000100c580040b21a8401e005030307410b040e070b1204003540500909031144194040c44d2100c0c07440c240319041d130007000c004a00d80700030012009100e4402c026079 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 973187832 1250 973186582 973186633
    0xa0914030d0813020112090f0b0a050603030405131b02160614030a1a13140a0e0a021e090a06150207030c05040e01021201080604200d030c050f0604060b03 68
    0x7446040403d40401828804800c1c00b841410b00d68110700f108540c250840d1b021078000d0380c00318100d614200920401d482804d80080008070180601d03c0d0141c0402c0d502e110742d00c10940109001c8141c07d1000c00240d2202825440050b142c21481d615a43d00030f40d15a640b001c0091119080d84000079210301406420320b80a201324645070959649070403c0005101c0800241c2102c030f4400c4454003903a5450f18800000e0709011b00001c1c05005008210803d1640148881c0181e86894468141e841d800107907100502d038112030641c0c01115840c455009010103030200e5820040c1c1c0c0c800d0082c0d00e04c903500018150381c05d209000d0381441c0040c1c8101da541c0058071004d000340c144074a0034802c1d410260020440007140c14009803901d52050580d0350141001d134803601d010780080c0140020441e1002070422503565400e044030f040003901c0300050f1010380c0500020140004c40d0820030401c2000e00c03128420315421030640340546420f0615030054404404150300c24000c408e0350204003c0760301e030100d01c00e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 973189082 1250 973187832 973187837
    0x1403062505070201030915050115050909040803130609060906141b1806190207052b06110a110d0207060c1506170d030501090605030c01031d030a0914030d 68
    0x446909100c2034940394440207080e4101900c8a0400002c24000c000c0300c10002c1d035030400020103615081003130304102c1460040e00100070b03081000028591761004150381050700300e400c00741e0380c1c1c5403803003150303400c3c0085000103101c1400c146e80c81040c414194000218207014250622401c140410030721b64880c0101d0304034130a0030740700c60044a9210600050000705400c42030b0701c000e80440c4000209690003400803a041640c201641d0004281d043c429580100400d6a1048980c0265031000005040e4086990707403001c070302c042a8003800402e8214415240c2c0301d0300002e5072001605001480307403000352226062031080c14811001588001403000c11117696a03204045d11000d552802213001d643d00c0012a180e448a1300460b0803507411103405040c00304071b00100780c00d0626020240c2a55016402207001501c2c2030001c008544020860110f41c000c00d10b0006065800c099403d03929116140c110150742c440480d44203020340e00f2040800c00d5030079244a11210359180300416036a40c40e2091074000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 973190332 1250 973189082 973189141
    0x509150f060403120c02010e0406121511070303020f251103030408030a0c022b0b090c210a0b010f170316030813060f0b0909010c1d0d020307140306 65
    0x132128840d0202c045c0340307441450800c503400b1440001800741c651580104824190f01c244150410840d800311552000b1405005d101a0f0780003005a54079000d801400b40a05030001030a118980c20842162000e050341e0f1190241803c20203800000a42800d8044801e088040c0d900a81450300100b03a50407070786031500540c5081c801d0704d01114018a412022a0420707605000c4040c00550480c03410f160b00c4403000d00403000006828024003130745020f041003070550002e221850440d01c803100300340d042e8544015065600301020cc5a28a4203010013000340c00d1036480d0002069618081042508541503000c640d4031005040c1c100580f079106100c0c1d0400c054000c08502c1001078000e2000c20792008000351814801d209a403900003d445940110301480f91303a810503100c1616041c00820f40100901e002049405048000a410244149041d046142010912192642e149002150800c2e4054280d4050942d0f489200e8554804507000b5403081c000d0200059000d500301c0e003001d95043c0071007040b59 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 973191582 1250 973190332 973190363
    0x12061905130b0f09070201051e070905091806070915140909060109091109041a090c2b0c0f05030415020d02071a06010e150418060509150f060403 64
    0x801da042603007500924800f44888003603583c100c4031407007042a03400115181c40c0c001c81c80348010000c140003101025508060098407580f03c1041400e9445c1903c0305e034500c2c0c954902e14240b20380206000f201902c24041002101c1c0e0717000d4014403c54180c400c03001c0200004880c00d82c0e42d030b00c900f1024244810b09120320b5520b4600710907160342020060401c1200d0740d4a6088244c16035510300c40c0080003600026945900b814240305240a0b1301b08443c41c0789050140c071000400240b00500207a0401c413001c600700d41c411411018403a58005940d500d00c0704503031346011a00c040d0a071226404007094141c500c6404103400340c0210b922a0b607016224800c1d5903414100c0900070342081c03c007443c0343c503400d203c5180050201001d541d401c9111040c2d058240c038003000010300516400728007500401c00180c400c5a103409140540c1c05403200079030100c551011030b0904000038212907000541c00410001480301c8000582c01d840c981c0501a21140d030842074040904c1754a100328400204110701240814 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 973192832 1250 973191582 973191619
    0xd0e0f06040803030f0907090e0613031b0605010e0c0306030d05070f0b0408090436021201020f1c060303120c1101060b0a0e04050103030c12020f010212061905 70
    0x2512216008280a0400342c8424500e45150411982e820040f039401c010b0020300c900030845c80009190300c0c0350600c00200348210203919104c000d800c1200f10095800000100350007044d502c00507000088800c00880400d08002c0b01400081c45003032100030421011400f0507060340c048920134100a001070500c0d1000704d90845141d44100001d480000704030224800044448110300e0046028411140e261a000001c010031240c6801c2036040b08220300d80c2a4880144281030700b24018482d0001e01d031200010f00106558101d488001440ca5100281c60046103c1c148060440e01d80c5034130801c800d24407401202011140e490101a01040d20089502e030a0300c101d0700b060300e0401140ca04201095130300070030182501c0b02900950b01c0303080b0101c0c4c4075456a520096501e00704c0b00c1164280110351440d1005070000c4000340014004d180e04407100b029040c006c00c1807004070303005000210340c0d500d1800440003900c03006450030b07842142c0001d00c08400c00c04c038136007460580f203004108803900210340844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 973194082 1250 973192832 973192849
    0x302010f050d0605030304090f0b01080f1303050705060a0606112a040f09060c020d05040e07050702030a1a04021302070c05060310050d050601061806020d0e011b1a090d0e 75
    0x204200c1944030f060115a40d103060019000800c5910fa01052003404a42840c0c00c1d2455001224100000c0340b0402502400007034405800c4410b5540c041c2400d013203070504a41900c01c0d036001608622505040c0220041d0301c1e400070382181c5155036280c0f00c1d0040b62180a40303070b110343e0b01d030152915842c02144901c502601000031002c440140001011a440c001d01029a003038080c080c1d8100b41c0e1480318250780c2d03405004c0c0c1c1c038040381a481c00518190800208514201c00070703000f9420003402213252000c540b01002080282a00300c020658409031407000c07000060b600b00d808a00403d40c42c0b9090042803e2802510010f0f41d108410170005810b010034803045810003040f540852014250005090b11043c0401008a010b100500015810400c01801d6000390b0404100e2250302c10a08101540d80800c640f400200c80c1d14115209000241c0120382c580000c420302d942601c0030351060310811801c4140f140d041c0840c0c641c0d071801170f9103280006849029407652940491100c012662061505060 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 973195332 1250 973194082 973194097
    0xd0203070c02090406050a0c020726031c0203190c08060f42071a04020a05090112030e0a052b080307090807150e090405010b04020a0e01090f0302010f05 67
    0x9007545014010b400107003802d4030030749003a1003495692041c800c401000d400350051003801400200025490b00d4020307410151182d9500c02807403240c540704082e1030424021101d082000100703441000d2020000c00c002984240e42c4642da1840d0b400a1240040d502e000f115030314001134540e1000e40e5a80400c0c04068203040000d04d41c0409005484038040441d480c40e4062503503160032200302800207504044180c2106100071201440c140020300c00124100322103600c030344010000c0c140340e4a551000c41e1010305503803c001e41c414400c02c0081040d54004180c0d20880b402a82d407000c00304040b1041c8101c840d41805000d8001d0456240f003101496100d4104c049042c44404100c0342005a4880d081b26410030303603542d0000348083e40d04101e2001e0810400000d03000d03101d48880e486454400c09030540c0c00d60ba42440c050801c00b000141841029804501e019001400966032028038050007800f6800c042e0605010500031031000c074017060101c0fa60400d0325810784400060410f031440a8425401c80c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 973196582 1250 973195332 973195337
    0xc330603120307090e0f0c1b010e0a15050a2a02100f05010602060f100e13060606050a1106010503030d090804150216140906010f11031c061a0d020307 66
    0x441401030304503007002103115070b120750703100c41050f42011903100759054060080102c2d000070030184125101c01000300c0d0002c6c04d14503541c04c41013070300d01c09144c05060780c50510085801410f10000a0150044a46034402c030100b100b0000355503041e058004480d00758010340b205043c241c1200c003410118080750031000131140100d81c850003000d014081941c201121800c0859190001001203176010880310760482d1152a29240c0b03880e01114031203861026118120403101c90381c01140900001400e110782044d000390091001c00e0700d455010b00b1a90242c801c203c0001c41d200c1a0f4001d0200201c3c50742e060301c3d0000c2c06507151500c0740b41060044d00ca0b0b000d0644449404010024000058081e0220440c2d40c3e078003d0061020310010391100d0b0400ea5102e04060301c502c05804115640303c1900300e0f800102401c10140201c94140d040b1407000401200400d071384000185581c1201f441e03141c64036040340300001401255251106018074000c0a442100100340c2400842440304040e009542e000b846071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 973197832 1250 973196582 973196593
    0x31009050a0b09010f06081815190e0f060705040e01050f010314100e13210306080106170d020f0703080325200613030513090e030c330603 61
    0x181603034400380e105c1620b50b00003100070060103410904166016440140d0031803032006880c1215121201068104c0096900c140044c407074269940180741c10100d40c00081052140c00c0c0c2d2000e9640d0000e403001080781c441c2200160010340f0501c101c8042e14408242072040c0e074130300802c0c440e040c6007480d1414103041d11140b03402e0141108460b10362182d800c074050084a20302d4031342c0020510f1006007042d0145203058400101140c1c40004411110001d510014045108440128000c0440c5e4006001075421b014000820960072040404200742d4070044e180842c030071440c242d1355100406003646198000600030004544200040c5a022000082444140e80b0700105130400260a54400010940404005550450310f8203c4501071007000d00801042c280342c428040d0310681020000d081007400100f5206092000c03440314014a0a00c0c0d052240d812210302e1076891340c00180304e00702d961050103407071018100d0040888012280c0d034040c010b141c0109404001074200300910094051188 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 973199082 1250 973197832 973197851
    0x10020c012d0b0103140708041a011e080a120c261c0911040e0a020904050d1106060a0303030b0d0f1b090501050303030f100f060c03030b0105031009050a 67
    0x18240301096040c940400c1c4030180c82041d446000300e40c8030496290415151202c40d02c910454501c813140c00100509040d51141e49502c1c10030001c240300225441c18030400700c00018503c04152650610b941040c203002e500c01e4540305038598562036180c02a11940f129010215807a004680d01c240c940e016806036080003c04609400d0340000c2d612810b0010031001030740a1042246803800408400d2007603040c007010259803a0004804949940b02e2305c925034030307000080000410005c0c030301811b034080c052900302d01c0c0c58107001da00c6111115944000c00d002c40040c40c8004804501140314080c02000c1c1807145007152001c400410009075156044890280c0040205140340b41209031032388500b503404095442034114004280031a80243c0200741090010701265401005496100c5a00031200c5401d03a0b5854440e82d50b001b032036003c6d41e5032215840d8003140b101d91158541c1400c502a803014024058002d00449075840121280c2d880d83d6504a000e0144526a820054001143e81c03030200b0f41c0b800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 973200332 1250 973199082 973199111
    0x303090f0b040b0a060b09090f062403010806060a03050a0b0c0c16090f0b0306041b0b370203031609050a060210110306010915050d0912020114060310020c01 69
    0x1000c2e901507400c000c00c007081200c100441d0041001400000b0f1400d07060245640100300c0080014141042d5442e4001c0014440d03214103159096201c0321030220891014025040b80c4164070a0103107014900a64000078028100385039144102e907802001840341302c44a440d40401d2603406041240c0c0404100b041c0260910200040b00714003149031014001c041c03402030700e4012140110202c11049040001c403201d03da40100343c980d40140c1241c001c0300701005895a000345014550813882d401d0501044d1522200d01c0c25080400100046006810500d4070980d00c07000c20b00114078450061340b0800c00a00e0340b0f101c0300036209800c0003d0900040842e110710000760384038019082000141e0040390b803406020b005014030b020344030018140c1c41c514181800001c01d031080d035018203004100c080e9604e40c0154462001c030761060f03204000c02c104410140c41c001000c0d5046070340030760056003400511041030802c0300801c3d000f04002002884541d4a26041c0740c0a50401c8000d120255030700c1901d80c1d095074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 973201438 1106 973200332 973200353
    0x150603090c130e070b03100503250504060b09010e0a262505010c0302101409010515010e010f0e06040605070c0b130909051906020a03140f040303090f 66
    0x684031070706647c4088256201d00d426104d070814804029208110300e51020007940e00e8500c50b20760750410001a80d0040c081d40c072994408004400c2c41c0e4ac001c1c26111350a4501605610b2655030328890102c880b500d00e41c21071081003d100280c0c4441105111010803544156004809040d074200e6034a40b807000e41c003502d41400340700513001082c10700030010b54500e5400d0307030414001880d6207890701a6001c030a82e10345241d5802c007030200303480824492710020030a006075650741101c01814011110360138200702503014090480c48a00c03c640710350300108042c0200303031290395540b505441c040c0c1c0c00c0945a40914000c0c0f4040c441c0480309209402c1c1c40e021901c114001250118050408500303196682d22400c440c00c1c40503408a0400105030042c10310541d15440c204003103441414403100c07403074046980381d02c9041c0400c00a00001d0003613101d00107190141c1c1c800c1ca0a103100d50348260b90b85 = true := by decide +kernel

theorem cover : BRFrame.Cov 973021582 973201438 := by
  have h0 := BRFrame.cov_init 973021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 973021582 ≤ n) (h2 : n < 973201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
