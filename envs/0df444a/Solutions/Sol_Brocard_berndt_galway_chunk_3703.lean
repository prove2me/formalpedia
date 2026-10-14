-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3703
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:26:21.716982+00:00
-- url     : https://prove2.me/submissions/b2ef23f2-5471-4938-bfb7-a92b357301aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 665827338 ≤ n < 666007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 665828588 1250 665827338 665827343
    0x1a0906040f0e1605090702030c07090c02010b0604030f030e06040b160501090c0f0305070e041205030415110d0509070b091002070f0b0c060f100b0c0c0603130219051005070609 77
    0xe000d28020039011000303d00c0309540094808410640d43d810050340e40344038031303040c000c0d0952000310b08000c901c2c0383c0d038131600c0b03200020310010540001000010311650031603007094031880015200c5608064002d54171648100d0140c07451802c003803030446c0441c0d06009180e5410906c07921654400c080107000c1d4001005d0302d920424145401e40c0700c15800d112004240401c85070703442806000b00d00d00307c080b580940710b26448041c0f445107040c01e0200b2a0150005030085035160149251480409402c1c0a003501454010b40c81e04c0d200c1407110084010351b00c0c0900360008940050000740b041c070041c0012540341c0001501c120b0b9a5103007a40303080746064101e600814190344a2500440c100d41c80a00030411802c8102c01c030380392921a54444078110b08180c40741c900ca0910800304101108074030001d422980c000c0d400343c8040f4104980800c80d25407080710600000351408400b6802c601c0d04130280c41480308030122001c0308a042c2000b040d0b500944800d2030040c00000300700340e030070440300f030300410308a56 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 665829838 1250 665828588 665828593
    0x100902010917100617070b030f15210105090115030b01140a090207080306040c031a190314030d0606020604032106090f0b01080601020109080d2c0a061a0906040f0e 72
    0x190b641210001342076200c0803512090046c0b020000340f00042c1e4094a00510302c031003507d100c0782c540100b003501c00d41c449907015030041c452100c04800504c640d180d010b025a00c5100116861522084803803c54028991062058902d9481840801e881c0301e810341c15200c10002141c0202090300006002440c26401060074500000e40701c01000460009140140c0b8152401d00014102d0382d42541a00c1c005c1603101e01c0082100408811468064448007a000c1d0180c05100040c0c0c0705e446404031543c4801c0c2c048210b500014101080032414419100148080d201516103414541d0f0300400c69103600f2a141d40035191443c003408468080c1d4030000050000080400980c442011004090035410306e15501255408000940c3e5500600170401e08941c1305062038580410b0000d4103004255041964206100051001c40001d0400c1000c4a60261443c01000d0f41c60052400ca000d845d00c0303108070721215101120100007510369000c5c180d00300c0ca0071100031440c61040005c990040442041e0b00180d813 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 665831088 1250 665829838 665829851
    0x70b220801061a1c0903111603020315040b070507020a0e040f020906030c060d0e01061502070e0106030c08010603020c010e1002040315110a1b08040e0910090201091710 74
    0x2420154416070481d42581c001e01c441c5040144988207034020380840742203a0390b84112500c0340007840d0b800617501c148a82481741c411954100d0075840c1c2210200300960488a109003803040d8541045150107032114102001168601a030f02c0420800c40940680288500482c0780c1e01155503c02120000d4060010160201e1a05040003114019014816400b50108501052241c1000310795140d40c014003520252078402c41c445030400030100d482200280d5581c51002040e05d24200380350161951242e4024000c8a080041c481480e0300c1c184d01640c141490070a4401105402103511411154641030060304d5070071621856015004204120f41030340101000e6840034070080d07000e03006076030140c0d00e0b02d00500d805c081800c084822210750188182001e000c51203200303101c0d100380c5480000340d03c0c500c0c1c802c0000350399240c810b402a07000f505044a5480400a000404000071071102c02a15014044600c6d00d80010f001442d050043c2a50001102407285038030381e00f04010041101482020041c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 665832338 1250 665831088 665831099
    0x40302190e100608310602040b0a0801030212010b0d080304081219060501140f0304020d0f0501051e06010e0103020a090e160f0513090b040e06040302100e0f070b22 72
    0x3111079a014441c00300707080d500030803403108103031300765039144004012455132950326103503c1605d0403c0300341c040754000d40070400420a0705694021700b84003490364841d200154110320410400c0d8002c50282003242c0c1c541084c0c1010b55403841040402d054000d00c15a541313440d2410928010721850501c00c0300c0040c0380c404c0c0090900d007043d00902e07078110040e0030404035032141c0044821b10303042c20b1010403000003400140700d000042001550010301c0100f4620a980d043d550307030951801e0368102500c940c2d54a10800154500301c1440f0049442c80e44002d2045150a500280030f403994194107904065010888a080e14014888a0080c041d80700d0300e1600f61130054074200b0821413a189140010305c0c480c2c03a11600381d014400f03461294400c200345080490030710b08010000c040c2c0320100d5910580340c105103000e850003802303101e0007a4040d0380030b006222200598501603403a034182c82ca03020f40c0300090000d441d000c0418a00140e61001091039994002c209907ca002d00c41040b08a14480d40c4030f100188 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 665833588 1250 665832338 665832361
    0x1404030c0b010f06050f09040221011a120f060a170a0606090506060414010c020405040305091206090d050d0905160602070b04061b06090804091e0e03040302190e 71
    0x505105124401e0a0380c2c80703400c042d854542c1d41c41288040f0702c06211240c108000440509402080600014200b404c1030003800f614040e030300217215220054034010b03c86140e643c4103a014440f10307442100d00e44695045001c4000c1401003d00d03a180c910303c0f0220381c2c0e41d91801010340050103101e100141d070b51524907906071211507407481215103905c4c205001510309107a01419200c0c0301e00410450a1520300070101042d040070b51170309410000742512820050390340d4851f0b107010b00c0c026a2074940310102007060100ca070f1400c54451687c5e0f400b0f4002c201c03490100099001c0c8086180c6000c640341c03c0d002d0804000b810039128014078a0048014480c801981e1400d81c40450300e080d422034811540d51400c010b090310580c01001c0000d03201d1a04e0001c42c51944030100c02ea24030541000174502c525031115070240e00301e500042141621840500720600328032032401410071040108001865035000c05035628815880028001c4214030700c51740070301900ca20464010280d0140341c18403850100708210 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 665834838 1250 665833588 665833607
    0x30b060a180212130308060907110601060903060f060e0a020c0c100e190e010e0723090f060909180a0f150e030a1409191202090f09190303140403 64
    0x11074101c000f000140c0c80107640718010080ca4060701c1d00e52032512040e06014109400a12440c01d0291081e0640724105080040b14028000c039175070600c8840c21494440141c50741c11a0104040b03050480a01100c0118544207411042d410b00040e5925891317150181002c410221aa6100e100d504100e00c85581000c05031005150846880d4205851521800c812036424061205402c107514014010072640c081866049091030920890081ea0300041c884213100690f403500d9a0fa0340403c1c22142e50502c034401c606404000c842c483e081ca007003880851400c0000400c90b03000c811a007035000074240014003d6075442c03034205150b54ce03c00903504056502410b600c00c41481c40c0d141c408901d8083c0c00110903207840b1f048603034134500300542e5141c2e0b8800c103030800f80c0c0c004d40c0408060b59480b01001c0740c81a0300020a0012001c2d203a4070325900412440410040188940102c12010800940c0c004210502d030386101c071800280b80d103036a0130100c3c014215102c141054455800c14001455040340005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 665836088 1250 665834838 665834857
    0x30a0603020103060e15102a0b0a11070f0f020d030503010f0501051c0509010b0604091e061203080a02120a1407020309030a03081902120108071e030b060a1802 70
    0x901801d5521101c010741700744200d8070a00d91b441072900400c0305180444078036148200b20301e80149001621580d4602d003810201044c81c54451180e0900304012007559151760181191004008290209201c2003c03413184e220000c200c0784d55842108204a0f0700710440080d503070050010b5415000c94980036045500c203004112052000c41c90005840d0701c604200c0d4280040f1400358007030714884501401c017405014004141c80c1d500e40030700d440f03151900b02c09800180f440c1e500210f0703480c8001d0b01c640ca00100020040381390a00b0160144001080e007000c2420703c5038503150188c2c0b550350301011080240100c00d8005c4500034003c1c01e00080118a82040c0c2440030300001c40e9803140c8600009070f03968810307003440300d030181c01501042021034002e0307584541c00340c07132046c8200c0741d0b4003000da210703040b0303072103640c1d26010048940b0041c4200c41042021401802e050312400f0200440c402c005602840f0501c002002100108001070083d101c035284440108520b01c3d0180c2c200070b286070a04044d41200201 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 665837338 1250 665836088 665836091
    0x90301060b2a120a0e040b12030706050a05011203050307090e010b04061b1e051c031b0c0507210210020c01031104050906100507050d020715050c060a021b03030a0603020103 76
    0x300e0b82c8000840d03010620016051024503002620f901078410030b040c8800705038416920000d10115072210200c901300019050090b41d540c50150bd055411a01e0180c6020103a40c071b4403005015016490345402c59a941605140b5126139a04104840c11441f0750840750784135494a000040c5c5040c2c201c0680b041d10800e842c0e800280304c800c3d000c0c10740034420340d101406001411304140322829401b03883c40105d40c01582515088880a92241644401c0c134106000007580d4250800740c01c3c0c829a100c10340701010f45803020840b095611419075403442c90091080b280a009124164800c070320419044859000d031030f64410050709440030b915496605001f90109080540c501c2d1071030001d908440c1540d40c000d08054094032f500c1d05120040b2060001c400038401e0030807440c3d0110328100856080407030154020800e03d41084990022a01c0c003405130028070009211600740c0b540003107100c5600001c22500180c84002d40403405085101d50860042d4a000000074004000c0007600030005072030003070300e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 665838588 1250 665837338 665837407
    0x30f150e010b1e0a05040213084b0a1b050f01050708090a030c09020c010615050a0f0203040504060303020318060a020d1b0602030a0207170a14090301060b 68
    0x501034282c0d581c0591480d4041c0007011111000054407070f2801c22641c000d010110400c3d100d10210b01264809800003003094131042003000303640750070000c102e00445010040020040707484000030780000701041d0388101e1000c0406080710910000f800d80c409124100880c0d100c60518200300c4503000c000002d521003000c0b03868000c201c50901c00d09441450806960f424a010130340c0c1c64580f12904140002a03105452020000224091080d4035000c1c00307405c400180e94528000c152421540706500540348035550919016003035070050300b610080c800c141800c11108000041c101c0c1903200e0b98000303940c0301e0f160641c04404d0682c00006894400003e031251a2015805000c200b182d000e00305003400140e0001c00100082e07885070642000300418656420400c0080c1c1c0d513100c0aa0304101e0301c030203000d5400314800060006007005222402100c062091400c1030230701005082040d000790141c00768ac0001021803040d14254020801407004804050f1144511002c441c0720740c421011401c500c41c0843e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 665839838 1250 665838588 665838611
    0x4170706141606110c031207080103020a0b0d09020301230c040e1b043b1006050a02030c01050403020c0102070602010227010e10090504111603030b0a030f15 69
    0x600444003690000299003001e400010090240d81c02c404100c0781c0720344840d02c0d1142e05012802400a0703041040c090358664041038004130704000010650420800c540c2c00420140c7c698088007025201d90030091644c0d192190815030140c49403600007901586014841b181d09222450764810003202084880b1194070340300808030050017907000e0404003600d54000320781800400d401d03c00644280241c8035080c0303655401164401c66890034810031141c0c17040a03040a00e505032030603440e81d410782c0030141c2c2c450801c840c1e400114007042c01040244080010210740031802001698003c921000092006180500e4003c4d1107281401c4503c2c05031060f04008129240107000b83d039000e00707200c98424401b0703110540da00b9001e840446000d0600440b10680940d035107592030b02c1c10b11032285d500c904101d14504010300013107884081c542014004184414030307000382d060b010b000415406160101d20b00e40e0100c00110f240e203141d03100038131842e451042d602c00c0041c100c0011040d009030308410800400081c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 665841088 1250 665839838 665839847
    0x4090228090915020a02070b04080307030f0f090b0918040c0f0e04030203272e02010207030212031803070609060c110a02210102040924150309061104170706 69
    0x9040c0180f412040c0042ca503000506503010300020710151045510103943d400c00410298020707042807809400c00110002459080f0300050032101951801080d07020209000422003034940c015200034550000f4800e0351596018001404032140e041c3c040100d090a18001c240d00007244200340c0205814800069110b92212503d88030700e4040d0091854004035002c410801071314410352803002d0340340c4844c00301a6110200040b4480134000c4801d00880001f864903a0b460094441c040f04580c0100300301000203501284940008411440c4680c5984030101001548220419101000d21011540409021198110100d407a0040004102c0740600402c12103410290102c092060b500040c01e0701c0046c00c0002280c0b0107500c000803858203900300c0300b881600b681d0090f4480803a484e00d82c0200340b091210595059078022000144c100403d15000c0c04008015203203040c801070542d0303400c1030f1043c0505071b08801c0c40594501d0f150b07640c2d00d4442a1a40c00d2030310010403243c0e43d109584010800314000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 665842338 1250 665841088 665841101
    0x50913140f10050618010306180f2306131103070b070c03030806061e18131a091b0d020903010f021b0f03030610050c0109080a0f03110405010e0409022809 68
    0xb0380403600c040d1f800d548035a40982080c00001d00b8103082810407002051010010840e0342d4407403c0d01c40e0700000410400b5400da180300707a00c0070381604280107020b4100c1e00e450203902a960b000c0104400038440c03800082c140002c40d80140300701807001410780108400100301710140c0c1d229031070712401030319140103001450185601e9910300034840c010f038080410000001d886080e07881003500210b90b1522002c03134402c8085252010310952510080301449024a0298121500599001640c0e2402d025001c9020741d010206002e800800292041d4501d0141c048518002c8041d0080c895a115080300c10000d610180603d0496043c01c04040058000810082204e030541c40045045855a404100303022020f44100d00c14040f0800001d8142c0c40c0a028200c082800f4403241c40d110b0201201c0070b00402c050340403d20400d883c0084900c40300d0344240c255800d45400b0301c1c050f0140408007001c10014221610069409030810544601a801012010150f800c013104040c0c1e0155890f00324074180d808 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 665843588 1250 665842338 665842369
    0xf0d0203090402030901180b0601032307030e12040e2e150315120302011401080601180905100f0f020913050604140103030507021009050913140f100506 67
    0x420003004000e460190055908001e17074400001c0c00b81c080c0002104541120a02103c4011000701008259a05403140c11034034260442e40100e964000c0030000c400d054003d20707440c141175503804501c5480c90100003a41e07070915040d0f805c56445487e0140c0140422017140d40450030398102d41d032030358410b600c8500d0000451124102e0150a4140f460000703503070f40d0b080494400c065540840c3d4900b01545401c160051509103803c0c00344c0328250900a003510403c18000c42603411410040180d0b480000b581411101040440701c004110560b1410240c080884040c0176072088210441c00c500c41c03540718001b04d0300c0f0744c04104100d507012218041a401041c104039804000f000090705105030785d822040d0720540040000654074142007240002250a0f0004e400064012078130408600300400d040c42003009a00f07001215a20307240c00101c00c054003e0441c03c0c080041c80614080081420100704044c00110503140500c01c40040259541071109400b18247c1c10701d00450524117001461100111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 665844838 1250 665843588 665843593
    0x30702030a0b270a060f0b0604030c1e030b041103120304060c090f150c06060b04060504141903150b040e0d081e040f0c090515180106020303160905061b0f0d02 70
    0x4880e1745885006055840140785c0954494102500310380c2c40c0c3c4010406107100d0202007055a0400c1c5420f050b0b607601190301d002c0c41c200c0e0202403000c1400952055481a07125183c0002d042941011a05003611480c014410309004421b101c100001c642204058100e203a4903d60181d54070604681d04110354801d410981c000e5441080c240c51040c00740790304482c018107001c40c1080c0d072003813910340e80c0e40294000800a01c0100c2c09119000300c104e05112882811101a0381c100c000307200b4080290303850701c0018940014502e05140003140c40e0025810020000c4c001c00452082d048840e44400b43d10840c072002820400001c1c1000e0302004c040c031005202690030f1300035a41e8070354641040011115058070200c0f880b007400034050040f13000d0903109401c50600b48904c5007507070040c0610040300403a0394180b190303514010700510f503001058a0740422040081d800906001405417440741c01c2c0d8100c03a07000400043d02d59080140090340909a01d0010100ca040c0e0103101e8043e503d440e42c43d00e5200041c2c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 665846088 1250 665844838 665844853
    0x114030a09030519090e160e010e0f03120405030c0103050405190201230d230c0313080c060405070510080a0c0e03011b020f030414060309030702030a0b27 68
    0x1440d05a0122107003038407908085291220718085071100010030420b55001404043c001d006480b240d031403090700170a5101e02a034017000c107070b50301400000c4100c0c07034141040740480c1c40c0d9519a90310031065515000160a403480745c0c96214040c0401da0160240e580079100c0d051280200354464031400b4170864001001e0710607207980b400311108000d02880164100041d004c400c3ca010300c140e60300c5002c0081c0c3e07004000d654510902401c0140c51610b100c450404003038805c480d441d003650f2890305c0c1d405242e140d03030b5640d01d0307640b100842e52100500714084d1140c640803072001c0b00100e000854038011406142140da04c0c5640b081003150062041c01041c0010b400c4c407001c102c0c0702900b50440b094003c541c2c1050400c4005060220f400c4070740480c007521000d200c40d198080030580601c8003410580366a400f6500d02410119910840c424525009003c2c0c400040010a01c030010703c155450395a0080c01e413280c00a0600b0b1541d80820150744038064081564002c0f00c09800d0031011283c5c07407074000081d0018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 665847338 1250 665846088 665846101
    0x607020d0f030509060d05221a07021e0601030213050112290c0306010906050306011d060c07060503090d0207030b0411300106080f122101170c011403 66
    0x1c114401c00110b040c088140440070580d95040003515078540500d0300002c45141c05280c81003094118603603810099610529071010072200342c1c000c520034041101040c0b0689072084120310300f1080000c1c2d4044c00e030b040c60400f07180d0000421038904890080b079801c4401200c11b0103580c00c40303c080c4178611040005255000c005000700080200180790115206032a480c00c50135500b0a40301110350007211440002048100d6801c100024090310092401509615081d00064800c10201044005580c0401742c038009030350314002180d0044000030291401540d54500c0549a50001c1e06c00c0f6005000c0c41c08100c0ca200c1c400200d47d811650400c03029109500c0300c0c0c0302c43c10f4a59120b00440e420011500007410101b80090f16141c51280105000307802040d4110300c503003107a02a801005298000082510b05114000341c5282101c90003001c05644101c040a01880400781c80e495000c1c800034a800001c2c02030400702c029102424030000c0d1001d407a6503800441c0c542c902900319100c450420f20101e01c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 665848588 1250 665847338 665847353
    0xb1b16050d08070606030303061508090c0105070501021b0102070212210d0f1424240d052505070b15010c02030a0b180304030f15110a030f0b0607020d 66
    0x941a0042c4a02850708200c2e458900581301150416000300f61100800c2200000d0040c0d42c081c94443d5283c00e01c594200340c02c035075031030783c021010a40c1000303808164041400420350448070660320314078180c240c1d10122020140070350002d100076482651030807007840c44000c02058000008031450750800b066410050141259008170841c001c031107030b0701e1410f403443e480680302d02c1d41030713002c000d10507951468940c8142004000d08c24a914440c41d06d0500394030a074542e0300003c0d180480701916480151445c1e01e0444060040c651110f05190500040c0400000c160404040849640c11042001c401c200d10a03143c43c031590100420b07403d0f09500060528482c1e101802c0c07461f00503d00b0802113405500024a000241182918180455010310404162244010600c54001c5010b541428a50740750641c00e4241c0341d00c060078890000d1402150010700ea44030140b280780b200002900c0d000c40c4030006000301907d0b07000f070025920b004079040d200d2501e1030540304000d90007400d00b00c0c00000d5649010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 665849838 1250 665848588 665848609
    0x41a0f060712140c06070c0b060f010512061206011205150601200102040f180509010902130207110a031a070206150420030103050a0b060607030801050415030c0b1b1605 74
    0x700000041c071511315024000d0000341c1c022005a6030758030070001c041c1007505580c00302130310440c03180443d240b0112269800c01c0a44c0d030350b550002e06c03a12a540e00d02c0042800641043c40d043c00501078440042920b80045c6440e054107800b4600303c4e6044402e56500e444080b800f6150315012032507903213010070184418a10941181800400541081d540f1056440088003581103000c22500c01060360455103102c0c03046580c441d280c01c0003840104529004502c2119590311606203041d000a480d0b828440a2004d550491030701030004840240c2d2400d01ea440d916240645d00c00301c5a041e07001c0b0350b4403480014007500845200000c0d0100c42c1071001008000d01014090424004401c1c1d10070aa03000c030000a90300950041c0003422200c8004c0c942150300580041c03100d03218a005001103800700b540300b21582d05617141a100010030b001c0802d0314180e09603613a88003c1481010300070102e20344502074041d214841d160701c01154030036000103195403106400131450284800c00d110810041c60034200c2d10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 665851088 1250 665849838 665849867
    0x8040807050a06020a020309010e091308161203090201030b1002070b0a030f0204080d090b04030b0a0509010902040912090806042027040c061b060506030c041a0f060712 74
    0x380c01d400b4080d0340e120280e8001a980c8030150300089202130440d60401e2280444100460300010b50f81b600605a000c01314440b107000e40b1408001c116210708060807101a41015080300704003014000c5c1d540000d000c3d10070500700328000390520301410743c80d003000403d444e518641c64000e000254100301c3c000c0265003190030701d0310401d0f8a60065070030744143e81c4000c0000c0d01a00700074092642813130744060030f40b28131540111035402d400c1104001081c04a40155041078039910040703543d480300410b050141c90007143c040c0d807040c0b50110510400004003140c01038a045500c0f100d4560756183d0b05503481d034804841c090b000a0424000c940e220200c030201030704503200104191030f0800f01400c0d454011302a10208041040818140818003c03d8412000101014940705540703441200904440494070000141260b840301c010800996003400007c200701d10143c01001240c0220440044900f120702c140340c0295014980f034034160601c081110751454220038010950300d2503100441d0f4103003149020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 665852338 1250 665851088 665851093
    0x9090c02070f0b0301051503010e061017070806040506040603030e0603061810030b060607081e1b0303040c1a0a08100312080f06040c17040c0b070309080f0d0804080705 74
    0x4103001202002c814090311900200d20740740d41c100414805000b400120050b601e1200b400104406030421228580c440c0096070340c1d103820002040181d6007140040801070800700d9503010414034551101c0900d11aa03c215014001519024103010442c0d505001c0a00090100741c04c1140a00308540119041840580404030b040c48400105580340300c1903480c41011040c24808005014401000c9500480c0440d007540c40c01803c0e5032040300b9403080221100392040210803092807141740405503500c01e00f4010150506001d405006a1241d00840c2c048038011994003000c607603d000308041942421185841c1da1804101e05800d682c1200e005129240c00d5405110220000c0e81c0584c40c5000350308580c6400e01a42404501a4515040100103d01981c500400c4a05132540b000304000306100074150080303952581c2c1041030140d0b0440d00301c46001040019034004059000ba0b0400407900e4800948629a03040303090f5503154010030000c00000f4100501003800305604a0090007018443e104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 665853588 1250 665852338 665852353
    0xf090c04080a0b0a051b0301052808030909100509010b0318150708070e010503010b0903030405060a090f09110f090f0d120e06130608190603150e0c0109090c02 70
    0x590a180c24100b8a080b6440e15090041c0300d4100202d009480e00b110b10301d828244810718803203035440103000502c9810300c01c03c102c080000e01c6085c0c00903141000d2400f011015921a11101e01c07680d2640413020a500442c82a00003903504502112110180e0390010311030003c030b07483c1031881c28480d0005020b1030106641c0e5045c0884004040000010987e01c403e20750319240361661010780442c200a0452051000791101c0000c260382c010116419107480f6001d036515031202d41e011031700d517000d16000a82c00002c0054065071494001030303000c088544a160425903991260011000c2d43d104031440800e40307100344446250100104050143c010014040a41e900780b90000207030014161003080e6038030070411611501c8940d20924240c1607500c1625a685001c0480300c180c20303403080f1803103104100b10b030b10000709403070f58100004280c002c06101b4083c450070b074403403c16182d07484404043c0503500e407030803041c1c006801010418821a81058641c0c6050038901024000600000b20820085018401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 665854838 1250 665853588 665853599
    0x10e1804110901060309050d0f020708060f0a1b0e060a030908220b070b1308090607030801080606040e030304030305060109050607150b0f09011401090e012301030b0f090c04 76
    0x2021510640c095486041080700038418010b01d1801030304404101828150000d001c40e00004400394031008a152040351103050768000c90814961790031046441c0070380710512840346110034500d8000c02112004010b0892241030028191492103c00c40108a40820000c0185821000f40114200394200891010140e0f41c5080150340031001000420114148190071646002c1b15040580b0900200c14644041e94a0f0419401002441062004c5d0008901d808000000e4152446080042d000c02e8803910760f80b50241a5140074022100c05100d440005a0303a841d00b80540c0d00b14000e607401071031840d00c581d2800c6025180080045050010803c0006141c1d1952001044082d000b900504059000d00c400f20080d00e4640400500c110f100003101009a901c14001e0342c115445000c070541c5c001c0542005a62065243d80001c0047d0109800043c0c4280340c000040400e244c44200841080c8003080194115482500c0b003940240c01915038002508145044540040e04408481e007015540c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 665856088 1250 665854838 665854879
    0x1f020312071809060b1206060904180302190f12090f17100e0717011103010f080f010905071806090e031b06010303020d0e04140708010518060f010e 65
    0xe0324036000082050580c0c0210b681c05001da00094040b00c1402e0000900d0311920076464041d1100c211800803000e00031038400d94030001100d0090402030814800440184280782c010710310766a00341c1c05400380e070034100b1116031445da182200719413100c0c1d281e9420706030340c030360907500c10000074400c0600c5551140881e940c112010403200a09460742070505003056030b2426403c00c501d048103a90098148035866000390404900c0d42c00f42d80401030044501c2040002c0e01c1c0c050400448945aa900300000116065108400394015200301504481030803e030b00b24010f088680c01e4001030b00a811012040c018400d2001036000e66030304d10306002c5102c64550b103400c8100c0700c01401841c17070f55000242e0102881042c0740c10714440c00200f00901007035071568a01030b4941d1f4403481c000b82000152001c00c3c00e0b80d0344691062280c826044900e412505e01640e02034520407080c00783c64480c03850100c40036581c140340410148105c1c0040c000740748094540c4015141d81106241d030a611092940003400981c206 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 665857338 1250 665856088 665856091
    0x20c030709050709091104090e03043f0c05010e010210020423120a03181707090e0307110907170709051305071709011107050a0c12021f020312 63
    0x201da80c0010a402c0c0a0006070004c51584d0100c00d15505040d41041e280245000307039012178100f254003103201230300e040310030781944165001288002d94080a02c1045a500142c00484810126801201510580c4418040c2c41c801000605145041009108a511400f017070f481c1080e040c012195400c3c6038008401c2a40c009801040a1f2210b0703901200e4014075100c50f10308030f594266486100c08140308034280e241c0814500c094240031001003440c44140c0801c2141e8020320154200981000c400c5ea41251600300720f01c00c40052034104410880e040700048211200158072030004d102c3c0c0d4030200c09124558070000c000c0c0090011045034994120645642e06110350a036594a5100c1d81c20701e010001c01540c046c600b050a540707444100304803160804041001042480c84004c041d0303803151000b60151004400c0b2807240c1e0400703c0c1c41d80400c0320000310311058502c10303440305d800e50340c40f0650045030007000b0380301035803251a80b0a0480d400648000c1c0b0380d602c0c0410704c10383c0d19000e001500441c01010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 665858588 1250 665857338 665857349
    0x2419061d0901050c0703023a030f11160b1905010e0f0f0c0d0203130c09090c081209060c03040f0f05010f112a0306010906031403090303070f03020c0307 67
    0xe08108101041c5002e1007483c2c3e020380c900c07140354100700f510b840096503075489001001510a689500c1e00c49018030550140340c02c5482350b0034145200150350700802038010154004201c2d410a1041d000c514004000c0e15800d18100c215040c0c01c540f00c4c0c035214040b400203058008210a0321141d03940100381c9015660182000368200d200c9810018001d0602140080a4210f43e40e031450901600684000450309008442ca5025841e919102c4920034840303c1494011f001904138039001400e8440c035000b445041d03000b01c02c200d540d140da03922090340740d50806101003801902000083c410740b9025005c0c0a048075040c007201c0c00d15403900701c00032020a5640085c4c0c0030303042c0d00700200f040750703031145105800008038548000300680070040c0c070340c0d9a030f90700140c0051001c1c81d043c0740401000640c00500d448100038100e502c19699146030000410325404103407606001200c80700c0400b00000b0880d8a0510042c004501d4103c4503182c0350805160a00d0840450041031071080e10381d5010401503000c0c28 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 665859838 1250 665858588 665858639
    0x20909090303040c080d08180c0907021b030118061e090506010e0618010e070c06060b0301031a010803090409020a0504050403082e0e07030e0a0303090302241906 71
    0x140384c145140d070904a0340c0072502503402844200500c1d0b070b06c0301030541c01c460b2001c0595001c45060303c2075400c2c011300516054000119808110110f50700140e0000340c1c07801040364240042a403410301d030984007a4050114440d04101d06c49000406030b80c040c1214001c01c1d4400280d070140000100c040d555450f1060342c10380c2c005001441011030111560307402200c01c40d8103c02600c10640b0701110341c981407040090f01603c1c100000c85041c0580c80c00f00c19290b001740200106a1203410120b516002804180c9009044541440d03200c212070914a05850406005504205c403e004020140c095020704a03040091100c001407075032580c2c06205c1c0114402d480e0700c541c900d010300020070500c0804a204071030280b00c059040c10b940540304030100340c5a1135540c0554550328188250094208030303071041d007240b1440d101081415030543c03207050840d10035802c0d02c4c403030f503211291045184c003c1c0c1c80d14001840b48034041030140e0010110310032007085500001c503c040c4d8030300146814028401c000907515 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 665861088 1250 665859838 665859841
    0xc040f03110405070503012319120c090510120204020409020c0c04050a020f07110609030703030210050c030106080c07060603020915090c1204020d03092105060a060303120b04020909090303 83
    0x7898070f03029443d44484586446030a6601d454803104028120088100d1b00382e54025491019031200d250100c2d0441c41207801070410303a03072224042c07a6060182e9050f82d40c08080e05e0085010303103490092901443d4031040504646040603c01241a0107030701040342c0c4503a08020010740e001ea540064508824043c0c06492070850309428803094840062a51003601e02c10014440300c00c0781c035800d41d4007864110034008980d80c82c2c280031811601c209034032903a00d44502ca40000401d580028504420320107624140b015440c0e100110703080d0701007030142d500801c075000300094035002010301825170341c8c4c00b0b00c4c00030421684d680c01040346c13054269010100385ca44020b4207015420503089054001d24112445460700b0491038100b020f081025200030302c81c003a00704580061510903088440a000f00004d070504501ca592107124410141c07a6044031396000f10340026000b055180304950460781c240e11501440990f03410035000030301c01d07240801d60040c2e0900100c0c91513120019900e00c56000d00c0c1c02541d69 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 665862338 1250 665861088 665861123
    0xb190906020a0e0d030909020a0c020604030b0105150301080d0530061e0303090609150414090109150306111e0a020f120d050417070c0e1008060f0c040f03 68
    0x40c0040b5443c10b5000300001c424030360010b540160200100c540300030303006031141c4511034111140860010081e5000d54042004400d01020800d030fa03040310b9040351200b61100c2c400f0f08150880c08248200741d0f0035040f0f0210a1449400350004109403021010700c1c211105000a00341541c0300100318501001040300200083c07400d200da00b040c414000e02280c6160800b02c9000643c1c3c3c6d00c40c1d2804580210360110300202641c4503025481e0300d100e004068561600d49032480380442c14500030700c0612540042c000011810018400c40400d941e2120245928078190f440d00400b80c49184d0710f807441c02004100d5207001c03100f483d4a12124002a5540030358510800304028500300704581c42d14401d803c03011094034440c122070120340f4004221080840c1581c1c80d0f08207445405441180005062030003d0284200715041c00c1040c282c8000c4100300d0000d0b110413a0301c144100150190300b140354040e0005c40c201101240303007641d0103400650410b01c2d01e42c40c0c03a0280c3d8810f4255004503005010200700310030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 665863588 1250 665862338 665862347
    0x7050d141f090603051e010605030d02010c030b0609010e040b01020c030a0312150b1c060902070f02130204120b06030a020d0503070b060d110d1a10030b0108010c0c0b190906020a 78
    0x2c0c010403400340070b007070b0858071010388a500c110118910180075801928800c1d5080d08900c00401008003590446c094201c80a03019241d100710380b000091801e51a509030380b4201e41910540c88040c4d582e0507501e02041b003400700078043d101d5140c0c10f510441000c1d00742c0d950304004801045d4400d658025520088040e00800d0300c0b032442060049200240c41485800503920907103181034036450320304a0003514030300a10b00a05194101c5130380140006034030700900101e5245078203a288240d8541e0705500070700449070101d000d6400380f0003001e04440c203981c01081e1050407031500220000c094503040c02c9560300007500b140340040115851b40000c600f02040c011482c0c1c040b54840c0003a15084800e100365650360b11002c4c62940000e10500380e941d045024040003406100728940c508030800600d0030300d5940d81d00040362620084881051200c0003043d5440180600040001c180e1240707a912201a910464004001490504181c03c02100503056023218040e000007180904070042c1d1b50788515500030f1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 665864838 1250 665863588 665863651
    0x30e10111006060c031809050123030a12030b031203130b0a0513060c11100b0f06070213050403020307082709070f0509011b0606050f0909030307050d14 67
    0x10012881c2c40000c100040c1c0001010b21240d42c540f030900f5820350314449585000c450350300100c185600c0c0100114915100051034001c15000d4034620000d104031004241d82c6030010000209402105103409000d03601940041000190003815660194242c01c05801c06030001c45040306e01020907001c50081c401180300440d0410800d80d01030100d1b1414903007203061400d4580005085a9544c4640e80810b0320409070f140d004002c00c420b40c3d600760a400c403144d02034514081d4007881032a52000c10031151400d142110b0a05134041d00c000c0062603031200481c000c00000740150154001088130f9000209010000c010710703041c1000d040481c61000d03506002e0b2910a01300c83c7c2c0184000780034040c59541040c400c002e48410303494015520011503004031100d410348500c5840182a005192081081da41c20202c182c4405584c018424500e10741000440c482c2174900d0640f540081020904540c412801802026880c0c0804540da044404000424070400c8901032070701105a014102901c0b10940702c071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 665866088 1250 665864838 665864863
    0xd080d020703090803041d060105040801050f010806090106080606150c0607091401050906070609020f061201080d0503100b0c0a15020304060e0d022a0a031203060506040f12030e1011 80
    0x2513080c07c1c00c0c10988000090351802c0842658688400903580da0311131011a40078080c1d4100a01c1070f41821f00c400050341b00e0070701032921140240c0e00060040fa0052103043c0c00c0b00c01c40340042a06441390030500c90981e11442c0003800e195400c0100340410901000aa4040c0e034169940d0b03001c641c41d15014410f0340c00c40701002810080104803050306030f581c84013a45c04942d00503400141c810b00601c00180e102c000d13585101d80040303001c92084a4540c07240c1c0d0032412102c170310301a01c0341201032000807103092204840900b06401c0e4a00c06114141241c00900070010740c0608485080e401910703010006451401000c1c281340c0c0000c2003108004080c0610301540c0302e144010004c92000090107501d40150003000d0a0440075440c52000f120314426000719465805420301e40d0250301d80c208890760b400450300c440040b0742080340c005203900b800d104690450301c41c461003a0200341030038a03503403114000810950412058103100091540c5000050140040341d844108000200500c558148207401401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 665867338 1250 665866088 665866093
    0x4060b030c0108010b0c010e07090f0501050906300a0f290a0c120203070302030f0f0f0c0a030e15060307050a12020d0206070f030806090f240d080d0207030908 70
    0x14659070408083d506448885450705d4607500c00c448014014220b040710200316101c1c1090000340241240d0090a000401d0701d070030f1005a88071800c2c01004101038454640000700c1003d04600e503a2507088291000a030b200301c0c2c480c4103040d5004c8620b0405501c0e010b0f500415002030f00d8080004004100d02c00c01da40c02c10b911100fa260a07111215003800600751400c1c01d8484c01c900301c000d807040d00f080d5141218000115128241444014004c1d00704984c011800540200440e1043c691000054441c02c500440c500480ea9400c03031003602508180315420030b0607203c070b4548404070300502030240c0d10341003101c1c2e00c1e05901d01241010300d803256650215001c0c1803802010310420360b4600149813502d4056070415044559840803610500c1880d202810108a40071000c00301507000c0380c282d0041408a68100c140e844074002200c0d42001615400c0d4003c5080c13541d521101d219803a4030b9040c100051091400f041561202e5071590b014009614066500090080801d85c1000f014000303031618000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 665868588 1250 665867338 665867353
    0x903090a090b01092c040f0209010812070816020d0f0303060b040f0524040e07020705012a020102190c0801060602030c0d0e0d1e0b0a0221060a030b0f04060b03 70
    0x601319072818040d0351140c10482c0841e030303072160000c003181c1d101c1c05240d00849801d1405040a038481c1c405041d0892040c0000800000d148200040010729440220045894680780c0d68480750154003a040d8410020103100390400941d903030849400b0f45070702800e140302c2c10398010319004044a000e070700002c84944092105000442a500d15801030b101c059400042c030740190b05d000c86800100c05a940621500058042002010b099640740902450380807102c1c1c01c1c1d19580107403600d40d054086442c8040007903881c140d0907205c94004600190060041e141c1e003081c4141d6090030328018600544246c44a0039080040304401d01c102c0b4010310162014504084000001035146c0b4265481030b0200105071404c0000c65994034008507900d42d22510445510444158a6500e084550401c4e100d944800001441103c054000c5440580701180b48140300d00c42082000c144020242c141c80c0c10001400d4040000344030000c51500403803030180c071f201080c40d05e803905138142c13800010018020b800042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 665869838 1250 665868588 665868611
    0x10803210702030717160c0303080114010c1112030d0b01320d0e010f09050118050705120c0307260d0e0d11101d06090a26060903090a09 60
    0x2050f038110390783c008040c45c01121810341c41c94081c06024081c0408a416100c0441003286190703c039070032130344a074548003041d0b80c6e40e007454650309881307040780d83c04138400d00400c400062003450020415400102070700410010340040902c1d540000c0d6030004401d0fa108045045503802088422101c04603403a0a4208005d200403015010030850103c0c1c1d8032400421920009005d070b421150201c0b07070220007000a40f0110920001505044009a640303501c0e001040d50a40140b520302c3e4083c503044002040d10074030380014440e120403404482c800c180221904121140d4080c00130f01c0042c00280880044030b182014200c4095103403501070010340e070014403550301558025031000c5171504112100d058806160800c145144a0b400300c05502c5410704010184260704882e805c00280ba0170402100d000d03e0050600444d0312031280603580c4483d2901f02000005d01002000380038140112502640640700d80300d5915110341a18005200e030408500d494403414842044801090f00400a024204861 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 665871088 1250 665869838 665869843
    0x609031e320a030203070c0f030f110c030c1306090f09020a23010c021314090105100806010317070c06020303010e160804120333050103020304031d030a0b010803210702 74
    0x1560710b000b4140c0200020b80301600175290034148503085140d605900c519840c00500b03002c0d02c01d000c2d02c0403d001021001d20300500017528210550301400501041c02d500c000c01088216015100040c0303a00c0703038008103886150380916151071078107001c04a10021a4810804800040e421005000c032806421451000e801d9501001a020a08201d00b4803401030012481d8a1920030600440b01c0c108018009001040c40555104d0803061008020b04d8440400c800040c0707200348100125540484014000700ea001880c0d04107071f00102c28080d28100842d6580341841084d6840170f40503810100040145200300c501e81503215500565600d10782034a40005003410300c01420141c459a414058208194000d07400902280c00040c05d030080b000d0904415800b0711140c003032408040c007110b600020554083d000340d074000c3d98140c03296400c2d0310442e5500c0d0110400c01811039070501c10600d038840407445030301c00213001c0c1c001c080142d555800c092070302d1143c21800c80c54002080d0082c5082007a682d901 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 665872338 1250 665871088 665871097
    0x6030f0204180305121e18010c020304050604091a100f230f0703030b0405011e050904111302070c0e2e090c03020c010e06091203130609031e32 63
    0xe04c80441d41c3e511595034401061407003540d505e03115804181444203108506907d01203141409000344000300c01110304a03140c1c0100d1155a4001c007080c0020300c00310000d80c0241118011202e1400058007076840016580201c8440c00c5001c030300c0140c20703e160a0741c025000d1004003503240c07a42c031000e0498240d0810381e120b40e81d040300c07110f01d000c2012420148290050410404014020f2120307503112170042c80c1e00300c150811078048a07a02c01c3e0002d10760510601c3c0c0c5100d0b17a04403606114a845000c140141c02200c54154a155030b403c1200100003054101ca03c0050320110904103030a2a28a120807051510744c1495105003861a1502d004814036400210581d107501c1d001042d41c074141401600030f4081d8803100c84255013000e0304a402c200340000c0080c851031031281150421001004076000c544415a00010f0111b003850005000c1041504540442d51003840c040c4c084401d0142c0400c01c04e02c121034054001b03850b402d54545c25103420018100000c40c03001840e0b0b0b0341070890040d074405100c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 665873588 1250 665872338 665872357
    0x21507020d0e06090d0b1812220f0f180b03061b040e010815071d060702010504080f0a0203120909010330050d061202180a0f06030f0204180305 63
    0x5082d190050030b5100c01040d92080d84000c1d0240798101200d15000842d01400c8940040e00d01c0e041403800035030040000d2100800600c120703103916103202c0110202c046030803284000c0402440b201c0005400210b0f00000004200c3d03a401200d5960401803034025104c00200e814080509002c80d1071a079a401280c0d02d60031100c115a441926030b99900c7e4609140560b5202980c5030b000301d80001180780b4041002040700011412503d102c0c0d862100c00d07141280501102100c884a401984090781020002040300c00e0050402130304041e03481e44028030301211a2040d1045800c035070282e901b141010441c051413180600196070421504401250314648144005030070078a030b03010038214103050410b52215081607124007402c54807144070041d0880e0312030550091102c0c50280c00003445079801c1c1340d612120740d000708410040d4006021a40580d60003800d91440c959803000269182d04d602d1007060300039803041482c455a00c0043c010441194620000004042030310071282000075400021942d1018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 665874838 1250 665873588 665873597
    0x20304110619030f0f1518020c0601030b0601140a021605040c020c240406090f050901030f080a020c09010f0812030f0c071e060605130605150705010b0a15021507020d 73
    0x1004e10818001034008240842060362424905144180c0c003100c0d000243c80702c81c0c0e0908405d0320b00c607000d8402c03407060442e2007400e070300204014030000b40030302841c0b50003003414507007001d504580210300c241c80d038048401e800150340440340030388480c203030304480000901c02182c082190040e1154017075221100034809a105440082980c104e072071101040303c0c803010140d80350f88e03142c0d500d8900140504400d0302508100d0355511100080302d15203652140d041e03d034030261550f040d0b160b80e5a82e11030343c0c1010385a607056000343c0200d1003070f030303141c0302c0d000d0340204610007607582210f00d06548281800c00140140f00f159104004100c0480c1071a0b6006400a10a208803551040141403045841e50641d801a00400518030210107000b0150403040c166602210010908425844200203c0d503540c450700360010801110740042000710030203071408900880020030598900700009092081580007144400c062442101a56a0402400d244c8004020541c001800c007644041d5455480040100c00c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 665876088 1250 665874838 665874851
    0xd09080d06091a062a010e28031d0402120406050109140412050703050d0606020c150903120306030307021201091a0708190219030c0e0613030f020a0b070602030411061903 75
    0x4d289648611002c0380340c80081081440c447d4501e51140e8003880c0300c040524001741c644100d8080d81c0703185071041d64941c40c4c03840e02070b00d0000380b50305500e0307521890b941c0b0690910183c03032007034030b180c200c2c5126522881d80082c4130343c10f000800048510541d450042151042c04000005014a40d0400400b4a9040003900c07483d091030704a403648030300c4410558181c20023600042468000500000103002103d042409002880781c94640d8018441d0480e031552088031310b51080c10fa103000950f000400641501d1504c085900071600b4207018441d4a00036139034954106040c007641c048400500b071b000d6001d000c16401d01c980003e00001c006442d07240c4100200310310480103c0e60780c1c116030a1002c010000f8030052400c0c4c1c2c1c081c00504034803407801c001c81c000340c179003a816141041c100e40c444009284000000c2c2c0c10342d02d40a420940c0c1a03412a040309070f203038010412500060140c04240d114280159413864549400503944066550450081400b48510b00f400d101c031400c062010b00040c80d0000f5032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 665877338 1250 665876088 665876137
    0x12010207111c1a0417180109090218091008070308070b0901061a13030b07020303060306090319030b0402070f0804030c06020129030109020a06020318061e0d09080d06091a06 76
    0x103003810007488000301179001039040c2050720171070b00304c2a105400743ca03140281c030fa07100c011074213911800058034a40aa400c0300c2c000c0525144101681040d520003030303c0c0d4500d4031170010718585140354000b07481c007000114514003007003015542e031a88406088001e01021746411a41101d941c500c080382190040041010001140c12007804401540c001d4004490b509100c0d0010b0b40700e510a4490f640a8000c4400007400c082001088540e89404e021240700140c504660440c01801c411920641c4290200541030100784403010791410300303011348000c9039920300d1440d01029203050365200e1402d590402e1312503200a100c4d85082c425408540d60081c175202e90450000c0d0042c101c0900080d442400c207040407400e0341e400000b41c0300c0004008180e9180031800d004000c5940113006503270013019950092892031600302c0c0050840e15120303010204019010f80e544120f2600306890100d012070703a039001008045070a0007113a001b20021000b03a0081c18622011034854481e19607500906035160662146 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 665878588 1250 665877338 665877353
    0x1e0b0d1a04260a020d0c02031c111608070603150e092a010e0108060310110c07060c03034704090813080607080703050612010207111c1a04 61
    0x8040c2c0c441d00818240001c80701d02c0600981003a10702c0e0006104243c407010324207010307030881a002d98008005010032112040a155101d0640e207a110401041c10301d0080d40610803c5090186261180342049080c20610824980080d0740d200c8010503080141181d0a06a030043c0c41040e20701e080420011640e591001c186898080980d805d020038810940c0b9019902011211141c03070026a0380d42d495109420044908101c281c0d10745a00d9040301c001e400b003448e41d5074040903500c040c1c91075003400c0070541c04009003000f04561000000c0b0f00601061420181d042c410440d92001c4080b07100700c0f002c81d01c0417800001c4221404a04851018408034445401e450300010300788000620611400041745000ca40c541c0102d030a000074507403142c9002c6103040d0041900303407081c2e94a030b0740c0e03040355502e41030118080c1c00050201e9401000740354080c50148400c0c0010411a4000c0c1d580404008c070035070602c60300c04081c2659050b440313200350000c0002480805120210301406462240030b072994200802c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 665879838 1250 665878588 665878613
    0x41109060c0c040e030a05090d110a080c0907030501140f042702151e0d09080a02150702120a0e0301270317060108070c0c0305011e0b0d1a04 62
    0x5911580104203081c0d00440041c9880e40d40209540a002045103940742d59584c0c044c00101c90b020850a0084400c18240700b550701d04480d0042a02800b03442c80400030034000280c030741007440307244c010b02d1101e83c041c01e00f12001c2d42c1024941c98100310644c5400000318110010070821407040120210380c0e4143e946580007000d000440d80561100d0380403a03000c48140d0111a60202c1c0200c0b01d010180a094031030105994210002c94103142d81302c0182008144140d01030560410b2559495400d100880c1c1244042d2207449640e030000c103000e0217031203170001d0000001015481190f1000032103207000711a41e01a941402d44509200042c540b83c1d42c0080c1c0034100750540b440d0030202588642c04030854482c0c4418240d802520b8001d10140c19040590100e403003101e010340401d0440c4003083c0c030f903032194540281d45405840106101c40e00c959a090940320045c1c80d00d020081d107864000c40740d14142c410001191004c44607440c001c5156660079500c43d5448942d2003415901c003001406004440c1c8080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 665881088 1250 665879838 665879857
    0xf02032107031e0207051204140112150e0711010c1428030c0f0905092d0708060103060f080d030e03070f030c11090906040212121204210e0411 63
    0x460500c90f80c0c0f40342d00000e400842083d10300f44507400140d8001040003086805440c144800142d45506c280e00548560012800c0c2e0140c0960322098100a00e0a01c540c0c0805003e02d500d2000c0a400e000c0e82c020708112810019114592520140c80c44c2c068001c501d43c0c0c4a10550203c0c03035181da01807400d80801803002d0166000d0300c3c40036510401207a503d40d2040e02071142c2030b103904414200314041218080111b0140503001001c482c04500401424402c40c1b241e00d0009070184131020400d80d185060b100150b03080340100c1d40000601016607018041e10014000e5980c5500c030951a02d111165900c85020010702810b0351000074030002a000c2c822540c129400c02c400321284012460000d000c8802c04a080d0b401441d81f101c00d00040c9040c2c111540203d8102c401454103441d980c081201c03a24004000d002d40341f051004c1d040480c0320400160160517020b0200a450b450281000803200b01e02e068003984009091303203407500b003a07080444a8403500b03081e200081c407101c071200051610320840424 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 665882338 1250 665881088 665881121
    0x3091e0c04060b0a0801060503160c02040e0a0605010e0a0917071a040804090f05190f02040f0e0907080c0604030b04080409050a0510060207080316020a0b0310060f0203210703 77
    0x310300740890784018940f4121503550171001d40c0e41c4400440c1d1501050b42c180c01d940080a2481c0d001500c5500400308660008000041c3c1034005001c05207050440c103c200c0da1603464a004115100b0008035080d40302888180602906520390349044403d1004410360388402404203d107401c0c4000000390421900c280c3e00100d42d1800d0904040319940c102d0f01c01c00c02410b082c8101c4180c400001e0080600504035907422042c00d028070070004000e460382802e8048c0715a800d2000050040c00d1a0804000701250b00a501a501301410b849060045d6608501d0031580145800d803907580ba40710466040341d4010203662130b03a40361031030000450b1199034082041d03513007002c003400144501540b040d40110a40809605583e03581c520681e22400140f0850241d50401d003c0c60310010340c14030522460500c0207082910b01c2d61154051030541e0000d583c180791410003694180581904080d084d2940c1019000440c00c1c090096001058006020b0078030070000c0b02c02e80401c0c03005001c1c1e00300601c4074000002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 665883588 1250 665882338 665882351
    0x507080f0909040b16030c140c0c0907170a050c03010b1315030e0d020703051c09050d0609020315010b0301050105070519260f090108100b0c070e09010203091e0c04 72
    0x3000042940306403112040d4400322005d101c0f00500a10407030017540c03110380364004a1400c000c00c2841e0740d042134240e0410f6000384020003030b1680c0e074252450b1182070291a0284003900039000184004401007090185501c1c00d410301c030340401d807002628119240d20182c0c541d91448507400714045146a030280d00000c40c20030b100e02c1c00741e405401c145041d29040044841c40007003004201d030340c2e0304503100c09403042e003106900354852012040103030401c0c103250820452141c0c0e20310100700307002d0f002c55095a10940e25012a0304520b01031048480c505e41c54001c1621550502140340f18610041c071505040c06030001d419401c200c1e051060820024004a885c00000150b091491104c100ca400b103803240c43ca00e81507003110844c504142c0b003014120314503884c00d000607040191410840500100082030144100250803c8180c004040210380c5002170488076241c00818140100080c01c41000d6034010700c01c07c403100030002b03000c080302d03180c1c0f00254a4400405290908109840c0c0c217180e0802d04004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 665884838 1250 665883588 665883593
    0xf1b1b0f121205070b0c0306032805060123010804030e040e1507031107141606031424010305061f1706040603120806130c020c030706030c0507080f090904 68
    0x2207a0307803250040c141e45009828030707a000c440307610038801d00500300d041c441c0103d589000104040e5038002e50280842d111070b24242400203555940d04041103d840880310f0b84d50410000703115003070041491105140c00000f45c1d20036840001c2400443c203040108580004060600c29826820b803900c01a00400591a0074110a070702d9002c003d030b0b503980800450000ca611540300344514150304000e40355035030618210355503138001000d4041903000349126040d4130707034003892450f0030410003842603440c00100c40e107499a180b05510300040243d005090381005800440c10241e0b800e0100050134600000c05a0b507030400283e10220013800c01c084e4841c002e025442840d00000404000100b101c05820359a45810410007500c1143c0401800003100d54064110b55002c2d000f003d0304082c00074402010f20b0810b074a03490448121801c08001a404500404c0c41400e0a0100f00d0107009203140900c5a00c80c54400900306208064004040c3c000009111b20040c2c0e05c8020b0303d10f02c000003810022141040e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 665886088 1250 665884838 665884859
    0x31202030a1a010504120f0507030506090307050105061906030c0207170a150b0307051e090406090201081e2a130e01170601060c0302030c0106150f1b1b0f 68
    0x3101c00780b81e41c02800d07901c03948a40c081c6042c4c8080b15540c5824481900656a03520080860800c1c1290719104507031703000c0b00003017061115034490081c50004588500d02410000e0075070b800540352500503401c900207154161180c0303200c0c1c001e071980c1d404c021031300d800001400ca10f04060395204507007100b170720441c4d05d644050102d00102c40700d0188600c01050780860284108880045038104d9160740030010030802401e10101c0024400003032409032062919203400325245c500d04990484086580d10001e000715070300102903940003c84004110274900710b140080000303007406005a22000e00c0c2c1a07171180000345510307010412080350b14010b40c0b28500c03020fa14070080254010002000c000d1400800e42d1f15100340c055200e501080001c2c9241d03407800400340c88008400c0300990440c0030801880c941c50030240205002022449201007165150a80c01804e40c226001c0002c00c002d480703050006045e50550070105200d801444489008080c1515200700c840c0d01e0748400c1a442c100c44001490343c0d1113 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 665887338 1250 665886088 665886101
    0x151403150c09190510030513140717062401120e0a1a13061802030a061d030c030304030e0a08030a02060601030c09030c0b0307030603170702040c030221040809060714160e040609031202030a 83
    0x1750bea25685110744601140e1101c3c41201d00e40400c2c075240314040c080c01d002c07802c4186d4411041c1403020a04d18005240d81c1030303d0544c001d18540e41c0c0710352140c50402000701c3c04c06480260040e1901c0c00c40c00c1043e80c21211b540145005041c4c96120180f134580058428400c0384450b41c01400c44000d10220307e0301802824440211030416005120080101c0802008460503030324440c002c0d5141d550b660354191054800700005a800012444020400f10400c2004018106164000703280c6403400c440010b0a4488464520041040b0213038100005000d40e24140c040c0c41c80c082896840ba900c41c03800701c1c014a4298005814101041c1d40c0c54003040b0110001c4c06014000c0d44c041c07085400e01d8a00f0340c10391151100d8040a100001100c1212507803074440590401c0c80fa405c07040c6000700c3c5000250f01c179000798000b13440110b4100a4205149000c002c90ba80f5290642d0000d06401d290038511018150b006002030030741c47e01d8001c088105449904008040c90f07840c0000c64072400c01e03038a0300004100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 665888588 1250 665887338 665887349
    0xf1106090402220b0405100809030d0c1e050903070b03130b04141006031509020a1502011a030f0607081909030f0f03151403150c091905100305131407 66
    0x3c180e0f070b001c200054424201d40030f036200601003100305109040d0445107800d004246002c680400d0019140301c0d002400f07101d001c00c04559070303d60024078100403010441084149242402020000d418260b140410540200e4895544050b180c1d81c03401441000003405001c0249811503140070403040042074034500300c100c0c3e410801c40c1d407699030528071501100d41a00000d8021134221694104640c22600280c1c01944042d11000d203180da0307100900e4107410818807410242c1d4440a2118507401e0740046d003036084500b180142101c1d00000d0312140c9038000940320f10101301050300040d9140c0f809211044450a003850100710701d004500b00180f0380d02c0316860b10300018403805850070000d88070f8014a8408440d802d0201142d41c41c00c4103208261030024000c42c0c05000b04950b6081c201c40c0e5038402072040c11b4a10005a0305c5070310700d00f00410000c4001c1e03400d000c42d0b0041001e020310b8451075074072900502c0074180000d0079100d00c24034603030700c00820310001d0500c3c400150441d000100420306004451 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 665889838 1250 665888588 665888647
    0x1407141207021c02011b2319062c0102041d160f03060b0d0204060908030f030105040203190e0109020111150a020d0b030313150c0f1106090402 63
    0x200414504040c0d11414401035840703890400450300b070740001000700014610505204800503480501d41d0032881007080150342003118170351714074034440782c41c5101c508001004016005035045602410b943e00211000034000c82d64641030a50b801d5000d00502d400030b9885040207000c4041418414080d600a01a0b88034001c001039008009010b4800b460b4065910081e089550018010b01225418030500d55101095101e400008030100380e10002e12420384107200150f941d41c03c20394040c0401d0000d90003041c0d603a10400c40035614809180540b0b056a004a038007694130748859030411403038240c0c0000e1480c2e9a01d0890b02c50394440b0158055903410b8400c3c2c80e0f60f030141015001c03454507a03145258124004420500060349540194010600c200d1b001d10001100074024010034a160044100036800603400340d0b080c0940350b00540b440380841918034201058032103541d500790b400b070302c0c20b0b0004180454007031046510741e681405440d0001c0e0058011903c4180c03088152a2030120b4002c0d55035a071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 665891088 1250 665889838 665889853
    0x20102150a0216150b0d02030c3a0203150f15151602040f0501060912050f0106030503040611060105220b03010f02090f040501140603100f06052106030d030c140714 72
    0xa00340105080781b0316070014090f20b0070141d100f00340030700040c3c078100d102d500717940415034031544036403402c00f513007010011401400c3d6201c000d02c18185080d003502d507100c1418401c0d600300701c0640d0003440c1507584400507000c16066105080c0c0480ca440c2c1e4650803561004102280304201400210302251030203008540500c5241c40e100d0109007198000e009500018400d40c400703002c50301d004010486110b105204072a4400d403c40b4000f400c6849a42040303806130000201040056030000d1748480b007045070006007a01f5450100081c0301c52050885488012002110003411850103611070b140c4408003034000e1200d90701c0c41e450040258400d0703941d60710074610f4038010f003118140b51017010b058501003d0751b4500d0364400ba0402c80d03643c20050034411148058007002c1019100d05003001c009203e5603d0f0591201c40701400c03c603c000030711040c5451031401004000080c2da000070030030038140750f50400141c40d44980c14116500e60901c2258400400000303040d008100c08a024150725100e4103040c2c401d0f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 665892338 1250 665891088 665891111
    0x100b090a09020306060d0c0312050307270303121b080106030c0e031b06070606091a180613020906160204050f0112020f0d02040f0603020f01020703020102150a021615 73
    0x48541d80d400294066000a001990700d0030000000e980660045001c41a0183e172070360380071a41050400394000054001c8288200940c000000c0e00b4070003008131210509070045000070304010654480501000f6281700c0100302900c0651020038030303440c100c000c041c00034244a0060305880c828460b541c000707450004800790091069041c10b034241c074006d000c0c3c21219064071201e0584031844d44025841103080155900003400e502c2120024051807070080340c013a0032203500e14600c1c59216542070141c003802c02d41c03641e6451403c039201d0307100c070007140d904420011481405009029003400c0e0b90304031000280e507c00e042c4038100700c0508603200300c0d0300344103581d1800c0350101490b00c28800d13a40b03000c80d094412001841d10302d15403980c80d440500300a050810a4001030180c40d042c1055805075980e03070780e0500035820000c051010150080c0001d2880510310340c0000d40d10b00500c814000343c1e02c140001302d90100030540464424410292040f0b440c42c1060514104c003400700d50590b946213241c448a2100b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 665893588 1250 665892338 665892341
    0x180309081c0801120606050d05060718030807030f030204091503200a0603090807060f0e0607021b010c020a030203030c0f0c030c0a0303081b0d0218040510061b05100b090a 75
    0x1c0403001a40d50103031607480c1c2012052500103100044030826112113000c2282d81325800c803007066601441c02030400341001c00c0040c0041c035034007200b111016411f00061010440d140c04403494070741c0c5898040200b100c0004110007d000b950003040801e8101803400c6178010f01095040d040d80e024182d0a107030400e0041076810390800d8001d51503040400000200b000a01980c8800740c8a405840000e01d054000d990308001c94080e070308c3c0194074654ac2e8240014031602041500d070301510f6030000b8600c0c82000400e44800000320b00c030560422042425000c21511030603c045c0c015980541203c0d21243d50075102070b06d50b41840110030b0584148203000007540b400103a2075003c3c2e01d014150307030055411034404441c0b9035401400c030010f40c40c0c201c0b546600014820010305031503038010030050320f07213003110034024803248604940e078801d904000071f000d445000303090408200c0d441ca05142041c0c42c48041054502103071040060100d0151b45882c518600780b68101001d07400003143c03017441c580d03501d84a600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 665894838 1250 665893588 665893633
    0x904020f03060c4f03150c030b0109030201020c12030c030a02250f1203053a05010e060d0c030812061804050a0308091f0f140c190318030908 62
    0x182520350301080c600100031076002c06001050000800c20305a6244d80300c6c1103005c0001710000c02c0311655000c0211f880343e85446000a850024a4010007061075030300002e40d1952000407980c0b10701d40080028108400401c100d40c04c0c4111182529250780050001a494060348440102070160140001c4440402900b601c000c0d03a02c03952102c2d00a07820700300b0b04041c680010310102c2c00d0010400c45114510b9400115200d10000c141000180c94070080a5000c01c062046403c441e0301d040000610055000c485100e034003c200b580c486034101c07298103205009020507800542190700001d02840011000d2107400d10910303054500c15403101003460044142d8100301c80203416a00540c05c2c250000384505074880e0048440d008603112781098003410b41624480ca081c24660555a40c54050800d2a0780203144a002030680c0c0d03050380f0b14003da180001c0c0d2051484201c0100a56626488014000d03446091849411045440b1083d12440c0140114040303000e03400e44c80c4151505421452038050400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 665896088 1250 665894838 665894917
    0x230114040807030609060603020306090705030d0311030c090301060b0f07021903201f080a0b0307060f230408010b0411090a210f1a0106090308090904020f03060c 71
    0x5012407843c60300e945000300070820003194a0340c0c0f19007000025a6003048024064030659001e840b85500d010300301850412038030018814942403203401c0840c01700711016281c0c400700c60002241e40c0c11140001a004000a4000d411044800b04445010034000d4018040342803007078400380a25440e03001044120b182900c8020203412410066440c51042c0701e100d2031140402800030340d4841d400b1070007218840c480b0710b80200040c891004110200c00540100c680d007060130f030041d000c1c980c00c06800400000320f405158090085c149012202d021380c0c0c403013001c0c229a000d00c0560322a5203404406011b4143d0050803449241021482c028001040c1c1c200c481403000280106c002c0c0d403034694001a01031300d03103520618820081c101800440c0c19100383c118486e2003a40c0c0460080800c040c2e0b6015141c068004c0c200704906c81c02d0a20000c4c114604485840c04200e40c40b01c860380d12031000541d110321020307105816004940610005000c40c0300030300b240e4045202c80300c40000c103400005121041718000e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 665897338 1250 665896088 665896093
    0x5071e0215150a091802010914010504060c031205010b0c100c0816030b09150a0b0301150e0619030e0106061b02150d0e07030b0a02031501030c03062301140408 70
    0x42103050b80050301e185440c91018200c80341c030b295a03ca40d00300316410048008000d03000c00300040219030703101c0c0300c0c07801601c0d14100030b1301c4a004040000702140113034082d100134042407003190014540a41c0c0540c61442c00058140003c1d03845039410a41c607004000200283d12480740207084d07102c5503010720b4020503066038900c101c0e6641d0980905020040c0c0ca00d0304103040e41c41005003801e4a0750944644120081140d82415000030411f004030201e850303001c401305c40300500040c450701903600416a040b0031180341c8000b103a208000001d08600c9503440240c2404021000c0107a015010f80100c051100154020008503580700c5081d1030341e400c00400300700200c454032184030046c40d01c030750880384000c1744010081c20102c0c004100c80450740ba1104410203580070080800806c03074200c003216406800300505604504200f80d500031140c1c03050b030b16141455140c1c40381d407407042e00c0b13503004000814214540c22003080a054604070209202203c42c1d0005259407020801c4900110440d011120135500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 665898588 1250 665897338 665897341
    0xa020a02060705160506100e060a060206150a1d0106030501210204020c070e0c181203071112101505040608030d110915030f090d02070e041505071e0215 67
    0x400c43d91648100e50044860382c1e8160900c000c9241000743d28401c2098445460b0540d0404103445100d0b000100780078840d1002c002c0074840b140d80450225040b01141d400e030301c10780000318001501c14480350801001c43c45001e03050b0300f10051542c6114100c1d070703040d20100f081c0c0e44c9890404803501c41150102c10746621001d140001400d10b40d000b4825114000300ba03652558407040d2003070244000782c926440914002c0340208111420f2800000205d400f1074203007016400c6400d405451380120940980004152080f0303503515100c0c03e500c0090004c200d001d960424142c0912100180050301c60b090b001c0c01c5240740802c0506151041e1810794030500025410140d100391503402410702a4002c00c0c031603406008001803a01c40c0b0341c16101c1d00d4119a042600e130f1900600442004500804141c100c2d88080c60a01d42e094001c541c080a80e0080f111a04e482c0d6141e080620218030002101c112a42c41c2c4010056801d92000002902019812110340704249850089130756071410040d498000c02200d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 665899838 1250 665898588 665898601
    0x60603030f0304060605040c110d05040e220813031e0201050708030c04030606030c05190b040b0c150406050106020d050a080703091a0405010507030608190201080603190503120a020a0206 82
    0x20b150711a1140c10007040341520790011a068408040300d5602003044944001c05c50320051150402d418400d181950409140ca20104c5107500c2c06840c0e00303600c182207241c1401c0210402c512100711074224070016074030103040c030841e880003d0341e01c400e40d029001d80300c1c80d40808004d41600901103405030b42d19070a00609882e00ba10700d60002c0c10349000c0e400200b100000180032070050100640c000d2403400201864201804100d200c8254a1108040e27058001d00c520700c180740031b440c107843c0403400072030312160f002421515180c05899120301c0c0b00c0060003007004114454105a05035541e035402e50b48856090203055650740140b4000a010802d6900015400e0b4801d134426160280524454a2400c0c0719004900741c0d824141c600355001e0751030b1400c1211079a014020880201684802031103103000996034550702e201401002030411076103002160640e40d003005910b004006044100c007040700c481c03501c1641e0341d1140d103c2480340066040003540d400218400d4642070045a00640f0450f503c41c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 665901088 1250 665899838 665899867
    0x6031b06050705060c090a1502340902090604050405180c030a050304061b1b06020c0609030c0d0f0c0801020406030b060703081603110f070515041e050312190501050306060303 77
    0x210101b94100203210301c005030b200d1a05c200c8440510701d64015001c44c1c00940b00d400303001ea941880340d0040d000c1c0000d80550260750b101d1440121249a5401a00c49400d14006815032146500c0a90700605010600440d43c0313a0b0f0601c081c003108040211104d801580080c11b40340c1032500f00161868205110070484a80200f002000505022010f809205c00300e0340e500301a00c80745900b00380101500e40c41400900e404210404100c00c1c1107030001d0820a0740300000341e0381c02e8a072500502403010035985004201c000d03045080b2650340241210f505640340c4041c00e000b50424844e5400080c18441500c0e51405c0100032101c0c00c80d0517540360000b41d03076041207010402210016100415580e074181009100285d4050105146400e140683e02c5296040c402d25242c0e020460707100e000491010b02000410f41075280b003a01d0840848600c90002074140f60741180195609006c00629960422052802c507030000e0a4400f0307d60810030150b40c0301c0c1d080c96650001150540c1d0182c0c0200300d80402d90380390 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 665902338 1250 665901088 665901097
    0x40818040f0e011a220b0a08010c08161b030804022116170d110111032805040c050d0606090608070e18060606090d050106031b06050705060c 62
    0x24102052118584003410110350003903400003803a965502c03c081a0010301030202c0e81c9907004540c424211400a2000003180c501c0c298040b8410b82c0d40da0030200c140e207400344900008c0c001030f0020007041542d0394015060030801c03070b540c1c001c030044174071011007860090603000c048480130201c200801e1000d50f0280c443c00b0003d0001d0b41d00c51a02402c0b10000503120800d840f03c950280d000d000782c1400024812211100c9810540c00c0b000f060110710241d0600040c100c1c5400c0c01072600240e903651170f005050040000c803000e1008a0350000030000d0b0040940d00d18078082c40208642c031400d400039100e0700100c2d079003030303078028405d180703001c0c041201c0d1802e0012003038440d001e070038001100c039a2241c01074103c403902d40c01900301c0d0b00510002c0200d80b8000116640c0186100135511240c0c2140d0042501c603100100058403414010034020700da84c444001e10034803a9405002001440d80f20f042c20602e000200c61038481a0b88483c00209079581710303a041d1001c1c95845002042c0310f0700c0303070705801415400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 665903588 1250 665902338 665902387
    0x30e09090316060213090e03191106070f2006070f0509130906050601050307140a030207080a08060f0a0605070609060b090403110717100e010f0207050f010f050408 72
    0x40c06031200001d004031503050320b58410701d0300580c0c800c0b03a140e164880d8038880d4007008400d45041004c20004102100300c5000310051240328601021422068449001249030020244158010050300a4200c401c1024200c802d4480c00456490300303098601600b00d000c590060364000ba0f000c902c80c01d00515120809217010300740302d410800c130715011500c0030380c0e04960070200c59194503070642482180d02ca2030303401c0202860641e10310b15040c03402401801040450070154107002501c4111103200b54195110039512031a503554400d6600c000512040c003d039809803003803466690110451034070210780740c00c40d0015103d103410621280c842000402040009072011600c8000e10a219950034101d40d200d14400e480b669081071701e00d80d0542c6000303000e401c100f00f01019080e029894034400221400308902c515004214040c070010030760701405a0000400107503001040d0340040000c08074402007542503881c003c2204c3e2914546190a86409440142514800300820420f170042030203400404013 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 665904838 1250 665903588 665903593
    0xf0e040b12010203011d0903042108040909020a23040b04020c010510090e0106050105030609070c020a0b07021509060913090b0c030a0e0f19050a08030a0603031101050103030e0909 79
    0x569090110710031800c40300c0041c4a0ba5030000c0140700742600350811601c6c548421084108501c0c12250f5075a130307480f0750300400c0004003c6210030504400200d0440b4462903001850700e49aa903182144400303040c2424040340301e151804004603084002543e2082c20000000141410380f401400740802480a0108287c0180d020400c03a0006642401801d00031803402900328a914580003180e01150352160340184142d040c9101080b16a0344401600d801c00d0044940c90450340780c1d51030585003100a008000e402030846403001900c01030420181140500a6a07a0b19610b011002030a440e803040c058142ea0090b014403072110103040c441e00c84100c0540e550000166100c154950150303900007107862400e400000010131810040c640556101d42d801d0360010400310b103074110307159220700502642c1070090003024044003d0003020407054403200d0300407410560f2410704040e01e00c00b51425006c2a40403a24500c0841da8200e414424a4100c0f034240c1d65a02000304040c04010a008000c0c081d03c40a1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 665906088 1250 665904838 665904851
    0x6030b010c1b0611010903051e1605010b0f0a08122a0d030e060601020a030815090a0209010206090708100c120e0c0f01020c0603010e0405010204080a03030b0405060a05010f0e04 78
    0x20161a014800c02c0c41069480040a152500003040385206806115159041030000c4001039007010681f440c450400e505101140300c1038040e800f1303a00815550b4080038640e01c2c1c41070144501940140c0c00c450f000e4542140c2d481c0e040c0103000d21010305100d1001c40d41c0c41407500101024118015200020a9522000c0102d0322480084081216400011401e403c004e040700791050709440385070050380c03012018010501d4100000303501c1c0e540c0c0e1440903043c0101c01c400501880c042c6a40309034054001004400382d4200550600001d400c4810b01d0340c050b116171000700316900400501e1400b11220b040013401e12403042440d0384050040381013404184840e628200c0b1780e00303001e8080c950422202d400180301d103101ca682004000c4845000c1a8150b40041c8510202e40c1c9500007100d0644800da00c884080c0e444034a840790092069a12068042c06000c0643d010598075801101c2c40c6c4d94112002d014075200c207800c014807203095201d11400b0a2a4148030003500b4011a400b14941c28000c1c00014003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 665907338 1250 665906088 665906093
    0x4020901031d0601060e270c1b030d0501080604052e11070c0b0307120e0c031e0111090d021009030c0b040f08030414061c02180906030a0c06030b010c 66
    0x508642c0768881d04650401030041c0509580010003001d03005007265401818400b030400f201000b62114034940e49025185c00207a8a4184401203c51803d44006e031285903c1d5000c080070780700d03005032440001c118180400082c0c1400000381c81d9004503041800f0b000000304658403140d0246495000043d14150a45071503a8200c1c14402c10b0304090f0702d40328080c0e41d241d10380b502c41c0054005030400c0240c21401e0041c0940c0c164400300c0013541c10032500002611b00c0d0306c041340c00d2421152494890303044c411100e0302d4000381da81c0401c0310356010000c4000d106004510300300c2d9629006003446507401002104060001d0729020401d80440b40c55401c00d805032a8990301d40d0844012550480c50010400040c1000b0000340081000d004000c07a60185041c40e0034100ba484c0b00240070b01c6c0151003020301144d501d202c080c40c200507014090384000110344e2281a4107006d0080e8202a4840d0306c11010000011201d050118601d45144d80c007820314106641032007010750003881c2d000b0620741005401c0007440300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 665908588 1250 665907338 665907371
    0x60315060d020705010b100807111501060504060f080103110d1a010305010c1b020f060f120108100c020d12050a0212090703120c08030c0a03022b0c0318020402090103 73
    0x240340940744015a8640042c1011402e4503030f002012809210440000004c80f5403103410b56030050103910f031020f841c44c1c0c00e02c0c400340b4020b100380407840c400c07450b04000101c03540c00a00400841e001512011a031030902041501d00314070900c0060301490300e404280702186041c1c0f4140300203a108110403252403080707204206441d2401d030402c0380c036699100344004826400c8110309500540c00201808410034541c08200e007015541000c078001d01010401d0f14a80c1264000da50400000700a400503070340e560303003280c2e0b42c0301c1c190890b1080c018600705050f000c40f8808640e4191101320303610b65500c02039442d200803000f00001040d0744042e035424401061000703800c0d0f207014010300f900782c0240b02c100d0842c1020307280c4d036140084070b0003400b03442100f590004d8a100d081d00d502440c2c2c8004140c9491072140c0c140c0191103540400b215102603e220040760802c03400c10981042c6040720200304800725408283c00b1516280c52905000c001c0845460041c6840d8004201070b24040c5800300f410925282c1498 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 665909838 1250 665908588 665908597
    0xd03020a110a050c01030608031e072102030904110315010e011e03060306060b070506070c051609020318071a13030c0e15041404030e0d150e0c03150606031506 70
    0x10f8054000024101072903a150142002500c41d51000e1458500131b03881c078043d1100c03071100580309070101007503c000340840c40703801a040280c00b5032841130200c00e1180080d01d90380007650302d07845680f910100655116a44064a06c40c00b2000352000c50080740704015280044804042e6040111414031045c00e801c5121010320815016100481c02c00d05507d408000c1d102150048940a10700740164800304100140c001e411003407500f003040e80c0d4032640c14502d04100702420004143c10205000103070420459005502c201c43c1c2c0910142e176107184140b040d07150740c01031003407420044807900082681140e4000800001184850407452039a0340d5a41d585490455070010700303d4be181d0b0302000011401002d44010001c01100e04010010100c8418911b0120250000d410420201640011a214011001e02081e004101e054030102b00c007680d00043c0174083d038504032a0044660490031802c000403c50401c02c085484400c6030b940d000d0500c00b0a40005082e45034044075003030220015141c0d6401030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 665911088 1250 665909838 665909843
    0x1101050c0f03041203030b0d030804021905030d080405100b060d0c120507170c070213020a0c230d0e150c0a0804030c050f060304110f18010e01050307080703050d03020a110a 76
    0x7003001445c2c1406000c690481507080c0c001c01c4400310712070000380c0c0322041d1640700c2e5040f200781ca001e248071010700410360110381195806100705100f40c0910780d0001d1805120714420000c466a40c3d1400c00e0840035900b081c026207401080030712015030300d220700307070070495200c0c410745002c180048115012206890041d40c0c0c0030045440f00b000040811200400a5440308018074654a00441607000c540ca16180856040560b0707130105460325654031460300741442e070fa08410b030120095070342400d8003d1802c1e0400310095030311640341840d55660103000420b840303a40c010122582032559a031400003da010301d402103c1e5000701110b020000d900303e00500301031809010020841420141401040340041198602c035400620422002440d407500c92070000030b09513148144c409400c008501112000680301d4100030001002007540b0400c80d091904a680403012644c0c9156164a5103803039031880e002c050680d0b08950584040140650024002c000051074a811301944407601c0c1d900303140d0400c1c402c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 665912338 1250 665911088 665911109
    0x33f020c040f0e01140711060c070602130308120f01120f12020c060d06090c09050d030c03140705010b0f0105070528020424080c03210f0729041101050c0f0304 70
    0x10301140c6c95100404003000e0900301d008111038108a0030031403d40c0503d403c020000c1c4d030000b0b02c0c0c4511a845c003903a04015a0300440180c0c072400200da401c074a10100315007203541c0403031400000420310185402c601c80b580d080b00602403179403010784410600b60021802c07841544a0181990342035100c00f40203180080c4042d80000310a42082907810507200242d13640010840102c1042c09680e46d49400c8282e01030341030418800741031043c41c040c1e90241590703019200b10300002c1002c02c28030030190040600c030903040383c1e00b0725449881d00040d2030701d0140c050050202d81c8002c4450b0120210901d08506c000003035013034903020707400b16800102518022030900000c80c440340c113aa4070481c1ca034107210002e0103140014000569961000c650703580c480c0c01810303c481c0404191800d20301080702c103c58443c0e10300e11085640d02205e0808030b40441d80145105a19006030307034100e2024032a894040c0c051a4450b200b20440c16201004481c260400d03010801240201815445008405c000500060046048 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 665913588 1250 665912338 665912341
    0x120904090606053d122301080c0114041220090c0903160b030a1104051503040215040308120403020c120d110106080c0105070c033f020c040f0e0114 65
    0x2020003a00200c8401e4120002540c001909155001141070b41c140b044405c00003071481a100c0c07601c49242854031500710303ca400d1000400c0345800462043c00040080e00d9078030001811407166034180c07045200781061101081c1e52000046c0070750542c41240b9020399110301506441400080340c180058505018911000542600504050040c0181440703201031130042186043c040803150b210050122070040c1d95448413205a100a10681e4082c000141035620100a21075049406510070b03103040c0d209410804a812429030540116419a40d000c4e540d0303420709585000301782c0401400b030001ca042d8003900c1c45125241d29071250f2104842250b600601021002c0c403000340c5520070032060308070564148042030106480c00503040f0300484081c40d042c2da80c1c01d6582032038142000d05400082032150350682801c0d10126114080401c681142d4012190003028554155201106d1605401503080780c031003031406141951004010a1202d00d0100d401c4001c4d04149007140c030112070880400013080b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 665914838 1250 665913588 665913649
    0x9030c060302030708180a0512040609210213110c0706030506010507080702100e0d0501050609010603140601030b0103180c1502030306011b0804171b0312090409060605 74
    0x18018006400c0461039400e1925004001071002403005041403107054040810303007810401800070755046019211241c0301c40300c0c0306401d41e1107031190170006250000042219908083c1340302084100c0848402245541d44c2400340d41144003420315030480e5503490351014845110700500980800f503010742036141c00c120000c0e0450705c01400c0703241008818020302000480c4401141c0c0d041e60115100740c02c40b1030000007103552070076001c825500072a2481e2020100001504458041c070340841c0c0084450b82c850808404079507107940c50500716400714001c00c1855010b54400f4038a07903010f1401083d0120360403000500b4400301a42101e918004c00410400c105032403179069080c0d201c0744084c3d2f165082040001301128452a038803504002218100760403c6000c104a80c001d0141c512080c02958600c020306444000c84410f6007807a004520806c4414031340411515500c0c10307003c4009040c0040c0702e003804000c028883d01202d4565803544041815560702946000305080351208032a002001c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 665916088 1250 665914838 665914853
    0x20a030501080714040e010204080f03031e0402092202280506070c061b0204062c09031c0e06130213020406080406020d150602070609060504080303060613030803070903 74
    0x591016480e034003e0141800454580c9020309545031040340e01050410060356520300901c9a40e00500d01449100c01910034007802101851048194141740d40210b010b101d80314115100854000394404c1c80320340047e050800360403203011342c03400b00301003038220040d280c0c04100b001030f00410002d1014a04003024810a40c112207640c05040292401400c20b1001d03603c60104130000c0c0900000d11418100c1c400e0914064402c0010707054008100f8007550740d0710281d071146200070020300c001c0c0104803d0040c500305013440480e07000c0c1c0b002d03a005518140e00032906611142281c080342003100c3e182c0c0c05010403000100711580c080c9034240b00703041030702041d0700c100003a02c10100070300700c00b130307401803004000745030b04190b0f615446604202c02581d40c0c071040c290200101058840c0c001103078240180803511590008006041d544240c40d40040103494070401d84140c0118881c040b50f9901c10400500503003031280c0a07180c55840081080c0905440e5901e20340e054000702d42ca1400942d56400810a00241 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 665917338 1250 665916088 665916091
    0x1060602010e0703021c0606090209040c0519180f080d1806090306020a0c02090a090b0a02070b0103080f0c072d23060c010c0c110f061605030f030406020a0305 70
    0x90008015082407000b60b9619804a480081c0c13152440202420441650b20342000c443c41d40b0245c200304943c0c0b140840e038029003146412074000e83c607088041992a00440c01c8502030038211750344030910f02400c01b040390303614046040c420610100000c001800074950480b10042e041a00280024040c061401042e0326007800030079401c4234600b00c0c01c02c189500100c02d4801c2d02c1d08010090fa40e00841d81e400e80300d0044643d0002c2d01b104001007000708460a96100c0f180b95031040080040c0b546031241c03580243d0260380c00103451051800010400940507100625000440040c0541403881e0f41030214204400ca622944805184420449201c031407020704180703291034803c0a007031150410440400103900c030058001c4017400d0f030580342210381c1c4105c10745121030740c1c1500a1000011280000303011184c1345500f00d43c0305104a4040e0303001e144c8604201000f042c090501030800070600303000000c480c0444420f440d00e02041140c51f01075007109004610aa005040c056600c3c490b8400050031a0390 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 665918588 1250 665917338 665917349
    0x280e0c090601051207051e0a0e09010812071401090c1502011b05070f05010c090603360305220e0a0501080303010501050d06050402130f06050f190c050a140106 70
    0x603039108012150307800c8020b555181c00b40e03c1c268041680ca2130410b684078850b121000b40640c5682c04140c02121040000b00039600850b916110202010030622640400a000301c112301d0b0061340010130011302c0040903220380c0380203c080c02000c44909a4060840701c4040068400004046041c4048e010a003008001da42141c03008114200d00c00780c6e890304445840c0c8640041000005602c81481948107100c810150000002c2001c2c0d841010040c155010f070384140004a820060b082c41e4901c09251451001c10600300e0041d50003414418801b6000341c080d101b1001c0c02018080301c0c00301c8007401c100d0486800310300c207451801414400c1501018000800c0d4400c10790412005104100e80401600e044030820b00302139813265541c0480c00090842a04066003251000c95130812010110442c03104036160246065403032500c5160440340d91081640640300c01604210414642804007040000e034121f41c913180d13010100070307900c05080100c03844043c0e80e10707a071b170011030307581c1d0002840348000510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 665919838 1250 665918588 665918599
    0x70506090a0b0a0e031b21070b0c1c020a0815030c01091403030409020310091b0c0b040c0810050f15012015010801020c0d14070605280e0c 61
    0x40d49030752500e85002c0014840ca4903281c440e15a9015500c3c2001502c0d4034036101ca04081212034500c0c5241e0340c5102d003401708207520400f140b01e101105841811189610b82054080c80139548104203c9000c0d0300c5600614005003070581c0c005140400307840038010080560341c954405041c58416803403400c507210149442500305400c0300799140e80004450f0126250003803003078109000c000008c1e0440c00f07103034000c4619034000001c01c0f8030101c4c00e0880030156100311070100022102414601d1003091104194000701302081c4980004c40c800c010f40301d80c090321880d1803044868032026074600b01030149207c0c040141c0c03601d040c001c0011500350400e0780725964800210403a0b8280000a007d40041e40f5244070503541003151b11001c1c00c06010042c030220106403104407550b540c1c2c3d403840c000d512030214520140030300301e141c0d05914858444040f0780411082603030300309400c648a0100500c4044d0100d01000f41900b03d50305000180e4107668400d848231100080d40c420844020b600f40001480e01d1071190 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 665921088 1250 665919838 665919853
    0x809010801062a1b0801090b07050307091a0904021215040e03071103031b0a05060c09010f0f12290301050424150314250b1c1107050609 60
    0x40202c0f00d8543c1c920315604000030119401810400c1c1c55070750501030035030f2884c1502d00c0030800b010150040c81c0040e209a510940540d5110b80454003030109a401b88001883e4110402541c5400740d08921039816609950b0b161101031070026049a10028860160181841c1000a01c203058245c00030144401d480a0210180f24035600b900ca10600a00815110f48021409010789042080d41c0b0400410382c50035180d80211011140d4480404008407158071030440007480c12001881038500320001a1548000e04440600503100c1511070060780003082500e00750034074044014002c0c401c0c940c41d0b14000070f46401503105403228625280b9207590080e8142405d010004010b8000590010300040550340310046001110000d0005014070f05204041d0f101c012082c1300300d141040d4011068102255000e0b07400003800c0304046090a400c0407042c0f002c20081160701039160051082080d10b0421010503185c1810038402c0755030380000240301010104180c410030904120031504851a200100041c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 665922338 1250 665921088 665921117
    0x2010b0406210c050a141002010605010f0804060e070605031006050f160807080304080d0501080c0907030f060906090f0b06070804030f080403050f06040524040b10030f080901080106 80
    0x505190310390007440540303074000c2000e003c10094a00b0142200170000c5200039030310281007242010000380e8610500f40c014008176010300501c205002c40e00b0684503d000008811029601ea04005002f5200b036901c0c0c80d5052000c42c0c00b44074610181003291102c54a13402c108002c040c003002c10390095010700c40c2c100855400155054156000c7d8110121300b040071051500e0403c001e400303141c6000b45000408000d120800c00b2410150082d21034071202080641ea84009040e40d031404200d9241d080003e8401050308076200b50030258803441540700120700d055646d0000f004451169000501055a0744011032a0807118050046402421503102e42040010340300e4000c940708611004190f90340c1d000700d2104104a0000352001540c1202c25201ca0b41da840c03034003a0301d88404407001c50b000c0c000c41852030340c0c0d421066606c86a0750403090f128441a0741d142d84889184002034901c1c14010300e80e00c0700000160f0030600010a80384211030458852183c040090010710060300310f00103011300925203811 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 665923588 1250 665922338 665922359
    0x3c03020c0d080306060a1e0806090a020306130b0f100c05060a1b270b131a250203030310031101030b011407020a0306020f042d1e081b0102010b0406 65
    0x4100a045502e595981010a4140c4505a18030603c0c40501c55440c86047c0351500414050711a5800361154505a607440c0c0703000c0100e110460780254454a8120071505840069004141d8150041e05004c004100c00000607140650072010000044200103242c0420206001060308a08a03807414030904802e030507044050545401030604201004001118500c6404403075400414072100b024045a11022486055440740080d5944841d4174040068103001c9604020540c80c8401d15150802c03080300030030710b500307040c0c1e005400001c1d0f03080e285100543c1d0280700540c0a5032010041a4130185540340c002100d80041c00c0140c1410702c3c00d2107600047c0d80001c01c104201035514501566040d00d4800600074103629000a062684007181c403110240003140188240c410403030b900e403612034094026a00201d168942031110611400c810800a50070484e1012810800500c085c1d0040c1c40d001c3c231031300d8024592151f0b03040c480901441c1c003031035030284252114a0000c0e00c040c000300f8102402c400c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 665924838 1250 665923588 665923591
    0x41a0c18030a020d150207061104080f0705091506091e01170f1b0d0f0c0306050d020a0909080c060c040611030304120e01020c13060806100e043c03020c0d0803 70
    0xc03d940805d400381803080038103504036480c8943c003910070844681140c0c07460200307400c24081d480480c840e034507444080c80c0340000c0030000c841e40100b91890729034030340c0c00310400d40c42c90044941e04080140318844161b6145a60110350000e2103004841e500d04800004003421108a28062420484e509010f10301b02c22111031540300c0008020428442050031500e0424450f100b0403201c0c4030701e8890b91a1214001d5044000c3c50b042e00da60600c8040d40710030802c1260103c0250081d40900504010003901d00143c12403031125004044880c18040b10700209401e1840894202c100d000c030006041c0705441d0080348032031081070104011802c0d8a05507131104050010040c161090140781c0340e0140356680300b0806138011901c040d0402e618550341d03885840180c0103034002c0c0d40e0700c0e0041c2c00014211140902d4540203c4240b4007421020f034440c0d440b8061400c80c6050403101c4850344000e000300319213002600303000c00d82c2c01c0da0141003200d030704d81002402d0a001c215118031034220003e6010100d0062400e03217 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 665926088 1250 665924838 665924843
    0x203061c0c03020f0f041812050c071a07050a0b010302031203010503030a181508010e13081e07020d051e0105090a0314070501051e010906030812041a0c18030a020d 72
    0x1010051450004590721780b006400c0342d00c1802c02c0000c500b4003c0e00c691000646118105042607011541c10959090046c61440005a0b022103020402c050075130f985410004000c0f072416150030110788070b00b420500c008001751342500c9100c0042003141800c00c66100240c004901032815035043c280002d4aa101b00c040000400040c6d040002450040d8100c1400626840100c50089071a078000a0710710f41c000d00c1010821008400005d08405a03c0a0b0380000383d8001d1030f491400e6540b030307088003000045a60702410480e0500440307005071101040d10508034007940080002c141c05440c920a5044130500003010781c1d0411082c070160240000f030280140c2c0d8941400c0c48500008581070140e4050444090015820001031008212112483c4d13910000a500b4001081e038840121800344c0c2d1107440010b004100c00c1205440d10403010012542251003800c9043c0041e805a903154080c44041d01c00e2280c1041c0001c04a8102d01d5100c6007030988041075014000100403900020100411407601 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 665927338 1250 665926088 665926099
    0x70e0108090c03010204062106080a020d150f240b041427010501200d08070c120519030504050a03030b0102150f060a0e1005060903100f0203061c0c0302 67
    0x120307140038024041001c00c900060300031901c81d03030b83e440c00912604c034048024100451140f800c480e41469801b4a50035640080b0040c0080b0340e45034207000141e0301d050b10641e504000040c0c2d90401129500654a0403888050b005c2400c0c1d05119081000301080d980c008013000f2060000c104030000078095a0407607641d1880d00c03402090b03120114a404006100c0c03a4406034655000c08034138074407203030154141c8400713030b8641c01c0200750b9414010803038003403c0d19414a54088401d1540c018800c0041d182d01046514101514400c242c0d20662246498080e02021030070124000c06107901d00d0000c8a951401da240a200d282000d032201c0380c840840c0c56003e4105920341c14002c801d07900030072100c20b00da020708400c0906072501c0d040440c91413106607043c1c1e1003032015910005403c2e1102d0a02d43c0566510150308010500e0304042080590241011076018001e0001c01c400030502c41c0302c1c001c142c80400c00096564540344080003a1140b81c4015280290303442c1c14901c000c034404049a0041d00d42c113440307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 665928588 1250 665927338 665927341
    0x70e010e0a0b03041401050612031c1b030f270b090c09040b04060f27020a0b0a031b031b120209040c0203090102060906070f050f0c01060816080105070e0108 69
    0x801c0409403550407079604120300000340020008901e815854401300a0004c20036134a4202c100300794401017460014844d481030000e0402801d00b584510004c0d030090800040240070800d9100c6280c52070425040801d949aa500080e001e25000d10790006c03c0100b01c10800c845089801140a0703404200500350041802c005080503c00700078a86003183c0042003640c080c5054034048000d00c1c0c04039411106036081c180e01c4215056280100b55002d03171809075070a0001180807040b91800c80140d8142d03030104001900240c0041000010240f80b11310380e0700803a001c03030703019480011100c800e1030701c404052a14000c1d0300e00314115250361f034100c3c0a510b800460340300000c02101c068011010314541c401d14003c00540100e400100400c0541401e800783e81913983c9140d1820b0700c5100071105200440c0c542c0c003206201c684100d006058030892002842c0c145001d0f4400039007107a15940003e0955484040d10f40c02c0c01c2044c0604000411030140207111a2808000041c0540b95954000741880411310 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 665929838 1250 665928588 665928617
    0xa060c02131b050705032208010609020f030c071502030c0a020601120c150903051005070f11030a030c020109050105130b010906150f17040b0a060902090d080c030403060501120c060206070e01 84
    0x200c0d6007c130011481d22120200300c46c40031b1103004140c820b100441d8649140020445814000e80d0a02c2500d42c0e1218155a198403850b0420352000340e080300c05001d03800d8040c180c4d12880c401b039806504008a45503c80ca00c11a010f0f240540c103801600c3c00c0c09056000c0800295038154940948a01d40c00d21801014440c2c016148155a500010058040c6c5600810000300d10352003c0c2c8038030f03110f5a4600d01405c3c1e0070700554202109048421954208004a0048501a8011208080e82c0d44000181a801500c6542c2141c2d070641d050040c400c49007100340c00340700c1024a2607000d0051403400300f120702c4c80c2c05828002e8079040012042480124030940034401e010f041440b1032282c1c042c1d200c004070718080c07130117071902002140d601030964542007000c41c00e10b04a00c2a601d01010142612a009400c0e468034201034003d50080e0581d803100304004000203525000b058000e090a58260b0114031031850950701001d41508003004552101e020800890fa01034a034441c600028240302e03012003640c0c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 665931088 1250 665929838 665929843
    0xb04180210030207330513030e0613030f060c030b092412060f0105010311090102190206130308091c030c170c0114061315030605060f0a060c02131b050705 68
    0x40e01d001000c100e0b510031000d1740d010300000e01c900030307050003208020740c7e507980241451000b264100500040e000703031140307202400c00c03100a0015860b05500b07160210f61740c3d5102607850400c0c0c3c034100c804545944110284a13014003442030022402c8801d036509103440c4600030901c4c3c0d00b240c00002c1c26030100c44140c019403124805150415810425941c061130b0140d00b01c0b0a0f50303403c0c41000d00103850044c00901c1000380905031503900134164050060701e000b403a80101142c0780f40c802680d0240c410801e2099094104540600862080c1310064803652030b0000c1041e408a508040121445440301502c0080d90240100c086213502c80e034802030b468070f02d0540356801d00030244011029881d2100c413a88006140c03224070b1003000c0c1106d04081480000c10f445042c3d921490807803222034a801c40c203000240040e0011540440c01800324606007442d80001458005181d12050100d075044002400b581030072000c1c40c0c0101a642c20501011011500280c0c5c400700071199001040b8010035100f040040c203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 665932338 1250 665931088 665931113
    0x6180207120e06073f080f1018020f0c0a03080c090f0d1b06110705040c02060c180a120308060312040b180a030803250c0204022b0b04180210030207 65
    0x4044019a000003000c0003a14500380ca911701800f150321080020104c0039018001c52083c1115041418980d240108003151154010440c0011075000e008800c038050700c441c048c1c50241e42c0784004003040c81160801820100c0e0280200745080c204004207400758850003000e4241c1217040c0c81c8203601070311904003a4003002450109105000c0308610000e0341d00d030700c40b080c01206118441a83d000d517560f01e0800c41201d0100f0300f82c10150b0041c2c00040c0d01d82e00d0820280820050602d000c160b04d250800006004c00d41a800c44a680d41410000c04181075002e032480d80c2c000c5094009000b81078030540b0502160082ccd12845054031b400084841450b00e407044a00403603d03002c6d00d031030302c1e898483c9011000d0380c00440b03202050070080f10000c1003030707003880405c55001d078040d0700c50281c000c50076000d1001a5003ca1500c029600c4c1e00040c0d19082e41c981d2038032424084032a0400034a2820040802081c1c5807044681344107601d1081180c00580e84200c07002107480d525080c0160380c0d2441c0e25140881540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 665933588 1250 665932338 665932403
    0x91203050d060e010f0b0712080c0d11030a0f0c080105090a15080307030206130c140103090506091f0b0906040f0b0901080303100603061d0a06180207120e0607 70
    0x20032400090480d038122103e130590700042281038010351071302d02050440c094001c01420096080381d8842415000b110b085801940302500c0e0ba00d4070354000c0000c0c058524101c00c01801ea0800400c000c1200800e200d6945040059401449040241c54000385050350602a10b8410300700c1101150507010f00d0361028002083c41e031401502c01c0e94800c02d01c3c1d22038021a0040d0003501480001582121b0b4030700d000c1c040c007a480100341130007074245201000c01c49041c200d1541451764030785808010440401c001e0788a14000c0e00104600303580c000b080f917008100c02403030001190810300d01440c9030740c07900c1c100c130b1740480c0c01d0701c002403503841110424000d4008940d0312a044101c1200101e1149000701c003d52250702c9020301030340003d075203603000c40495141d07105542c0800001e900407151001c2480c0b031107400030155080451981c1d280c20a01d61011307282c0c203c103848103078002810727030410600042e024210489818075104011120001c03d03410f1298400040007404682c6895808c208040186840000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 665934838 1250 665933588 665933591
    0x20a020319170412062c010204081608070b0a030b060d0e100c1d0301110703020a0b010f06090b0c0a1b0e1005090613140403030608011802060d021e0a0207030b09060403091203050d 79
    0xc01c46c0c03003401e000358810301440b543c60040742d0304c14241e62241c1c1c040104455502000340300682c42c100048056800c5a00300c082019107441c46041d05540d0800900700b4511b00c00000209801c40c100030a01d030401c0100c085d0380305400c0c03420b80003810b0380000620480c14260795102c0d10741c404600009005000030950701c00c0c031540115a543c1819030008900d8042841048696101c0c0d8a036100003504071000d00c60302c1c1c001007000800f481044900d00141000c00788107011101414402e42d02c0c6100248011404034030110f01c040104044100900f0141e04101030075072502032682090081940c3c03404c0100028003840200b2805c1c080015a5403000140b504503040481d503a080c1031030010302410051080100c15800c0543d8440341024002c41219441d500815030341c541814600003001a41010100c00000d442c1390070403601040f43d46004140d11640f9a01a002d0b480c114940700042c8030001c0c141c2001c41d8040000c010029030090382206c00d5a0110401c546000420f140444052180f950300c2d04915 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 665936088 1250 665934838 665934911
    0x3070806010512120f0d091203021804050906060d0807060f0605010f02011b1b0f11092503020310180902130902090610020a02031917041206 62
    0x44000305046058450032103c1001d41d24444071855500c0c0300c00c2c40c42c01106035080029a0131254208028030540c004c411303000c102d180700341d21504156140c028201e4042a000980c107075002d140d032100120100c1003268200401c1c2003280382240da0346002000d560040c009030050000b4011107500340c030040da61140d000c0c01156802103586002d0300082c1701e8180890448596a08140d0040c001c003000444411845422426645400c44840d00c9255120083d04401e010910200e0100d100c0e8650380b034001c807400f5070909403c0b028041c040100504040d6004c0c5911010807100341c250800b030f00021201d00d000341e240c3e140c202c10b0300c4030350f4150f60101c03044012090011800c0302003504000c078030900031204401200e0b03800e6240e00560b152039030003d611115500c001349851400340218141d200c6244112a66800c040e40446d2800c0c8041e9486806102c004181d074042000c0f0081041868440744095070400b0318280020300410084d505c000c1007941c5800304050200b140c04c11001e000d2416100d140e188 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 665937338 1250 665936088 665936099
    0x11131103090115170d0c03110304090b2e030c030204050907020d1404050607150603080403140606030316110d0803010902182707020a06021216030b060d0c020c0307 72
    0x2e2903441e103440041014400300213080c45041e05440000801c18025002940c4094011160342030008004c5050040c40b404081500a0400251002e01191800001c0c0704918400704071b085410501004281c03444a060400c40840017600e100c52100b181c20b003c036040072030500076400b902940d0010390304404801d0402820702d600140a00c0f08442c81e8403080031a68500044041f030748500e00410790410300811000000611400b140c1c0250f41c41080c0c006030540d202d503214034081d07020764030030f541d4038400303980f0f41c03858102c28404550000f00850080d1328000c2c1e43d07180c41102001e0b0030005070000400304902c8901c0d8880714140c0380140d81c409025070b40ca603180c4c9800300094010000032040c048440000c860343c2d042c00c43c40280c003400600701682c013094204101c512801801041c1c141103000d000001d9002511038006401c0140210501c8a804e242001c0001c0c2a0400c2c00c80400030582000a030441503103809003119024160080046030130365140505a15003135954500380d4240c0b140c80c1c00041c0b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 665938588 1250 665937338 665937341
    0x70903080d09210e060c01060806010b03180a0201090512013b07030c12080c070f090b0102010c080f070905090a0203070806120304061218030e0a06030207111311030901 74
    0x212a1103000c03202e0104a90048035981038610300c240780d01164240746040c11511704600070f4260f0350507041c00401c00e1602d807070a6500b000002e03846118003117400710510110108003102042d81c1c0700c2c0a0018039402100d600024840d10fa20721406018100043e841c0805581c29080000d10320907203054100c500300d294129070540c070f00540080030340303862140980602000101e040070450f42c000416560751410008807544008501170110340c0424104400d0078800390510007080203120449984509500e4078007281c1c03e40310000c0c0c10604591400c40c40a404c00d03007242140c4c0d04036840901000541d5266401580c0d402602d401c01fa82c85aa118100b0024840b1900118450440d40e5580c20b070b0f64a402040c0000000341c1061868160000e110500480d80300c2c030042c10304011410008a1108042d4140004032000d5013015400940c1c22030b0508000e091444241c4001d114500e0110300e0b25211f522103c514000c009002c030300c5010745104410b0490500e802ca80034080c0c0080e2050350700d0510b00354450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 665939838 1250 665938588 665938601
    0x60902031603050112020609100e19030605010902191d0301151a04080a06050604060e04050f06070815120c0901080304140603060105030a09050708030408010c020c041104050108070903080d 83
    0x70010f802c1c80008115621515444220340d54081c04040c284070000701001420240b60082404200103c8618509942e500400110580b1240201512141181485010b8400c143c002844060040225030044118190f203447c810718240740c04130303615915441401c000c0c1009800e036a41982424940d41118405403800700440e4802100d9505120321029082c0b02d50145105501141d0414204c400100d1259046680d200780000c00000c2c1381915501d940b00075181c140c80543d0507611100c8000318600c0308000c055000701c2d403418090002c0c80d200d540c084203640040070b41c0d8010041c6403054149210b00300a254074015004000703d040e0740e11050025a0303500544039504000c400c814075119282880411a8010f08043c6d4230301d480c40c0d0311048803c0c094104900c0c11500c0c2e00c20188000f504640c1031000d4009880340c11300114480ae4410802481c01040b55601da00c1a807170205840c07007240114086600711502030174043c0540c2d41c0c10605685072003240c1d201501c01c2000240540c003180b030550180d0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 665941088 1250 665939838 665939881
    0xb060d0c0e011502160b0f1b01110702130b10050d0b0a08010b030607030b0f040902030316031e080f0f0603190602070209280203131e11030a05030f0d06090203 70
    0xd51280180c1c0c41c605c411442c0d01d1145841e482010480051018029001082c051600f40d07281d942c0000c8825245084529800100d101e01d08041401000c500e0428041003001c80f42010130b0200d0305e90400021079036500c06034904240400041c08800d2409140c000d4802841c0c020070040845a0354040c1e940071342500c104191013070160100085129000388100306c142e00b0040c00c00301480313620005000040c05214420b9916100620500e62620000620100c24030b21a03038600c45803443e80c20030450a000140080000d0001c0da0041015020040321011b2307001460440d440c050b9100e4101180c201a01207220340d8024a0701c070702000500501d50001c0041920a88055185039140b10319100032100b240742141002c0d080680f005d409108036005140c00c0f40802030940c1d502591941c5092850360100001041e007184d08044809028480d030109184a00a030040c1001d16004da46841c0c07a4130402210070b84c14100402c128400000d154001c1010704144032045540f0b0034441d80941c0348240f1040e21 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 665942338 1250 665941088 665941093
    0xb090a03031409030702041a030a0c080106050a05011403060a120606030b22060e0c060c010b0306010801051012031e0519020d090605090d02030607050705060a090b060d0c0e011502 79
    0x1c140b1400003541ca0540300d00790300c00103035003000802d03420480642040c0d0603c2e15a092445040c80351a0b4042c0a008046031060b40c1e85981c2170302e0034038a103007941ca050f0f2180e8414000000104450398000c0e40808070f0a920700e1106507640c2d9030000141d402c80090300203441c8a400524401c08000c0d003944802c00390303406080000302581c3d861100c91345401140050410450b103a115800c006a4160026200b03000fa200689a03064041008149603800124400096030b440e41602c00321414103006c0103001d051038400074091443c0000707000041e41954819403085804490002c01450300c15826040324030600c2c5400348000c80440d6008200303030803629444480245c0380c000201b200e400004e0034569220070352112501c0c0ea241c6841550306401c003a490b25000901c0806403001650180406c51040400b40c94280d10340c042c900b0080d140c548014064108145071441032404250018405c82e80110111500070703074601503241124440110354004400160050300219003040c40c2c80c111440005950b08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 665943588 1250 665942338 665942351
    0x6050c0f06040804050d111c0b010f050d1509050340230301060e10060905092202040903030506031228021507091d07020d08130b090a0303 61
    0x1205a15070390305550003041c2540c00c010810143c1412010350010a0044a030b00200e40108000709001602c0a802a00404a8008290100400b118405014146440103c10301d0b07410007003c00d006111941001d481104003a40395200f240c500e070403100c085075002085c1c80d00c0700301c200c503030078804004c0342200c42c51465401012089903800c403566107008071800c803c0b00b500c2807511b1800720704040c0c0c040144442c1c903000302c0000040c0d1030034007900c40140244c0a42c1d10480c5442c0049150910f03243d00210b08002c00c00004212940c3d03050700d9140c005c2c0c80708200c2c1202c92181483d10302c000240c010003e40050510020905240e01540618468041a81964230854080c41062a1845803140c65000c40800c8500340b42111014000313031003000c40c14012a49c1c0504800395465040340125005400500780384e005010001d1b440251242c1d02241c1c040c0d282c154200040c2c0a500c0d100c05220850801006100040806414030b41c1c10280c2c981140d034440071303420000d403030f0f0713488a2000500740c0c04281401c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 665944838 1250 665943588 665943613
    0x10020306100c0b0601080a09020a0e0907050303070807030e0a120c05031e0a060504021c21030603020f10051603030501230a0b092b0501061406090d08070602030106050c 74
    0x241010502c0d6000400290551301c04d4019280107001414a548055888849000688504800d100034080c100740c0012140741030750700903250400581015011750000d0180c500061100c400343c4000c40c1c1c2c07605040a000009502080d8000110342c01241e104480350510400d000584c0360070000e0314030540c1a210340c401c8034000c1003006440c0c04181e6480360300020203200071401540c841e40d00a88014000701c411707c044d041c2d85081040300401503480348800075841031015280d40041551441e20709091280c5440c0d90000385d50310281410356805190980d0b4280c1100d40b040d0704440c00c002142070b81103648090350800500802c2c0900540c0d40514101800b00d80329a08031120440550001302103045480c14a1303d030002c01d4112400b015005085010191811016030345c640740e56202941d0908405c5010b42015800d4541c02e03407010003407038025254414107454160440e403200c0720603100c001c0120b2180c40d1600c01b61058840c050140c0b4400b0001003192940000289030485403c0b04484003d540c10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 665946088 1250 665944838 665944847
    0x1806060203090a1202030c03031207020601051518010c06020d020409051003050a1202010e0105040b071e1409120d180e07080f07230910090803030c070507081002030610 74
    0x40b5542c0001841000c01040305694004c000440c0b0240556500c0140a00480d1a541203182580d04101c1c0c090208004140e041140a0050804a40309a44000f4582d00f0700707a544104c0281d50262000814001204e0340604120b1521562080c821556400c40e03904181c0290000e018586029003050017043e80300500701c20703070404d4a41140c0945175007500d40e0388030340304079010103450000d654075192403c0c08080c0a2080303a10030390081d44083e80c103161140f402409400c1e4090715080002c040b000a898640d840308403601d01c50302015134255151204400190f0070240840104603d10a420031815910f80c0400008104040b1040a051035521840000c0003600100ca1581c00919014002140030545495050b0445042c1c1040d8034002040403482080c503130110220710341c000c070000c1d982070942080481114489518540090039a0030051a00d44920014028100301003010410380300b80001802502e0042c808142101c1500001d8179968000e034108484191152120a9030740a28a029 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 665947338 1250 665946088 665946097
    0xd05060c19030509152211040b090f01210503070c0f061b0b06040209090420030f120a210603050106060f050306013b090703090503040920041806060203 67
    0x104e000b404c018034601d4840c001c011001010711a80390aa002c100c030000f4040c4c2520101240101100d003801201d1400340f0041e1243d0340000c0340203648400c200800290700d110352906645001c501011100d00d800d500d4691041840700c090600c3c00001040b00402140c483c0344c80460b0525903000803181c0d51924191189020031000111040d80b002e51480010755510341d4a5029800500c01800c00901c1d1001c034401c0325045038115540c2c004080c001c041402c084100e0316003140200c0080040e080603200594442d2000c600440740030001040207804240140c0818032038420304c5c52501c8000f030010300840080c00842c030040e50b1551910001052151050b990640e0414803a2130305490b58840ea0011135420203040c04c0c0310503c504d58820035001080c984102d0401a01c04880151818180070810440007805003070320382458a4100d1880000d0350200699080b9415178100260710b84501d00c0e642d034090781240031000400c400050110302800458204070349540020003c002050315500b050742c3c0c80c440c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 665948588 1250 665947338 665947351
    0x3042303070510080103032a0302030a170c120402030c0621010603020a0f05031b0a02070e090606090103020111070302031f0f05010812090a0504023f040209060d05060c190305 77
    0x4c1d000014400f00c4c0c000d8084040344070201d501014030701110280102042c04e00c100486c01038200054517212160711400c106841e1300c03070700003040003401c1c454490019403240c0311000b07415000003400242990740501c4488041c59014000c2d0365110310306151992480b02c1c610a610460912a0011942e54401e1094611001241d05c03904082150381c5404d1392a1b42009010800202095450505141802014007800580b9800404801d410b00000c0310b03a0b40b00080030400903910203010000726a69161005045030340a0904001d031007402441c03182440110380000c1d4051040420786901103c404281701c0140000b5a410024a0950030340001035940a110b0008964810714803001c2c80a2000012309562a0050800180c00e0355100032034141c2e048000100c2015070443c410502c0070b14060514078100f0311104000b03603500c08a4000d01c3c8031030000b42010340100c03651000560103448920420900319001030455055103440c0811452960140030744031201416104445c085500a0180c14080c05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 665949838 1250 665948588 665948597
    0x101704060e1e1005060f040e010f0f110403230d170c0a02070b2b020a091203051204140f0c0a0609030515070302090907020a051209090a050903042303070510 69
    0x620f8088240203803c01401540d0311411401240303856542e6403164480394610940007050140c0200200e80894140601c45c4650ba410a008000c032040b00904441c156035000d800d12003100b0b000841003582c4100300c424408907105000710005144e80081a040e1802040d482a1203540e54804a00c80c0038060b03200d01c4000360744400024490751903403502400c0d03510704000014080c03070310030342c0004648455440c00903842d40d40041e404180796407010729600a08039002e2840c0d109681c4e550010310718842c0c401e942c0348002e00500803404004c084581c41100c18113000448500404600d0340c81d0300c2c1c204c0440d60078482d400007003001800b64000d0300c48070116a00800506031041c1848032a0840e810f0050038002015401c00c1202030503502d0307446040c002e40303280d40181501c0c403c501d0444d2400b4920b03040441c81d02070511008e50a81d5a1480c940d60201152402007455110003182614501664102c0e201c480110008842c11489850500700c50000480481d0f146a0b40c07a4140240c11000424210008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 665951088 1250 665949838 665949853
    0x180f110304110f0303070303090b07053f070305070e1e0111010902040e24011a1c020f120a060503060414070503120408010506030c0f101704060e1e 65
    0x16000c0d4240b0382164005002a195001d141c4002802c1d82d00ca450100d0110340c0c0c40c0b61001c248500090956806141420194582040c804140c20303d04854000102403042030030300c40c4165403018400c50300c1c1c2c011301da44081c07040c00d0081d8080e010384421100000010301d03032441050280380140204150b0340c00c4c400619135500e0380b0b000448511020451410f015926400c070303d0016295403180b8203584405402034000e100c800da007200352455069002030300041d00580140711718070003111400c503401c01c0079402c1d0380c0e1940305801100c000d10800011641042c03001c61004502020304004111140500c0130302c144590ba01094103044070890f004440e0103a000b00002400036440c40d203120456220314080703404443da0750300080d1901c0c050601d40c071003642c40440c04000d060400d015254100380c04034090120707044014041a44420b0345000386100303070700748001e070600940103102c401d004070540e181d07580136031409003840c0d000340c01580e010000350701c101000130900d2500030705c5028520380c100b805004d04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 665952338 1250 665951088 665951093
    0x50406121401091a0604060203031803040e0f13120e0f01020a110f060f0d0f1a01020c01270807030b16080609040c0b0a08010e01060906050d020a020703020a180f110304 74
    0x400a180240039000c1e0740392404c42d100d0f84c03448043d00041030709500641e500d2600305808441200c120843c2c0940351f000340f1041c4030303181c00e201c5069840110f1010511f140d90b2007841303040d40031300c0ca00d80c00b034003922100f001c218a2561010304c841304120706455060b20014800c00482c2c0e6560900800382003910104003641c00c07413030700e88d503910550302c00144110b0030802820030b07030f010f039601c6062468841662070200d0048a481c900405e1a240c0c44803d040071500c003071074000703512150b08149160402280d00c09103151849401100059040900e0f540140c107600e44a103242c0e50080c40c0401d482d29a8064009207680d003070308c1c01d641809030040e40d6401560f00c0c2e00c0148141c12102410446407591403041c00f16588043d040a80b0f05046203a880e000c030382d45807491921220f8010703003102c81088070300e0ba0309201c403641100071559400c1841d0f40c01691a60030500803030030700300c050304020b51280d0040b90010b038101049034040044540c60004105a9400011b8070007101d0031078800b421852000e0000401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 665953588 1250 665952338 665952341
    0x105101d0a0b010207050303160b060909060609040309081b12010b01050708132c150f01120603020907080f0c070f030309032304080c100903022e05040612140109 71
    0x240c0b0b030018012640c8030350316040042d04507046210000d40201022402000344154200141d4220070700341c41c035010508040030a42d4885034003c000500039200000440c08141c880e09104005001a00036125414090221f08210022442500d8807864444000006909041c410301c0703508a8140c58440ca004104c0d51060981d42200300c209084c2905010300082c40460501412030f8004850001400c0015101011450540103411003010b800d440c03008032800e0b200d02e180000404c400f42011800080c040044038041d10880d00300a4000c3d07400c41c103200c1c000c1c0e0010316040c090501c604180c5030954520060703501c640280503018049102190295021078081d5202d44402d50081c0760030b00c50740c00700409003a44644c512000300307241d40000804200e40740302408041c0c3d21410468001001e812030032401004410103000c043d01c12200c0702103e41c20804000d002c0308810a552200d000200c45444024059070001c0c41581c01080350283c03103100703021591040c01c100200582c000c0b00a6400d1049407030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 665954838 1250 665953588 665953601
    0x9051212010e09070906060f0215090706050724020c150601050d110c0615040f090b01151b030e01030501210b10031b0302040b01090f03080702060d0203090105101d0a 73
    0x1483d8000c0007008100c0c68518041c40025101c3da071507080726580d004000925203000c44071300c040c51040c0c460520002c413401007408404c41c0e81500d0416164896410000c4004025083c0d400688201c020711640b040f03000d4003d0f10700c2110340310a48104440e181a564049142254002d0006608111010070074090350302c4032800d1510b604015081c284691001c905c0c0030401e60b449100744007031441c514460b203010b0007082c04005411401f4001001c1542d5060039008060141801d5107400c4071420308690710a81c014480668003a407000035203056420050f055080b1245418002030600d40041030590036100c0c481c001280851249051014075103d0710390240d0f016203010f034030507210640000850180d407100f03a0f1454400285d210450b20350300c1000704030380003171b4012814001450700402461107210041c2d0116500a59241c0e0707039a201e0b10005010344a02038031191060310100038000495015885036200703a0031201c4c007845903503c4540ea1400f01c007200c8005520805a880080c405007604c0c1c2140c0e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 665956088 1250 665954838 665954851
    0xa0f060804030323180c1e01030905030409090203010605270403022e0e01060602071403100207050a020f0105160201030b03150f150f090a1a0a0909051212010e 70
    0xa400310484d115107114104544800c406108044140622050040844400c6000040080c441c0f0500403000c81c01080b01c1019a01d40712400c4101440e450b400398005000c03244e401010b4a07691a11040301c0e50040981c3e680c184e0003076103000d8001c100b40c00c21030665861001c40000b0b4041d01d0030080180301c01510020300803411030080e0301012054040049940e030f0724602c0c1026180410700860840012504140c02881c01c43c0c3c1440130811000b900030071130780280e400944451754000500720103e40303025030b86003000c03e25174800200403041c88408140303040da1604c01c4494103454411000111007030300400e140141c90320080c0701d031280190300962280225000c060203642a039a1008098030400900721002c45500d0500b80410542c00c2120001b40c2c404442119007400d03105603240401c1c5070840c0101580022030303480d041a0f442403405a000110000002d00d0b0710059a2103a0301d070005066900800c0b100352280d01c485051600050301620840c4a00072440d00f0340703030711f400e04403000d501000c2c088 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 665957338 1250 665956088 665956091
    0x10902090d05011e0f1a012321090109021c0609060c020109050d1e0815330306064f0902031905150409050d0305060a0f0608040303 58
    0x40010030a010704180602c00082c513207040400000010183e42c29001030401442c5020000d220902e14801c00b180c03004e02c01c0c680055101c001c020b40300d091100114540d9023003c0080703481c0040e842c4c8150207001001da0039059a1061301d40200c06400e03203075100d2000354820132020311b01062900f0715114860180c002d10001c141c0c5003860716108100c542442c0d40c0030060f51103180c1c0c941407150401000d11044070b01c0c034103000000990450f0100c50890040c0f020100001000400d6943c0c0c003680e0041c83c8284000e01130302403c01c02c51010405200015072905500d610700399500061009801501d1181801a02d4a07140070720110034600040e030000c1d100256090a0b0080c1168a44121035000c03401d40c2c01c007a4502c0d80c10322290300e840c80c40183e030301c141402c43c010010006079105d042140c2c40040c160381000716243c1c54060001e42000f8001d00c01a40107486c03c144201888030002c2c0514110641d92403c20030350311960103001c61400c0e980100d0590b1140c100003008081d2042c0f220650140c000c2c40d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 665958588 1250 665957338 665957359
    0x2190302090f01150c110108040f051c1409010512130c140103110c0a12050f0a080a0b04150b16020a0b0304030e0a08190c170601090b030105070801090209 68
    0x1180072009039585076505208800620400ca0000416002c9002600b0600000e0506a4440030303121045103040d4104030802011408000384031707403013000c40e0358070501b502c458030080d21482843d0180030422800103000e00445600481c91807045070300042c0107039241441e1903102030301070104080217000c009410208084c54000308001c841d10b80e0141c80c0c08000ca1102030342c840001415600e4044641400040030441500e20040024000305015842403400c0d00e031590718030b800d4541c3d001301c40040b003101750000341c06415150300070300043c85412010400c001980c0e0303d505010851307460782103281940300388200500c852000540513000d40c2c00d1040744080301c0d40450340425507101c116030100300e11000c08002c1c8410190090341108065006503003483d415460b0510701940c880083c081d84c450001004070080c140505103101e400079081168603a0152051506000d070394407030901c108403529180c040c0c00c480c2494103004650141c0090745da0b5421503403c200e8001d00a40c4a0103030140d101803d940c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 665959838 1250 665958588 665958593
    0x210b0d020d0c171614090a0903020a0b070e03010e071a1309065102030d050103051e0706090504020306030c0d350708030c25020a150804021903 63
    0x7040c0c2c8000c40311140141180d2040c0c1901309100400680083c0e0040341c0507240d0701426102c03941d0340c0c4d510000850010401c44101e00b07059041c604006006402c80031f441d010000b0325030300401c10000085094000b04800c14900c0e640a407140745a0082c007c00020b8501c0d40b401189410024040b400001c1c2007194030b156540d248001100c205a1164001785620481030b40c440c0c0810350348040f4070500d0046242c0e103469003041009034000c0d0440c039420315540c150406610320b10170070070385189154a610801595849081c483d82d140310340c40d141c0ba4000c20b58010481e51070b030046000c000312400c07900c0e0818101c0c1020200700203500000c00250b0588107240021000f80c0c1c9019065424601580d2a62014401d100214160510299580c2d0421001c21480d03121010b4501c11100d030b1607005501c15450792202c0080e047e0520464418092002d03001d01c5013a243c0c0c1040607200c40441c400c60321118182c0c1d5074031149040210042186010426030400a005410442980d080c3c2141c0c107d24001c020703480c2c1c2d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 665961088 1250 665959838 665959859
    0x40f080609100c11101401050f03100c0c0215130501020d080708041103011a030d020102070b060d02060408030c0c2e08071e0306090c0e03030706020c0703020907210b0d020d0c 77
    0x180845c1180c2c2e1105101740311183c1e0b2502c1540901030075292224103d007a00003207544d0b10410070380e41124542d98440f14400c3c1d0b108040220401da801000e01c03004440541282c01940c0012141c2007100400030000035040d030000801207500290b5840d0500c1946d5144000e80781e03040001c0055800032252440c11031566800c4c4503d03412070361401e01e8003104a0521003403501d0104030403142400e40e031041000201041c00071039680c0d845a41100d202a03e03910b41d00c04502c49014035441060540700110300e00f07070005e50200d43c0220810095910305c9560090284c03c4862809007a10b40301c010303040243d89000c10344160003195000b03610707040011485620200340302074003040c0e28244000a03558581405071081501821143d00418541248190401c000180d00d03441662001000f00e94005084880c01e41c05005d408001c40c0c006010000c50300c0c000b203021308049601d074405180c801d02500807500b8048180300301a000c1038040d200c00300d15074241e428081c100010f142c040d00c0078101503400040b00b0495 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 665962338 1250 665961088 665961103
    0x6040204180b041d0a030f0e011403060d05030f0c0d09030221011104090b031501081e070f1401081806010909020f03121b0609060c0706020717040f080609100c11 71
    0x444002c0900265030701b401030030b4100320342c28501000465444a401603030711628268040692000b00d0395241c032120700160200c010118010501d001c045040c0c1c940410510107040c404444000340c4852040c0c6c2c070412940a4a2808000d5005041452080e0001d42c104210a81000e45800000304420343d024640c00ba80c00c181c5c001543d040e101c80da14441da090500204010042a55400d44d59504105206407514040021300324242503444001411010422840c0014182500340b403003560b40b1910041e82d100030382c550380c40c08110040c01050790745400c0d4400c0d4020755180c502519569003010030200203819480700580c0c0c008006d41c0740810a550a0021030180c3c07003800b605540e103801c003c001a0319540c50b40d80081c1c59801004c01c208032108082112030740051045807107644c8291901c0c0c400d0090003444000b0344095041d1424005111240d0018405e540400700ca074940142e50310070301c175941c681c101c605a07031a070480c3c0d0100e070180304141c000281000c140d040c084c800d080c00c1048075103841328 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 665963588 1250 665962338 665962391
    0x4020414010b0a0207230907050d050703050f01140d170c03030a05090609030a1d01030204031a01061418040509030412050a1b050303030414010b04020d06090506040204180b04 77
    0x3e14241c0c01e5404000c0b020040910000c400d0b150761282d4803051030158101217080c000c240303200020700d00b03a00c500100c40c072116142e1001c03c0315040410f001401800211500410040785600106614107641018000d084c030007000c0500e085100d55508200a800c01240c0501070000d010040b180101400a18401c05000c600014035142c100e40d41450903c1c0600129a01c0d0000c01000c0d545503032000351094150242c43c1c6054000b107402c40128004c0c0305560010b003015100c01e414001c03010914104504032811682e41c107c0c114007140300540b542c070035280f05441c903501c3e0792080e2803a400c00c0c0d0000c80d4081103503000c0e2400c1c1036580f1418042c100400c481155150002520301c0c1c20070034441d80c00342524100b03078030792101c160400b00800da8910014001034060303040302120383c56441d801d400000c051031028009545030240281c4040c01740c2103901a900040e03003840c0009006003420320a41d0111070141c000c0060120101c00c8800040c5207840c1240d030416214400000c0540100c24804a10340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 665964838 1250 665963588 665963609
    0x12060305061614030403270806041401020c030418021e0d0f020a051605010e1902040f02090a0b0a05040302031b03060f0603060c131715160f03050402041401 69
    0x340209a40b1103140240c0c00070414412030304a00e26107810b66105480c0c0c003a6040c2050082c031402c610080080301d10310705142142200b92000070a003950049000c50107244101d40c0019145011381c55075080c1d0045841e01c45250707005110402c500c200411091200d1300c82c2c0302c40107192601c00c400f43d042c0c40c081c2180e00380c81842c002944401303610308d51080300f03603146015908604142658030020228030940608102d150130b2041d0305014014203500012100703541c4800c84c0c0043c402c7c610750341c0c030340030501600740d10580c40c20881c018114002e000311030b8109001026800c43d1400c082c81e0301c200f600000ca003201040010b002c040010f0310100040700c51a1007080030900c003402c250042500e080f20040c00b000001e8032400521100da01d00003801e0b42c0111808141540b0b460501e40740441030800c5502002241041c2c2e2600840d9505c0403c102c48880d1505c0006103245d51013003015007070100161849000a030103c408001e90502c07070b40c0005c0d00b00d4402440400d00c5401864100340b54002038014041c4907 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 665966088 1250 665964838 665964841
    0x150b0a020c030f0102040e0109020f130312110a0c030b070923040627020c030f0f2107022e050a0c09060207060504050d020120060a150803191206030506 67
    0xd182c20405540108060b40c001e526003401d000d00401846018860350320070070b0b000705281404158020035201c0701180d80e0001c5c0c203855030301d0814103202030390851384401041611220a01101c00031a84050b15600620303104000303480c0d5980c2c9140c9640080c076060070808220800b00300d15110b807c0000c1c80042c1000708072603580360759042108441c0c213640103170000801c00510710007646841000d036031440440480107840340441003c481c00c610030150040f81d03c3c2000205002d5130014080070b030802c006600410161154440b1421038603400507240d03e409039212120103400d00d0305140740544d1102040712650820558001c204054441c00c0c3c03500f58060f0b4492140c81041c40e417108511009001c0362000300382c0c5600d400d40c00b42c0144951f0041e2801400304240c408190b90240c0450b5100055000d104042c0700d030340010150b1260003c0c0c074a01091400d00700c00100348041d4981c00410390700900080d501e001d500308134540c6010101e44060040c0503401c64480d464a090303105140045009a0180409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 665967338 1250 665966088 665966113
    0x90b0708041e11150c010606121503080d05060307050d0302061e0105010f05280908010e010b06180409051f0506120a0f050a06060b070209070c08030604150b0a02 71
    0x361400b08402c80c900118030340054010401001c922081001c0c00d54151550340340c3c2001075001440303510504202e42d801c1000003e0102d80c00700401041c2038074550b04206045800480c0c000440c070512000e002c1c02c0083c42841c414960aa12071034100300024104c0f100195550041100c0d403240e40320aa0158200030100409014060505c4502880c0b0b0a44030080d90b05100020708003034000d00f81d0404001300401c00b40751282c038954a0800c1c1030308513032407002e408000c1072005250100b940502002542010b0380080440300502542104048c01410781c0c0c24448546014440b4041c0031441036805a214101240030940501c003402c1074003890102d203100c460441c0003001c15108060170340f81c05112041d214210708100030a1560056034040daa0111000b018140300d882c10344520707000b07440c25260040c001000da0b01d172802031103400e1080e40e43c00340302d640b00c8001303803298040780c14040c000710b104000040192406510000c1c401c1c80b88c5c3c4100040c6500e45050380806e80010fa41900580e00c581c4680c2e22 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 665968588 1250 665967338 665967353
    0xf2d030309020112090b010b0c1e0a0c08010209060a030e010906050a050601180515211314060f0a050a1d01020406090e190203061f0e0f0402120c0d090b070804 70
    0x20b500e24004045c00303920b41c03580d18203c5500c01407240011210010404001c14142808540805202d600c1d00c80d1861072543d001c20344502c0d0341842164115254900081c100b5070600a41c0c0b840200148568201005081d0660140050348086041950380740c600b03100181c3c1e107203d100e010b502020f1001900e854030030000b50000c0220320004d0300d044c0000381c082001b5910000140380104543c50a01e0b11000d400c80c031056509128042d50f03101e03000718030070040c80c007000380240c1d0001401a440d030703404a5604800952500310540300d072042c1c003003480006950320034140c000e2030300144504000230340c80462008054000c241c80c0101c146903500005c0800100394400240380142500e00c1482c6000d04181034400c20003100d00e0040d418868000c00040d5044e9560740c04041710103490340e101440d01d0317110711008080c4a0325850316441101c503050210b01c40c1c1030070b00c2950264000785031803141d1500c810801e009076410106c0c165440340d8540d041c100002d00c200221600030356031521064841d0400b880c1010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 665969838 1250 665968588 665968607
    0xa0c120f080a14041e0f080304030815030a0201030c020f010f0605100318110a0b0f0d1d0703020d08071b0e070512150a05090c0a0810030f2d0303090201 67
    0x100d01d0b061641d880d40c440e0803d680d480d04550300014014a01c50341d000084800328100380302820154a0030241c1c0e0a004000d40118442c41c0f00e6607074030246585946848044458036400660107510903188400154026807144440000500484e00f20503181c4824a0969051288004555884010410580c140941440302e160000e040500c0084000031701010600c3c40d8010160200502c400340009580b200460440603010018045a85030f99010090081c2da0201c0c400e41c640d02d180200742a42d01c80c421043d9031010044e18003a10030300b4555001c02c041c86034845030039952807a08200010000e09201c80d6035200c11388103200c0328083c03494090b110040b1000100b60351305010041000c52150100c900d406039000540e042d504480302040400f24040525540200340c01004010900c01c407201d80801801200560b90380395410b5a40c0d0a1010710b80c828140300c000c200000f0004540d0004025000170140041076200d4800c08200019044ea042d01441303d003900440d030707140842415940d00c04080c0c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 665971088 1250 665969838 665969851
    0xf100e0f030301210804121a1f060c030516111008070504031518050106140619050912010912090518010308090d02060d0606020607020604050d03020a0c120f08 70
    0x150304561500981001130301c043c1520703668190f054110309082160710800c0d43d020f001d00ca80300f10000c14013454090070312000c01810985442c0c40400269188a4004680c00c6000800c8071001010340b618000307981d21107010741c0c218140001400a81000d03856540c2d00c44903140500c04043c0c03031500000034898030600481d803107801c001001c0d041001c0242c000302224200c80e8419107401e409010340c1c92820082250707500060202e40503c01c2c80d0180241500b20400b81d4120141c14000a440407040028070b1060442d0140c0d080407034010030355070a0187d03000e001d0616018141e28400144010901e08541c0e841c6000c54200a00e0800c80428550040708000609001d1300c802c1d69036100d00e00c4030b564000c01440300600c07080c4000762014958641522a01c0d100d540a4140340e1211600d048502c050801c80c0a03900061080e0000034014030b01c00102d103809590444082c0288a15280044000c1d40c010205101400b50306009100007481c100607a240d000e038a941c80c0b4000c5011034034001c04891014258 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 665972338 1250 665971088 665971093
    0x9280e0c12010e0c03160c022206091e0203070309020a080f01050105010e030c0f04060f0b1c1404060e070308030a1b02010e0c09060d050d170601051e0c0f100e0f 71
    0x400c2040c0c13002c00300b100c0d0810b59200c02c0c420b1901e14150300712000c03034800000a40108800c41e904d003082402d56000d00c1030407028070003070001c207031108160740440e1201000501080308825a18440064641c01150428168500031802078200e4004c18110062984078001a602001065074040b40c28030409000d01400d29100049210010000380e40c0c0300801009840380c940524407030001d5035590b2003075006200e042c0b06400c4040d519440b0a015030031020350180c65401488400c00e01c108644610140c886400e4400e01c21034031592200d1000b01103802e03d038034041c41003002c04008101c40d6405140320300040e1902050b6105010440c0030000302c2c45000800303580c10126141e01411011505861805003a25000b246030f42c0c08001941082105102a06502454140c1c030001a0b0060103c1c0d05a81605082c2c20b8645501d030045901d0b00c52490740c0c92840d00704004020104621b08010952840395808841111800089a5003400d0f403070750500c54071640e00c2e0102c1544443c280b000c0020070b50410301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 665973588 1250 665972338 665972341
    0xf080906070903021e0901080a060f20030a02040b030f06120d020706030b010c080403050c03061b0a0305130204050f0613020304080409110c010203070305060a0b09280e0c12010e 78
    0x10140101a4034000240301c5c19010b074030722a445074585080031194200408003034955039201c03034054a5880b00802655802d00704212080da04105010703140d810501038285d10258008900b01020340e4201400291040d902000300240442e9030f400503500455040c2c580d0503950600390200145420320304441500c43d004041c1e085c00543e0081426421502c15082c0410544a0500101c852940020000344134080114010081c454000780c1a002c550065045034410744402000e900303840d2030410801000d410400405e10f02510941015070401c503034032844411007802da40010280d43d0116000207109032000200842850001c031011944030451200f1859420941c4803070b13525102d42d008008407192540d1420901c894814101d520300b4103204000c540301d04119100601610055901c0d522030303802003030040366440c907642c11290b00714802001001110620083c4400d1540d4120301044112040c00c400115500d90700705443c8501d1440300620380c3c800e500c04c010303045481c060300180c240760410300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 665974838 1250 665973588 665973601
    0x1b08060910050a0608070b0a0f051c020a200f06060f0604030b070c0c0f050a0f0503100f0605060c030322031d03010207061113090507050f0304140d0f080906 69
    0xa404035401d40207180214440d80e40050460243c201035105924902c603020b00015200307210006080540310070390f40e02c4052100118200c40030301402a0b01c0381c1c20070752208840b44c0b80d4a02e5000702107000407410880401e0742528100200c810009207004626041428880c0c8200018409540d001e00b003150801030b051144c0010850901541c000240b09030010008900e05a001d08119000254003c05244042d40c503440700340514070701482003d00800700300e1004601c1410003900d90b02512000b500514004505020b41c8001c1c101014908800a54400e4041013549800c4001c040e0246e410f00115902c0c142100c2c0040c05500b00c0c07549480303003030344240381400080d4031205144148180103294114050b03804002402807040040080846151403845461840b07641c0160859a060740c80413901c3c940c0c0e6520400075103108495030b90021b8020030903800c00310160b5003d16000750048c04d0341c0f2600c008040d121031a0800761b084001c04110410910352401c2e40c005006079019031420040d00e518200300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 665976088 1250 665974838 665974843
    0x30f09060c080f013005190303050f0408031f050307060f02240c0d15150f2f07030605040501150b0721020313060f0f090f1406070602071b080609 64
    0x3600328104842d101620f030380281802120030480039402c0003d87d00d800c44a00c3c1501c1142e800840102c0c082400d00000520b81c1c0c0140314401c2c030a0340c00102841c51591240e00c0890030f802c28541c1032880b900c0d8004041900d880800904020b000e02c0e444c1d0520803a03504030f019182c110b00c800c111299104d20031494504000360102280c1200c0300482c0c0a07110841108054003511501080d8038400c41c10a000040045886117210301075141601e902200a50400081320202c0d40c0c122501425104841c0b10500144c6201265122000e10000d469000752203075542001c0d1542520140e44680d120784901401020103546280240402c0f840e1500c0c0640f5130342d84c3c00000c08074080031035108000c1641c10440900920486034007140400d41422184d899120182c1290008548500010300e082c15039954039000e0340c0c83d08199007501d4224184a860700600f001c400c0111303242c2a42001003482441e00040003030001e001080e02c20300c880d090f10700e0100068101e4060641c400429580f00078144480380340003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 665977338 1250 665976088 665976119
    0x10b031e10030807170c010207060e0f1506030712080306030124050405060d240e0a02090f0a060b04081b0a0b2712030c01050604050c0d0903030f09060c080f01 70
    0x100f21141c4030100b606020003048104c4260840d100d4000440c01c150010660090050038801c80080014400c002e04031580c0f1000c813015016190720011000212240031074405a1250b4001c089408043d2110003040da61005d0020444012402100340201c9240030702488098012502d00440c410003116500030214034244291402196624041415600d440b440616804e030090700b050382540c2940d800702c40039600000d41004035450310031900386650012511801d2250010118000394032440c40700c0940d0b000c0078110440042e908d140000e5800d030001d01070b02c01405030001034082010f08214200c4101c0c400d42546204030101c1c0824800101d0b10801d803007c1e600785002c1c09010708403200100514038807090003160b1001c03940160320b48240c400401014008070740300003030000307803961014007099410580e550004940284650f0720714000b9540f10501083c020f180110b145980000c006084458460096540c1c9440d00e040344680c0f90400201c64002c0c2d03500c004c14506625042004d540c6441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 665978588 1250 665977338 665977343
    0xc0b0a0507030e010c0f0f0b06060c030f0c0f07030c0e09210a0c050304530309090708040203010e0d1202090102030d0f09170412020f040e06010b031e1003 68
    0x1500c94440704141d10401c02c05240359804106c102d0034140a050514940b00301082c22107400b000540094040c1c2042001c0e101035a26000095040c03c1c000c071000c0460b0341003032a51070b001d8811111070061801d01080490019030066642c000040d0600c4c0508031500c60082440c10301e0750054000d44810314402510100c050100818151030f0f818502046841038641d0744054101c2c80081004242448108080d00c1c0440c3d5114a568000500c0c02640a00c81506d4803c0c1c248410b010210760030348070000c03a1400d42000000c043e00e01d05403204000411000007500c03c0c00014628030100811801c1c01d215420380100c003500100401c01ea0031500404d44518203550016454010a2100e1564020800d440c10814943c0c003d210101200700c40780300800859000b0b50320349200c80c0212140160180c111825500d4910119011450940900050b020380060f480c1c3c00503601c00c141c003503191050184d0b501074695140d80d00d5417070a01102c00c2e800791150a80c5035245008000070303c465a103158124204995 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 665979838 1250 665978588 665978597
    0x40c05010804080c120c011805030306010806210a0201030e03030f060f0a090f0207020a0509010b040b032d0910180b0a0e250e0105010c0219080f0601030c0b0a050703 73
    0x40c2c0c1d61402e00c4803030090500a819602c66907042602c00080301015211200e9107900800c41c0000b9450001d81558041c0170182c80b94204001091895218410a40e03100c6d1014016801740c10401800300700d200d03032a00c41e003060394100264100c1150703032500074100c402c40001c0041d811800c2441700c12108034400782845103d110707007088042003603ca082c00c030001000e83d04410040040e10321600c101079806510304a12405c0020740200c2c44d0f29016400605954401d04124185418190400710a0b800904554612095100302c034141900301407082d60f040a40b2130b80fa038400e00b420034815107800c00480050700710b142003d000e5050480707400d00304050182c211814484944811841030010003041c0441c81c1c0c140542e0a813100c20403500682c50304180450b1488207c500c0d501d1283d1048400d0070700416000420020380e00c005490b102403030b09a0800c406850010441d41e518800e40703007410400030480d070364101e200104203200001103640c0c01407031180c079080d15000d5508401000e61180c10030040030710 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 665981088 1250 665979838 665979841
    0x51305090f01151a2104020102101802130c0507061d0d1e0816110106090213090e0a02010c3008220c18090213140f040c050108 56
    0x100030400441e145000c48100800060040501030f4402c241c0034011182c3d41051001c08120403101d400460b95084621100e6a50004070010324041043c0054000c2c4c1c118425003945151030000c6110711240c1c0e020705031030100310b01ca261050141c81c80a02c0c41c1d110070985070540c00d4207442c2c1c2050880740c0d01039211800207003d1304061444498505505d2504641e40b08203100c0c40c001a0300070104980345506034415460f9071620b0982280c214030102c80c582e01c400440da0100c41c20500540e400c0c0d020000d4200049116030302d0312414001c0703030010300e007800340728600000401c42004103100e194524410480900030160164001811210940c07000a0006e0804501c004200d4040b03d0b1502951200400c1091855062903005040403810780e00700130021140240d00c000c5070500104010300c60b60008444d038500d8500014480b008800c180b04211444d05c0340b02c00401030faa20001c247c1580b444402c005900c10905204240604006041c1d941601e4083d080c0008100342c000e0b403a00302d500920303108809 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 665982338 1250 665981088 665981101
    0xe100906030b041b0f1d01020a020d03020321150612010b070c0306060b0703032307081e041b15120b060405060307030b032811061e0301050a0609051305 67
    0x10a0003000f070503100d40003414500801c0354000c06607032a4aa1702d541d01e12a03400082080680c0814105200740580d1114404400504142900c10180d60103401a42d081c0221018400b0340c04900c030203011465003410080280740660400440c800090644080d410724405200500441406020383d003500310003c51b00e00100242101d402015640c0301100b800303605c0c1c4c2d071241e020b00740e044850100c000c0383c203007180d4800310125524842004401800307003401c252200207084d01c1d0240c010b08284035212082a5804903204a00002e6000385d114010000d51058800314400d000800ca40107550310080f003043c5645c5803036110b00c0102c0c01c00007180001a46050090005607144071301c0d40300b950441c8010042101c1c041d05948000002841581034440303c01441d04e040c2501070701241c1103031000c19030900031008034403504101c1e0b50704140544841c0c0340a48409201202c0e03040203041690811000006010f5030400d900044000c5c031450521220140c180000036a5001e9410b444221640d07999000620 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 665983588 1250 665982338 665982341
    0x60c05031b010912182c04050c040603140d050a020a031206050a14030f12180f09012408040218040501092001020c10051215090a0203070e100906030b04 67
    0x480b00c1d0310681003111100c02540203070051240017803503809509241d00c00134803061180030380b4109244001419082010a6903d45281c03800940181c4042c800e1844800480c0c0310751042c480a9802494076100c000098441c803440d00700614040c2d41004014013030015031640000f40c030070b10542d00d820644a11304400347c455000f414540d1066a001d6008500011000035801c48140b464000b030b016035100e9807000e80e055940e00b96116080351001403c001124541c250b1520944041b90000d1040c18a0351141c4001041b94a007070300844140925922013540e9a54081140c00c0e5162403400d080b640c0d89003540014412030041e0760b010070040905000601045020350060007039981c005c2e51100055003445083c1c2260350a4a10325026100b076a05401052421500c40d030b926048540e59182f03000001e400c052000039000d0b0a030300040f150303841c000c02603541e62944548a03081070040140c40b0300d03203000020040075504054600078500c840f50f40d0b03030280e0700c0b0032040141c4036142030125031780100320007040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 665984838 1250 665983588 665983601
    0x90f0207020312210106031b0f090b070503070c03050303060a1202090c0f13030606080f060408090d02010c140606010e0d050601061119050c150c0a17120a06030c060c05031b01 77
    0x8404c640a4004507465406900804001c8a004440e46c0289510f0303a040d10300700c07c13060607080400c0d40c90000304131445041006041d03080c89082a20f090415640e1a83d110401c00d41044442d0340011040244a08001001400900c8610f000b01c0c2c05003040c9d004210025000b070000c696031440060f905814007082011903001c078058101521030541c1c3c17402c14070000d002c80d0041d42100d014500c40c0580340031002032254050307030300120480d241286044c104000a800010120b040c4001d0700c1d030481c0400c00900c1402015510040a46140d00e091400184403a4240410a114034805006400400c1c0d0000703055042d91300301e08100c1924487c400002c3d1400b19000308050881c10804910303010445c4c0450b1240c103080c1e040d07400c401516030b095034403000780c000c0e580c00145c25440780040d4400304110f24440400d011021541314a045450103140002001c1180e001c089991920000c00802ca4098500c01c020042850210190702040d501c4540f6442014071561070200c159801000e110020361260 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 665986088 1250 665984838 665984887
    0xb0919050601030204081b0406080c0a15140307110613030f111903030905060105060c030a0c020f04020c0d02060f09071e0f03050706020d05070201050706090f0813090f0207020312 79
    0x1107080e1019510b13207241440d107142859010750f041027800592244005001c035455040102102e010702d0034040220003207040400d842c41040b6108400c0d4010f900f80600641c010a425a502c00d44c3d0114000c1c214030305074003e4504003040c0307903c180c0b16000c6070380618041c000750100e19140c00721401707094100c0c1c43c24550300c44940e500d03003040300301302d04158050380000142c61007081642c0c1070341e9075030080103018000c80c92200d00d9a0030821030700c0e420034490350100c00c010348010443c1e1221000400820100d80000d207003500c4139482500300c20712a50301084010340c00b0350b410031010030130300e4451074050700c4071010301c0350b14592907a0041c0520602000c040d5040546101c5000d150902c2e9641402a80c4000500c02e4030054040c5c0030a280c00361744200b0031214203a806840e4545070030881e1307845800909406805590310740612400034001000200203021000e20009a840400d040880040407240c035030f103200444500c100304e036a0068401040c40c030440d0260340310540d100c41d08078401e509003104e0480742 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 665987338 1250 665986088 665986093
    0x3031809190c1701080604020a03020907022503151104090209040f05040b010e070809030406050c0f010c020102031005011701090b0d0803070207060e060a09050603070201090501140103060b091905060103020408 92
    0x15045407981c0003d00000801da240b0b070034102644d03150038094844109030b9010350040c109600500c05410700d06041d54001030240b040b1a80e92503400140da002001c988020b07240d0561160303081041c064141010320840244010806c801004821202d10a01c210b2290810450300458040219903956001c00500050401c0522882c6000e1901d5442003000b4004e900c40000e00c20045164548503002152240c8003e000440c601800c140d019102a007003c9642c074014410406801f010350030a0140c1070b2880000c3e00050788138180f00315140c00d5040250800c0381000039050780d04480290110066044508500001441d088180301180a8145070f01c130280046900005020403141d00040c980d040f9005d235503c1e02c5070380070301008000003803080b081b01c07800250503c001400146002c3e4000c5802074141d0000145500310341c1d0350942511107091701d100c020015500104240807240c02204501002180d40c0c00482c07800000d0b1854000e4041c00c0a803101d5507800016020342d000b0380c100c502820300c8208 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 665988588 1250 665987338 665987351
    0x28140a08010f02090a0e16050714030a0c0308090c010e040c17090c011e1e05090d0302100609060803030403031107140c01020c030106051008130606060804060b0303180919 75
    0x201c501039130002000e0f50140880301c0c0005880d00c40c0101090180703410204c9142c0b132090392141200d00c0d803c640c0e400c0e1a21a003280841c0505802003000b4204600c003500e8075200710110781400b5196000c01444040c160300070000080043c1e0340800c0e616182c0400304d600086c200c0c01c00d50100c4030007200b031410030080c1d10f02500b40060850b0000300d254011500742d88a502038010315a801c001440010301d481d020842098148000c02d1040080002d640c006191003414142c4440025020201500f4103070056003200c21043c01c4400c007030050314042d181200c0305010071441c009115036079100c014405820955144c0c10091003910340c0040795210341e0895100180341149290564a468a40d82d016026104643d030f04040c034201800354204448001300328032403403841000c0541d040d04000700940440c000039149580000c07014880c00018083e203584041d158501803521300105c2d400034500c41d110303500522060180210011403401380d690151192021901c0300d005460003900d07807003062a10780b801c3c120b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 665989838 1250 665988588 665988611
    0x1b080f0f180102010c0503040803090f010f020403030305010509061012021e032703090f120a110a0f080d050901031d0d090911040b0f13060e28140a0801 67
    0x100680150341c80c4102402100712140016422141c11010100100350709000080214038040091503110304000c0c20b40b4444c1414507010790840d00e147c080036005135404034051060541c58421140035010075a40c42140381050b0b4005075500095031401000c000020144c000c80c011680c056401d00190b103049212180900111811a0741041714080100d1b1580f07013181000c448483c0d810750303d0b1007442014514040300309060140d05071081d11401e4200d4510398030f0910290040041411a5020300c5484003001ca1010401640c00c500364403424a071140d90100380040300d0301141c000703044000f600700300d41c4e00c018440051b005003c142404010040418180da04102c101044001a01082d80e4501c0030840c2ca0358410300c1215220404003001210921003805141000c0000b001c40350409808281026500351000c1c101e0540c58010704000f42d0301d0015007000341000d522850390103403a0105200042a200095094500781e40f00300c000a008541c071301e25444c0c468081d10806408070800a00001c6540c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 665991088 1250 665989838 665989867
    0x80322031406070f020109021e010903080301031a160207150c0204020c0106050f15030402100e100504050112050702060708040c260f0106050108130204060b121509071b080f 76
    0x1103030f8040128a0088080c0c0286106210342c2104035402001c100134084641c0358603443c0514010010305111091001001060000018600039841140051038078070b40a0041107412001030310302131112000b44500d5100a402003080000c1c1c0f004410900c1900500000c102c0fa01e00300b025009e50060301c00070350100d81071019008a01580d0f400d817906140000d01d84180002d641e5030014040480c9404e01c04a0010300e000e01c2000e0701d0380c5051402038040404080041c6407903811107003103004600d00260410140d600300c0b0b0040d108901c8030314100610314008a001c2e4643c00020a0b610130001e0030380c009001c00c407000d412400a00081800105001c840011081707600414003801d00c0c0300d03c5206809803500ba01409120262001a034a4001d1900c965050100c045940fa00882e40f1944038007010400c0c032000c60240c140e1103440c411184407800d202d5402d17002c1600c8030100300d01035480801007140d8260040c403407074071690b242080d402500d0306906080096001e011181003214100090f000e0a50001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 665992338 1250 665991088 665991091
    0x703020a0b010608070906080a0e010c0915051306030207170a02070503060105091608040807050d080103020f0d020f0607110d1b080607080714090a060809120301080322031406 77
    0x6104458402e03603e908041d00e80c20401c407401c100144100f103081c0726140c07244180d1030b0010385000b4041580000320240509441e02112250002085107008102520781c2003d80201131045040a61034411605400c03020441240070305010b054002402d601004001c0c0506a1006900303130000e501c0d8001c068000b07444800510816110f88943c0d40042018500208624043d0f4437011300001c0740050796000b074408003001030060780d0102c014031120001c10300901405411008a0b501c1c46007560551040011b2884c0501d90036000b480b102d00c0581c0181c980940150f030b00c3c10111080e0b40c0324002741c908420384070400100c050b040210036402c1c00411009119440c05500c043c0c110201458880070410380e0750500715850390001d2007681c0031030310302c0e4040c0810078071441c0e2200003030f40340c00704400218044207081c0e44010002a030800800c07100d101c0034440a070703403003a0040d44640313554513007801d551380d90040d06604659040208007100c0040601e5290400866120202020001409a0f02c6486510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 665993588 1250 665992338 665992343
    0x11122d041d0403231806090319051e03120a0c0f050d0e0313091b0c080d020c010212041b14121c02010207060c1707110c120703021008070504090905010207080703020a 73
    0x4031170301c0a9180d450300c4010341d00141000390042954940c0304c80348041040c040c00d000d503028000ca64400074134040c4c1440041840c10320310011030703a034181d8154440e5a91001024074881910303101d03402151030760064039002a81c606151a41c2ca910f0388001000043c200d8902d0040c0d188000a280c2071400307094007245080b41d407503100030050810109201c903845101c0b17208800009101250400015045501414103030b0044640182000f40e03541105007203a0104002c41078420f9a00100001c00000310310380f0300d182c1c074036469603524946030001600e44086001d100b688182e00c4802601d5013072108000c1080c96603270074144d41d11040381340d03040030b0300075401070400352101800d101d07483c9002c4e4090ba1140b09200405201d0200702ea8801204440243c5250aa40c0041c02101c40202d62035486511451100010801902d28540b56104100c000001c04a9071428401a44200264603802801380d4045483e03508000c19240322903d003240c0203109d0000e0003488580b0101d048424150b00081e2101d0766807 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 665994838 1250 665993588 665993617
    0x2a07090501081204050a090552052b090b041a070804030e04290405100608061203090415081b09060111122d041d040323 53
    0x518483e0040c086100f1809002e41000980008100726003030b07540f24550045490302007443c042c07510b0100040e4081021102c031800840044880000c400350803403030000402c050030080e9018000c10f0060620b002c0c07900031490421078076168a003980100c440d030a0341c92500f030001f002009035500e80120071420958043e607602c46d425100701d42e0301c0381002e40c09028100ca070f251107140b580ca5545c129680130402d000b0075001600e81d0010040d2850402d80400030050b40740e045032850310402c050004590000f0300c00d005510110302c082140a0f00150f20300c4e00f00c03c0545440103801c3c0b905481924601c54100150b0300b0914000c1e200e1103408402802100b50390400c000d9075103e0344100701280b102005100120752024bc5103000c90390a60291602d200707554241c505a80c1c6c0b21000c6540c451860704550200708094420780842e901c0320300f0480c1801502c0c2c03401d0013410706107420050001e81a40c0d1210071351026084107800309041c90300685540120481c0242019200c403000b078101c4456800140781302c0c2020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 665996088 1250 665994838 665994853
    0x7030c0f09020a02030f070f050601030308070f08040b0f04020109031e020a060206061e1801170607081501050a12020319050a06120204050703021b0606010e10052a0709050108 77
    0x50300d503402103520f000c1e0720780d00450512010794400000c03035001e920308442e05051482c03241f00040f0244041d5000318020b8407800b00c20304d00b100016205070000c01c08042045440c1c001c20001900c2054800e420034482241000b0315540ca00c016142411150000390001910a031034040550043e14512910743c42070305c0240ca044c1d41e88070203980d6400c041e250581d1080262001c0303114160a4004d11640e288010101c6507030b282600300d070104050080e08281c0b0440c0d02010190f4892504100b43c82d0010300a2030130f031550303142c502c92800e1202038a404050400c540029040c1c00140304a0388903440712802d650840d5030341070000d1841e81d5140c5220740c2c400b01d00c2c140b1000688003220f511460301214100c0803c0d80d102d141c642d082000030b1a00906000a1680c00d1202030b42c4c00031500108000b803c14007000307000905018002401ca4142040c4480c4030f864150740c0801c060343e2140c150381000c1c0c400d54030304498150f00113030900100111007a0304050f2003031040000b02c101d400d41207181200c40c03250545020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 665997338 1250 665996088 665996099
    0x3031207090501210915112106150a050d140f091b0d05160b1b01090210300c090807030c120f06051e060102010b1e01020f07030c0f 58
    0x20001d8402da810030070075481c2100c04d48481c82c0e0300214800c505c1201610001ca03500d4039a6400c4818010301e0344003411020510310301204e40e50491140c11580c020f1060241c1c64041d002942004551103500031110003c030f4260107207405801900d4003100b0102003402111854440380b64504000c9074030503209108403002c40c0801e0404140900f203109005074403010100340805100d00c0b101440000c49003032040d01c0040c000700840d883c00c1d00c081c0c00340410459540016441e40780460105820480003071f49014190030041c0e903080310100841100d070406110881010740e8180042c1d003c1012944444510031402000c801c031944140061290368440061481d101d40c00155a0506030200500005061000380030000090f10034141c1c7d10311074900c102e100b100d56500e4006071441030300c0e0b1011021001c018a00410452201281e102d082840200103000e0550001400140300000c4000088000b207030fa071070aa4402c1c0580b40b1411030400c210b800c007940d24584031505558a100e40c0d07035072403c6080042071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 665998588 1250 665997338 665997347
    0x91b190e1801060f140d020c0d23070309030b0903070512040807050405131a1f0f0306051b0f1207031a04050901060504140631021b0a0b011e030819030b03031207090501 74
    0x407002040050304844c40380030050b00062f51113242c05400b0f005807101d001001910880070580710702140c102460712211246883ea16014126810200084d000c0c4014080c0c0c0c0d80001d00c0c281100c0c000c5901040c2502d640f595001800d20f02040689648184002021040011031445004440c642500c00445031005002c1e149011070380180011400c05500800100d466034009503000320f268810380301d0b50000c000c04015650700071324140d180c2c894081810b08860440080403540481c05080600c040d4065056810f0b07a00004a00302d4491552507000c145c0c6c0c64425070010000d4100900100104540044c041c61000f00803103038103116091036154201414980f4004070700205554541da606900005640f101a41144140c0c010322520405021030420041084105007030040103100155410520004100072101480406000c4000c0040000030034507030072140c2090b03e02c0c10b110700320041c0340002c801410a0b807050a40c18800410b5000100d03a008544500403003280e2070f03018241c1d50346d500544 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 665999838 1250 665998588 665998607
    0x60501141203030406051008060702070305010f0606050703120b061206090115050f18130905010509030a21060504020316020105060108040201080402091b190e1801060f140d020c0d 79
    0x3003642d082400460b0025220b600b08507045510a8041101c45480b0a0280d00c0c241c1d086030711500591000e6410011300900380705801030400303a0401032004604204d000303041882007a40040401c8099407510300d0494080c0d00c45640c130340b4000c1810340d4503202c00030b50070b03c040e00a46000c0d1240c10010000030b0542d0b541001c26800c401c150700c2c0c85041000142d521481307900308010100020303160f080580da59039103944044594030100040090040040c2c140182102d00003080c00c0c11651042149451160700a0031041690700000023010030201c40e0079130303100940034a43c8a213070841e0011046c031a91494a01140ca01001c0f140e00800c46039642d007004550800094602074040b90b44100424094146007555550080100c0c884002d60440c002e0707900c14a40c40503014640c00c4605210516886601c2440c9883c41c8130201d441003846c00c0322510000d080c050604c81c1e1824000c8051641480e240651010080700220b0301c0314036140c1982070b408070040e40c040c0d422814140241402080d07520702030141300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 666001088 1250 665999838 665999869
    0x27030201090605030a06080307080714010c050913020c0715120c0e060c030909090d18033306080a150203090706110c120106060906020607020c101b06050114 69
    0xc07100340340400076121544082d00340c81d201d50b102c0c403000c206c00c0d20810007408664403440d20300c1e80c0c0320105c0c10003c2140842c007004003100c3e41050180d5860a03406000e50b4034100048603896406081d881b0140001c0c401d00510054901036050b002601030b10f9000540e40094080d01c420b140c034604e0548400490700d250100c800401c00e040c892034502d003462409411940000c000b22440c010012001900e081c0080b0303000c2c40306034081841d900c4055072009840c00c81003808402605024110b68845110701206000480c840c4d0a400804100745107003140d004404203015010021540c1321244a0384074070b007102c4180c954096030506610851614400c0703d10030740660020341042d0b41000401c44400340e00a541294902c030314803407030741190f60300e40013842e00b004401e000281d480c0c80d040c8054540241039200b1000d5400c0141040358094010034191100c080480c2e100c90036241c28401920040c50034040b80b030003100c085400200b0400182c2c0481d05803200c55500f00700c2e541881c01005215601d21204 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 666002338 1250 666001088 666001097
    0x11d01111204031b051e1e060402040905071508070807050313060f061a030603060a020a02030a030b01200c0108090c13110c0f1018030e090714030727030201 69
    0x5021030310413840d100d500002001200d100150700c3d00c4044c076004124001032008491000013000c030f44010030203601d5241c00d2a904455041c9241c01c901c3d103c2c2c0d0000e002a0203a901c403011241004428000d2001408a04141d440d02954000000b441060b0496030800810800800b0442082c014002c1c0c910400880c0300c000c4a00003140c1d2003401400185115441403611083c0125010803001c042d100200002c9a086481e85400f20805140650250160b40820320400c07607100650350110868441e40d12508012440d500685c0048031700940c805030300c00c581100d0a001c91050352000c80d0754030a51b0001d9a44801c0fa4540742c47e1642c4130010b224105601034402c2000f118048110f40040c110100d201c0b0308039007400d00f204215814850104c19003183d540082007034500103400d5100d20b4090a1104100c0204070342c00f85c0d0040c0056503560041446072600e100042d05c0c0074442c001000c00b02420500c2d4546a08015002421505200d012004100b802d0180c1003000391103844450200d80d0142d4a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 666003588 1250 666002338 666002341
    0xd020a170a27030e04050717130803060909030705010f02220506041703040f060224090723100f0f1e1809050f012412050603010e011d011112 62
    0x100544503981c1d4101c3c140304812440700340641e91403051034071030719803a00d405010001c05084038004a40003002110044400ca5803c4040744110068035802101038500304540e84650860754034500031248000c11a600b82002c4400001d110b4000d00140000c41d40100c1d0052a04021040071401900034a03400c4501070000708449001c4051160119030305206503440e0948070103d4034034800940d004800541e102107141401012050521840295110030b954140d0505201d4292074014034402c4000829111050300409440c2550300344a1b800c0c010454448400c00501c050501c8103401d88220110762034091980d403540c002c41045002210a0f43c843c0700102d0b400d602034984c507081c0300c0c90420240007100c000c110015a4422940030350804000040c0e9585400d0341001440b0b9921007a200105040c00c05a1040360001010f0003450a0350f1808202d0340d0720840401e00412010070400d029600740107a84080060100750602502c2c0820000d02503005041400c480728415843c2030004c0c5241c410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 666004838 1250 666003588 666003641
    0x1513140607030e100e030f160f0b090906130504050105090f0109050304030b13080c03090406060e01022a0d0804090c0516080706090c08010b010f0e061804020d020a170a 74
    0x345040c1e0340601360030000d112129090110303250040d4480060350729484035401e4140d01425010340001070441414a4180e941014401001c501036480200c1c050041580868130950710500070100c0381c0d00080082007546446c1c108207010b080217489403d218000e0011000519006008000b121074105006500d42031442c0c1d694512414000d04914154400c51440700c0069180e5000b0f0840790b076098019520b500890042008450181c0d0000043c811020b6003e107560760007150444540d8101d95600b0007100e0180455007040480c0ba91141e40500100704c01000c0000c000044c0054500007a4104480c000e100c00540f0103215a401c0080c180b4a41400c000c0024003800040902903c940350114900e420b070b42e158813819440381c21400982e510380818541a59000e5120a211095880e0011380c0d04007007400711b5254806d000b0000c01c000341820414229881c0c03a01251224680340c40110741c0c0c1c12050b040101f240010300355030081184440040f40c0310880714082c0420181903800003a002e4000d04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 666006088 1250 666004838 666004849
    0x5070216170c0301020c0303310b190c05040608100b0403170c0607110616140f0f030c0a09080c01090e0604180b063c1513140607030e 59
    0x403079030356940c031400300520341c1620280040c10403407084400458072410501d00042c070402007007000c10000c2d00c0358140007441c103e03414101180503030070008140480e08c40100c070110009a2504881e000760505203400c465550150040040741c1c46a51801100c4d1a030340c0c1c40c0700c00b4080a01c83e1047e251002c0c170051000c54006040c0c154640035079410f0602c0c0c0003051040d2420580c0c01c40f16040402c82c000501d85001c2070501c40d095104180f400d614020310300c004805810041410341040241d10089443c0504040302c900b161000320044141c00d441e45418043c00300e460b417082c0083c0b000a559840002803025000075101c403030440584032204078078103202c0c082803400c40003410594800d442d11840e0540071318840d000a40c2e50300458201d800e81c60000c0510450001503071856460001440990064022a056180e00d070500031007980070321403503a000545601924140b03544041e0380040d016030324452240c00c8404803032419481030f44401000082000e51701488401601040411080c0442450725 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 666007194 1106 666006088 666006119
    0x1020303071d1503040c050114070515070504171b12071202040608070603051501030c0e010c021c03080f06091306020d060902070f0605070216 63
    0x1103802070590304426280e120504401841d444195a04880d0a0f022103100500c0c0352681803500700060001002e00c03450780807074010b068840380139031144203581c0c51503005000f4114466040030301c42c51110004004804010b010880410401004002030252111640c02080d9a444401850683c0380a11041d81c0c07141000c981c0e5175440803400103100d01615200c07560b10304d84000754404a0003600e030a400030071050142545c0810002c0c0e041d40028400c051038085608403501110041d4111130003155050001514056110f1181d4081d042c008c081c00c0c40549840103112034078102c0c0ca0208030008040307000908140c140408010311021b559046203003101c80310224280315080c0780b26541002001019641c01041001c1400c01c254060001000b05890941d03454545e450500c040711a41c0200319502468440410281440007070200c0140c06d00c003c0001c8841d08298440e0f048481 = true := by decide +kernel

theorem cover : BRFrame.Cov 665827338 666007194 := by
  have h0 := BRFrame.cov_init 665827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 665827338 ≤ n) (h2 : n < 666007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
