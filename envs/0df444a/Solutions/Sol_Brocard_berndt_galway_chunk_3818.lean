-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3818
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:14.634435+00:00
-- url     : https://prove2.me/submissions/16d94be4-0c89-4cdb-8db8-7be5fbeff864

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 686510791 ≤ n < 686690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 686512041 1250 686510791 686510801
    0x1080d080a110405090408070615141903140a0b091b0402090a051516032f1f0617070314011808030a0914071406090d060e030d0e10 58
    0x9498003a0a10816412405242d8201c0b0141d44090340c40c005560b0f15424414164032030340340000c211920b402a150070a0307068158a100f510401d00000300d809806008014030310341030305040c60f001c1c0c1e401d00d0700b04001184260014040c1c0800c40568140c1c1c52291144103190360200d070101c149401c140d03a0503a00c02203d99041070f03140c000315411810040450085400c2d0100c80c0280e6006030b000d030418250450f03070003083d0ba4000d240801162005082407500410a60248440c0925442008a0080700884259030360807004082d00040000d4800d0030b803802504170407503d0860784295101004a00808180312001100f2044401400130328035502e0003c0010342100030351111039145c11001c1c0c8040d003000c4410500e00b42c10074507a42d16074031012007000081c140355038001c000c940a0680c000b04c030315011552404680d030103803062098000d0481805483d00c603400481c1d0380580010090781c0013840c03070f5200d400d0006208003160f0070054501d03410381c1200d00901c62003109610410001485078054010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 686513291 1250 686512041 686512051
    0x60f0d060e1f060b0a0c020d050a0f0c050d0b1924080d18031106120f010e07210e0c03030301030309030605070e03030a0c0203120d02090f120d1409040501080d08 71
    0x10003405113400d00160890140b41c01348402c11000b145070700150f6486081c080c05a5401030190341c8440341901e8450079543c420482203c412644210000d8a85001211a08025006201e216503603446a02060001c8884801d070314410380c1d502c42d45201d07200c402d0850700889100c0d55074501c2d01414940750700d01d0603403003040010400c0b544110003046d80c028068111700b01d82d40035070303842d00d0807402d1000102203015614414074170b2179202c401c2281e0040d200c445103040f0364142d107015a844c0c5560004461000d04140c100c10380a40030a14030780400c0051340000a003064420641700b40451001c0002e05551080e401074001407101841401841568451590041400c1c10240744400105012a48134001e28200005000d1952140d1081d034a040c41a440c02102c04d003222aa18410054a007009402070409103000b00300d40e240700700a0781040140c14410307091103001407101ca902104111540010a00e140c0301e001e80520040c24181c0740c1d4000c4074060b0055101412010b400801c008098106c0140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 686514541 1250 686513291 686513353
    0x4090b090403200718020a1805210a0503070b18010c0801050d060f050c0408100209180a0b04021206011706090c0a0201020c0a1a10080303060f0d060e 66
    0x306000009400044008800740c0d00083e4405007801d1540050a041d115400304680f0300014a44240c0031685500500ca1106d075a280c01e614407091415010070840c4c84c0c041d458000400483d00c403960703030099004c455000c7d0120101c0303980410340d503120350940d0040101103691201160034401401070704000da11081401c4d5000300060036880e540101222010b12030780b0b01900b00942c03203070240003590b041440000502001400039051018190070154054454090907028260056070b000c0020300894001010003480110442509c20104d003e415001d0038501c401690340d084001e440c1c4444c005000d800c240d00b103040032076180c14400984045500408001800e0542d410080150b480c491030940180002091a0f10340003104400d0f40248602e501088981c413490f03104000300482403240c0048a031850003160003d8586480c003400500050050700480d40003400000e10b94103110311140b0003020000e0412000400e01d0f290f1381d044400d40d828140140e00b02024020401d41803003130002401c22480c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 686515791 1250 686514541 686514559
    0x70b0c0a020d0302030a1506111005010e0109020a02071d0a0b0612040b13150c020c01020d020a0201030b0d020405040506060306060d0503091017010e090714030613150c0504090b 78
    0x21030025182c0c1e4680360030009040d4040701042008916a01020030308400a4100c10425107801c0c010740080c02e08010785034640301d99201e41d0003292a5000d081d0403600030800000e030603428000090065004042110118410600b0000e52064100c40750304400c21240540d443d81e052041c10b102c199900c54079102e015140400c400a80603500a400c00e6000e0f410203001c40c00e135110030207038801c540381e41c0c000079004010311340c820b0100414540c0507041d103401c1d940850300d5071907248005a03114404000c3d500c01581219a4100142d4000d0b0401401070000a00d90a40c04201d03138000740840e0310a540543e86548a0000c00c42d542c20b0400050360005800c440c80181c46901d40d50702a5240f00c0d03805658000d40030041c038020840d01845d1a11221088044159240d68407007412444103181190040740700d104009000a03c480503c895908600025025041d50354541e046145118a210740c226014180702210f40305084492140003c880e1251396400e07942c42c50200000c06031074409120522400c03100c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 686517041 1250 686515791 686515807
    0x191202030601052a01290307060c200d050102090111011512060e0609031207091a130b13030c09050903070b0c09060409050403021e07060513090908070b0c 68
    0x400182d4100d1159880c0b41c4c0c44969980c100b02d00f2106000c5a0a04e9660800b40001400c5d00e84000e14021001145640081e01c80340c4000c061361010144140c00101e00c44038146404294040001d02c8085942c07a44a81400100400316031514007521082d00d850358081071081440d80e0001c07030384843c240303c1d500900c409031076140d40e0903a10070b1b5840b80d009101518440d40c2d0800009030046600d95508070262145072500c503c1c41034483d44858041c4100808110001c2c4819005e000f0707080503521202010b014401d500a0104044c0c1c2c040303002c164050703040500006440d130949000b06152420000701f4025203256140c4010300780e101d0340010460034100401c0140d902400000c2c2c80c000ba40041107a2804d0f00c1d4402c00000e03034441c030300046821010004000c030300010260415070046109508440541c02200003480220501402c2a015500010307420450a442480500b210206001c03854151070350b02d41c50b5404644100404072203120010441e402401040b07060700303030b2010b4402da01501d03050103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 686518291 1250 686517041 686517047
    0x70c030c2408010b0c070f03060e100203150d0201180f0906060201050438010306090c0b090a090b0f0315060102070b04081f0e0604050a060f0c17090f03191202030601 73
    0x2c14000c80f200c13560301003011408170748108000d1008007402610101140d4a0f42814000340c0941042010144203c500400b0358100b04c0c802c682c4210103809028245040e110b003040840100c016040c3d040002d011b03941940000c0c01d03c10078009094079800102c03210300d01b842000684080b54840001c1d64074140c100004100800700b0620003030b8100c64602c0b44a28694803280ca0b045011762084d8a1030441c2c4004010000f982d0701c600c208902030a02c60f088690b171307003003500d0442c45884005030b0841d00080301040315418940000d0305514000341100e51038010600403e16000e401307041504c2e40019681400700b656010301202010341054034155140500706644103580f03808118910300b82080e88001c2c0070340140d182c3c0c0541c180c1c04060702961a6420b041c2401590341c1d05e481020360b421841c0a403c4200202c0034482c0d42403150140c3c650303180c280c81071904602401d1009110702c1c0c642c012030344903c800e0310061009056001112489070240e60101000400308008400072000152042081c051a03a0f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 686519541 1250 686518291 686518307
    0x409020607060c021c0906090e041e080c030d061707061727060403030506011b02010503130c03120809030a05040e06150c0c04050a0903080402090a02070c030c24 71
    0x103000b60012800c1c1007651022031402c4180300700402000001c6000242050340000c1000072108680c2c1c4a07106962107140400da4003074251001007001031108800270020244103810b80080d806800c03079505125a0104103070459226582d0f204115945080510845c04850400d040101a050003484107038141000074002c00c01d00c0c6000c000020812000520001005c48083c3c5940c60760f5103050b4084112520b26550740340c05031012030100b03082100207441c951040c0a051045ca0000c0e00e26080c0c14000e40042d40d6036070014020504200118031071501040500341280001c0d40f160180c00d42c0711a4000340203211140c007400c41130941e0400c00202c660b6903130003c01d0710142d901011440246e9150311000070100a81c8074a074031149a4081051003461038045000030311040107590a104583e40c0d4a60030b000c846a20400402082445c0046005401c280071619401042a00010310f02507013500c900340c1d40760943d48100d42d00340c00006d082c0200d8461007070b2071140c40c0d41c00c041a6052500c1501c0601504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 686520791 1250 686519541 686519543
    0x150e0f0c070f0f082106040504030e041109062a010209030a021c1a01081b030d0804082205122113030b1003050d0804030c0318051c0201020c0409020607 67
    0x8411032980c00103022020104100d110340c441c4c00a035850800e0801585c00712820b10a5481403071500c400503901e4213050107200d01c203542c1341d0784a800d514155400c010081000302018100305100b44542c2d00b01d03446080040c1942d48001c03070180c16030440c410841d0b10007500d8100c04600c0d640180910117054174001403070241075a0403942d02e505801e06048210160380303100c001411291000d01c4100310101d070704061034142c0d1003240c00c2e40ca109428a092640c101d48802e001c5405910210001035810311510820342c015100d00403142c600ac9144512110000242c80421202800031408124034035200c030300601000741003030207881d0b03001d5813910000b24009250f2404003411000113800c02c1010098000001540d4400c0190a1702c0c100801c3c00d5205010a0004550b90b201e00c1e1002d0351124000d000491103150305598000c40c2007419034048400e00d400318004032450704030304401715a9a60301404a0700b801000d00601c0402182e90000a152003180303141540542d02e006103140240c1c032510100ca04407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 686522041 1250 686520791 686520803
    0xf0304030b0115120510030b180703060b04060803040303030b03010c090305101a03011d061f060c03030f0c03020a030f0c05040b030402060c0f0307050708070f061d0301150e0f0c07 79
    0x703d9440da1083e120000410101e40c245071502040107101c0400c00a01c5c03041d40d008420089081d911b0094184101542416000080e0701100d401c10000f0001c0d0013191442d04068004a1495581d1882d58a50303003081d0030803004a40c503030309001000d060034031511810b84200d00c3d00d2034600d8a9070725180e07140c810007007903d10810f46680c00600200b59900031105125030141c02003180324030042840c2c60b0828003070201e0610f401003801143c82c01507072023003240d040c105010180f52042e14060701a01e0b04100450101c085c1500c03003001510813161449015001c460540300981c0e181a2240d008044440300b82403011210715052000d010680d2140503242034800446240ea03403030300d0301d0002038801d014500004070944115480c25a1106020000d0180703d440b1b5804c4803003540c0c82d541c980d0b031500c0c0280190442c6401c100b4007000103a20070424a064401d9040b0b02c3e614941046e00440d09440086003842c1d0041e8110004100040703203442c02d25445440c805003205c00b030030501061101441759407009000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 686523291 1250 686522041 686522069
    0x309010c0b090c1309020f370801090b0109051311010c030302160f03180324091a01150203160b040c12060911100c060e0c04060f03050f0304030b01 65
    0x20080c0d04004405680d48000c002880e0000c4c440401806420b05640c02c84c040c0030003c0c0d00c3c4c682800c00c80c44000030400c55062214884400010484444030040c80d400170900d03001c60b000841c5402807040d00703040d42c080d03e0f041c13500b076041c411510b0951304041d207400b85454003900a01c0c0400c0f401c0091148448c130034a0308080c02a13007410100c020f802201c00804010090543c03c82c10480100e54111030307203100c7d0311801c0702803a55070440070b003504591201502c5030301c1114501405810380380b103103055510151000102001c081d00e0301500b204100460f0356003a61040d0051203104011880d0440d2843c49200851402c24000150075100c03101410082c4400341c0300d8007080400c02c1d1410054050312544603804060f000c6400e260f4040c0140220950b030054440c1100115800c1107072715460704480c19298600305400d2542c441c0001c0c00c610100074281e00030900120465902c82c044d4500405041001c00c140c4e50450600601302003800328801c03055401003004000060b010458507045803c0c1c48800300c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 686524541 1250 686523291 686523301
    0x209040b0306040b0106051e0c03030109320406020c01150608061014070201170a0504030801150807210c05030a051f030618020406120b06090108030d02030406060b1c050601020309010c0b 82
    0x10800b100307201239030416100410411100b1800001941c100d0342040d0081c0400814681903003540c20807122035203040da03801420283c1940d01c000825030410f01c41d240061410480004507421078072042901544840c4050082010591060038260442c00495107600c00380c0c00800e01400008021a85502034500810b2850540e0700070107185801e041c0e0f1640d510a203207460a2840c00400d0200c800f2408105043c0c00490904e500031002500d0000c1a2100c50864544c18002d0b21021003000d400c130404184841d10152100c4180a65010043c0507184c1c40c4e201d080003002d40303080c4d81c001800070229800c4000f04410000d0425140790403a50090300004070500003454500440c1d01c000c602942150416100203042c440d042c20b88102140120484d540a031a580d0800c440c030607081c8901300146d40140304407403400c00654021604240b00e002c00052150703079050001c0207a0401102c640b140000c0c20801c80c000c101501500b54403003800d1000d50b1818100701c001a000c13801c5200e0103008a900040050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 686525791 1250 686524541 686524567
    0x60303070b061903120801060906050307030b1504090902030c040b2803050706050304022805040e031309020a08150102060705030a140108030a020f07030807060504080d0e010209040b0306040b010605 87
    0x141d40f42d420072030408800f680301d0401115002458400300000b842903800040d06070f10544040c800e4414a0ba0f40c5842d54482000881c040c06c44500495070100202e22016090041080200001d000d000d401007886801c0340101810305d41c400103070728003031403d108420726966695048403030b0074810031403d00381c95441c080e038001407004941c00082561256000c04207450350860f020710f106070b100712401503003008410f0500c1e80c592141d0745030031012651468140306524094102807100e8080a085900780700020a85001421781540000e542590001d2540066948140c0f150760091029103801c4450245100003035683c040200302e0000c000c4044089a99414260001c01540340466151891035031a2081d4644943c420072a90000d80b1640001c2c9041c00b201040c0b00c01100e400542c602d0400c03240b9101c3c817000d84801817003158260b00c10011801c3c11070141c424a0890701141e03000603201c0c100b01d8184003c660700905c07118884d511a06c10400000e140c030b0600f6044d1640340c030780a0b44410f80d00d5030740 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 686527041 1250 686525791 686525809
    0x60e0f010e25090315020c06190207081306140301060c06021308150108012706020702040b130501051507020618190303031406040e190c0e1e0f060303070b06 69
    0x141c5078140140400c2c008541c88400c0c0030683e40581c41040c849400090018200e102d0180354040503000380e0002501c0038561800b001500401c1e01c3d015280c0840e41d0307201d0a41e94001c16000c0740504200030f00303110725a030005138082e048600718a42d0703182d541080d801420348000701d5002010340340c0000c0c403040000100c40003940208942012102e207400c0a01404445403002d0003204007a6280010003100120350403e180d00141e201c2c0907118002002e902c50901070340c85182c050fa0015160b5641001c0b0b51103c800c0c001c1350380c07844c0c140003e2550501d810019042c00a0301ca07502c04400074060034000d07942c0c0004482c20f01c50343c01d1580d0304d0780541101240160050552020482508542c00810700d50950460040c6208881c000080c90303032804100001c0340e40d19074240c0c405a00541da641500c00d007400010f00f085000e02182c5070040d40d40c80c58011304050448042c00c0b000e84d100320024032017003d09400d03134100850001d0050b00d4900100820f650780223190001d000c4030071000211b00941c6030704483c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 686528291 1250 686527041 686527081
    0x70b03062403070f02061605071b0e1005060a080601050717180a050a0303020d2106090606030b040504020603160c080a0504061404030206070308090f010f0f060e0f010e 74
    0x281815071080324020002503002100c441001c150300310200079400b480454064480d4060044090074042c0c04402110150007005080b1b6540c02103100e2444103e18000520000300049080d0003500d1400404c001c0070303518540e20650080f0014052464595000b0403400e5014400b0720740680c5910140c180381c2550110b260070490700301d80015100510b01040005201c4d4908151480301c0001d0b03640013409880d07801ba202c0900160895241140154450070520742e040ca4100e00404c21034148014541c00c039115548070100480e6109000c00129406015403800380300b08940803c040c5c0b030141c01155127440002c080c17010500003400e21011060160501000c0303550450521038580d481c03001c01901c1a8018040e0f80d01161040b50f40d074450319409422101034990152401d03051901e1075500f03450142c0003601e621281d0050b140d940442c00030074411072502090020011602da24118107110031180242c01415a0031144000c000c421000c5528141c1103410303030a47c02003180e491801d2199080d0722004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 686529541 1250 686528291 686528329
    0x30b180c0409050106170c030706030203191802042f090102071a0403050c090103110904020d021225030305041206180809040f0203041a1008101506020f070b0306 71
    0x30b416043c440154418030070b840300300e82260842201c03114131980c5d07400c2002040da0301d41d002e49414072629101c0e030080c68000c0c10b034805400e20752003090744401c2a41c0300707001c0740340240403c1c1c07032901c0c203500e401c1c041c5403110390500c20261105c09076120070308a079100c503101082c610314000585c00c0381c917442001b0890007420180d8680d100780380500180041c580c842d200c10f5805102d0701c141c481c000d280a03d44181260391110a901c030941009040c0a40803030000e2040c0e90042c2e0044c1400d02584400171015081c2d070f9002c2c007521102015034401801031150744883e01c502402c4180a10011750001c089030107403503201e5121078040440b442d03d04041c001341c1ca90840100e003101168020030442c40042c100700d4000321402d100b0104498800c00490100320b4003d4410b200c042d542c04400390045000b2500822006d1288103141d0315030030b4640c54000001040da0311039984142c0381d0480203001026101402492000c0c21000c1502040c1e00d5555134a406254020040000801d010350b5404410780203004600e2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 686530791 1250 686529541 686529551
    0x4080d060f05101b0b1338100b0d0b0307120501140615090f060310060305060303130312030b130b040b041e0c0309050f07081501030b180c04 62
    0x1006055140c9018031a203030082d603c040081d0200c0340511054005403114200105060301c20303450314044800c02078109802d03d50610654008203008080e0600482902d84036000300c4004204402a0001018600301d02001d2150920410b5104558210203c03265140642d4032281c284800c18014044000503981c548203075a00003800d00c460f070b0134108000b40203d008201c00c26003005151140c800840320f00e40d02c4040010000c10403050440900302d840c02c090040b912848107400400c146030b005440960100c980d544042150300c2d45402102d030f016074154040c1d41003400405080300e5901480c000113211041e00b0306400c45242c030070350003916440c2000b8082c5035402d50034070b01c080091912031491402242485e14425403418a03000c3c1c4440c60a03005882401c03400c1c548096070042c030079000c07184105515204148045101042440410705407071001d03002045c40c3c004c80d01c1c500316840c00d11200381200a0010008142c02109990b408020068014160081200080c1c105503080da139960b4400d10302 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 686532041 1250 686530791 686530799
    0x6050a03050f0706080112080703050c010c050310050d02101b051c120203060310020a021203040c090e060903031302010c0602030f090f01060b1611060307080618040f0b04080d06 78
    0xa1500403142c0000c02c0c0c1d41e0494030341e0021140c4c0002401103204040c841e00003000000c1c100c00c01072400900914100742480042f80d00b060a442d10802070900280010050140300b8a0f0003540b407006040403504000d00d8401540854030440000141c503052008404404405080c1c0c03030104000c05a000050790750800c41e03041089040000d40c0d2071000060104809601110755900c2183d0107402c0050040440c500a01d817260041c0d4804c032084c004600455000040c44034148014501803440b0b08422030304141041c1d2900e049640703040e0b035902154810818030108030f00100803a070304688d6040702040058a0b03400182c1c0c01c4008000001c05040c0300100f001003469108500d58005c1c515074065946452070301c480642030718014051503407440c4c0c00308081200840d40c00c2c0840f0009103d000d400d81c66102003c0090b102d900121034080101c1c0341c210400c05075190030300f51405020010a01c0c040241480c0d1183c1d480300e41845002000141a20040780c00d000303038401070b81c0318a00d030068244455521 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 686533291 1250 686532041 686532043
    0x903160602100b0103110304021e10030914071a03060303190302180109050307091d030a0f091d0408070f15060305060a0203281b0801060809060411010c0606050a0305 73
    0xc00c48004180910308103e41e18150300c60701413883d0100a610001d4110b0301c69808004003060041a4640ca48240e400b400c4540e0320781ca07800d24880146034070000380c21901401d068100f0105a1490400d5070480481400144540c1d00401c038032400d2249159100e90b91940031030f01c1e612606040750381a6400500300f0503810b90640080c0b08654030000701e0186c01d44101c0c0151001c403c140201a45a000321409002071040340c3e0060318555050301c40e945406503171030003460a580c00640340d0310008202d9804200e2850f0040c000c000180f01200c081c6200301c0b019501509500c50140000b0080000029020103000c00741b000162195000b1880f00c010052018520303000301070718881140c090241a000440781029442900d10550b1180e18800078007484140e00750395103404070b80d03040e1620f03661b550b081c3e010303030b0280400c0c007a1400700c1e1150701c81941001c102400a407801405040b581c2c0c03041c41040001000f0840c0d180c195002030070142c41103011340c07502078060403407500181d4010070290400824850 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 686534541 1250 686533291 686533303
    0x81203090a0f080409110415020c28030c060c30030b03160e011d04080a0f12050406050a0b101211091504031a090d08040f2001090506040e0c0903160602 67
    0x2c8c20030300a100041c003140c0300766115641008900d078400c104082454450043c10646002c18118102c006c1500380c490303544501103481900000001225081e14404000d1141c9082d08883e140c0241d450005014414a10104000748510300426071210700c1c4000b50340f006c10010040446409103e481c46403100303219002c0080074422095030303090b00702034420b82c01002c40c030350340c007131500115501d02d000b4103124155140a60001c0000070032500d070303100b0882006035224941c040e40c4140c0d004500c07030030301c0f600361801e407682c16401034070540804114000030354000c44a660101120000030442c00b90196040c1b499008110402e50401039000340202c14100e04d0004000f80ca218200051025680e00c0c03000cac5400c1c0b0300b104c01d0082680003290714440d0b103003c0d4805990041c07140c18019071050b06965440080ca142c6540b00c80d1034128012969420340c0c10a05490140c00c013540c0c8a030401d4503040f86084407050160240750311480c0025014032544081c0100c4c03100304503a41d01001610356510f4000d584079 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 686535791 1250 686534541 686534549
    0x303090f010513020a030803060f090711241524030406110903030a110a08040806040212060c0d0b0a0b0c0d0e0d081b012004081203090a0f0804091104 66
    0x5440c2c00c000404031108188111260394000d0000c450490460f03890b5841c581c4090b1841c1d030f004090391282c00780c564030407640c103119940943d05c0d810380c11034605900d40340c00c01c01d20700003240c0ca13040381c800f4403d8500701c4030041e400b45820a402e00d82040c0741020070100d030440a00c03094042c2e020600188684811001035020341d21903036040110b03001001d481c1c4081c0c0607140280c0c4d41074004001181d0000e11601c0780080409404003500e41c002c01075030300c4100c079500a901c04080341e004203040106502d000060007039654804c8024100510b800c6800031107070f10030341069001e810b648210711011629020f2500300a403104811159a54021014881d51800b10f081c0040000e8103040c4494454101601c1d0040240ea02030b1101d424103402a440c2415856000302600c9550b6a44003008070002c80c038000350f42c200f541600002e60302d0342810045410407803288801a841c000400c20f2004444000400300c03c80f0782c210385942c0030410207160090941c415940140d41044c101801e0098001c01280104221 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 686537041 1250 686535791 686535793
    0x3010b0406110c06090108190f0603212015010806012301020a06020d090c03320c06160c060f0f0206090c06090a180b18010e040201120204080303090f 66
    0x1903442c03a4480e030756420143d02c107180c100b0402e004901495005100031500000489440104032141800c24030485990040d42103c958079228200280140070122400709401a0301030f041021508202414540c001c40c06410080603000d007005010009024000001585000891581d60740300c1849550f03420a00400610b0707040e40c4107200d02510580d10003001d160068001d03042c0446a0780f280c0c0001d4202d000440e000f81d485500020000350000c0101010314840c02078a1000d03035500020180b91015215140303510a050951100e03504400601040300381c00c01c4450320303628024045280d01e000008074008100c1c80b0000c401080503600f050884081e104aa540e540c1ca043d213000c0f089907140341c141d40300c400d01d4010186d10312150400000810034020054140c910469469100b800c00081c1031103410710f4140d0340c5034030401610b0100c60419036400c5030510640b807541441c1041414a0011b40000e0600c120041c0d03005401a503074059030002c11070117050744d4692070170382c40182d00c2d40f031140003544007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 686538291 1250 686537041 686537057
    0x5070501020313060311041701090b1506040504020a1407030e030607170a2a020c1503090303010605130f12050d052a0106080d050712080105100305070c0803010b0406 73
    0x8a500c000180d680100c20380e1004602c0f145080f006400400c418048400716490401000c00c80c0f551030714130303070325480c0040700009406140b03810030340244407002e045c554220102142450240c1d90b03002c1520280d80044030010390f1244240015030f05024500c04100000f8030100d403002c241a04801d5038042c011054094400b55641e000d0111084141440400d0702403070001c001c1401c100e0558450f1040f04105d807aa500d2100408008500304232160440f00c0058bc808028807801d800c20a9034140708040702c01a480c2141404200c46499010500942c1c040220101c1c028150744803060702400100100009854440c0d03e07809800d4540030140c03000e83d80c2e84200103030300311003900c1601103509031b500c81c2203880402d08601019072000c4007202e916011940d2908400304920805001c3c0740801e0b4626100c036a0b560b40d00b0320788103040b101e0100646081c0481140104180c1c0c030b0303448030340303902c04264a00003c5e9541c545005480074051031030041c0005034084004100554a0b80042041d11182d0b15a440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 686539541 1250 686538291 686538299
    0x141b100e0a060506090c03041b180e190f0b13081812060f130c180b150306090606071a0403081008010e030d1508101b050a080103080a02030702041401030507 69
    0x21741c00c17400781c8043c4000c94003080018041542c0c1d143c1e1541692840040d03558080d41d0300c0c1e20780030040d08442a810140d03620004400c5401c01081940540c201d03c01840c0d000b0305098850000740b002e2500302402c5038018800240003869552002e0b5031169004807403544030110424604104061208494051004102c460004140c0044c02d51300ca03c048080c400c2082d40c410100f4009549400750454801d6000500481d2001c0c8007618400c00031000c00e400900f4040140070401d001c2c0702e4265800d4808002c0040c003407544c4403401c0c0540d024105603280c40d65441d4070324001401040309603002034180180d00c00e0108042d03001500b18001c604549042400a4554007450300700d0b11030001c2d014440d8030401001d801490560003a28501701c04a031106003080d40e0b1814039040400342000340c194a42d5510765a40101c500d100c11205550807031038151706011158102809898060101230840e0f035000c40c40000c040c0c400c0003154402e40d8064020b102885c203080500c0c0e100781c07003800203d54074001d40d203000c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 686540791 1250 686539541 686539549
    0xd1103031e12280b0f04061203080f0c03010b0f07020d0b06090901060b04030b3103080f06090403111914010e0a030c12020a08041e06141b100e0a060506 67
    0x45400081d041c241422402e108500000704000ca64003034201701d5040b0b01326440e54951003520014078040d018901243d0b29842d00401c0448000c010942149202080c800d56403000c10070f40b4151540d4911840d035030b00450002107498082c41800a6004a41c0038114013000104500240155015a501e503115151a521203098034224090014491010300c010400f143d4041070281e0441400d20004000c0e800750300110f00b004070894803038040303185100341007000c041d84250b1255104850740d50034149400c1c0a80001c201c004003070000380400016440c1003400c5a000d0103541c80140100c43c1c03580301102640f4050005902c40c1d50701103255440d00c0039140394001c3c042070000305281d0554909404017103d556807078203103603106980003c61080c01404000103a0001c028070103400400c0b260702d0b1842c80d80d1282100030ba1950005000c0049070407100e01c21849080658040140769028064242c0490710454a048200107040d001c15040100c0f0020740300b004900c000030316005040522855451401744 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 686542041 1250 686540791 686540821
    0xf05090c010c06020904020408030a08010312180303080709090e0a200f090c0403080f07050c011e0c031b2f01080f04051005070504050a05010207050d1103031e12 71
    0x5001c102c0104104000982981c028580c20304d004000504050715842c1940c51a001a000000070411040060051040311481d03000f5040c0d541c0b61203070342c0d08441070010892807128400241030011500200c2c8226000b42414009007200300000c2200540100ca400d41e22689594281c0b20510b24103c90301e082540c0e80540700b5188009010741090203d40001d115030366100401d880030884040c0f00100000c2c408030002c0c030550781c409284039102c0e501400c20314102401c2c0c500090610101c1d0341c0240407080d02c640c440311428241e05100c1c080d200d4600781a1205150300030301c80d080d070023031011001c00c000200d2080f60f11031000703442180140d03903020110303070205c402401c2850100f11002c00040d4a800c091203426401481141940c071881c00c8000c94205860f011380c1c0b6940070a2000c01d0512090800a0304000100004d10041c40d2891619001c07603030756007a020003d0140e402c4d032010500f05440130007c80c0c2d10406021980d1348458015124aa02500401100485009034001040700c4201078910 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 686543291 1250 686542041 686542063
    0xf0f08010b040506090a092904020903070b13031a070206070815212b020109020d0b1b0726190809071a030105030f1c031814010f0509 59
    0x95140b0701410102084003c0c1c2020801c65440710402c0d030301040141031030042e910f28008450583c00d0381c0c5880304070b0018171200445c5240c001c1e403060001b402180e90014688046604402c491940d034608000c0d003280c03550540d08060200c0035403c268000c0080700b0400380e4400c480ca40e09845241d11010b00071610703668251450131030700c8172504004d8920700e0b01305c10b4803802c0c222410101a545600344003a41c2400052282410f80000f440d10400c950311541d00c0300d146404a038030082010040f15030014540020300900a0500c110340c0d00012003c080400d8110340e0a00001505901e980d101d1401041e004121500c4c4020b600f60046007849100282d070a483e140c54050380310ba01c2d085c1c00d04200301d41400000b0701c003440c03c2c801c01c2c000042c0404504101e030b405000a0804944d650f0518040c989444052840c4039010340c000c0d1400483d10344540701000e1000c20500c1c0c081030814210b288000ca08540d204080c20b0580d01a07065070081c0c1d0154000800c1a07010b500902030756580504090311004d0303440c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 686544541 1250 686543291 686543309
    0xe040c050903120a09150201091403090d03050705030705060c0d0e01090f030f140406020d02190c0e0c04081504050d020604030f03023613060b0405060a031b0f0f0801 73
    0x3d003202515901c80041c007a041c0a52502e98042036503a800c51004101c05200640507035520007114082c07241c612010040601c00030000d520707124200c00031031007204d1400c6015007004000301e58281000418421601959081303000c56145041c0300c2d1454040d5401725007130481c500e01d800300400c403911301030180078903560704816000a05001510305a0f000c042030400d150811402e40101c3d400ca00980007e04042c120590041035000807030708010303283c580300c001c08400281034104032800040940001c082559107400010344030f80c80d84282802580100d8015403d6409804220115020f0400c80180729601031b0040781c02203603014806a0b16136400b581c000d0001803d04180e8034003107000b50020000d446041d0031001500c0f0340e014a80c00b04040104403c1000c50400c610a00b2524103c0070030f900e203400e000420403000386001c1c0001401d110f244034107801000040781940c0041c1c000da000c40b010164440c4114001c00d03149a004010900007401507005c00d50018800700c40d107108200c942c2c1a104581 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 686545791 1250 686544541 686544553
    0x150c050102040b0a0e24070f02011101090c05100302030c0a050702060d0f02070b181c1716022e0504080904090c05030d141e16050f070b1912020c010c0e040c050903 72
    0x41c88541d012540c20500780d0510107030344d41c022f8085500b4840e255035a4000c85080c02041d08020805c0a965045d03001601014014018803800196401c101d5803400720608013a9070305c0169102141040c0511345810000c140b4101c40e1a0b11411a0b4000b042c2c02407041014024959400309002c95814140c51690600ea011803007035412030b03100c00d2040c2c05903600782c2807100e18403500d07550038100340a00b110902c15a601200460442c980c0400841d214004420000c8040150140ea2822000d64450800300f0440c0c94bc0003040a014011044585410b0003810600030300c203840c102141202c0b880c0c82036602900c50403801041c4a40306800203064040480d615929282d00d102409101810022141a40386070803c490780ca05500c00b80a8000b82d80b06001615007c0a03490490307042604540c00111500404c1204a441c0c04000b140303070b035480e003041c102900d01c5100c400142c0000c0c0940d0321240c85541c6010351100501d60003412000003000200c506206031402c040d02103e643c042d54580315055444030b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 686547041 1250 686545791 686545793
    0x16080c0a0506041805100b181008040f030302030c0d11130509010f09110c0a03120c020604020d1e0c06050c0601051203031b0c060a05090f0106150c050102040b0a0e2407 74
    0x294012a030422840350742c6c1908942c0350b1200ca1603550011006020788481050200d50a0610784c40f002d401012030700b0407003402d1902d0745500320410070078400101095800000503a18411710410703120401c4504800300030f001e8440306401e08660000f82405c400840f28040040d40c1e2a00502c0c01e0705131007045c0159001c8501c1e00307014401030300310b80c4c408282400040c4002901483c007001b12266a500945c0c84050100740c100d290400c07614102141c1b03046401c85810040035845154076040c842c0e40c041403065081030060a50b18880741c0742400103185112200d4001510343d8804007a14443c0b40c68016200f0a0f642c072006c11404280300c25904110350000e0001507000305030a800400300381856552580f0f410511201c650418800320b1b184150150703104184540d42d44204100b920840d12103008000040c1003041e04501410207503074500401c240818241d08000c4290103a90081210304503060b1950310091001e049016150002c41c042c0484451280ca5000349947c810380408181c01c00d41c0c58201c1c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 686548291 1250 686547041 686547089
    0x4050105090a08060a05010e01080105040302150402010e0907090906050105040311101202130e01080a030e040e160e070f020319080402011106090a14030a1b0516080c0a050604 77
    0x19a40c80e6072264002c0740005141c002405038520403590300302c00107090341c1401454150058180c10131401c5a240000b00300004c0d8000038002c0359584071a142081300c1d40c42c0c1c40103c8464060004290b008010001400b00700c0b90400615010f51364002001e003e0076407100c00450780b9005a01c00a0100c1d80d51410042d03081c20320b80840c4542c0c101c1445c0c08141711001400d00301c1030b03a114004041710b261107903c042203c40051b010040c0500200c4024120304030494600a1580d00201ca45511499840c010882890001c2001d000c12040e02006000b800f03559070170481f10301008503181c00c0441d06210320842c00e1840401151007440c0c8018051205550241c4c040300d034540c1c0240b00728181b01d041419651b030070700100300e0386108a1440009080403849850014143c00384454880400d9105111052010740c0080545080c0c1e82003490517080344c041030600500d4520f035400c8829003c3d52000300440c8041004c682c0c812514820307107039021039641e10014000c480c8240c0c40758004206070080458210741d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 686549541 1250 686548291 686548297
    0x140303031f0b0301030c090c030605060306091504140402040507090303050711010201020f0f0310060801050310050c16051e07030b010e1506130512010605031e1606112104050105 78
    0x240340300d28000750603140d2401c144aa07000b0782040d245405044010411003805000340154011580b07410f01c013052801000c6409400045d183c0c602c90703600800014018900c400941c0d84d1140c006205010105130080b0419100300141e170140d0045040200103401107008105032002c0ba45c0c56560340c0e02e020034a80310340c0f8110244040b424119502045100310010a003009401d9101d803807000c041d901c0c00c04200c3d520780c907a003540c08441401401001006070380d9000c610307024890300180000c110740c5d44000c007408003842002c406600d40c0c1d0700c110042c401c2c40030002d20900229910003800c440f0b2042d05101c02cada02d0b68540300080001a01d0b80041c403900c0e00544149411443e20703850046d64805a90000d021600040801c480c2030b807104004118924041400382c5101c007895008109a900301400b0a40312112459003895510601c0c10f13101d0700080810040340d104c4504c0d0042c813409611a50000c00c02403c10344001107034450358484181c040c2d080b8a8510008181c0300003186032601e003c0c010360301a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 686550791 1250 686549541 686549581
    0x405030c010c0f080307090e150604140409210210050f0105150928050402040503190f0b070f080c0a0804020f0102011e020a260606071103030a1814030303 68
    0x10042061200006424102070350184400703807605007c3c0c5007005a5a5240e4030010b0400360362056407070202d2116110b400440e1705440001070708039030b922144000308000e400d0042d001042404495042a00d1074880082c00740c101e03009600340c482d6114000040c0040c1c86003591020746107000440100304a1070301583c10102c02c602800054101401500080c0da805641c0c9440b0b120402c03140c512108048500c41100050302040300c0071801d080c10100407030b0b5100c1d0492600c03002441d1034034445041c0a90300d5541032156500a840081030310b81018001c1c5440b403a40b52420114540f07001040308642068241c07401c2140c1c941c2c0d0003d540d5219000c000f00e0818a40b840350540d56254058003004004c3c0349103158511803450b015039514881d0800030010080413541a601000d0100c00c1d01e80c400084513541e4011a00301c91264840c3d038181401948103010541040c0d26110010301c440340583c029035040141802511103422040d0381e0209020384004c0700c8500c44d41604200b0014222001d000e90103043d031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 686552041 1250 686550791 686550803
    0x61e0c1630020f1c060507172403030d022203050d1d030a0506090d050a32030106020a0605010803041214030912030408010c020d0806040b030a0501050a1a04020405030c010c 76
    0x21400e12022402148004010b5841c03118545000c04c1030121030700545410209038580041e145802206190b00710a0103080211031540d200c5010800710007542e644a2000c0004054944d5800b851003500c1c02588013a0400d119003214400c0c80a0540d41c5882c110122500100038000d645a540340465042c52407128443c2c503480c2091088109480402000380031910886c02807103103080c24180c940c6400324804079401044010070410140076880030408980d020000c40d0000720618201c14104a41c00300f100074868404084000a0070940c002020a51107006141c200810307620b81c10f03000d48910540c0207034010342030308071188000544c90a404110915052082e6820050a00000350805180c050005559440407400303100c1548280b150404400072800144424680001c1c05031000074010140d521450307942c40320b140e040d00c0070300c8001c0c40c13683d010b4001c0260f40741c40109000107140300c03205214a0503488918003898142842180d05507040100201520300c022001161540102c181c1110b00b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 686553291 1250 686552041 686552059
    0x60e0a050f130501080a141212040302120331120e06130b0a1214130201030e070e07141218070b0c0105070f0c0b010302061e0c163002 59
    0x4550702c01d104090280107002c001e801c0030101c0b130901c1a92241d104020040da038016400d862050181c180c00c407100c1e200c148072620456a00c1d0704051341440500042c402503100000104020441d041b078903010400203290400080d194890300e10307500c0e811154402045207801080c00c100c0640079111400d80c808000700f00a10302254014100400e10719684039580a901c0480e4055950750072079404121001103850070050900550409040d5000c0a0504100300c2c0c5544102800d591013030b04601403042040d421503840d190344407202c84096800312a01000252100c92001c804210f000031500e21383d041d41880070740341c0c45003100364600f892211012241c0d44240500025000e6500015264001a11000040c4d91800300009060b980d01c4031400010000d124903004c0000b0741005105056a4050714001c0d1210703815440804070b182140b0750400d10304808030b01c0c800b24a10010710800c1b2001c21074400e0b41502d613501400c0c4402c0b04400c2400c1108003d103d012104008503000588041d030000704200c031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 686554541 1250 686553291 686553319
    0x1709060405120d17091002070816111504030c090c051306050301031a0424061a0d1109011d01030f050a020c06010e1303080a0603020a0e0a0501060e0a050f 68
    0x200300e82c0703500e4940b0329030010400c4080b02c5402c500b03003030983d881c006403c0e0454507200301d2580e11650002110000940c1c04036001c810300026600f580c404003184141c1580c41d008905224203540412200da92044000b954005004100c0c0c20654040729800318800001e6410643c880000e02000c0d00354404102c0e09000154401c510200307038000500303607501e50f50788d6075045051078481400070a8620400030050f0041c403000941c580c0c05015141a82c040c8890f20410040c40900508a45c0d80301d4140060780e0a4000c801103007050007803500608202041121030018540220780d0b00403a4142804a0710404100f010010409140d08221105140025055406d10340e81c4086079400c2c0c07042000d1903130108900c401ca40b400c02c0342c43d000d000c0103480030381c862501e514207134102200050010100300110303000c685405020b800140c0650340c001c110244640d290110028464001c54014001900b410000240c550040d40c080b82c06590281019054500700000d000c4030084546490742c0094650315461 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 686555791 1250 686554541 686554549
    0xc0206070c1d06010906050f160c09142d0907030602040b0a02010e060127060f030302010b3d020c10030204050a0b0906070209060a03050307050c1c1709060405 70
    0x140141c00d241d0b010012014121403820035000009200c0b034103000501d00180300103500700e0160754540d085c0822981d9510000c0402c403012110b4000020052100c47e0004203400d20b0a4005034441f4008810110761540c590504442300403081c1240e84e110552405c0d00340000d07190f020402d80c424101000c031226560349565990880c0c1c02944003001018001c605031540d43c0e820f003d000d01c008030050040541d54141300c00301d40c41d20082000403201c048020802e0a00c0c40894001ca0000e048c0c4400c46100c065590030064007038422000102d21801e01c038180440c84402c80c0c1c00103141610f69000318202400b00ca81201c021000c0c000e560b909600c14441c0c116140d54580d21704410402d21581c001d41c0b501c3c94041400020440b50700060101c003410310241c0d803580c544e102a589036030f03011112103205480303210104540071101d41000d005404001140b406205001511170801035040d1107130140803141e410404c240e56086040200032852085502002c1c9128202405001800038081450655600001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 686557041 1250 686555791 686555813
    0xb04050d1406091f1a040f0608060901090201090b04060f0f03020d0c09030312020c03091009030506130c06050306091501032706050115050d05070215090a020301110c030a0c020607 79
    0x100342c0300d5110800300342c1c10482c0307894000c03000d0200013003e11011100310001d503d1005042c43d800d0241d80e441c030200340803800340c0c0c000000800300e00042e140c0c181024091035001c0c20081c8003ea0100b400714800082a034110001c9030102d8055540ba0086803081c3c400c104c1e14010030101660400d6000d106020090f20107210309950803009440b1214150300d10710300640700e10001c00c4000021407040c0501b01d428440070044901046040b030f4071603540f05103c50306480022542c6c01c081c000d440380200304036031540000f018052080c000c0b02450a5036039202c0742101c0030300c401c5903c80c0e00306070610f000c9600b6a058008030490701e0030504001c50034882400c0e60300e010352002d002a01c0d07001400400401881683d21503039000d410441035403031981286401c00b0b031251040591140300d055840d000a200f40d4800d0080a95181c5503c0d524171403400c289000c0c5030b0b1403403c0c01059120b0b500e00201386d205041c082007241d5201f48108051801c00c42065000e44844182e420240d0708264204842400030b103207400a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 686558291 1250 686557041 686557051
    0x602030906010f030c23150c060a05130f210504080c04050411010507061d0c09150102060415060f14090f04020109121103060a20070803010b1b1b0310060b04050d1406 73
    0x34031f07901c900208100c14a0100e010301103601c2c40c3e1030b0030207019001d03403840400301d5000e4108003091010481c6140c030305292030313780201f00e0550340c204200380d1100c0e81c040000e108841c001011100702012907010030045440c02c1e01e0041c1070407100c0c032110321554041e02c003810070309004400010300d040c080548030446080c5401210000e07042020052242d2078034025907a00480d5002028038001041c40020b565810050005443c0d2108081e0b80d00150301030b600510003921441b1070031603400741e0314848601c585a00801403446400c0c0c40740042c640d48890410700784101c2d016910100c0203450894040c0c00c8407000e81040e9030a240210002e0125202001410b0083d00c01180004442e41100c5004010074103110810750841d10400c01b80000c1046001500e06491a004d5010366895000300c5952121010b070256000c14061150501110240c2050b003410f0401c0560503103034690b24402284049031502c1c02500300343c2e4404d0106000c503050001303450201c07503c503030758200d000c1d503100c8440d41ca85038040325 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 686559541 1250 686558291 686558329
    0x2090f0105011403060d0f080c0d021e030307091712040f05040e030a0203030402010503280501060807030c021903140c0604020411090d060c0e06070602030906010f030c23 75
    0x10051543c1c0102c403c100d10301c075100c1c1e880c02c0d0f0500d08000307174811100382005170100c888001401d040c88103002c01ca0b640d01da1354104440c4000040d501c06034440360203140b1988002c1180810780f0329591701004584c45040326070340d900da0260a1411b80031449003103005015262007403d0501c290000c0d850000c101804000da1128140781c41d1600304002e0b20b45405544803e60420b0104000703594001094940017942400c4c003a840b42c0d030741841c50020085107050345400700141c8400d1092503110340d00050503074446544505e41303681c8180c1c041e0f0a40301c2400117100140c7c041c2002e008901c441e81d1134000d1151107072504540081c10303d103452015410100701d6030015041903041c07008602d058030940032001e5200d445142400091000115482c121150281240d5110f00d51001c0c000c0c45201c0200045a00130324064507101c1c141010802034000b100c0788581841043c00101d8642c481c0c030040401c6903413103603c483ca86c3c0d081c0400e5025180340c04500824202c004507002440366205042014920b4a02c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 686560791 1250 686559541 686559571
    0x90f060108042a080f070302060417160909201513080304150e0a05090606030a06030803151c02031f020f0706020a1b0825050706030912030c02100b04090209 69
    0x1c03841900b84100c02c844c84000e031b407280100700010703100c55080d90100c80d84038003038082c1c00d04121202c0f0308040c400c40000703c011107020804200b40c903240e84480066401241d54200c100c40e480440c0e4056080b04003410750080c955030b2150f00c0340046100500001100c004040789181d42c4280b0180346030080c1c0c0010290410700f00303001006952100d10b80b10482c1d42100d8100d006071030719000c80c8040d080680528000c0e00b0000014404c1b05940d003010000719403181400e40c0d03a107055007044145141e08480248140300c010440d40e0f907404942c2410790116001400340c40e842070481290707034401d001102c0944400e5001e00c962480c8003604009060468010b00f07000d0383c0c44c50300ca48020010130300700c009124100e103503a00a0f0007050f414000da400b0b42060000840081c220080a16010079605400034a2481181b078080361044c0c0c140c000c1d010151081d007502130b080801c05010f4043c6c440c41e110384801030340001504894509039400012404401400c000b9205085801117443c9200440e41c0d11506c0041c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 686562041 1250 686560791 686560799
    0x50f0a08041e05090402010f051e0d0b030105040503090603041b08010c0f020607020a03140f04140306070507050c15042301020601080c0109120206041806030b06090f060108042a 78
    0x90b401c400803290490302d11001e0a041800084040d180500007a04005140d0062401e29010781c08480c40c1170140c60940b4602590382030b28030459030180d082d40c1003289c2401e54a18142c10140106d5004a5110014608200c80c040a011494100070001d8902d00d2030722054041c101207489201020306292000031551621321480076040008000c0c0510031540314804004445038080f0b94890b02070391510340741c0014039034001800d14070b004003102c41d0070001001500150452400011080e926410760590345180d80385030b42a161f034025280e004c0d11235040300c0040b81e1341d498601d202d9141001280d050500701038a55014030007110014045408101c403038000c684881d81c04101c00341c014020f41000301090684940024803002181c490841c50a030450302002c11545c984080d00c0181c011443c0344d0094088000b0081c01502c00d610059a10240c0c66021130300b00d0400c60b07201c030b1003071001042d00804c503128100115005400204181e8402c004442ca01c2420690342e1034000d60f0511041707106d0202418 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 686563291 1250 686562041 686562059
    0x150b0a06110606010e010c0b0405120d090203010c0215010902090a0902030406090b0c030c39060f0f061804030e0a140f031b150903010f0504031b1707050f0a0804 71
    0x400f400c914140071820811510903030340045007120440d44075128640e80e440e0f62a000340350002c2c610b110500355030b0100d01d0601c1c0300000da12810780240200c00034468040c201c242a43c6441e1145045444068004014843c2c0c1550750014040d1200c00381807600d103265500305c048100d0f0010303a000c8984540300c40c1d03034505001c2c6007001c003904480b032602010b185060501e501c40302480342015004407018800058245070142815803020403651601030984a060099611303100c02040341c90300c04440e102c1001c2403000003034603560352140d40c001d40740ea0b00e8039400904285000390020000c45c10000710f00c14454003034650b103000c10003c101c1202510081c0c8070483c100a202119404580d00a5000420b0440c401001e5075145803009000d4800001c3c007503035001e001d06141714500d9100c1d010760038000560f03030f0003039103521040c41103000341ea071486544401044022800720704040606585214602000e10400500003004c02c54480c07002c5452640d200441e4506242d0415015100a04042410801062 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 686564541 1250 686563291 686563303
    0xa06090f11090126010b09070504260309090619090e0d1b0f02010c0b150f030d020c060a030906050f1b0406021b060f1207030b0a12150b0a0611 63
    0x3104580b503215030341c1400140200c0a106201195610180b40d0f03a040c070f218003c0d400181c1604014240e02e0385ca15020f04082e19030750003407080b0041c0c0290681815031402600d200f0b1090201498080c601d02040300d03080120214014120690298811013100b01d00d4248180c00c40042183d402c0109000003d84e640724184440f055005050040507400062000c0702c1554510741d451b80308021005002c07860004a801c00101e5000030f103400307000c009001c4102c1d0034501c11803040108417030308610340222005150326588400103034409603000ca0751215803854800d028043e43c0c00a4600010554065110441651020b40300448509640ca049c007100419455241400c50304015007113150a00c0d1090080d6140405641c1681005100e07210354259500c0c2c00032034202010284040b92250f00164040801002c143d1348000840e150542940250904580810454440b031481640c580c02d91380740c0e501c128581d0650f1140b0b19641e20200c0149175101503040000e800306650b0303a40c0c0700c070309402c143d46044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 686565791 1250 686564541 686564573
    0xd02030709242003030a0e0c10081b09060a02060a1109060d0e0c0402040b070510110f031302041b0206090721020a1d011a0405060301090b030f120a090906080303040201110a06090f 79
    0xf250354a000301c5981040c0002c5d0044e007401c001cbc0005c0c4000020995090040340c2c1101d6029100069400c11747d54005109800f84214a001f008102c1030410b4002240c461034080642160003401540c8100059034001201300300d0200c1030300d80d812480b00000301207920035002002070031004601e16050020400002e000d405000b0b0040188180c0c0000c0d1034228040d12481d42191900040012840c820b6030860b0010254007030703c2808494041030904e22240010300e02c4000510401d00010b0085000040140480305420b0142c09000c1d9100ba1881c2e04601855023030741c10000d10b40c00021091100c0c0c032001c907085200504000a5414509501201c82300c05403810248a000d0006200c0c42c0d5510040740c4c11a10035040001d4841d0b15503001c0f07424540c15440b0a00c0b1402000b1020001001000081598006541e1500915519035010004072092030182840703981c001c1c00010010b5004640005884a060007110480149581d4910954580100171100104c0441200d03042000101c8041198 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 686567041 1250 686565791 686565799
    0x90b0301051c05120d020d0b041118010203040806071e02030f0d0209040914011a1c03050c1219170f070305060a030501020d02030709242003030a0e0c 66
    0x15525040010780b003044610201c160211a05507032208101d0208029010f280c80914629103400c40c441654009410072014881e620b400c05424906e280780510480b0100ad121306280c7d410000a1080400811840290241544020130021030b80f1b12080003020b224003204c1c0c1d640201d80250f03401c08040300f82e00c2011001075500074040c2c00400400f0006540070880a007100688450300c00000601510b8041c10103403040c41307140d001d503001000640101c949044481005020402c0603007d000c2d400d803460002c1180d41e6407940303130700700040d201d030000304000031a02003156203594880c0c82e9581c00340d01c98509111802402c206680010b500040407c41da00d0060030140e14600e040d2100e001c9019008090300105a600c0e4001299940c651040701c001e1034000c0000c54a8a1b001c811480c02940140e030b00d600850048000003525030380c00082c4140680d402103810b203040c1c00360700003664003480a1650100c0042d1a941c010b02590080003e184503100a1001141c6070303145c45001d500b05070102d0b40060203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 686568291 1250 686567041 686567047
    0x60612070b0a03050a09121107060e09041103120d0605010207060c330e1e030f12151f030e01020c1911090705070c0f051806010e120d090b 61
    0x15006045003500d0b60700803141400328242d40e0312142e403401004400801011100c2008603140c555911040d4105032025001c219201251184015540e001101c00d407130381e01100c000002000626548810400810017034110340080114000042c02030b04210703d101c94081e40c0e03403420841580c2c1000680c0040c1403e040103a148805600c80e400e04002e114400c88504070f500300442e45c3c01c407582c640e40004044124081004035074002c061a03c995000c20105d0440041030401d1110040c00300464004503601002d0614040e10320300350b082c041200800802c1c500f070700c1d401808080c0d100c451280f0140c5131a079800c41c008442076030018007120602e42e08250f4030380c4180a8882090000100a50b042e038010f00500510301240c43c04060000032100103075086600c807000c1c08202a000b8015000d02441160340e090b00c55111085590005c84030b1182640c010707002c0c844002e50781d141c00c481640050043c03400450003401e21300881d20380d000c0c00c03a08080c41e500401071001c2d125805080071000c3c09280c8000d600e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 686569541 1250 686568291 686568299
    0x50f09070302041e0204032607022115090c01020106080c011704060b030a0807020103150311060724060602070911031302030a020d030e01031a0f040e03160321090230030c06061207 79
    0x585e981421256a09200c1e0043c010034140340c0400c9800b9812520001220cc1450036075000350301d4402410300c840c059820808045030300702c0c0103c0c90021401c4103a660032640d42c4c22106008a803900076109881c0c00344d030b90001c009551010312a600d0814060030a090f40c07881684001411200d405500c6411417144c85024800a06800392040100e00c04566241d220002070a21030040d000503540001090090104c00c2011000383c0c00107002c5440b40c0c2c082c0c858081d03540c0174001c240d90420003032100a140c1080001c4400100c08098184240042c0c101ea1255115502090002040755000c1c6c000c90903400c1c50010a40e8940201c40c1510b0009004041281c1131401140020701c4807044148502c3e220840c0000f51102082503070305401d0040003d40c07214840703040180c00301c00d071040c11031910b015868400440c41c1090103003500165024101c03218032440030f104800c0f44078400c903002c6030410300342c00d4103107a03600c0c10030192084128444c0980070a050600c100100c40d402c00000542507042000100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 686570791 1250 686569541 686569549
    0x15020303100b07211812260d0c03060305100f0f140105040c1e12050f090d0c031e051201080105010e040609110907080a050f09070302041e020403260702 67
    0x540313a9618a000b42d00c120072464240c8140c010079058484c0e80c42d14040026280d9100103034003074940d0040d84400d6900e290300d128410726108804885074004401c21809000c1030155002c80c0720502c081c98000b810523201d503246414690311a0003001201d4561740c043d06079500300d1180e6603e001a014040051203406107800c2034005051141a1040f5030381e50160500c01d015510001443c640242900403c0107170750340c0605a0100b6003d0040d009113002c1c0010340e000d45000340f007401401d0000040403810988101181d0380c0031101400c50420031096a144d128190000020503e5101601d503581c86001c509550115068142d10420b296810440104588600781c4492504076030040c50210784000700e41800300c400c02c2885c80703a540100c070180400241e03550011103e40140755202c414442a260b070703100c0c94081c00d01a80c242440d034000b040d003000185440d40c444081e0100e103040c0ca110080110410340c0483c0c101e584207840385c08054003502c1903030110f05e0b810b5420100c5041d0301800d042a64002c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 686572041 1250 686570791 686570813
    0x8010605130506041401030c080d031a0d020102010e0f030405040b1507020112180605090d020105040206042702030108030c0d050307050715022703011406032515020303100b07 77
    0x80703107040d550b9802091a544958103d248404103031046007100e0b5969142c0345c0c11200851060072030601682005599141c407074021600c0030b602e8150007000c1e030100d00003040075291460400b00d055660381e41900c034140406020107140c0c000c040e4044d5440c2d904d032009010960703c06256581c861102d41c1120810642400140e9401c0c0c0e4082c640000e901d02070b031003800002c06030000b040c06001000d011480400200346c20240c4944000415901c20a0700a40181d080e90030640d4020740c000418803051094518403e40f0010300c00c5a03074058031101610340401d00803644283c000010a400001d081c0020318000c008801d08801c0034030b0701505c0c40c80c0c40c002c000c02da4021484020300d1041103518980031500305805072501441000b80d41180a448100c0751048415454680d5001e03508100d40c000e8001e071075000c0075119610142c05000901450717064007032111840c0c542c10100345604000032400e8a0028098485401d140d00250394908004a86030701042c200d40c484005c01c1001c01440002800303094403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 686573291 1250 686572041 686572069
    0x12160e150a0e03032118010213140415120b01081501050409080702061b060105031f09030201091406041e051c02071706060f0402090915030304050909010f0608010605 73
    0x2000c0d50309451440007900794445e140d12035100d030a0f10a04600588020603500c1d004006005440a1048880442c94241d0040004d015440c95078541c0402c2078580840b441410719900800010b000c1c2c0410280c115910800d0f0011036244000ba4054410040300e00001c0c0e02410b000380052000402034442115002d205001710742c0126124456042000651000e6810403940140129100d2415040030b014101c0584000600c500c19040006540c2c1408184e0702c00c0c80285c0c810241e41d084055884030098200c040f01201150350b200c510401040c4440c0700086c0d1140c0460240031541814140f00d20b0085403d1340d41c81003030314595001e10006a000a210804c40d00c11018094180d032015820b034180382c81c9911121103800c814603204864640415124031491040b5142d1500d40d25410074003040b4091102020b03000380316600400c0700104c4400540e0f0385010f0080c201c1e4602502d40380030070304800085c0c4d00d1071810b80d1240c0030110b511549004110140ca034410013088000e140c000016004140d2800c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 686574541 1250 686573291 686573297
    0xc02040c022d030409020c0619060510030e0304080109150e010b0a29040902040614040f0302131b050309010c0e03121c060305030405011701050604030305030c12160e150a 75
    0x1500b448000b010300659004001c040c004546800390803110030344440080f070301107060544845c000001c41e10a4416503064410203088610850044041a0018a94168907c42500c4207200000300c5401c00d00441e083c0512403450b030300f250072040c1d1011003a242c040ca40455140d0400154480d6900e5042c40d0340c0444422820f65010a2100d070015a800700c000c09071b00320305000000e404210900ca5400500c00c0382d8841c0e6882c2e41e0144060b00203020b81c00742e800f174081c9403980c0340020005803030100c4805e00c0240c402400000c0d9240c144044481964003a01c0d0180030900c0441080702c008400c2c41000741e00304480c180301d1070000c02c14000035207810418040b0014403901003103d07207107a0041c06941d50310b020071400410001b620303420b085540343c000344103480c0061003c00b001c030748600c05005400d04884010b420340c1d05050540d6004c0e2940d0b0001064900100f00c01d110602c080701200c00e03080e00500204550032003005030320700c0c0201400c000d00041e6004140101e00102c104c1c5091044503e0f1070640d00d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 686575791 1250 686574541 686574613
    0x603080729220c0b1c021303030e030304090c030605091303080604020d09080f032205070303030507030f1b0f02030901020601030212120c01020a080a2703090f060c02040c02 76
    0x406602c400e00d010354041d1041d8101c08010072152400f8005103804031503081a400540d0400080505034804c03001111030b00b2010b40c44c2000081d000e0108803014800081c2a03a003401c0e11440321004482246584100007070f01c1d200c040020f41880d420301900420f05c5203000708071400c2524044c10103040075104034003869001030030035240e25442e0302c001002917000d00145e5648001000071051900140da001d035424a440700210011410700344905d404e954440050080a469605c1c00e0700140401014542071688818030856001d405100d100d1581b9030380318403140001c040c0e080003840784101031401c07001d55104100b001216031b000941581165030444220300400384105003d0b01b0300e11903200c0c0c12020440825040a00c3d001034000e08080d030001d664102540d07480a0b00b540076038140d4203100002c48240d10003005014080c90903078551a0003400c0c01d0019039618240c1525642c2030380d2210340094040040d4108615040c0030b100d10002c480c1c4000c16046a60381c0d10958003083c00000c42080074082 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 686577041 1250 686575791 686575831
    0x6011d030c031911010c030c030c05121c05010503030f0702041a040e030d1524020f03040b0a03050109061409090f160e0604050f070f0c060603080729 66
    0x81210041010001d01070354602041c45080c8003903900010804c8604a803040030440e0507500c502c8440e0304a5425558000021844c0c0c2c0782900c46140303a95082d68580500002490300740040d40c01440c040342c45812a990305640a13160340704031201030700580d200b90001c1200c40d0801f0712140c20b0b50400e5404075030002380304d0040424008410b154031105a04541402118258200c011002d015032011600d41070005a00c004800700b90402207004004001c1035031892082c10000d60001c006401d6030314011102c5034558210b20314510380056014002503440005c4000600ea0301d401524018a94110140040390a00c1055401e181051440d10300401200c000558507640030884030348400021b0040c2c0c0d00c000c01c5107481e5030620440c0d0040d902002c0310b12012640c1401e02c0e00c40d06202d00c24849500540e52079107a0100c880e0741c2c200240104000791551050046442031049a0007188a090415a10303030191500d60f0041d868a403803040407450051502c01c883d11818203c9a1160601030b25050707518103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 686578291 1250 686577041 686577043
    0x5060a140d052d010504050303070540050303180105090118090c08010501020f0601092d060e100e060904170304050105042f090a0e0d020c0103110306011d03 69
    0x1110801511070700c1003001014910b10350740c10340c403054122049402601d1045071040c901780d40d020b5074000d2199000704009501d151055000d8070b4070083da07440040d0200600801c260192440c00c0c0880c60161241c09001041d00400d1100c03c0104001d4015600300084640130b14841c580440310f50317043c4400003c42c0c16260703100e03c07510803041510300c20302500146c80e500300c070f00109401050040031884500021400f5030000501d40c1039100b81900500441c1c0c20091210080c096100b00c290003000c4150708410042180d40034906170424884002a11524100300f407007580170040d03c80148050140420f000c0d00d4070a100e0541e124005a844242070b07102c45c030b01102194400704400902c43c0000c4140b0042140640020f401907004151120b19221028842d55010030001c0b01ea09840d0303034806000e042070802d41440c0b039010240e280009240010b0941e46030411000420410043c0c0102d5043c8030a581c1510036181c603c140100c80700c0c15480c0440011303040008590340c1c2565001d0031010310319150343c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 686579541 1250 686578291 686578309
    0x32b090b04090c1b05070501031505210c1302030a06140a061103070c030305090102070e240d0203031204121d2e09050a080115030b0403030623031005060a14 69
    0x40d4100c3e001c0c01213002e905003991640c0a501a0328002814050720320b005a002c0399030340c2c05640004021802c80c0fa0004c800f4030490312a0304c9151382d0350082030202401507460f0b400d00a40040c9080c0c0143c1d580c078244001074111512074100e90418080d00c40c02030115220907240800ba00c006003000c5080301401c42d449491405500001002c008070350030003100701031740107000d001005020303000c545226403240310385e03541c000c2b0840e4081d02500b001c075151103412001079004c0385040c1d0050284002d021194010900f164006030010500031410410b10040103980c0354614041070040c80e1450050841d124a103032030103402405640f280caa03100c0c420544031641140304c7c0282c80c2260b0b0b89041e8030031100c07014184903424804c03580300b140003800c001003226040c05070314074147e5655040c401050541e51400d2000c0310280c800e40c101a6258800306041c0412140304030540050301c5601030000e03030301c4109860f14103900d140c43d9809047c6028403065807a080e405c04c081c0c0d0913030f030741e8542c9541c1840b020540840c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 686580791 1250 686579541 686579567
    0x7050c010c0515040807050f120d09020f06160c08010b060306041a0a0e07020708120d020f130b0301141002060426040b07170a1b060209032b090b04090c 67
    0xb02d020f030b0500c420031052000511010b071280083e00c954480700103100e5241c568405030ba01044c8420031141540c04159407242c0764042c801400b001c0c0880f441c0c404100143c00c512030880c21f1420740d62990060140340c00d0710300d00801008000741f01d03402085020841900002e07041d80c3c0140d4a451810b901e1205001d008001001c0c054002d030744055544011445100c001d03035200c00540a80c0d440030035149404102c1020354940303050f0140c5410070480315800203601900d1102d01c1007105000100050000b03400010003800340301803164480d4101540e00e1050391035a1141031149041440a01c803040d00440d074243d116030400d0034824042180000e00404040c0c2d031160040f5030000050100c0d00b1551030000e07201c054003070341c18541d400380c68401c0a5241e120344a40b85021903c501e4814040102c004040c0709111701c104805401c2c0800e0380f010910301060f1111119a07454003094002790440040f007010000085860b1005456107440c21203565440765008809441d611440303881400c500070007040c4440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 686582041 1250 686580791 686580823
    0x10b07030c1b08300c0303042003190201020c120607030c030b121f091a090c0d0b061306060f030f0207020901080d02060f01050a0618090216020a0b07050c010c05 71
    0x60b0641c6a000d0310500d03031410130784400400c0d07045007082c010588041c1e4461002d000010b610715101c544400803184400d5804160032a240f0780d8041c01a20705008540349001c2c41d00310b41100010610000e820015007149403401144006c0780a02000000100070350000760900740040c2e11146840120044d1004001154008614003440d40d8001000203007080c009a84170070000c00020009403d0094400c040009810200580b6a40141304041003200390460054000c40b04c001c041c20001c030340c510741204810f4860040703000402c501402d20042100520741c80a40410026040190140c15000701010b240c04159076125020392004256049964072034004044945640c0c2d030b041226540c5005035085001402448081003001c800e120782181a68002000301541504201d0704560710ba40101c10388100380500071000510b2040781c80280070200984400340440b068600500207082c1141d40040320324032042040b01c01146001c112401182004d2801c0c08585150b070801038501a0200c0510402c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 686583291 1250 686582041 686582053
    0xb0a1113030308091006180509150f0c04090c08070e0102010c2a02040e0127050a030e010314010e10051909020c03040308041806090c0801050402030c1e09010305010b07030c1b08 78
    0x10a1f022140c403444d01102119052107295906d407501c9484200e413030710032040c080b00036022840384041300404036031185041c0000c0b42000d50710074040064440d0a40c41ea000b0501c9a0f041c000e240350b10071520a00d0310780a000034400a4a40c100041c5103540b01e10b0704200301508050302c10202d080c442002c01f40c444d002001400815000104503008085503880004c414003101c034828441806814908495030304040a001c002e105a181550307904889503607241015950040b2000019150352094043c2c01440000b01c091702d0030801c0340e0b01408044d003001e407241d082d01c2440d41840014800c1d03407081d100d000001580b030307d01c1a00c07194551700480c1c1000f80034030404070340414811055000032610341941c032010700c4181d583e040d0040071541c840e400000061025001071010741059001036400070003103241185050070030140d4a0540058640d441400303000042c1040340d660303060140f00d000d89940722045203080c01c0ba80d4084c11420400400401d2000900394402e482c100904060008115003401e44070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 686584541 1250 686583291 686583299
    0x1021b01020a051b040b010819091e03030c0e060c070915080d023702100e0a031a010905010b180a0e18070b090f0105180d0b0a1113030308091006 64
    0x2c2054041d800b005d0085103411324001456205060440c0203140d002034042540c0000812000030300032a038401d079441409400710b1030f0342c800c0c55640300d034001d4000ea80010313000280c02c100900000031400c1c0a84075050134490000100360100300300c4112000204001211070070100d983c10611404d9001809a0164240b0300c1c062540105054134203003c80080009840c2000c0b6145031503901000b06e0700c1aa0107086c12f60001414241124051400d060a02806501e4180005240441c2039001126401d65040f980c0720740d13440707400c4014003401080405020540c1020103500d8140154a00081030307040c0300c04d042c407460f12481c220401900003440445c4481c9032085241901d11544910030250b4800d12000181400f5140e0641e02881c600800e11200210b04100448464002c01c0a80c80e1100340e42501c583c0c1550b03049402c2c24024810340381c050340d0f80751008240c0d045610f00340b00c646003a542084000c00b03001b050700901007900e515040107401078a581105174503014604144a03d0701380b4151002c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 686585791 1250 686584541 686584573
    0x203070b030f16032007030c08040b0a0210050f040b040f05070b04050f040e190615171903050d050403021905010b0f0612010311130c0504061b0201021b01020a05 71
    0x64802d801c40307483c20285021020040f0129001d42d1042c0c03604803010240d1484000d14040100390481c000d281a03403140189440721400c03640580d024881074140010300c40d8800390103100c282c01004111800700501d280090010f052614010070085c40c401c1c11a0006040041d800c1d00c2c1c8a085403c002211081a01d07034101d18440e5020740140342c801c0c0441d88083c6010b10b4a80241c45c9010035440180c115a80444565000c040799030b50200c410a071111071000d50303a845071087c00001c0c0120071102e649146107440c110308040c2d072440040d0b0240036000900c004250048121011000d00e0350b400210f030395076401d040b41001190003210050661b0059400240302054000c1c8103046011541c00c00740001d08401c10a5a00c1950b9458540c18a55801080030841c0f051501c0350040c000340c074070700c401e40301801b0502c11503c03041c440101142d00410140641039005036800c851610b1451302c20b40c00c2e03101d900003130760707860702000c8404803828079482e5080d1310303407003400349148540d8010101d606180b00a038a503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 686587041 1250 686585791 686585821
    0x10f05220501090504151b030203070e150301030605160f051c0c02060403031a030c0402070609080706021207050c060f090708030a050319060303090e04050a0c08030909010b13120203070b03 83
    0x90310b038a1800300c032030700318046103100c7c004403101103030602c07600d5145180003035001c0c0d04000e0042050140c030302904181a160915078801c40340c211042d1540e290304610b0032200303d610180003021680c0300160041002c0341c1101c1c65040040741820701e0f54945074040a00c184c8002d4052160340b1003810312140301d09568000803200d0195200e0785007444150104c101c000b0004c9a241a01a4140c0c0b0000f85050356081690007444464007030f80d00486c40c0c0030107451390700311940464000c40e200c7d0350005a00c00070604104c2c3d241c2d080810b03454242d29104150503d81e40e16103018140034030080c1c4560101d11012002c2081100921458050700c0d11029049806861030300121800d01c041100c0c0a580d201c1540130f842200e059a90685800c200c840c181034002c0450100100212014070803000e0000115100c0c16144c001001e000000355611140302003031155800c4107920080b014017052005080480c050400d007415a1603035407001154a01500001c2d107400003651024810340c2c800410b01ca002a02000c41c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 686588291 1250 686587041 686587043
    0xd0c020f010b0a050f0a03170a121109011b06180303050a050106050f030c04050901090e0c030a0314090a03020405100312050a09060302090102010b040c090603060608010f05220501090504 82
    0xd036010303019003400c0c06080c1d400040322180e000301c050030207002d945071640080400d01005415229a29280c0d51400003005a00042c3c030320506021820101e1558090031880e124400c5e01c501344902c4020041061040c05081e844a040c05800200002741d24040998a0f140c1e64002c0410f01540724899200d0540f07000c1d0b4202036000030b0400000a081901e503024440c101c807101e40d070700c40c0f410303181440208a50304064a2015510020000010a41d0792407a036079000c0c00c042030300001d6242100015500d88001c00c0c42c00e501030741001c060b880210390008411555240c5079084266544a0300000400e850481d810003540249000280f01e00c001800c1005401d99110300f500c111201000d01040d5080d001d20341c14030001841040c42404440e02c25005003400c02810300000c924000c60100207010b6418580c50303040003401c841010003c4aa140c0a80b00041c807603428100c1c601c0d410b05041030091041030041074043c0050080311400c0c2050300082c1d08901e045a08200700da540c5415a1130054002030318 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 686589541 1250 686588291 686588293
    0x5070c020a1e0e04080d09031701081501230121060306052a0304023d0f0504031106070512040305070e0a020c0a060b030309061206090c092209080d0c02 67
    0x180031030043c100304400c43c00345402c06901420511002c21342001b07480380100441c1040400403d8032000403100c01800e018200e00c2000e080003912459508408140c140d00c03844131003036007094800d28070740072211b4041054002c2ca040350504201440003041080c40508201c4454178164000082c032100d90320850181108003201810f6407a125040c1d04c040c90903047d00c1c26038800420104005140a8140100003481c0c10203500300780845140c0100d0a01a031849046441032000100c01925481409804400070f5410f086040a095807649040d59000300b0106009000000750182131100402c0103080604c400003240e642c8a84a141146e02c901040c82240f804a81c080d000c141c4031242e500139a0b0502d20000001c0195211944403080035001000c0c0e17041d014082008210b88545481d001403090001c045640350041c20218103210325090014407c500b15041030000810b00e581d00d00c03001c880c00000480d8110402450301e42d0000900031110020910140040d03c4074400325160820400400350f60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 686590791 1250 686589541 686589599
    0x210c030c230604021807021207021801030b0a0516200f0d0207090506010206070c02091e100e15090403050310090c030f1a060406030e010e010509060103020901120b010905070c020a 79
    0xb6607600d44e41700c81500c443c0056000014204a00b00c2a1703c080c0607428002085558044c41d5400310590800083e04203441824485040140d441218098150844c00104000d13004500c9600014070004210a111a1b810005850364441d15010040340c08020014400d0792044101010040d588000c01e106a050143c02c2200240e0198000310b031161184849480394a85030a40b503003042074001009200c1c07842d000d680003110481a80c0d4113181446600c0104241c5210f508152070703443c2594006054202d9041e02e440003150544070001c455411640c141070039038980d29600e0300342e4000405504039168492501f1010340c9195032541250030004a810780c100180c0c078800b8012001c1e9400940480d410840401c8200b140747c2c0320750f220f00c0d413000980c000010551710b807824680c207440c0d060b1030b040110380c04080184250320b00003000034014404a00318030354000c0c450b9600913400c0c0051240c007024940d1b940c0003a05103409100d444c5041540148107600158480e0a0580200c403680718200c8210000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 686592041 1250 686590791 686590819
    0xf0f08060c0304080903010f0f020d0f0203011508060d0506090a0b0619051201060e100608162a020d030909050c0711041a060a050403210c030c23060402 67
    0x1162080c0608441d8040300e1031940c45031070f10701c41980000d201503003540d82e6a0359080000e52910078404c00d10388110300581d9400959140340700b81c41940d00e1010040e8410001004100c51050b40980c1444240c01c1403000f0740e640900061400c40309180107800c0380581003c010a030040400c0b0321080c1c03407107800005029240d0321f05210072040400701c0f404080011101c24042841c160481c00d4265005000210b012511102080350b4400152500e504403446100c082c000c203604186015071000540603100101e4540c942c00171318010f034581a10f59003130400994008002c114144e100e007210f80117008034481d035a440c40d00038881d00e100d104d031810039460400800c00d45650f140c05c4505450b041213659080c4840c0b8020840100411b00000d4030b04412295114080d403030388400740500f801180c665603115450350503c14219401611032518101c2d01c1c0254122040e00a40d910b08a96050318268160103a1494080301c40f054603501c05203c2d948600300380007903040c001450780c49684250341043c00050b00c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 686593291 1250 686592041 686592043
    0x70206011d130606050d0311010605060f04090203041a0c03060909160e1512030a0f031415010e19030c080703080415090e040b0411030a0816050f070f0f08 68
    0x881c0c045001003050011803a1400b411030440c2001d802001c001590ba0b9440380084c001104c560b82c00c030701255413000700c414851800c0c03041c00003d203001d0310014a0071106128450403803255004051000c9d5021010506000f0803822140c014040514083d034141404400c000d8585c100700c0312144240080000107402e242d012684030304403207441d5407410b6901d0410b1a00040d040c1d000b00004503000001b040001190741e42c40307015180020600c00740d170303960350584002080e0385101c111100a160610b500500c41249088030107a000215000a04540d50f41500490b230f071003a0a030039103a2002056a01e510820038038180041124805c510082d00d90396148102070711540240300140803080203100c100000354280140e82150300c4507140194035140c8880040407000030a07641640d0071a804020481004007903211802e407090110010318036038105541c0c0030b076248966040310318501c0408110400b00503080000350740c2800d1050039114100c0e100c0350f81909200486c49061003030030705017a0000d10420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 686594541 1250 686593291 686593319
    0xc0306040c0f1b140a061b0503040c03030f050909040803180a15050711030408010c0908150a0c1716030518062a030907062003070b0c0c030304060507020601 69
    0x1680c0701c0030312001d00815840d10944880ca0706071000001c9800c00b8805071001e005c80c0580d28862030f00051702c003154510203003007252400491014000c0800611000c1030f0465264011254146801641580c400000311828041d418450380c0140c1d0368428401041040c0c400f81d4030425504003440c0010110880d11513540c404500f01401d041001c0d4101501e0340c0303c0b508a43d50050840c18020b0085080160540c6580d00c85e501c001c005035501c80d0340030105a44500400c0041501c04010312503544903520080518001034201040c040c0c0d50129001000c4c026840781d07906e0004400c8a24980c41c20051501d000480c41c0066000245031000084c0d44403411100c8400490900000b0003440d500d040700b06180d0900c00c003004c01458134990300c8120100d04c3d1001035114203c19005800c2c0c203468004040c4c0082e50038080d0301c550840c550803c100300c00d000001e403240642c010000c045141c0b43c401d000d089130f1083d4001c001c1c650100200304414481c0680090f0702540e4184e00320b030a80c0e070b611518009600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 686595791 1250 686594541 686594567
    0x20a02030c01021b0d0201030b0d0804051c0203100b0102070b0a02010e24190f230f1902070c0f03051605030c1513080d12050a0e06130f0503030c0306040c 68
    0x480001d82440550030071005d0360130214818100040e820000c04005005614010350807503007401d00040500003811300d400034481d4102d081048084148a680c0081c0c3c0f1400301c40214074249585401610782a0320030080c0da80180355580403241d03607481c1400d00130302a002001e0701c20304a12a42c00030300c044000810600c02c4005400011041644480c0402c00c54078101c01d02c088081d949500188140310400c2c03003980010341c8148c0c4050503080c4006842c0c00140300040400504190743c00401003000a41c01c0056601020203200503036810310b51410640100d01900668100e89854901004204002400c0b10408803184541c0244c0b950303842c2010354a140c880d80150f006046080d4400000c02408040d040410001c51501021504c41841503d04807600c410540018880002c2d8445c0b12018411542c0010b1001402d1042c03500e40d000c525078402c4060903001c840c02031202c0754014030038400c0d98031450b25408070540355a401c020508400c2500103035041d5100f246001c070f03281409030081001d80840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 686597041 1250 686595791 686595823
    0x150c0e0d12050d0207060501090608060906160c0f060501031103061b1206010e1504170102070b06060318030406120606030209090a0b0402040306020313050d090b030604050c1603020a02030c0102 85
    0x90011002c5072250803100c9403040c07182d024408000003034401d000780c3e4044d00c2168000220b4929202c591442c151001d00210070741c1c1c100750280464030001000c51401100d050510316542840c1b40b4150a0880000d4000307024140341070008020000b0b420392101030840d0841c100c0f4010785a031a00b81c03d0021000203c95000c1c801005411640015925075a91000301414824201e130140c1c0080b80d5040521091080c4809000806001d401604c20359501c540042d14000c50504040740e840b42c03059038002d80302034890200840054515801803180542d8400a042a00e840719034405014000b9070017100b000007442e0401c0804100f81e80300f40b00359066501c000b04002440d8595002c20401000c4c021002600b240d020030020010400600085000301d0a503c1c82c07800003000c50030300d02c0c10103101500d1801000200384080000c55004000d40c1d0704804202c40000d003540300c813000301c1c4a40c4220b040742a603081030a072400041c190082880d00105000f6415144842400401241c983c0b000051001705 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 686598291 1250 686597041 686597063
    0x30a09030b0a020c010f090b1012080702060f0408010507140c100b030f0a0c030212010b090a0b012c0a06090b0a180f1205240a02030a09150c0e0d 64
    0x410100c592158000d800000010328024004c8140c60035507103080750032403445443d030b200c0308100412020b045074010741113250b030038800303040100d065000c0302c3e00381c0060100007003c40c10038255601e0746c1c221410b44460501055030f9603a1140c40d0f5000c0d007001c42d803c1c0c020800443c9104800d1341c100c012549209074038005491104005800200203103145030030300744c040c442e5080303030303406803004201c0210a18001c0164200c01407a510400c4040007440e1701400c5030380d05000e070742034880e1100e280c1c02d5000500500b010555507900070040740c0c140c40d0f10b041c15801201c0e0b1034051135030224804800401200660b1a01002034070f072082a1406101e80c884c0c207041107010403480c4480c0b44a1000c0c4003524451604603000750b55904d00c3c42c00040801d80040c524603400b02159810060208210184050788940000c20800e28507800700ca000030050002009035000400104840155446103800a9000090510290a48000c0b100070010801d03a100400c0c1c40400c00b021614101c910b94200551003080040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 686599541 1250 686598291 686598293
    0x3060b030a21020f01022106040603050d050307050f030a050121020a06050c0f061015030b101b0b0a0c02010b04200f27040606170412020307050a0b0711030a0903 71
    0x1502c4407080400204600030b251210f1101c1d0420300061000c07142c2c4100c5c0120003018900703850742d0202d001d01034030b10440c40c0c10010030008001149440d100c0c100e605100341c580c0d031030003400d40d0760b0b1158602c8490b01400c008204518404542d1180e0b060303820141404000c2240c07198a0034551b089408041d5002140100030020f4510a5000740380040302a01503030024201d904449181401c1540c00c01006c43c4c407420180080c0004204401866402e0301d8184020b06840300410100a18440808100000c98007120ba03120404800e03100b186070300440992640c607088000c8802080d0381482d480040d403c002e5000c080d8a45406180d8030800340904517101d81000000030a0a80d011407a800ca82c20000c0c0992800b503051034070031071703182c079141d1602e200c0d065034041c03c02c012210641c0103d024400e9000000c5c0b4240c80c1d107415958807650108080801e00d040c14030903407441c002c100d4000c050388210f8401e0410001c00055190092003a5114403191181680590703481c1e0049809400004400f140104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 686600791 1250 686599541 686599583
    0x601030206092b050c1e012607030c0e030109020310020c0c0913050106060908061501050415090e01121e1b0b21130222050405060103060b030a 63
    0xc2002c0c8014a4210b000240c0001c40d0442d0f00740b4202006481d020006090601c81d0620030350718540c408079102c50070300440c01c0e40d90440c0c00e00081a6410084903003820448020307044008606644034500d1030803c2d14100000402404115800074000780e610f01c020074243c14140106a11158014040c2c404060f180314078000070b4125203140f404510400000039841d0712a030b42c20310301070004014001d41c0054103052090030350300c0c55071145041000140003048207036804903043d42c0000200d40010302d4004000300403607030340c000d64001c811058400350700c441900340c00c441210704503802000c2c85403081c2c2ea11030300c0c0e480503000040058020040030340c281038a03104100039141414032805516070112101030807151880c3c000d41100f010700000003000042c031840d516994510740c0d100307142d854030b525110203e440444004070b00280102c090742d000140018010301091a13001c044071003048545404e0a1035681c0325001c1c0700940f10503103407901210503801e01041c5180c4480d000110740d20506c1c0c4591100c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 686602041 1250 686600791 686600797
    0x20f1909081005130c171203040b010b0c070e010b1c051e0a020d05070f1d030c1003020f0c0a02011b021516050f03030702010b03160b03270a1208090601030206 70
    0x1070f6801c4c0302244420300020315654208405040c80b400d003031005603001d558041c0b1346201c03500405404c0e002401004000354042d52040e065802e0202c9658032900e031001d05524021b16500300d488203070346c050000314030000c90b100903144c0c9615142c0800c814102840c0f00e001151816a1a03141d0281c43c00014010210f121031103907004580950018501500044640308458003035800c0d400050400151a034560f81c0420503940d5011213005074a41142c90f440020380d1041c4030790030b445c015020b1ba1000c00c04240281e0640b00d80c8004029840d640e4005040c4c03058850340c030301c4000c030b021420b58170308800c2403611440480404c44d4080c1003148031198030401007040350030040c5130f110100c880030801e000084080c00f420b217a10b60720200554407400c20b160081e0130346003451b510b036004e54012039004048010004600301102c0241d01c03c1b030382d65118582100200d47d400c51844000f1080c0b00c1000c3da40b8000080ca03031f110a8007a85820000714107030031080b08c501c0d009640c0d1a5050f0300000050015242580013 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 686603291 1250 686602041 686602051
    0x51b0402040308250c031b1508270f031b19020402090d0f0c030b130503090f12061e0109021c0b0319060203090c0405041e02010210020f1909081005 65
    0x64210745414a41e9440170b03011142d0011940038440784181c0c890000203c9a100146c03103e035801c0d0031002d1072171500070041c070710040c40e200920b20410700081000706094a00520703600032406560702c1c00300d00c00e0b07015a80e500c40b1a0742001e03204104102002d02e113022a0000c1c0c0185101c811104251050b001c003c0650807010525034000d51800c1c11b580000c11840090807550302c41c0c80c00a82d8507156040108007043c00400000a82d0302801e5010005440442198103a40080328500740b80d450040115071484142d04200341d00d0700c14182403101000501021418820001c0b0996900d82e032500558002d1303010304000440c088c1c7e03040000418aa54640081c622000d003d400c96408803401d0810740e010f05171010060354100e43c0001488a010414024550541000d0380c082c03040c1d060541d00c2020280c1d00086503000d42c5904000d40c0c0c11a0f03c2802003400030a00c01d1002e5440300014001001190301060007969601080c1417a89a014002c444003c2290075440142c1402c00300c50105074090100101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 686604541 1250 686603291 686603347
    0x180209090f150c120708071404120b101a1804060f05062d07020102060a0506060f1c021201050420250804080102090a060504030210050c1504051b0402040308 69
    0x50443c2d00c01c8100c00d013511400d407070b64450420b805e12010207840070500140b400008001004107104200e40c9030781c010a0300307511281c11840f035901d244034001030070045d03081109144162080181e0004007000a054400c03280c54040281180040c100001c0b19510300c80d0081a5840c010100110b2400c040600790903046900700d514441ca43c00603130005290769402c0d0341000c0030013180c814295681045419409502100208068100100001e103180a60404e00e0140075000031103441603d0852501410221000400c2d034484c5081590302d441c805090003040c6c011494504030003588080c400486010707503802041c032450136900500c09042c40090b540c011544000c030420000028038400c00400040030308000041c1c40350846008c100d0214880c1d4842c10401c80d042c801400903a4546100b40e031305800d075003801552803400200300703070800c4800c018030680711030f01d202048240074002c80c0d00b11140341c459043c1500f0101c0002084100c0c0614000540001b000384a4038121701c41a0600c418080d1181c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 686605791 1250 686604541 686604547
    0x302010c03170907060207060216140a1d01030b0f060108151503040b0f07090b0a03020310210314070b04060e0c03030706020a0206010b19031d01180209090f150c 71
    0x7090841c4010155481c880135070040d04108015075050003540c3c0501254800346c0f080728070440c544401ca010302c4c0100c06e108101d00d00080ca46a4840c4030348801084c4070001c2c41c00c0395903503c009200c1c0200900c4182c034100000740000390740c00c80a081940c42aa030503101c101c42c1d80c0314141c02c0112250b0500016820914100200d80c00e190014099441342d817048248662a107404010260524000f41012090285100e8284070b20724060f800d4904554184c900182c807580d13541d40754030362002039034468800005229290403a000c00761814541990180e01c4078001400d034650720007411301c105403014141c0c50280c00804d0005000780c002d00f41d040c051200315010040351400003801c6600c40c5504984076030780020b0028400390140b01c007130300420594a00f5401d1a1000c12034030548050000f0f080e080543c0e0710340c5003104490014600c4031040305400204076907a1082101e0440152040e0140c0c810b1000b0030005038030140006a03014a400040e028003941840b407081d915004002400c40ca44066081c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 686607041 1250 686605791 686605817
    0x1a1e070f0e2b0516120b0703110c0307020f0105090a09020d0f0509070806061818010f0615080f040c12150f1d01050f180708060c120901060f0302010c03 67
    0x2068050303512070032110890b24840851401c285411910480c0c050320640c003110402c52210030141d900100b0b50402c10b2034075150b8908004800400d80050120040040403a14250704400000036012051007520306650806902d4015505400350b074450a501c024400c85c03d0090180c0380e000ba100c01c00700e480b00854410300d0310801005035003003110012030130ba10003441005410003c00c1103a0b0003280a540f181c0307285d608810010704c0305000804608060015190661407103509501800c040d0006030710401c5100d0300c40c0d428040400101d04440300013804040465000324002d803441c2d009a0380034110340e200d5460141c070400138180b085001d440c00500791802c403a015403a40612a488100404000350010f244c005241d40c0c60031107500d910b4160301d424100b148080200e2001900b08403a00c16007094410040800d44c90100030341c1152800c0d02030402482a0341c0c1031b003070240c0100408000c0b01d030300e00d60f1150a620300700c505038840c1540024107481c042000d9401b81011903d854020320301414601c03c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 686608291 1250 686607041 686607079
    0xd06030f0212120f0724021905040806070e0d0b07030606180b0703030504080f040e04020103110a0c2307140a05010c05121602030f0f0d03090b0f06030a1a1e070f0e 72
    0x3480859040c1b040d0002560014013403010008021000b941c10078038201410910000d9442030300512440500c29010302c10b03902c3d42c0c0d0381e2540600ca03071341c030240f088030700c1c0307008080240a0030b031600c5a2004500c03005040041c2c80300384070704030f003e56413042005410120745440c02c4004d0840940256070b8541c3c108242e0780c080000368024000392141308400815410035100040803608454245201d1810034401c400030701c0d510556460900390000702e010f02000102c8801803450700d15260070701d198811220000303110140f0141d032038120241203c01d0301c200c41d5600011341b81100b0b0404000c01c146c221008180d0b0203076100f4090441e0904002e034040d4118101e034046860892511004003003a402403444640051080081286540180c034042c420007925582c0c040100101a140d4161005803500081058404118040100b030700300381d40603810100c14442d43c4140300f00307a80c41074031003607900711416841860003107060180e505a52000e01c50959490100d504192118040c0e03402210b00070180343c00c0340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 686609541 1250 686608291 686608343
    0x15090703020c3a03020c03180906010f0f05180a080c04060501030209130915051e131a1e0a1d0f0c090901020d06030f0212120f07 57
    0x80036280160b403030301e0300e10415203420421805040d1204001c0d5080900711120441040d14204490140d03c095403100010380180c0501440d400a501c40800c00040030b0381c40308917210094006032a14403858498000458224100308003c0e800f045001c0381c010b00243c800c400418015401030800349804913a640014105120356000405a501400c01603045150601c6500d00826090030214600912a0007003402c10117202c801c2e10700c2a0743d902618081c040c400444091085c0500c504001e03030725013500502a9400300380503982c02ca500c400002015071134040d070070f24034458001b07942404030001d0400c034003896a00185a48005040d044117643c8824003010310a014070002e0b40c02044400006400320703190100c8004401032030b404400a42509000800d804540036425109000c03155205504640680704450703100700001d01e0007034000107000c0001143c40005100f22030805074071b403480380075503600c081e42c91408016032030820840b0600e45610004014451180d40c8094a54009000083d1200d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 686610791 1250 686609541 686609551
    0x7030603020d08040612150605163309050606040c050d090c0513150e0408041a030402100302031e330a080604260c0609010f0528051509 60
    0x3010204080c401035801c8056101c1c00540803100300900c04c6034000303100806140748240014004001a0240c1250000b12010b034501e810500001581e0411901c621603100c0b5205d0810303040040c02f407400314100d064018100c485070480001c06158440c442040000c20f1040800000d0103010004c1d411010058001c1c040da141c021201d03041103c4c83c050910102146a000682c04c2519140e80d100c9000320203013009080e0742884010315140c0e9540c1c50182c1051042c1d4004521403402d2000308040c020000c03005610403407003522503010708541c40c8000e44c141c0c041542c2004d015940e0303c40703c1d0421400803814a40c420100702d00c1d200640c80c2110403803014141503090b0191440300d185038004c0303802e005102e50020304100c0f004003914a070a4448100000780d081040c0718044800a10040443c02141a1410070003118141c540a08001c485c2030b000b080000203400007141888000750440042e403a45021a455054204503442c0000f00c1000042100401c6490a040e1852540c5015220070a001e8410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 686612041 1250 686610791 686610803
    0x60c0412061119030506010305090a0b04080c0c0d0c0f0f0305030901111906060816151202040b0c0c0909010b0604061809140708090d0f0e041b05300f07030603020d 72
    0x1402c146c000101500c00c0180281e1380c03640701111201c0043d002c40425940181c0021f13001d529040280d4100b818088015081e680c06134407a0200801e010840c04000e013265411840d203040b0a03900c21001034080458440a080c5030000d100d84e207200c3d400b4480300b0505101349000e440c0c0c51400404801c0c00f4400d110010346140b566010240a1600d080209038524840d110082404030710341020701c0d82e1155141081001c000300310001c801a18070540549000c1c151011080d41c50b911000403c81d03650229000042c030600c45080842e40d2590188200d51130031700c020346400d25041c20a14250b840c0480c1511050003d0643c64000403030085600c180800c82e544010301c40c0e000d080240d001001c0b20710262445507140c00c0102c00e41031030ba4000014001c01100d0381040820b4022040018005241603005082002d8500c0204040700d903012000b4507100c0c1c4403240c000045850a100e1100100c100c1e00220700003103a55012a806c0d04086032181d41c8201913180c0801c0694499001c100c00994804040f90700c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 686613291 1250 686612041 686612051
    0xe0109031e02041d1207020603070c031209140d0c080301091a0301051312110615030f070915080606060301030209091c0807090603090203101517070503060c041206111903 75
    0x1054800380666010318001796440c0c0d04151803500011124440a044981071007002491541094060300b98555032040d1030808004400d02410100070402e29100103103c1c6004010542d900c10740290506076441d0341202455041d6800c00c0704203001030446100c1c00390380408510030941140c8e024028284078460344500250401000e00d4101180348007000c000c41404180d0400036035003200000e19a40c8020f8143c41d0511a000e01c0e00882d050815441c204040d030f02900402040d0b1018a4101244114003c00b2001500c1d955004468581d00c05403205035004808000400240c9401a6002e030045918070550700c0a852100c80041614074004484012a40d01000c01c5440303504840080700030843c600701413003008850390000703407a00717241e00171900d80b0755070748040b12592000700903400701070181110360a4003035840044982e6200c10310312455101e84603c000158030035804c50181d404603900da07442d0a01301c2c107150707481c0300181810701c0010880d000103203c001003240719108111078421081d10f000031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 686614541 1250 686613291 686613341
    0x907021c0216140a33111501081009051b0a0803040303030507080f010e0a09141b0406080c0306190219110f0f0c06090418120f0e0109031e0204 63
    0xd0440196000701541002e00032584170003803200c41500002245d030b001000c1c0b00c500d03c0c0d5013078480201e1500740810034410300c100c16903145200c1030100e060301d002100311864480c42180c0c0209440b582c43c0c00510581290502a65030011641018800c0c81d005203114086512040143d1954101d40d0050340000d031504103204e0030303940207414190006401c0a10109546c103103540900d2065000d440306800c0c1c2c0e44d81b410003080c40700c80f003640603030302a440d401d40312400501030042d00900c070b01c81d40007841940f401c000000c0340b0900041e00c2d840c018001d4050505a80ca042102d0341c009101c01a141c41300740c00700504904001900c2e41070344110f4090300c5441d201d08161801ea031a001d5802250b106a03400072480701018071001444c1c09031100308651041e0380d88010408174020f4842e4152003e075130440445503600f000005500c042c10654903940d00c1e01d52a4840f9003c55444107400c0a440c04500300440134808185d520042c41c41c8186031420603202203126501040881d520150a015400010350400c1c0e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 686615791 1250 686614541 686614549
    0x30d0b060f0c030d05100614070f08041202030c062113060f06290d020f090405010e040519030f05030c190906030c1d22020703080709050907021c021614 67
    0x96000b500501d07105c00c005047c4180039142c100c9000d1030402204000c5441400c2020400804070801d500400180e10b030b55440e00c04600384d21101100700d10900848001424a0904c1026180c08401442130700039942c0740d2414440000300068030188410005c100d007540030400c603000382001c0c0d8021140005000d4503040014450003503e0f0034030081403200010412801d203c007000d0b1884a507440f036005030340b541150707411080e900c1410348440e001400c1c64000518400f0580441c0c0c401e50055040e9040c000340b501110f81200e018800081c003050342c13404807510f0240b0a1001e50740c80402022980d141c18444c002a034031141d40c6065242c0020840942802426814011080801c246003000000e9048010b401004000c7c02a842d501a003040760111450310540451944c00038501c580455070307506035040c010002001181c07034402184d0002c40014030340c18140071003480f6071303040c0e030203080c441285c1c06e420017466607000d0001c021440384035115882e548031500395034014200080c081002c0718903103041c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 686617041 1250 686615791 686615801
    0x111c0c20120313060e0406090513030905030303100608041e1524120201020a150603020f090c03040303200c0106080d020f150603100f02070302010e0f030d0b060f0c030d 74
    0xc001c0300c0d0002e00440c080d2140f90480f28013a40c15034100f14184201020100700100340950105182a05003010300052610070303440c0e11040b5000340d480091150710303401415070360b1006a4021008160001c6c00300300360b80c82103040ea074125100b4403600c86002c454034030302045c0e24034101060350130080e28901800c050046218160402a5418a105c0c05c2625001030106502280c424540f50b04569a406021680b00740304400d1011b9212988169003820f44400500400ba64003007203020710f4001141c04160700c1c0c0001220701c00c0e070032411120301e10380d640d0360110f0103014280c0040700d034952500904866810850302070909a00450000641e80b458000c181e46130011650008042d5004800d24070300d01c003004500100500036500c8402d4080d00e90381c3c0442c0c604000352220794819458140103c1c0107100d10303001400c01600960007800b405204c43c842c07644030055240139401c254010000f0401c082c50581020380340c600000c04480c148000c45207082891340c0601882281034000055106505920f4407a0f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 686618291 1250 686617041 686617069
    0x6130b0c0f1b0f0606120a030503090f030f0301080123041e020603091f050f0c1e040303031d0c330304110a06020a0c0b1b0708100c111c0c20 62
    0x1503021020011000c7c4c3c0751500380c2806410810700200180c0d811408222414002000d0782c201d0740c2d5410841440341c0190401e024204c03055080007020a90401d80006400050321211081002501e59680c0c1010182200021800c09444182504007503600d48000e10310030500704c1c0c003510044028030342d90a0988015510303215403525000603c5112400d0110041c0e2118842085903a115100001e03045c1d9140b00c203042c004500c000007404000c141d803540010001240c0305020520500c00000c4130741e221501184030642000c0b101d505e00300c01c0c10300000b4440300d285c0968072403100c080c100c1e42d0742c1c8000c2d8001c95047d115a55581080e0f0040e0030651001e000400311031000c1c2c0302d20101503a50110001c00fa1203400c40c803880118a00501003030400004400354990811240c459684030715603a21081c0c9064450304e16450003105010303050103030704008101b1030000050b000d003a061109036070104685040d03090402c203100b5610000100f400d035601307210981820702c0c81d00d20803900040001039080028 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 686619541 1250 686618291 686618299
    0x303040b070605060310060f030201031a0f040b0f030601170606090f04121e020d03060603020f07061a090c090f121009080d0903090806130b0c0f1b0f0606 68
    0x20410444818251000598001000f051548500000a24280751809000809032400a00203412010118400c003140d2003a01c0620454282100c03260100b40d01410041d0048059030f4036403190310306940112120000141810360308010400031915001e0240c00c4030501c1e008009126485480c100000e650000c000c98007944c0c80d151111521b54a008090b000910034040603001070b20301c90195918009000109250022081b0240002980e94441d51780b4a00401d142072004a0502e2090080704d9690751266100c900c0d043c200da50329030040c11b0b06160007040365000e1710b110f2826075805030018052a075000d22680c40d00c512208002000032005038091184003000300c1e0000d88440401ca91001c1002d2002c000740240302c5e400c0070744140c45682c04080040e440d10000c0302c10940c000711510240c4500504035032403955070460074041e40b50f40500c09050364001e1030000d17042610a1004111450454103e03d0528110844c12040710b40e0249010003190043c1159102a03002005007540c0120216 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 686620791 1250 686619541 686619547
    0x1204030201120e010603060504060c09050103060b093706030c08010f0312020109050f0d0206010806250e0a0906030302060a0b060d0903020102091801180c0504050d060912120b0303 79
    0xd40040c040321468000386680c103031680810b03080e01000f03621190040d0303040302c1d05000034501440c0c40c100911a404241d000300724040030108040d4424070691056910400819140c21075071000c001029400f45c21040110206281d00c2030b009240c0c0000d0718880a20b04901d074481810602d0140c140e0b2864100d0f1400c00020000402c20200c170040701504a81c0c01480303800c0080003c0e02d00701e000d08007800d0040c3c004d22445a91380042200010040f410740020303401d481841c0d884851071038540c0307030680700c4002e0980841880100e52000d241c1d11403041500b41070203030840baa80404981035410981c410000c1d50b031744880410503d5010300c041540060741c040c00304850203a40300010b8040c040e009140d01c400da075488007c130806000b581100c80320b071401088101c2031615440d131107240384824001c1203401c00740401e5020304200c8a00417031031011059251141007a05010500030754441c401d03816a010b40e114030950000c40c81c0c00c1ca42540455280e03860f9180201249080e200740d840064400c0e000303034010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 686622041 1250 686620791 686620793
    0x40515190f05072315010f0503010603170912070b030109110c070603320106110303040c03121407110a0816050405130b07020c01030b0d030f1101060f080f120403 71
    0x38044580203a80b05041c5400c44200840342030800081e040134030603511030b82100101c10880f41140340d0407204900788101403d9103072828075080c0d80f600c0c8401066400041c0280000340c04042c0948060040034110b00301140800c0500d603c0c00c5202c1d408034221100010040c80f0360381090040111b44418001d826107400740c030344c0c074095603800584030704c504040e1769000240402034040342c00a170300e0780341002e00004420358400c0905400802c0c071452002c58003603d46030b904c00c0004003d991155420a000c81e681a14584414402040b144160b1040000d09886d528103a0212400f0745031190282c0950304400340d603003003130002d0028603400640c3c295100003143c400c4880705039140f07410b880b4262804103803900c070143e8100101900b954020841c03030341c072410480c92550008d0b40304d800c54030980e41031012403c103000340031050302c840c030007e000120401d8075802101c2c0039203009040c8411140000a0b02580e98005100080c0b19400030b01642e0821034030250091000c2084a00c80d00c0408003507840c0c00c2c51 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 686623291 1250 686622041 686622047
    0x120201230601030905030409060314010b0f0a030f0602040b030405061005031c030216081c0b0d170306120d020a02030f0609030912100c2109110114040515190f 70
    0xc0102114101611480760400300700c03003070050f1801405080c50074000b8039102d1400d0044107030f0042d006d8819620341000d43c0190320303007800c801c00d00c100080c2c000a4414150f4443c054031058485007560820303003c010001ea00401c0000561040d0f0041740130b403269080c03107019018840752650110b8800d901c441000492034451040005905e000303401e00503500e00c2249008a484030038450003401e00400802c0e101901110003542c00b05442001204000e09040d5408001c10292004006020b1010b101c00c11030700c80d030105000b5904010300424080807042800c40d400e20300442c0340a0a80142c00000c02c0b8003c504081101400c2c0450701c50240546103442e064083d601d00a04101c0e900c16034140c0010340c02c0c3d200a05c201281100d60600900140622080180103803540d8050a0003440c4031008070321414078503102e0744002c994001010f80c440d00c104001100d0048490b900707032500140400c8002469560215590b9816001c0710311607071540303070a141080c50722a11801790000d1100281c0f0203a0394541c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 686624541 1250 686623291 686623361
    0x11a0702152805090d061401060203071b08030d09050312092107050309010c0804090e01060f050301090302060a0c1214070206130c03080a030f020a0903050d11030d0f1404120201 78
    0x50540740c0391003600250800c040601f9034800c22100500c1d181002041c110fa0100c020010303a0301440c1c511100580c01c0082000c802e100c0d104092450704140025940600150081d03082e19004100301c90412500402c9641c2c00070f0700355070002180e4000e091000300c010340c400c04200c40c2e2074008a4207080c56059200d813922846881800d43c10807071614408801c1003500800c0d81e010306130f84941080f41120290805000f000075006025042a61740703c002050311701405005902581a4050301461302e4510110f000382901440e088103000c1140c0c0b0b903008880300c621030903984174a18640b03c0918209254084d00b0024090b200000c5860310910450214400500c11011070307600c10413090740d50018110407002009102141c04025000040001d0385640c819002c106490041c000c0d03603941c040744c96041c1d0300e8825000c8620f07000d4006010700b521038141075000c00e010f500f8a21020886003102c1180190030403023201c00b21600c01c2042d035a2507420368240f282c03142415805000320341c0c0c0340020702c641010b92 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 686625791 1250 686624541 686624557
    0x1b150306360b0604120b0a06141806011101090506060a240507020103020708120402031225020f0916030e0105010b040509090f010509030a080906010509011a0702152805 74
    0x10b0301e51890103030940790a81150005d001001c486050b507407003480c112154007426148254014102039010904514941e40d03600c00a400400b20801c248007420707115220f69000786101e044c85101e5504001c1e250081c007405030340351f1040000e006545031500c01c000100c0e18036081500107483d05c0900001200440f444107400300d40500386907840d608140b0048020303214100b0014011640406d03860303261865019068000c034821001c3d0b44444000a02105150184ca035001c0c2d03201c3e40510784044001c5001c2032481210f400a4140036550441c000845c2403a4000c2d5080310340e45201480946000781d040c801c464003a5140c0000340300c954507025101c102c41c00f6078010644108031040100b904007908000030103a10390310000034032003858a034a03203503209c0e000201ca010202d8490400580110b03404102039059400003001d0015990801e80c0305600141220209034001030700304148030145c0e6401c0c40d88102d08034007050050b6a5011580084010601e054070155940030b40d4051011580c3c208007995490 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 686627041 1250 686625791 686625899
    0x6080c13030f051914010b03061611070506070308190c021b120f0d0f0509030a0f0206070503040806011d101811070f121103071b150306 60
    0x41410b90415604082010b0350800c04038101201c1c180400c180c1016251500303e0700d00080016552071414181c440c4c41c11141d90701302079081d190115003203018499240d0a50030400c11104d4260f02d03003000c1a00c5501c443c0c800d80c00b0032500001c00c24843d03444a4044043c44001c4001c3c418803040d100c000c0e5845901501e1001300300d2003000117142d5a102d518403911415202c100f151000340c0c122813011b40b140c074045807580004065511140040e4040c10840e1344812016004024600c1642ca544003c03404004049a010304100300c02c00c00300d24200060b0002e00b07100005040e40794900306100c0308100210109412400d1000200100160690380381811590100c1003021540ba010034410010003a040e134002480201260907010300110032a0000329920410100406059500050fa00410724580750a401e0b882000000000749840458200c1d01080750001010152105010100c1c0f101400544c0000380e071700ca03801c00420011520362550050480c0605908403e41c0080e4090000b045403683d080d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 686628291 1250 686627041 686627063
    0x606040b0712030b18270606040216021e010f08270c2709060f010618050406060c1505070203040501030b0a2c0703140a150510020706080c1303 63
    0x901c1e0f01035000040d039144010840b403a80160030720368180c605001e035203c009404c3c040c8078802c0f808043c02c10117102c68546100070520b0790380d04d00800020358481244042c0c0b080a140b42080142c07074083c0d04000201500e03081440c80e00403e80010300c4013040044250820040ea8140041c1e102c18424200c031000301108110342c1217526200c00745c900400c04440e44d400c0401c0c20544e0034400340c9042d1341c4041e454810070a800703a848486145036201010764400580c1040e003401003000341c0c0602e00c005800c005080185000c40e50750340010b011990250b0200b40442d141d0303945501000b2044841c440c4008444604005a05210000030368900039405010305066903103010b031105a8442d06613a004140c40392242d08090310004045c03529200400c0f00400c040f41c89030100300014041d000d00c1c9158240900301901075580c039011203004d8428807552105c45e078050700c0b000c5001e440b00500e00c40c208460f5002002d101e03260040003864503000a10490303030180240501c88511541c0d000c030700c1c01c480d0010240e9003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 686629541 1250 686628291 686628323
    0x70801051b3108100f02040e07051804020f0d0b0d0b0105130608060a091a0415110d090b2d04020d080c0105010f05010f032307020c04091a0606040b07 66
    0x1098580e0001d1012040301040e10000f0b40c2d01d070004a0414002d90884280300c21002c0540010a074003580c0640146007c40500040300c4511940142094128540c01e5a054041c824041000c907440740035103e5040c200020003003001c2c4007a010300b0703050050540300d0000303d035810b0307c0e003c00303640c41030091510070305102d0015502c0c290117800100280c24070350300351031031418542035000040101080843d8105070f5180005281000601d41034441c41c0c01c5800360700c4030b0603480c0144004088050040904602c20f10150b4540e07481840b41294251103200c0c4610741d828100149075140f5010010410705030f5a080e021540070110b00c4440e41c002c1da050358901c00c48003143c0740084080c015001e11910940c60076000040c599008021101282c1081e25452090800c4a50403070a5450b0000d0250061181610140c03298144015184d40844644162060801041c0018040d182d0310b80e0207445001c000d04403444d801c40c142c08030582245c01140c076545046d02d0f24a80b4800c50103203110107007802580c180060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 686630791 1250 686629541 686629597
    0x90609220204291002100203070c0f2019090c020c0d03091505271c060501051915030221090f0c04180809150705070801051b 55
    0xa0303015500038010701000100079166078031420945a03844440308800d07091a094105482511028070341c0758003a0901c10b0103c000300f00691303c0540344404020740300741c0e204c0c0400c50a110002c130139403203803070203a0545241080380c40d10304a01c0096148104854240300440d60b6860644a040720a03d54003c41c80e854400b50076814010950100c1da00300d00001072620405501401c884180c6400b00004c01e04180589000c503040e0140308c0e04415a1a0f44042100003600092400c03107098100070300384201d01721200c1c401103108178a51400c0750f0098450340184001c1c42c0000304001080400900c00c008a49498407040103820f6041c0780710141540000c4040311a4a407040c0000500e00584011850b0b05020b10540d40e5144101c5841c241800303407140141a6103003e00548407911010340607903200c00740c0c07500e981e00e0756881101900d81c04411010008204169080901a4180a0405448010b10b440656803e40304018001030490003a1101040d0880119094488441c1d42c1d61901210f90301c2d8481030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 686632041 1250 686630791 686630851
    0xa020d15050f0919020d021315090e07120b0c130302030a1a090c060a03020a050405030703050106051206070c080f09040f020310080a0b070e0319030518090609 70
    0x11040c0324103100402450024041007a8003d000420880300c030360b810100c4c5214181c1c3c1042000350f016aa1442d42000b52802d0102944841075104000414505652000850714580d600003c103040c0c0300c4254129881c82402074000420038000740d00300320062643c41c010f10b01c50040c850b005248020800d03405100b64258402d01a5901030201c840d0900e450031f101c180c0701c055060b141280124900014884640800c0d0054030000140049040c05d20b1050300f6406074000500c003100300081400002015903081182800540c010700000030581d00b0141840302d48199500e00e441158460814806410f602031805660150130a000c19140c2c3d000d0a1503e00034456403003200d42c0300e810321580380b102810a6000354010032500507608110340d5210b0b54103884000c1a04040c20950181c4000b402070741c050610050b90903401419680c40b019a40c82d09480100e19940a9001038408121000482418001d602c040c401c00c4909044502d401ca001504059006001200681d50442d424442d00401246 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 686633291 1250 686632041 686632073
    0xe07090615050c0a082b1b0f050c0724091206021303020d060e07080a020102061f0b0a050c0d0305040809010f050d11210c0301031e24050702010605030a020d 69
    0x10f011b50306ca0300402da640d6035407403010301100d0418548890032012515031041580740801c58034a142c54203100d00050b9518203030810b03000c0038418100128808400b040c08400b000c3c00c018602510308007041810108450950b8015030184060580c0c103120030740b2100c0201e540a5880500503a955000100d04003005d07000d5803000f50800170400c800800c101c0c0076044000b210b45c452048410171507075102d04650742c0402031006409130304071101041c1d400c0319001070600442d14900c07501c01281e96507814248540c2c8107161650028501044150b26070b07200707000c560b0f40210545428829801c10b0340b54000d540c4907582c00c8505101c000200c254059008a0958040c4000382d80102300b82da110045d0500f1691025901829083e440300d0408003410000000d98014514040d003182140c0c00c50f603030101c44a800c055418108001e441f0ba41740024080b0342e40741c1c0f4610f01000b06008920450240c01c041e1403024002d1415a41009014000d640300094819544d940480d00b0451942c42400c100304035810382c3c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 686634541 1250 686633291 686633303
    0x6010e0601200d231206040e0f1608150c0c150a0902090a0522050f10020a02010e06010302010f030c0e04020f190503060a0302060f090a090e07090615050c0a 69
    0x50a141030060108030f0002d1030041d900c0c2d03411001d41d008800b0143d081001c0e07000356000420300201e001480f22416495201c180640001000300c00c42e41d18610741102040789004139804621440071003a00c4010f440c00a04000c8000d25426000d14a00401144000e11000e40303040d01048a181441040114010280381104a4035850500d01110400b034001070106a0003a2034680101d200c6105500c1068403c84c0703160080300038a0740c8401440f0840c0b1090320140c031184107007079141d507241034244a00107000c10800001070369020396840190a49070b0707170100315140303801c08001000541d0304100b0750382501c070f0303180340004c0e405611a2060700d000000500003504a0701c0440d24046c41000702e130003003151101c0014812840c0500300001c440b42d10007140c80d0b580108078644c00300010304050001c0c00c2419a4001080e007400e00c0d903004900f242c54260700004000351a00c005042080061009101030702d40204107004045c202521a02800c54011020040000c0000d2440510205200004d240d0758460307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 686635791 1250 686634541 686634587
    0x80606070f050309030d080907050121061211010503041709040608031227150c0909041209050f0d0219030c0f05010e010306120f02040f14010905160206010e0601 71
    0x4105243d0760b8002c1084140070f84182c10182400c580581c200324404c1c00008000c05001c4d04010046640e1618001020750a49070711200f07000c0c3c59070324002d001c05040601c0c40d00e000c100b007030305103040c8442c8143d541c00d0502030100b0501c40480c24484450700d12034a501d41c0940d0318142440401d004040c03660001a080c003000c0340c2d0300c80c13158100d280b0701e000d50b091004400c0d40400c03101042d10914075907c007070000e0354000e840d03050461026400780e40d4400070751509607092038070000204074600030495003200c1120454210480c01500069902c02500042c0d03407405034040d0000110b4400c1c1a0174a003c0d01c2004e440003010707c22100c0341c00c0708000c0c55110300d4065540f0360316408406a03c003036005040c01304a9440700a1a40e51180c40b54808072503a000c0440c0a0303a030b482e1202000c403004a0401d80c0c2194440d40234600c0b2039041d002e5a86c141c0c503141002c0d0b1040d8900940c0e201140c00c0581404a840c1d51020303d260040c3e0b00240003415210540300307503c215101e14006030b51b26402110900e800074295 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 686637041 1250 686635791 686635793
    0x309080904061d1b030103121b120801060f0912020d0f030203040305010e0c0108180c0a0b0406230405120102120a0b01021009120e03100e01270b0601080606070f 71
    0x2c80f000c40410001820390320120b44500301c0d51945103500c3c02c10700355134680a00040000c1400030100c03054921090410302086484240e0440c1c3d8100c2c4e254040c0c5540c404c410103480b0141c0d01c0301c0206d0040000340780881511040d000c0080c42802c03540304201102204803010015503940381100c060341580206000e041800c686006512600130348016100b9500c2d04c0c0c1111001031000c6120303500610140d507040183e950366900b60521040898034000b0503c600380500240ba11010341c4000038001d41404192a146000e10050040f00180c28500e201000500700c01c2e41044203c00f5102034030b4007100c03103114002c0101d03440d42c024018010781e814040d9419060105004460f413000c1c25600080e42602c000c100342002d800d06a8080e880010440c11000c0111180300e445070754401c03916500202a10800c030203c0444005447d005648202c85035034860409800e02c0c48407034001468103114807480300c1e001c1c9a0b104c90340800001814a41400341c9803001400c06d654003400c0791011035025429580522807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 686638291 1250 686637041 686637059
    0x17070503061210150e07090e0f0a0b0310050108070b160b09100219081f06200f0721050a11061207030b030d05040f140a21020f060415030908090406 65
    0xa6403007003d441171410000315030410701c590160b1098400c151045519502d40d040c0710003501c3d60003000801d182d40d66040c444407980d0180400900c50005000c081041c0d4141503040c2d05115550b0700003a05c01104100b000502c10300d09003004095a000071411045a542c0c140b1079040904078036450f11514400108004601d171401c0d02b03a0320724000303907950000f181d6903a4551010b80001d0900c0115285150004205c0d080c85040c41540380303680400b8128440d01049400d41c502621041e4081a0f600f0a203000d01c49406e020061056814184050500c0d03604a07403507c5446001800c1301510b80300c80e440d1100e115484042c1141e11840d40c40c1c054894074941404020010724090079058802d0184a41e01c5928901c240d0a903416a0701d00c00d0042c91062070f25203603003100c0d00c03440034031600710381d0600340000e40200110101c003c2c0d40d21b040003c6c0100d486881005051401e11108901c00c034028441440761143c3c00c03104804480b098117000a100c0d0690900703424a00400d958140c4c41070900303401140c0041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 686639541 1250 686638291 686638331
    0xd0e12040e01060c0f020f0303091210050f0402010f0e0103150303020604061a030304092307090311091501030213030215040e01050f240c1c17070503061210 69
    0x10051190700426600d034402141c03180e1090074050004e00008041c80302600d049000e032550008028100d901e0000e11a01003035280c0b1100b460710840e0303001050034462028182c01801d5004007141316403015440c0650028040c1c041c4200034500300000080074100e42d901a501c10b9901c6215088402441c036138a240003951000110740c111020b03414108200d04a210850b000401e000005015505190602840c2402004440341c080802600ca50054081601096246009802585d0b400c4000790450408d40980e02540d030040d40111003a50810100c0c2850156200b14007409103000341e924041c0d004480c00600e0320703800c0a0f521030009103200c15141c20840042c0215118072941040d103a0340c5900308440c5001003500103401c84122455130803610500780030041044103201c2907034100400c00d0001885c0c0035a8440e092920381039106584001d540001c810445d281800144e11014607040b80b005103a03010140c00d0034050540400e01301100704040c01403800030790251400f0000d540c100b0181d403068030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 686640791 1250 686639541 686639549
    0x16060e0703060603030f02060720120403061d0606010e1203070615050f0103200f07050d020706110118080d09140d0306052d0a030b0901050f180604080d0e1204 70
    0x142100c0c1006d21482c0041622403003007500e902e40c0c00741d0f9460441c10b40b1f100211584400303a180540d580c690461941e04000d48055402804d0002e403025030071703c004100e074000c005a000e00c0d5000c002000281e03a0f00c02d2440c6504441641c08038660042024114558010020b008003264102a401c3c03070503000254814003203403c203c6103000c1c1d41c0c034004019001c94030340c4050525428101c0307a252514000340c1000304010038100c030460386480403e03241d0b20300f84240c104002e001a002030030b04110a6601c1906001f03404050390081200314422412402c88007509070740181119804074003030401c1950b5a103c601c640340c00c92040c406403d6015441510ba240c0f4900c800c0100e071504401182130700380510280c0c2404002029811964950b003102e1260040d02103155912111414000c40004c8160001781e0041c1c10403000488c01d810414150351007180c0007402820008180141002030380d1001034180d8125800c43c103520340e2003c503108400c0181c0100004522079110b4031100301d0110146100805c00c171 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 686642041 1250 686640791 686640797
    0x906020304061505010e0105041502160609090f020405090a0f0b060c070f08010524040204030807050109031e090308070503090306040c0e01060e061b0c0a0b0715090816060e070306060303 82
    0x210303403114011b55200018102903400101c050000f48013404040c80340b406040614011034448107603c000051140500c0d820903400100c8403d0200003241a5004007680c1c04403480044d41080d0a2801245036044010021007107a9240c1d182c038084401240d000c1d00c2c08060141006a885448040321991203003140b1a032490300d0030300e1300001200101031250034018121650050000d0b000d001400b909443d03848403056109a080100100240f42c1400812245c6d101e50004994403410b0704020705255040e4102e2081e02011000c80075840341d00c04504420b4a50050302c0340c1d12030445040443c40e60207000e4890703402d0700c11003081c0400c3c0440d1481c0d600c06c6985000e0324015607a26100c1c200d900c031140f1685550000001c1c03264441202c1d6641414030035403000b40894120620880005030040860b510420030b6681c00100d10081c881044002000c1c0f0001389400c0c4100101c0d81ea031214079100d5000b80c0b003910184118985c0c1085016084081001e00b00c1080701c0e40241c41c0c4c03c155005050340d20045001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 686643291 1250 686642041 686642081
    0x6162108090a02060a0f050d0c0306140d0c05060a05090306010602061b0406020607121b120f06050a0e10030b010305031809041505070e04110a030b090f061003090602030406 76
    0xc10500080c440c40b0903502130846410169818030903038401582c1c1c07100400b030141c1400b45522201d01d900c2148a11081e5980204204c0d01d4403801c0090083e8402d09103005031030400303004020070940e001b01e204584099508030707501c0f01601c00071500ca000d4002810b5050103880000200d082e0b0010700140502e200681c03042c0c82d591100200c1d00c0e140708900c030300405a0070600000d03186d82d009441400383ca03500860080b039018100100c10604480e1160000045800d0502c901c1078007a062080c3c05242100d60010400c040c100400101e0400c501e2041d2260400f41400188900c2c1284940360000c550100c0c100103079585a103015500c0e1340011480003e4290458140d600a1034029940b502541e0045c40b4650380d4055000201b0140c04000d0041e4188044503075000501d84551041780d98191600e1251130b20307000d030b0403c003c0030764410300c2d94a07119140d440d05000088828220442d04000104d03558000104041d00640103007070002c81c00f41050f0700c080300708000d00c00da68200040380d408001011074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 686644541 1250 686643291 686643301
    0x50a140a05090118050714070f0c1215020f0909010909060b06090f090a0204080f07051009061416020d15050f010b070206070203011b0c0c05040c050906162108 70
    0x1070005003440342d0144e482c400c0e5103400100201d80c2c03007242c10040e00d19110f51000454406420650700c112021610b440100c0710f000c0c188003400d06108050400070001d129490150707205c1c80d40381007011410075065503000801e0003411508904407030381040058003800c0107603501c0c40b40c90010661442d0503101d8a080c03200782c92484c584941103c2c1000b01c02482c0c146522410014405041401021585040d5007080301042c810070402c500301d100c0c118070008100340c508107003d010200f02121008011700c002c0100904c8021381104494104540184250780c0b1003082e10705c882c160380860040130303400c42d5000d0a04004d0094400011100b6010b0750028011522040313043d81214800348101d105800301417252000500e4214010520343c2d0009002003207010714000c01c035001346140352840002c0344000010700d0820424031403001c000e110072941000b05590b40e042c09803407031181d80f0480e071040d03200003091400c00d030300340d00025a4540c12400954500409852400003140200024400f150418000030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 686645791 1250 686644541 686644549
    0x80708150c0702011b17040801060303031109090712060f15030c0e0105041215180516031101030203090f060a0f0e01051b0c0f1006150503070c030e0307050a140a05 72
    0x324943ea040e5142030300c000115060300141415444115048036103d000c41040040b00300c00350014041842c00014524a076140103800c45184070800d40c0c0d0b41b4020722140c1050380e1600c903040d034800e201d8142000107840b140d20000c024419904101040240e40c14003150030350307100c03580d40c18003503081d00d08004107445903900382c60500701141280c4c00034004000c18001079503414a01c3c000c980c422554619400d03031138a511029920035106064008450702d103541c0034804108a40c00c0c0300c0041003041241181036464110484981120446c10b05070004007050080f0001c1040708480d1140e44199031540c204402440064258001300d90401d41c1441040000360b101131060f00c0c0500114220b81130440c07000c00001225400c0030480003d240110f840301e8609807400d01c0b9031800340c00461800903125080101061a5400020041d020841c0c103004010030241c011900c031a0954250400314000302403c4002858041d040d000a5003007140349600060b5075010f5804800000411100300c19510b803500c00740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 686647041 1250 686645791 686645797
    0x3010e2e060e120709020c0a05070e060f09010b030f06010e21011b0e0d060e06042103180b0402040b030703061409060402030a06050c04030b130302100b28080708150c 73
    0x1010580c02c8401c1c05c0105e140154020712a4041040548100110030740300c3c00e0401e0b4055100c2c8001c0c0001c1d00400030185800c030f8108010070700c04c0780c11a443d54100003030107801d03000080100a8041d400b4011a030141c4c02003076010b4401d07600526509550448221003103d21034121000300da41c1d0b003400b9030f1a540e09011689100340b00c407203a5905141141e59010402c0781400000c003640c003680d44004908a007441030120394440c41c05003060b0400142c04401420707a0100c00e008174000c2610b4130540500c0c0c46103054250280c4c9400c0310048009441d5800041c0c0148410031007185e06103c0c008000041003c80e4100c030a800303042180000c83e940d5050200b40e243c9504540003941904800d0365070340012020390041e600080d0060301382d0304041c0c0f01d9584441e05002038491400c850400300040c0f040550401c200e8210030340303241d0144092107e903400b140b259221540341c104101030070010080a5400d0341c0d0342d10002c180c440111500d0a2352035810703545402c048080300c4c20f5401b82c2e000041c4100201022 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 686648291 1250 686647041 686647069
    0xa02040f0219081003050613050c0306010f0302011206050405090a05060f01050f010f03180305070219060503150402091008100f06050403111c050c041a0603010e2e060e 74
    0xc00c0c40c0b02031404960100e00100002801c944c1e01c4408004560100022441514007840c580030301711300c41c2081803400c2904c2c01114404d600c83c2c401885043c44240d504001c4940c2803c2940e00100b030540101c000e400d4603000541c00c24a40300c100310580900262a8070100c0c010003c2d41c14907292440d0154503407400740078554029500034940c8959510402e03180104202a1a002986440c40211541d005001e000190001803000c034040082d450000644040581c0280304c05607c185003000141450000600004c1600304010296006840d00c0d01103983c041c0b001000304114400758400507040c01e800303882007190310400d65004a0b41c04002220301d025030314a500c559050616640d5290354100752054002e03005800c0400341103008117003502c030524061140015080d0500c0050030b000840d000641c007009050f450840010098840b04200c0341503410801011000ea074690000d000c05800c40c10a80c00b620b080e084081c0c0440f00014803040c1510320396a0340140034001c900821046294280c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 686649541 1250 686648291 686648317
    0x180903030f07111615020105360a060204031205070305160f02030f0a0b06060a050d0902150d0c0e060f0a0c140703080c0d031104030f031e020a02040f02 67
    0x89a0301c010003125159109400b49000010900c0881d182400c2c6080d1001405241d11201e800307020138207152a00403000c0c225803000b08414901815200803405101070351001e003103c80350b200030980706030b407a183ca422040760080b6401070b0110f1510100941c054070054900c3c0140301650740d0045d1088041f2429543c00d0f0b6038481c03c001c5820300e1400d444c3d9000108a6182100d03040503070040e181484041440c211603005091040c61a09000300310510003441c44e48200401c0040c0d19000d5003090503501c09030300e444000103c7c8011071011590003c0301d5103400848543c0440c1e06c004221aa8111f60550a9150380b00100181e141e010301086000d09100d00745003150910141791490b204149040d401e6000b8820342035900300c0e548510341482c00c41e03003041d6410310300011200300742c000c10000c0c0b26104e000342c603041040b0a4055106901c50185000c0109001d20f0080354809043c41840320107401d5200c410805591455440040d42c2c1d2411081d00306d000c2e038240341c45071039206051701c21b44004800140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 686650791 1250 686649541 686649547
    0x10203040603054c0510050c030408061320090103080904110f090a170a08030901020d020d0204050907080103080a111006060305091c02070b0711090a0209180903 71
    0x201c090303010b070100034201c0c0304582800c01400004800301c9140342d241200f61120340e11140d4454a8014101004c00314440c4082041d101004035840c0d001075200014042d180c41511491400b460a0451081b503100f44424825401403081680600c00017540e0688103580d110140c0100c44940422081f4010303041d035010005600420100e0410802040342d104020f0000a00c0c080e80459600c2c140c100070724a407030300c0d00046071154290611441d60340160041e0408003403c0c1d02215000359a40700da40b10000d00301c032400b00200e4036841c025019251101c4030001c0c195160132405401d40c00070340080c0314040c0304040c1040030414450068004c103060380c0e00204658641003c104081e64039a40c00c8601c403c1511904800883d890510703c6080007500140d600031a0318200b016003d8908a2800c64a03000881c1d402500f0079050303000114002250130300c51549803542600d0500e58083ca41c0c0e40f0348183c202c1c0f0514200500d81746680c0c010030b81c88800304c0f56042400c0311f11010381046002101e800d607440e0f10030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 686652041 1250 686650791 686650799
    0x9030a1205100b1b100608010e0a0b2e0902030f0f1003021e09010305030c0105060915011b05150702120405090f10150201050702010c0c0f0212030c120c0f0c01020304 73
    0x5440101411444044401d980f0318158004d1850301e03888500d101c40c0700342d8590050120880030302521902002e0301c00100111202501d031480d007800064a42c02050240a484100d215010760400e07120300115183d9807041b0f952541040d01a501c05c032860f400d0f08054030002206403404030f01aa0082c0c104c40300c1040381d0340c11039081c054004821540349190b00c540e401080d1440c1d0303541d0030f624069071217032020319251000000f1a900303549018000c2441184108200071000d0400080c41d903c210092a00ca03034482c03800e400d621102925400c02801e54003648014829801c40401c249001c0c881c280c1c2122000748114140d10700c2c80c09280101036200480b040070810000301d000c066a0440110030b00903d809036a1180d80d40f15852103072203040580d442e0300030042729a0702882000040059401c0400c12040c1560b186c0e08504015540248aa0038101c038490120b00104103075145076490383e0444aa0f400248000041600074070700321401881101d000e1034cc108004a40e032401c0e00c1041e002107081a0034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 686653291 1250 686652041 686652059
    0x7080604150503030714120418020708070f0b0603060601020303160302090402040503070f14010804120c15050703060806061215090c0d0609021206090618011409030a120510 76
    0x405610341006401d070000100715079070284020300c0390030300c01c080400710010004c82c11800c0c080c5040c159612070030140401c00c41d0740c1c1070169404010a505200581d1280d80c0d1034103074100d0017001005001d40789900021010058100d80c03990107000120111041c603541d61004981d2840100d6414600c144510400200c0c280642c0141c0406580280050308194644000c00e1a180c15940524000d4030101c82c2044010181a00781300e0700042840c080456181c141ca50382c00c59084003081c1400c20200003c00030901c96004407862000e61300c020144924240300900501a01c220b0203600c1c40d600682021130401e00d1704841174260030b90910082d207100200c00d44211400c141c0100242c901e4001d4186407036643d61000d518810715442100002084141c03801804501c003600b40c102400e41d880801440f0000ba400039004c0e030302140c0100d404c04000000d2049501500b0700c28075640c4181c003a5010300030506e1020002e02615a959078071070000380320308034101083d58400e8580303071800ba00514081c001099 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 686654541 1250 686653291 686653301
    0x904030e0d050a0f03050304150b0625021905130b0a0608060a030c03060c09090b0a150c06020c0601030204050c0a091229090706031505090a0605221407080604 70
    0x2001e0000d4548a4a29840b80d044c180310201c01100010b00003c20002088070074851600102e004c22010000a4210b40101d515403083c02da0407001c030303c0c258511020f00700c1c41c18400038110f0360142c1110103640d20540210760000ca5402070500c41c11100c9803460881c45148624114048001c2c0507002d4940b4007401a14184030181c0000d0300000d609102102003100811820002d501c944030002d0041489580102080000d07001580c002e4106060b2000c6651031480100c2540c3d441d40320202e034640c48801c16690851903200041040317001045900c007040b40400d0700c84c102c900903201409250f4550340030864900c1802c13000ca0201c1c1c1d50351b005010441ca0300c050000803e12820107440c0118252000090992191888483c0da0400c0c0701000030100c0f003408948020040c5040a00103602c50030301d100f62019043c05000e0081ca00a80042c50320000c0d80c0110000b40009881c038000c2103907400c40b030400c825962544d40341c0c050803c1c401009240785a0043c0380716001d0b070780e280505501e0340410403029007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 686655791 1250 686654541 686654543
    0x3060402071b0807152106150309060534020a020409061a0121020705100903020d1404050a1520070504060b1216230c06060904030e0d 59
    0x40c0d4284446000500390004040d2950b20103070300180b0040ca0540703a50320b4148150052003005182e800542100341d04440c0c100c0c426041d480708107120310046000e4000a10b8a03601940c00e403a009401d000c00d0360b4150f4880141703a03000d00c40c180f0865640c0841c0400000040500c0e41034030700786981c00d01200740481d0082c907402c003080c810b0380c0b4800155000541600c050800030350342c041d620701c040c403600312603044600e0b10302401b0708000d501c42421442c00a44004d0354002404019000515402000700501081d441007000d81010040e00c5940c0c1402565148101030780d4000c41c4950003000c043c079000301c091f80e08480b0000c141c600d902e4100000e100b4220801d050080c240041c1f6080301d81803105840c1c0450009080c13500030040d4034507240c104010f40c1c65590081060381c80c01c12540c9861b51030300355040c1c1c0c041c01d0b030081115200030381d6200f2600c0f041c81081043c078122007404011541d00c400c100030704800c6441c000f25540d64035104100044540c0c2582c000340405c0c4420810b99a50902d0700c01c4010b51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 686657041 1250 686655791 686655799
    0xe120a050d1401090f05090c130c120509030c1002130b0d0b15250f0b06031005090304180213170c032506140405010845150a020306 58
    0x844181403402e048400c003030b00096449500d03106510140e990900c580356010301420f009160744800407021400352040c0081c0ca0b141e076034880d26450004ca015541c0004c0b0041c09a80c100701c5450030980050720307600594428201401003010091416904e40256a00b00c3c041a80300a5100c0c605014150301d50321110304000199150100c0602d20b540d4010b01400b4504034441e070941c1c1c0c3c2d2440407148070703c2c8190b001c814410749810402030301054109006441d0f4651210700401d581c2c880740300080c43c0200c580e0031b0703210309800d01041010400012007d070003221001d049444800c1700038540c00081e4010620ba48401c1c2c0801303d8108807081300032015409100784141602c01c841c4042e00400d040600010711207001c814611080700f00c10529000c01380c014941e61402d0201100718006004203440746104907810046400003145a412030356100205095107036120940300316210100c0d40b42c0b203510380048401c00e0081c070360020140030003180c19100c450810408208695440901000a40002e0041900 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 686658291 1250 686657041 686657051
    0x11116090203221a010504020c070b180307060c020108070507032709020d1d0309090703020a2604031d0105040528270c05030423070b0c010e120a050d 66
    0x81a001c00c001400c542d8044c40d980d08000e4809024141180700680c08140114410840362060100109004040c1c445180300e1513139030000714020107100e5071070000f555814003801c02d00003041d41e0800469485e03103100380c803400389581d941c000540c0c3c07070b0095041c098042a400811844280210682c41106640c80c14200d0140c0d074540b148142240c0006002c400c0169650349011590800c5440c110014aa9040190702d080340d05e01c08506100070141c1420189500490082c0c9000e0240d141d05070001010a03001e01041c54603142103052520541e0140c010895640940d00400b405410030764400d5010f03142c3c145000d20300f000f030128124680360001814549a02d22622503044e07405500002e0a1200e40404500c803403480303000100d13a0b14045200f80078501a1015042900f1070141c4c4d51142d00f00c00094059803600c090030100c801c40b62100413990003050030200c1d03035007010800f502e0001c8040d00204010075225010594507182881071000c4900f0500003151280c1c40751000f01b041e44401040415 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 686659541 1250 686658291 686658331
    0x1e0d0f020a090e2e050a0504020c030901050a11100b01120608061801060e09011d0f0601060503040f020d081b070f15021c0c06050f040b0609090a05060411011116090203 74
    0x49804055030101c1c0e440d604c110f030204458600345410b00060002140c1c210b1400b640105c03001e60320b10030020000e040c400d0114000107010f00500441c5901401001510004011401d0711801415903c1c002d90100d095000003440d80d400e07511840c0251181e50700103114a0701d43c24038400074800c0d01503240109640b00c4c003012600090030b003041d074014507612001240000c5000401c224072070002a078072029a01041a082c160300000031000c0c11203c650601c0c50386c9403134906003071000416040d0065040110404000200400c55004100705203c600384040440b18145000740c58101c14031030f04403d10952071083c0400d41d42140f90040d041d0302801204c4024950760440c0301401384401501c07001c00c4811514509115050045641c810030464444050703180642e21022203060140c0341074020750841c40000c060001c208104034049803c0411960340c2d10b0140f404c44c0c50b43e82c0c1c04600070f00280d20107030b450305040d0300052900700c0404d05481100c1440c0c1400d80410094200402d0054100c00945500c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 686660791 1250 686659541 686659591
    0x120e0301090501090b010510140301061824030f0618050606090a030b1603050108192a0315140c302401020a0303020705031e0d0f020a090e 61
    0x513480c0c602c10840d0b00d2043d0326020800c103104110b2113045043c0650600110094050f80048a0640301c80f41090f0f80c4940c00c2e4195014650400d03002034808180007001075182200c2408007000420195505000b00400c2d0381e024000e45004e880b928103074210a500420402c1081e070007840d070210b4003820140c20050000d00241d8070550640c8140c403d1070b1100e092060b00d080308146960001c0e828207080c0240c1d407415001a940340600c110f215800034181c1e40d04020450441162a0303244101c6110050400010b10020010241d9110032a401104280d0800d040d0202d030003444c403201700d000251012940c0f50b2048042c00c0d80090445003140c0408000d08446d1040c0d003e01c2d004d10107045282000c0f600e41410f1911264944048610105064001100d110f80c0d000450840300c56241c5001368941500d440c2080c50740c000c480100915034000848210800d40c510003a003c90031070540c06009111758001018100c2c03091a100d080018040d4074244030030b0a4a41038507800070002c480526a61079048006 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 686662041 1250 686660791 686660801
    0xf0a030f02041401121e0c030f0201140406110118030c02011823040507080408040909080d0608010b030607031401050603070c050a0b060a06090803040e1807030602091309120e0301090501 82
    0x2c205d54003003c1c110809220380f1444468404107000c0c02480c0d00700498480d00007014481c44010203244183c81942c046912541c1c5485240015040301c541f510744038070001d070125a5510540810b50f10707105a00c0c0c422900784041d400d140d030f00b58460084403070305500111112000001841e800c6020424001601c105004810113030421282c0c0240704401110100b00a840001e031522040108100502c804680c1c640116402c891561400040c1041a071500200901840700744544092411328005a040740641003c41c3c247c00c100c040e00c1c41c9039915603055044481c5070824808000e40b460050100342042001950002d0b43e60502503420540d40d514bc81c41d04440c1c03034048400d803140c0e07414810142803910144015010728282207907841d0a0400c01c60b9240140c2c810b41000c80b405401151a00001100c85c211459803c001d842c102a12810410041c1d881115100c0c060aa22038010541c002284030b1412890b0b4003210005283c403a135074003180c0b00305442c46041c4d4155611340200001690074451 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 686663291 1250 686662041 686662049
    0x15020102040b0d0b011701080a0b0c0315040e1e07080d1704060c140a0e1302091c06140406050106020d0f1d01090f031b06020a081b120703110c0f0a030f02041401 71
    0x14905c270405440c200b85901da000d030010b041c1c0042441400854403c0c13940c2941800410340e000100004407022861030703c20001c01900c0c510355445080c1801d40c001103808410f0701c0c2c0e070300708440c0c1080c0c0c004400c0380c0b00f0354400d28542d40c82c1b0307070500450009480c5400240c0761807000e240440f050540100b1000c4d896210084620115002109a4059041151000f4081d45070450b045040a000341c01060980700004000c030341e42021810640104401d07544000c600b440c89103241d000728a0180380c1100145401c6c010000503204801c0100c0745184521010381203020313955100020308d40c481a00c9101c50300c1d003140181c1405110030000c14807050203c030385002140141e50181c40131640da1515440107295400450441d0045020f080c0030400540855002d00760f0b01d450310046010452200b0b0030007080025019000100082100030302d540422104603040041c81500c4200102a0800c0f4040e1803030444540c00181803d020400305202d00c1d0180000d40c0007070030105492000a031802500402604 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 686664541 1250 686663291 686663293
    0x3080a020307150b060901120207080a1206082404030908030309030a09091119050d0c05070210170a0e03040b040602060417071a0408071b15020102040b0d0b01170108 73
    0x1022401d000540003032818414260f84200101c038002800301e40d43d440b40101d2641400520058203041e500140e0403900c06030f0b0081e244036140e40c0100c2000741400c074043c0001130060b04103d4041001c00000c100d0318441046691300400303c84840303850b12031400008000380c003489861140003500c114280010341c404c178540b50165503500c0c26101c0c082e00788603550f00069889840c01909140d03911002c0b0444000c0f0003080341e5001945245a8219000d00c1030000d12101c01e402c29101418140d00040a8034410744200d660308030501030b91b038081300c0101000c5040d08003241c0b1440402e0340c0c640c041d403200365000114410f50f4601034440d0050f445941c4964880e50040c2d104800308424803118640a596503480305840920313180164a41c141809801040002c481c240700c0c0104082000060807940300a6015003420a0003d040e0415a03111550380301d00300303500000c002d801c20b60b04d01c1803003113900307607080418041c1c10b006a100c00c0c0382c0140b800b4080c2d035050111042028083d01f03601c8120070b000703008000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 686665791 1250 686664541 686664547
    0x2c03060115090f35030703080a0515420c010c02030c0c091314070611010e07090504050a020901181512150612050304170a0309030b04050703080a0203 66
    0x100e0700401003501e907445212468450b002c140700c000c101044a08418440321040303280c1c0f001030000728000ca01141182c02c0c0c1d030b200000b00a410160000140ba22546501c40b0402c40b0760340303c40354200c4d80c1c0310410680398440607401009145913140010880c0c200451b140700e50000e800c0a40d13042035002c58034a1104000404190520000000d00840742034085c02d2019500340401102610b945108103220075204403900c0c00015503200180d1480e06000e80c216070429050740fa0240065111003a9000d000c1c001103040c41b901c42c1e03d900501071a564280520000e03c10301d880c2620b1040141000740c4101e645000b04d88242c8096503038132088501030300a40030541e1070b0421403404403040300c402c031441003201070b038011080054410740081410301c02c0d04030764031602d040c01410842c0000c0074142c0100f0841d40b07a540c0c810301402400400760050fa000140316800004001ca82556605041e40d030043c006459844203200050600140340d8200348554106c0740880e40b00d50f10175003503410440750f07600141d0002c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 686667041 1250 686665791 686665829
    0x102031807051c03211a01090612090501140f01090c080408030a0f0f060f0305011401080703151107060b090a09110d080f03100e09010c2c030601 64
    0x400381904803214803000800d561031602010480400034903107410b101c421556041002d0600a0000b0000d4000d83c40040700c010048641490080400c600a2004d03107026007001c19142d402002c2400c103440072910ba417400d02c500f004103107001d0510410304403050f5496182c68a15001c0148056002d0800c11030441841e605041c50b040844544194010401040b1414000404c02c15411a030f00401049070116407004d090403208054050b500c0d01040032450020000386e02141072143d08241d030310920003404441c14982c1954001c0381c007800341d110309410280040000030310a648034001241e00e94004034824081d0000003880e0340002c0d4003540e40c00d45601c40610b462400303103a401d43c4142d141d0010044101c0d251104042c002c0f50141d4903000c1c2c0f8114901c0000c0c081c4010503150899000da00d0700790f581c5010320b000d50561a00e48100c0700c0079030302d010114170350004c103008001d50300305107a9038080030418a40d0341e0381010740f813103007080c001c040c0014082505807000c1c04040e001e8030103e550420482c5607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 686668291 1250 686667041 686667061
    0x1c0e01020a0e121902040c1e120b0a051305040f29010815060108100b0c1005070c05030715090b0a1b02010c0e09090f0d1d0d0b06210a05010203 63
    0x44a51100f29007140300001d504c2d441c400c110350680d0350151400240203e0b0800b0135280c0b4042d10307154145110307030b661442c41e00c01d5021791550603031000020180040e81100703084c4112040140201540005800504240c07641c4680c011a4081e0040d180748509451035100e484202174030240f0ba50003400310b009102414803080e02254011300340c0313030024011103004402c059200000501518104a007400104000810751106503018006460304195107214245c0070a648400040010300090308200015a041d03000304504114250400003451400a195690701010b00031045c80700c410581e9002c1c900003081d40919410310035a1034450000e81c0d004000f0102d200e0401124040045a0610012001c21039101c0c48a140ca100f0a852440080d254200d100b41849007143c4a00c08510600c4a4038a5184c0d010070940c101b4940340044100207140c0302c040c00415001654003501c80d403201404103c1c1400c100500c0c65000c1960020740f848540490f02c480d0030078030024819202c980d0040240712034129 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 686669541 1250 686668291 686668309
    0x160804030302070e1e06041b0905120601060f030f09080f030709140a051e180f0705030103120509030703060510180905060105090901020d05010b0a030c090b1c0e01020a0e 75
    0x10358a016504c5502d07203091803400260101e00841c0f891a1441c0201e20161607d0b0001800e1840e100b45201c442606490000c246424a01ca43c1c0e2240340422840801e9400219507030703040e141d0a9941c0070002c2c0c1c0b1101c0541c0a04002c07094a034a00e0303610f44a11000c160058003601c031300c1000c4c01d40d45a0702d0070702000c020b01400094014401a10b0005051015560f45c07070514412110151145a08604044030003000c20b55031820554104500050000030304691070300b403078401c6a03c00108600d548030340400319800e002c06d001c01818101115449640e10340030380003504031450028101c0e503045449a68050a545042d07424140313a030038005060061504020840e03022481d90f000809c0307400c00c0b0303840c3c240c0e461304103100317a50040b00d00d031002c03408c4014290100c3e901d061100e20144440d5135a50346100300c5e5030001d80b2110010b46410042c00c8410310484410702103034038010426041801c00d0500c054104a40d034000c1200c59030390941c3d143c00c1c107400e00140c00120142c0c0c5482071a00890410700900788 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 686670791 1250 686669541 686669549
    0x1d06030f090d03050603030a0c020103110c01090c1508010302040b1f080a1a031b011e02030301141806130609060b09030706080907031b051c0519021f020316080403030207 75
    0x5410f10702002101d482c000148c40a1171203a1170300b0502c04036a400140c00400d0003040d20780202c0c10000b5003015000c4150040341d08a0b1094407003144c210b685000c05a91010342d80c1070000016061030040001d0300e419005602880310041010300b11308034078074451b0480d002e412562000b191901e810840030000c144a424000c403549600a1090307042c00d00000d0721041d01a1440c00d5600d0900384c00c80c81c40e489041d28008086c000c0c00c2c4c00c0501a20403101030b50380d03002481002c1c00d03068000c14040040c00d00f0340021100090690284005854180c10007004111001c4500000e03071352000c000460007140c1c010000140020b4980c980c0d6882280285401c005080d0094004e01c000f03041400700182c1e00044240440b6040340c030000c401c010711000c0f13a0f451030b00c0f54811072348a10503182c48111542c00d00808080c09205004940ba030a80071840c140b00c8004040d4060360024101408814549084034545004206481940d01c0c190041d2200314074400b01712400d403100d0301e0100b018410507804100d9007002c0c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 686672041 1250 686670791 686670797
    0x60b030f190b0901020c0d0507110409020603070806150d05040b060603010b031f0510030f0e0606030a080d0609060e0f0901060b0403060f0b040f09110618011d06030f090d 75
    0x4000300034019a01000100d0780148540c40b01800a6000c00003981034488240458055a6071603255000003090b64000b03070000c0d82d03140717040c100380d0301c0070700c3c0a1040c042102d42c090100740c2140d456180c00e845c0158010100e50f0001c0b03845000c4104403041f03100508400340c02c004006000d09050400403100200208001d006140410041c010142640250307075108400382d1001320301740d00462a40b03001c0031a0380d0003950403100240c050006240c054000b641c2c0c00000070010003052200d85040d65450300141d80b000d40681154072050042420343e80201105444228007098044d525008002103c802c0c0d8481c280e0040f0400902c81c403078940b0b07141d50ba0841c04200003840140d04000002c1503e10540c40018400d83d640c00304519614943e0700441c002200080c401c2080784039050460010b1b100d62181100d62038803904030440d65252210984032000c1c9032410310741c0881000001075440a449805000488000b0741704000980c1e070b040015071260740d1040c0441c0c4642864840c6610301084c07200f0900c28 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 686673291 1250 686672041 686672053
    0x17011d0c0c1c09050a090b040b191202040209150c2406010507021f0201060f080105360304030f020a05030d080601141204060204211e06110304060b030f 67
    0xa10880040c5100d9500b0161a1120801d041c205069a00c1002d07544080d410030105080054803003031035440310b464841c00342c5050008059a20400614004400900070818580103040c0544100024040f900c944050030061502100400046a00c08001140303440c001001500c90300c00c020a0145403511415042c42c0c2c0d00d02003600c0c800040d0300c0030080159040200c0416800d042d507440200c80881003c4080101814050300400240601407a004241a110410100050003001481071303d2181004c04403104600d04840399103104110031240c4e00c54001c4c0d8611440c8003a0342d0600c0140f00070f610a10784070035040840c1c81880f081107991b501c403521a03000061106440c581000010303074400802d01e400684c00c0d901405500c4103005e00001705006000c86010041044560b0380140141c83c4c1e104640307101040081408001c5058400c00240310406074204410006280031940d180303036128450115a4401390040e10340325820864090f0741068a9440c00902401d00b07100d000041d82d1076a0240003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 686674541 1250 686673291 686673307
    0x501050304080313080d0905070311010c05100209040603050304150e06040503100b0303211b0406051b2a0a05092712040303020307120305070c0602070317011d0c 71
    0x540c0f800020039038502d608040111004000a800c02c55141d041d9840c0e0811030054039040166440300c040c0003c0392501c1144010018640c01042c50110b80340e840801003010462000701c40e0003a421500285030070640703507800800052002d0010340701424074001441098400401d0050654000e00c5c9150301503002004140129100840c00e2460b064406401040d0b80c4451404a0320311b01c5541c10303100d00b10a002ca9201c00c14885110b240b4065070018680e425001907030b200004481c400c611070800031850030844140c1c0f004104800515000d0b130001031700c803a150080031071300c0c181d0142c1942c0041c10306c001d07816109910748800b00401910301550001e00030f107040c504440e00c01c0015800f242c140c00074600c682910386070070048940850005110700e503e0303964910780030390381303800c0028115400710000400602c5207100c0c1c403500348035007402d694219a8068603100d040084d1300843d41a02040a080320280c420300000060700c2c02403004050205041c00c42900d41d048100010700451a50841002020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 686675791 1250 686674541 686674553
    0x307080d2a0204180b180f240705040b3903180411070f02090a05040206040509070201020c0f0322050603010e060a090e0c01090608090a060506040f02070c06090501050304 75
    0x9074440e4142c600094007030803220040782c44400003900504205906007000201c1c0c0b01c0b1000a1818901c01048a55805603194a25101e4414a42000c00c0e48108603071800b401b031007465155040541820481e24183e00c4094264440c0d21008400081030f014103450049070140c0070040790a0702d6440d44620b11480e401d0360498a03446101e150f80c080c40031038088502140e1311035010b0031034500d450413032541c1c4848a141804e1a01c1000000342e22448030380000840d00085070160318840ca41c003c00062030107003803000f009030001000d0000b004665080c04103002c81c5200308002014041e07201c00647c0c8404500c011a0703039640707800a1019102d105507c040019031a00707001c1e0381c1520b20300480c07480150b031111b020032000340241c0d0020708a18201002d001c400e01d004a41a800c0b04820780c1c40c801c40c180c480c202070310400c100b590b07a5200c035400b0712640c601249560f4800e940214000f80085808540d1201c020180e0300f015006494080c408a02000295086501e000040400b0b0030000e0451405480311 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 686677041 1250 686675791 686675867
    0x90c0a090b03060118080d030b030d0905010f05221a0405030a0807060b0303040902040e1806070809010e0d020303010906051c03050a02070308040306141f03200307080d 74
    0x4226410702101045441e80108401100402c0041030b04003210390310322244ea170312600c0d00041c6010134580307103541e8942c0c1400308070781e41d1100c425107804234661700d0078004540380a42e01c400c40e02040300a03c441c40518940002444c43e1034450703002d850790603042a00c000ca804a101c415400c2c212820802044591030103c0c0c100c031695000307000d0340d4403920903003000c0d000307401c560401e00c0c0d06002c0085e010503895150b9010b00140e07103c6910300307130320b03582c400c406880029401e1811120319031015001030744681c843d90016900c654054008244c0c0d06e2200941403030047d59810001c0941c00c01f00c010f004101e007502c82c40000305412035510740b81103240c5000079080501c828000d010000000340b8000c025000700214401554480c04d01c40c0c0e641d075a4100034000b004144d0f25413002d20403940128091403540c603a0207618400e20f00d490030f0403525565982c3d008003070260300c00301c0002700d40c401a622580c1c00c3c4203c00c006c0040302c01510300300c0000071000708481c840c640d806c1100460100d130b540c00d10a00f4042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 686678291 1250 686677041 686677049
    0x2010b030c191a180103060e0a09050705091501231204030207051903060e01050c0405061e2d030c04090b04020712030e120c063105010b090c0a09 64
    0x3041c206105029060b0302c28402507080189450308440400705000d64010052020b41070100d9004d20030700380340c2c0044040d1031280c41100f07548860364003c03540921680e440078001d680f2410440d07402565510208040240859600035540d0b0880e4102c00b20b56000030b9031040c0c04d80300e1012160120700300400c550040c00703a00709046441010100241c01c050081101d01c0103050010039910a1000a4808460300316490008440725428010303545214041400307003034003070250340300740d103042c10f0401c02070150a40101108000b82c0c80310218590f02826024010950104401d21b842042020003118040f0f143c0c2418000111040800802403a45410800c1c0c9054811400e0b010501c1e03a154000500a4000d4071000751012800343c405000294265100c4400701e181380080c1c41e942c40481c1d42c50b08440c0038460440702190041000550031520081c0e07500c480b11584408030b480014048825800181902c504841580d500c00c1c1c031184602e0500000d0341d110403500452482c3c8420120010103200c905e201d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 686679541 1250 686678291 686678299
    0x504080414031618110c280615081e0a0308100815100503070f0329090102030915070e010f021903030f0f0b0a0e060114040b071202010b030c 62
    0x8442203540c050060012040003891440c1c40c02e921010b450492980803140c6074255417502e400300d101110500c058030030202101001c0c028240c40b00c81c4141c2800200709818050040c00d101ea0b02c0029140e2144001d000c3c000003101170b5041c203080c40300345010000742d0002a03400c1c03c5200c024000e00c002034050305280d03140c036160300d540c2c4403c0d0308200b181035160803090031030040c0d030394a00ca1045020100780c40ba98034410000034660340c0340d00b495118420360040541000308900184003082042d0041d04091038640104680c1c24072140c3c0132050110151030900302c0740d400005200d8034000820020010424003030049140d403c002e000540010b4840d00103030b042c0002c0c03403a4039a6090013480619605088031020355400e8110749402001480180c4070081d0840c40c08501c0303031010440d4070801c0c46c102d40180035001e0742c0b401d0203070000800000070700c024100511121142c5000c80c121028000800c65100d0150302da50300c9180c013524000142c0044400c5a142401d100704c542d030005101049814181c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 686680791 1250 686679541 686679569
    0x10905011103220602121806010e1012110d0c030302060106030507050d1d0d09061d01050a18050d0b0109050f1b09040902030d170a050c09090601051306030f0f05040804 74
    0x11030164007900032106c130319150070006030401150300c2032040c049021490103001d03540e1980c1c80340d20203000081c0a840d90040c03605012000d200907402e851070030b501c40d401a0200003642e1051400100c80e030002c0842124400c203415020030400d0780402c40280504180e040070710441c070349184014124001e0503c140221a110748149103c071842e41c50b03541d03d11344054242e5800b0035440401030400c8185210340c800150f5140d98010301d41c00842d00c4800c550070169681c900d0400241e07022907910380044800040c0710303d00480016595030354105481000e1041c60a50825850503c90320100d0328014080c00c003909580040086c111541c901e50b060200e9201d4502d92540740c00d40c04540100381e007040003905481070864295060350400344103042842086619407280da1104008800d50b6030a07030750b8500d250018044520b00e460305070300744c583c0710300103141032801c02415102d1940c100e00294480004030b0b60345c0c03c61134000806401400003040407104180726030700b00395032075502c14400e03441000340400c120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 686682041 1250 686680791 686680793
    0x90e0f1005162a0809030c09010b030c03061206040c03031d0130020705060421020c0918031c050c0c0709090c030203070b1c091a09011d01090501110322 67
    0x1c02920060301085802c01440543e10380380001c3c02d607100074404e034806e11901d9004c40003440c1c04010b450590b52140700541c00c64440c81e15029190f080038040ba51301c41d180350007030301c2c1b452010000c962045006800c06400c0918508001e0301d40c0480240f01c464141300c2c880f201c2000c2e604032007228208201440100200070200e01c000e0020080303012296821800040c0001c10305c0740010f9018090740c0107003074000b00c1e00d401089000031026034666000140e042004114858a442000c482d8001d0103903414007003c903070301861326007580c0c012084580ca600341080190300f050361500c00e481c0d00a103805101860210b2080304c00d0364a2a0901c1922100381d110a0040c0400040d0340300e0400459000c0d040f902c10a88500050300302ea0061001844492188444160111000d006008283c3d810003024600303218201c10074906c002d0020100d001c0c5640303a006004584048810b0100c60000402c0001501300e150301d4200d0070740303110003822040900c0034020312030b64401c69a41c80d405030070203c1401c681c40d891 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 686683291 1250 686682041 686682077
    0xf060c02091005120703021504030f060b06090d0b040302060603070501050706020d060302100207062c010e04141602060f010608015909060604020c0304090e0f100516 73
    0x8035080700d5013000440f07054207414080029040c007568030031141c0e140c5000c2041c070001c00314012444043d000341c0c003c02100e408100107910081251034003501061030040d2813030206d902c0d4a480300041f02c03800c2440c0300300300c24140d050100c1504440201c0c050004a840c0c60300081160003551000750889500003000c0c070700410554011030080da8050300c100602c006035031010352594454800c2030086811800b10300203280000c101c8040d0000b0000c20313900808485001101d031410308603080340d081940c480ac1c18241e464004e00c094424004541a581c1c400d8003a100242800300c080c00c40c8000c019010014011039800454541c19540700d01419206a18840390b80f80350340800132800304a000802050050512184030000c09509000c1540b0400c02681c1102c40c0d40300c0011101c9084642018010515603d8140c0040c078544c0e80c035000b00c3e42490b45030144042211400b04000401e680709204500c2003280900883c0600307041480c0c20484c030701d4000c0c800c888140c00400c103201080a07600c0700c1c0c001280 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 686684541 1250 686683291 686683321
    0x103110306060f131b090f060c1e1a0109020d0608030c0304060305100b0403050d030c020a0b0a180602040f2621040905070c021f0c0b09030c0a0501150f060c0209 71
    0x22020003031041760306026040c3c5403503009803080314402040c0422600d004048041c401580844d9100486810710422100c01042a03c2210804600e04d6101000d051500c03a10340a040c040c2c5005030303503225641c00700003250043e41c00a0421b410130b10460382c5040c8003106540c00c5484500700803940380c3c0c4460b5000041c4910f80c00042a40394040781c00300920600152888002025440c2000701d60039005080c0d07030700d20500c14028031407801d0a001600b110803c1c2c10296441600c200089020300066842d58260b0304140c06c400f2041281250410000c0314103004240f09507018841484011120820381e626030749081c2ca010114180700c006a4000385100c01102c00800c60400c0c00c00c45820420744c000d00c40c00d50160103074450020354901c03030b182c54022000d0361800c40c2261030310168400560b0341c611508100034444c3d111400144500e07141700600780070164032244200c0c0000380b0044015044018414280c00c00c03000d0003030104061103a10382040983d1505601100d607001c45990710a83c02041c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 686685791 1250 686684541 686684561
    0x3061503070201020c0111040b1c060906180b0103020313060504021504060e031501080d0c0501090602220f030b1503010b03011b141e0d0b06040e0103110306060f13 72
    0xa4000081002a03641907001d4140030101030002e00c034102280581c600240214010700c1546541080054510010084140c00c5214000e20110780d49596403e14400c0761000d51092001218200300c13048145080c1c440c09569a8090034114114145049101c0444590340c2004000981e100c0c0414155681e109141140442c00c803074480e55a5140c80e00140391140041c0203038080e10079080ea211110f04803120b094140e45000c402000c1d909001c0c0001c46031050708900075100795580302c040c00086611800184140c0c803482c0c0c3c690f041c0156400d8041d041c0040b55001c1f0b078030a0340803a4103000162141da180f030340150040a1721141203100700c001074010080070190035031547ca00050104410400f140708051070809454503c452032480261180d01c0c425400407000039a040c0c15011050180f00d0050000c00032100400250f030065900824050b6005400114101300401e00400c10012880e019a0314020705a0103015507040c40404600514050103425208074242c50405a0b2400c0369880354540c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 686687041 1250 686685791 686685829
    0xe0916110307150f0e1c0c030e10050901020f031207053610030902030604020904051c05040f05190509090f0a06050603070609030302120d0e01231302090406020306 72
    0x84120480e4038010056200c4000945080a0aa540822000c5000e99006c0702400c9200b4030108031101c1212400b40e12001182409601c80088006458142148840106646906d1366880fa0100003901d45081e82004018603481081200f6000d00a4010f80e0b800041c0ea040c11601c031417010141220138217280c02c200c11aa6902880b501d0030b40c420340b00d05040b50105803030f800c0541c1c84045088043d9a041500a9059842030000c40d006040c031408081c0d009014009030b034125440d0301c10a030200c8019010010002d10302041c14403881c20b0400c0b9050080c1030443d081d6940c100201d66481c503403031183c82514800c111203400281c41c24070511003220010b2003001a608004914070702500201000d80d8501c0c080d104d0807802082090181d401b01003507a0300f54000380469080022403081560054090f29042034841680d0350906130f09000d0310700d100e645020703080010020614800c8509100030b0401010f103e040c001320000d80ca03101d003c0c94110350000c07405650f030b1703a03180085280150301182c0242a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 686688291 1250 686687041 686687063
    0x7050102122211150d1401060c0c2606070809100204150309030203040807090f27060c03021b06040b0a1a01050d2711060901120b01090806090a030e0916110307 70
    0x70171003480c0c2c007285201c1309014112050380d895940407500741d9004100240b040c440f0901c1401082803004503446078140320030003035800014070a0b040382000070a550010204d44044107203d0004000c0c86038030200c92900c1000c5007071a14180b109451444898020703001c0c0340d80e500300a0306051080c0204c50152107000c003114640f99a60407803200030070700c00c403445140525008038165420030000c42203640c001e100ea802c1e500040307903846003401480700c0311400081c1682008040040d0301c0c044440d400c150403240c080c00803450141860305400310700504c02d5202c40c0c584102e0020301c0c10b0fa150080c405641c2840c02684822a0800d490001e042c00e480318041040702880480754200a0442154024440c01000307810791005d83c2804054011081400d0215180071401e0395a90f0311a40404403003001494400049030380c80d15140d00b8500c0c10344105101c0d40000740b4800502da004100c0d240a80010b95001c00503141a8030101d5a1425000c0b20108000340400c0342e443c00d00782001138580e82e030b402c402c5081d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 686689541 1250 686688291 686688307
    0x1d0f03040504050c09030304030210030207051005061e0307060507020102010917091e15070f0b0901050610021518030c0105070905010f170a150b0705010212221115 72
    0xa900d8000e441101d01c034a00300000a28a03007074090a4800841018006605043c00c5030308000981e50800784003c2099030a00400c1c020070341c10804250803000e0032500003081e0030072800b881222801100200314246011171000d003151400940c0404980d040c1c50b26a0b180c3c410783c40100d002d004200000f803d2801c090740382030720711020100107104280c011200100c500c0e42c18881c1740500720500503415030210000000d0300d03080408a00a0041c6071141e100400c510603a80d9940101080030b441c22280c0b070703544404200040c1421030781840090300c1800140788401c07203101e45401640005103202031142246e529524500c008005072440e01100400070b101519142030300926443c0d19115890001d5103081200b2030702d6000d02d000021080c000591b400140e9907000682000e8010842da6654008101a0010f070303114584014024087c071803400075984542c02e103100c1c01c2c03100d8060840340c46c07400c0301c01c48114812202c0c101c01000b10341c88030312012039a2181c800a10300344103015061219500001d4004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 686690647 1106 686689541 686689543
    0xf110d05031e09060a050a060b0d02220e1605030108031e0432010215070c05070506030f0405010c0f020d05090613030b1e06060306041d0f 61
    0x2042c119581901070100c803012079080300103801001c00d0040c00419070060f182c10929102050141074200314051030300784107c1102e602d500c0e6000a40d81e2900c01e241c0c1c010081e24151040c1769080075503844012a5421003104c1c581708080c04181f80d40065405402a01c0c16070742c500005504040d0502d480b0a20021209402400880140800030702c210712481d4281204070300031f603058070b000c41c4484040c0c001046a55241c0c159008004049080b00b1a52100340e880303051071a00295104150400b0345c10080941c000c103410260000401c030b8074494051840d4002c40c42140204821520403c0031109204a04a90170041c5c014a13640b040c41d80c0300300050940c80100402581c60a010f00e00040001d029561080350408180001c100100c00c44140030301c1200c0b400e151110700341c5419000640284070040c1014412944d4076001c9152883c10b0030003281c04041c0034116040c079503103001c2ca5 = true := by decide +kernel

theorem cover : BRFrame.Cov 686510791 686690647 := by
  have h0 := BRFrame.cov_init 686510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 686510791 ≤ n) (h2 : n < 686690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
