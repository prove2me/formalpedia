-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3526
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:54:59.142721+00:00
-- url     : https://prove2.me/submissions/5bb0ab3b-657b-44cd-9ec2-f5835376979b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 633992805 ≤ n < 634172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 633994055 1250 633992805 633992813
    0x402040909200603040c140310020414030c04140402060d15090b3102090d140105061e090c0c010f0510080f010b0f010f05040312050918071d0d 63
    0x2441c0c8901074a004000c0c074144140c071161611900011007064410303900c0d40c1090794418641401c507103c3c0355a850722400100c4810b9a0600100c2c2c807800d8804400d40d02d598840e51036a41801c0040b50142c804c0c4220342c15102d0b1401d00340980621000c045210b290310355a04d4003484000d41c0102079a1403601e0780c1d0b07201c1802079000110f0000250031720f29000503044040310b0910540a140040e0f00da680c01c48a0341400f03180355500100809000c04000160301ca0241101103030145080351001004000d0b610602e8491400540c1700f40d00c00c5e54103c41c000038040654117904e203092001804d16030440030b4038000071110b03a542d000034450110510700025407000b2503119001120001e0301c41a180d01d440d0310b810000050200260311510255000800941444030001400704119010307042c1800001c1018030101401242560000c50b004014611104032400004180758440340840303225401400e02810480d010b520f09c50301c140003545070160001d0502081c074900c518a01e49141d07000e14166002d000003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 633995305 1250 633994055 633994061
    0x181802090c0f161202060906011a070203061905010501050c072114060702010b060405030c101403090109170306061e040807061e0e090103140118030e0103060803030105011d04020409 80
    0x11240f2051118011240f428880107500711801c102154416001d10501010120b00c9604452484524460b00440e071201075420307008501c4041c0d414001c4c90100050103040a003046600050f9220411450780c031040190307818003600501000c3c9600000707040c004e0700c1800d683c101000403486240d000690513540c90400300c5490501160b10781d013151007888a41a024042d0341d054060840340745050604080100e82c0d11041c8099403803142c41c2c00c00340c90312440d004001d607821946071900050743d01e10b07122024a018101911088800e0b010945032030700d8540d05102a01c1c080e0720700619451602004242e6540c0d08102c1c5444c0b81c3e07095034100000038140308100700d0304000380455203c9042400301501000b1010110102072414400c0d901451151aa02c8200c5141540d81c0030350214110780d005070103180101014006401c002c2950001c8038207040c1c002041004d034103400d076014800305072034004407900c0307002c00c0c4280c82c0407408111300c688001e48200407510514a01400040c2000c1d0307070304040425 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 633996555 1250 633995305 633995317
    0x3240f020d09020306071d091302030105040c030c0603050103121805030601060f0305130b190b04180b070e09151c03031b1e0c23030301181802090c0f 66
    0x4032a507107000b25400c41c20148911584920036081c606a01d1a28890910010b40c4c0d00b04001d10441d290000940c1040400800c11381c0c0e60340140c002c20130740c42c0a142940c03d80050f03000c00d039140310500d080010302501c80d000d005d06882e400400512b003c500d0a2055440c4452012080c000355014080402c80d40c408000c00c6009114582d103480c411541507002400300ca0010701360b003d80b41101c0506602050174a218250001a8159042104c0b590a400e58000300f4603190415402801d01118102d8541c0c500700581c422800b0b00712000c01070302d4110042e510900d107050303090b800200650001d50128010220800c0c0c01c0c00140801d0b0a40b013103002100560390482e0012400b0035903421441c844841c8454100509015900700207500d002c100d5503808042d280c2092842c01c00000303000d420208550161004105c0008807041810b1405020701152290401d014400c2d04040003100207030602400e006502ca40703503103c83ca000d00103001e5002d00507440401801c600c0362943c1080444607030383c0c0843c02422 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 633997805 1250 633996555 633996577
    0x181309080901090503030906071218030510050c0c07030816050f0703061104060c021509040f0c0e0d15051807030807050c010c0b130510020f070c0b0403240f02 70
    0x41c0d50041c18002610350364143d00020b00030307801480b0051040d00ca010440300c007290401c3c2e40b5050403080e581e0850b1000d101940340ea00039107001e0000010803100084080050100c203e060045540e1000100d1950141d0418101942e1203c1010004140302000a00d511450a20f40801c0c149031512810301d00f101002c180d00030796204000400510680344200c80b008080f4114844c03030030b480c090b401451400030400c06032246d002c0080d0114003008030800c40f0b218000280c0244200090604100002c03d4900160008640d800e0309000140c940246058040e031703030140724484208c2c0049085001417000030444049800c1d9031060900d112420401c1400039403181c0c00c7c55a4450003860000e080920580a66040c0b20205404000095100b0710b21760703021443d003c00c19400e54803800d04901e050351224018264034400074080300b035203a848006098880c0501da626861940c0e5880c000000c0c0f050b44030207000c00d461142000c0c0025410403150002c084958800302e1000781c2e1025440890788910074082c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 633999055 1250 633997805 633997807
    0xf0d080103142109011205090303040c0b0301060f0c060e0f0d020d0503060a14150a0e030708060c030c0706200a03050708011a0c150103060902090a0b030318130908 72
    0x10402c51840c40c00d220b24194100508007140d90315000815104401d1401030003444007107001219a4030604044d1301400711a2005c1c4002d0620303810780354995200360340a0f903a140d0ba030b07100400c0040000342200e04071603a43e40d41011004029008440030700e444541110899107400400144050030041d00d01911191000b5201c5241b5200000c1c3c0b0f841040a10502440420300030003001c0c0da0b41d403003240c080f584600004c0d00b010480b180000c1c07282001602c04c4d00500d001091020109502c15400c503040c9600740c00702c07011592038032411035550404440e0314001d21010000070f101100340304064003989128090110b1408201840964805a0308040c01c1402802044040070350358180180303504002c090402306a80d5040005000002446009040d441d90b4005450b01c0ca01c0c07010490354185a012600c65107503075031a8600000500010402644121071711004150074500d00e120300b0300d10310701c0103004520301030740994040440314044155035800a0386600c14000c0307a015000300a4880e115a00003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 634000305 1250 633999055 633999059
    0xc030316030624050c2506020705030303010611120d020d0b120c010f020c04090c06020f070605090906180a0f061a12150d06050a1107051e0f0d0801 65
    0x8000d00c60800445181010b003004001c1107080c0300c80c3c10032100700080422076119654038180558980c8036181c50b880c200d105000002180088001c07204001448032096000e4682d074400c422656528907000b10f9a160f013040004200350f83c0910702145018040304140d4000ca51700e003e07072a031540c0106425405240e00090400d250300d090b07114059102d40121854105641c1031110030303a5401e80540240d041c000f40807040324809008200d0546c25400c0184240180c903076520344080c958003240319240152160741d0501401d6140826004143c81e142d5a4250074100320388204810800c0141c90550456005c41c2a40c1000f500303640100d100c1d00b502c8001080c81249260500201e0f034441c2d200d40001200720100c446400e08010440f4486c2ca0300d200711080d00d03240d0b2000d00d800c450414030300640c4100e00c4194541000445d8218030304c0b501003180c080008001800030b92003c1d20480d1401021908214003403002220250110801c0740b9003c000c841c10103401131a62407521280e5440100403405c01001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 634001555 1250 634000305 634000321
    0x3070b030a1a130f0f09030e010c02040b30010b03030d2706021e04060e0f121906150f0522021303050709091a0903070c03061b0311030703200c0303 65
    0x950542d005c02d294100007415460718000c0c2000c407402003080c10403803807103505410355503076421400c0303051002403540580c41100300189481c0158294031030003508002c02c2a458400c010300c5001c10101c8041c1c0918581803940c04980b0003481c0032090030210001300110521881562890402458800c000043c1e483c0006503030840e0020401040740b01211080205000705079201c11040f8650200751140703402c2e43c203101c001501c20740d002da103c0074040c4100e584100c0c882962a004407200f6000701002c001540000c400100c20240b9400341640ea548c522204000c50706000107444000c1841e1441c104d0003501c015200c8080c2e03071250a20801c0c4100d40386080c018401d0601001d0020180e0010400c8060785c13503940e00b03204030200300c1c0c0f0503607101400300001c41c4e07060288200c4110701e0340030a05644558891800a006244248070740010170105211b1300b030014000d100300214001700280c0681959103000c0704802400031082d11102c3d01141c02e004006180300c07880a41034244001000d0341d01ea02d4540b03c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 634002805 1250 634001555 634001561
    0x10608010303200705220203040b0402010f090302060f0705190c090e0102030f0115021f05010f06020c0d060b030a150b2403040f02010e09090d090503070b030a1a130f 73
    0x42c0038100d040c58500504014400004d0f001c00700c64046d6021603140560050301928464030001000109000000f000100490f01b80800e105da0b1013600c54015042c43c2c244115806440760200a41241040100340800200c100181080070b00ca2011070700703003d03d4070040c5650075002080488400b00300309414844404a030050241542922000b1030652910108043d10081c040c41450580c2c042c0041c1c021440e0710078081038903411030310300794030b5604038031101d82034000d100c00d1142c01e202d215000c1d00440e42d5480440c04072500d24001700710a12011079620f408006000c00f400b100d07071510400181800282c08404c0d4101800c00c02c074800951110b954044c48503840c24114803204c3d43c0038850200d02c01a0000003965000307900507090075169041440160741c0e40b11280c0c0c1c242c1c4d01070001810091302200c0000c9082c00c8840640d03036080c4281d501d800340360740c034400d90094512004080c000610030401c1a401500c0070301000b042c00300d80400c1003010401200c03d1400f040d0103991190200703105544d881c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 634004055 1250 634002805 634002827
    0x8070305090f06130204150b04050f0d081b0115090e0d03180f0c09110712031802190306050403080901051e010b0d0e03030903070308090609120310030b010608010303 73
    0x2000e400010302c410309158803034100411900d084180b040c03041042d51a264030075030040708002c1c0e50360300c83d80d02c07505600c070250068400c1900c2524100070202c02401d1401011011030b6000c0d00c01c80c14422283d26411440403c58051800c66580f01c0300c61034880b00c082400d50060401c5c0b00d001580c00001c0d0204d030b040c0303c044020442814108003a0b01035181c0c1510a12110681022002034195628603101e500c0300c429038040d5520342e08211008400c0b145450040080a01c5444a92030032007803a44240d090340c0003894810420b1198010000260910303502c43c9540e05850255001c030749860780e8a14045440650701640001d019a042098031f50b8240709007600a03081d032100340700c17503003402c644c0030980c507014059400d060380c0103d410000c1983e6900409850081103064985070f20b080703500581d0340c1c0c01404041c1c002070503007004642480b20108036940103117189000b40078260480b8100085950015080e01c003000d0040c5d10000114010102e41406007419031764800e400d500d9410002c1903a180b00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 634005305 1250 634004055 634004071
    0x501090509030f0a050f0715180b15040f0c0e0a0b090a06030e0313150f050711120f03040306060608090610052404290309060703270308070305 63
    0x300c0d040c8041140c00009540028100151072540c07556004811035560040c900c154140c0180403a540080000300007560b6060f40e00d0320703400c03c000d141107103443d204c8103249031014101005a0002c503185400110300711110040182011950704490340c46941203803071503011a00000d80402001e81c1624100700304100500000c101c603410411907800103500c800061007030109140d510320020504038403e00654000100c20079240e00312954640b41040c013090f040e800807000606c44030700e100503a030062007038801c07d5400c00700c0c4032036040e000704c28020710400c04600340300c881c46010509450710380e0800051019510510010840c40d16240780940542e0f8080e01c0d02c2c00da07030003034401c01003600e114003404000c907941141c44401c0518a404060f0401207018084c202405000401250b01c889850051801004010b40e002214406001c2640c00b4042601d0708090368102201160700280309030050584070003a01c120140a8004611503044a96007480c2207002c103903a0020808100e8140c4a807d51042003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 634006555 1250 634005305 634005311
    0xc15030a05011208091017070c0519110409030c0c0f0f06260c09041a15040e010603090c0b03070804050610080a020d05030c01140a0b150307120e0118030201050109 72
    0x1541c0d0704e4603280514035500e800713020303028441c4100e40e214201d410180c5050507003480040c180b002c001080301c111644141d549102c0d11900300785200841c415080c80c00c3d0400d0080002c00100307410800945070ba00e20540820442200c1c50010500c0400c1041c001c02c1d91110302c0545d82d2030580d0070020300348682c4c0400c05002d1042004040742c10031a0310800e0500c0580360324281c90780c6490307a01030709003c1c20f07105036041845d05024004031112000c0109080c1000c9072107549011584900c8100c3d80718a00802110742464401003200a02036003110040c0d0f44290090400503842c0c25084019400842e5038500003100d1070113100522100f884200e41001500e603005460600700f8004650722440140001c1c010010444c0761002d001060054480b031161120080c000300f00480e40f0014030200c00e0303507544100e5240c04c441142c1881c0c00c441278002a01c00342d000c14159074403562b058881c80d19200b45040020b07128072104145000a11a00c8105060100c01c5e030340c0442e06080090854105800803069503103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 634007805 1250 634006555 634006589
    0x90c0206010303080609072a021807090e0a0207150f0b01030b03030f0a0c0c090902010215010f0b0f0c0d0306091a0303040b07020a150807033b0c15030a0501 69
    0x584103140c0d550003001a1884806c1c3d07141d0310350482d94151020311507100013a6180164180200001d40c0d01100f40c021596100426003038040180e031280282d4101000c00c8107a0420426900070851946d03014441901c01414082c4645901d100480030380040100a03036104034018500300a4824110040b0b0b0030b290802101d0072907004680d82c0c0c030803003106501f100b03000705520401a220358003031090103511000d00104582e903124044060500740d08100d025001d0030204550004108040d641214642d140004400d132410028070019841a966207881c04004c008146c080b900c100a00c061130702d456540081c01500e0820960212102d503440318040c02d0603c42400c00542d030001c2501d0a441901a0781651003e051001841d110300780c0e401450060003007260701290305d400140306482080b06403000d000e00109041e130421400c1e01450320044022000099003030406030340085041c90303d4280101e83d0a8040400041c008402d64000c10f88060b100104020524102c2d019150040c40c03200460030100d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 634009055 1250 634007805 634007807
    0x91204470a03050a1e0203100314030a030b0303120406110702030327030123061804080c06070f020a170d1103040215030720011b0503100807050a05041a0a0807090c0206010303 77
    0x1c550b94161902170790040046440840101e01000003558802640303c0300da800e02c124180c403600040101000319183c15003006907030501208549102c02a8045080a5a2035581d10b000912202003244001c08041c404c503001614104020101d0300b100c204007051b0381018000d180144044510390902a9040c000303118004030043c100248030b243c507403038140d64540d100307804101c0b0701c0c0c1e1a8402c1c8081c11021000d2000740b01102005168000c01801901d410b80d40704401501c0c11300a5270340d414016844020900007240000400180503184401c00c240f030051024080b10a4440e01c042e2690403140000c03e00046141c0081c000c0c0f46240003001003402d40ca49190064150400c2c00601d8070b0b0100c10035220f1700a90030a42c807551050044803068142521050350080c400c0e082112014085d800f40100841d02500c0000c000003140e800400c40b0012500300403c1c880640040881481c044001c88440019507a1300d101410217400e2150040c040345240074a0780007a160302250803c295005400140082 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 634010305 1250 634009055 634009091
    0x9090108072709061d06070504140603040f02040f0c090806040c0b0a170c120901061505071406150a060f020a0602090d02090f091204470a03050a 64
    0x30b0024101e01e00038290966102e54080d00e00303400000c000d185070074001c40c458101c420940030360808203012030340d04c0e035100c00d0b0640d060f00c078a0142044d0341030800e007451128035041c4011640948581420086c50722203a010030165a00b510701080a152100f2001441f1540b001f0080300901c0a0002403105042c2038482070142c0710240078442c1c00040c00a00c03030920300e00440c519800516100742c0700b021440e110104800d20b801840b013040e1001c15250106110030014080c590a132940800c80311520b407143c84065030303181e000c81c00031258031960315007580c141003050001038440c002405410300356802420400c0910805501f26200f80044180c105000c3c1d0b500080240e0200e520910060759982804001154921014002036010444c0030803c210200c018000501960a140444820f4010007039080c840b401140070700403902d14001000001544410a800402c0ca5400d5a075440013100508000203507603071007121400441c00061030030096034144078440e031141030405c0030020700d41035400c0d103a12 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 634011555 1250 634010305 634010339
    0xd06050a0b0613060c030915080604050903070c0b090a030507120525030b040c03060507090f050a050114030a150803090117130605040c0b0c0a0b01090507140a051b030909010807 78
    0x10805c1d50ba0b86031040501501e800c201034940ba14151500c1d80384048020810074007192094050780c100004110f141c48000283c1c0c00d855844031012444908000b4541c4032034016001e0240d200e03207085000400b00e081440000f020b4212896821904455818214903008100710766a884180b414045803000070b0710f0f03480800f1b4130381c08000c0368400c0e112400e11304800d080f2030704090402e40c580740901415a4002031440112102d8406540c40e20340c1e40e2007040b68010071440f442d40465500c141254118401074021988a601148005511030012144124080c17854111120310380c40083c9012056801480503205848080c40d040c829140c030024854141040460080c043c0340c99402160410803014051005405407428803a2645c20b040c030f0180e85d03038040340c1003511790001c40300011414013030318050284500380a444034a08902c0161150b9200d52021070b2070010420244411040d1810380000103268800c528015510b8407202820054a01da041c1e000c0403850b40700d86000c00031107811a442d281 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 634012805 1250 634011555 634011557
    0xf02191106100e040b0a090b07031b110304140616030c1a010506120604271a1308070302070308030a09050f0604021c030908070608040b01060e0d020d0609020d06050a0b061306 77
    0x10340d01d8004c0d881b0003400d41c40c6002071002250b9010000c0c401da0641c840c503194a4400400c08600e8144ca030150303900d04d00301d64000444d4000b00000d0080b060a030701c43d050501c030041c0c0098909001100c00c040305115a801c120300144124500005001a004280c10001118088443e155141c0700000b4154030a06481c10710201d1000c0016120f9540d66000c030340ca01c0204001c0d10000d524602d160283c14403054011034240e45c1c19800c440008404030040e13840703a08402d8409400d04103688502610360030802c0c00b141107114600000c00003c0c0d084000e103020f01d0a0610208907003000303241050911808440c1d01c200e603444202044090780e50100340b80c01c542c4484200d8101001d0318203007100c060500c1e07003003840f0390311035507000152590b80006c00c0d510690051480f09403903621103200312a50800d0314105c0703511000300401310740507107003000840484074429400061020300c1503010880b2040c031380d8829200c2580c3c0c0d0302005241041c1d4055502045000c0711a503242c01441c0b844c0d00050644e50103131174 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 634014055 1250 634012805 634012823
    0x8120c1b010309050105010b0301060f050403050607051303080a030b0a09020705060c220b09180705040501031d0d090f09060302010816020102160503070201030606210f02191106100e04 81
    0x69059020341e120f20700c095000360082c441980c440c0320581540c0c2c002e110702000640c0700d03100c00c0f480d58420f80907a0256a03111000d0486500c4d9454200c07141e0b0031029802c040c01a100384000002030f081002480c1c210500e407004100c7c1c4451104000428145030720080980c0d00410210002401c04210981c2c455109203c440d203912101400e041d84c2100c1500202404842c0100401c00b0001100a440390130000c840c04280540303030404040c0c90b90800d48840300465810300081c00558003a13005100424070200040b54419160000b45180160750700e00d2802240341c00d0010702040343e00d0075071400a410154014001c0b680746500007041100c004181c11702420300100100c2001c0c0c402c1d0111100c24a12140700c032980341c12030401944a0b400b4500880c080307481e0220000e603280c0528142e180c56040b040b112103011104000d468054000d040e17030540141c0e420404000b41c080800000c450600311036407901c3e200300d0400042c0e460000d002d0303c010410030345180200300040075201301c0c66200307501c0135001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 634015305 1250 634014055 634014103
    0xa061106010e093a0e091003020d080c21071403160f14161d0c0a03053c0c04030f080a12020f0304120c050303060f0f030d050408120c 59
    0xe440c0071381100d10803009a100f26030511195401003140c00442d8040b151105039807100300081c10300d80c210b4803000f034001d190110201e0109086601a0481c41c0203982600c11070a058100c444840030007503815902c241c00131a0000c20b100c08140e1184045641200840c548000c2082074001c0103c0c0500003440b46d203050081e20100b00c1c1d451000b00344803008104490700704000300054035031b0880e14081c286041909a0180308680f40402c0024060224000d41910b014084902103015240040000b00209580c051242c2e01e9907040401f0003040395500103440c0c03112950f1003508200c506c06880c0200d4254140814004124803c203140d800b1a402084640d44444000081d2180300340c03561000c1035144041b41c042d4820103c54015441030380f00d211070000d1030805c00000ea0320034800040180603980148001803090402010050444400801e0303001a4440c59001030b14101d46a10048000349006c00c0030402c80d0800c009641d4101440500103090072040c0c400150b55007181c4480310000d079600c4410b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 634016555 1250 634015305 634015363
    0x160f1b02041407090314010203221a0a0b10030e0c0103050702070e0112020109050420090a0305030c07060e09040302060f0c0708122a120a02090a061106010e09 70
    0x3884407560b282869103850202d401038050f1480e4401645c055048030101180d4020610880f40b00313840c3c40010101e051007034074281801d10703030500f400c540f4905c117110800c0c00b070540356070200c4c422510341030007052401380103003481110342c030340c0b0740482c145030603c0c000024512003c0303001c9a1100080c640041d03030350345400702245051a01c1e03101c48070308040f00f0300100f504102107080060183c000e89036410244e54400510080700c540203002c03554a065070941316a0404070700010718421400501c080c1d030b02d80d01ca460301c0c1d0844d03002e0540d07110564446002040100d03045034415842c8101210300c0444e034503142d20003030340340d1200030b00d8076800048038400903610700242426038584a800c2483d03182c96040e5445040c482311801c1e107442c076080c28160030000c05440414810001c064100081c1d034149000600300c1c2c00c05a60245c141441d45400744a2b00032181c40394624000100110f80e50b076003c0300d10300c42c65030f4141181030300300c407083d0211482006004800080e80346480e5040311350004129881002d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 634017805 1250 634016555 634016561
    0x603130f02220515100c031e03020408010c0c03050703080714030a051801020f090904020d0b040b01140102030f03010e150301230901020415050d02040504050f160f1b0204 75
    0x34020b40c004086407001d012006074549103980307840303034460811103500c6158100c070100703900341e4240e540308000c101c0841100707104480c04000c03580300c0d040161011494404d04c0c0261307800c20040305c0000b41d000c2020400705d2801d00952050700b000b810314030396100081c0c0300107149124000c00079050040043c0418070340e0340300d1280c5c7d03129440c1904d18a43c0701c0c00c0240c5001c001d004144d415001c0508050640f41a008040c42142e21000307004146a14180c407901c240240814000c20907688046244182d030301150039100464030032441032a404101c0e40c1441a20034600c0c0c11840c00904551040c058100007203010022a8107660f40a4654070041d92030721501c8090300c050f0b540f055095400e203042c0680005034941d200e00d4074202010b2440e0130350b4920315070f43d00f00e000340d100b4448a103041c40203040807a0f010703900516504000110161802da00d450201d010b03a9402d072001078481e0000701c1000301712581c5107107070b2100b02c26501c2c00d1110041388000c014a200c42100c404280605084030b84011541c95074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 634019055 1250 634017805 634017833
    0x60f0409090602030702011b0f1d04020309070602072c18010c08010819120509030a1a01030209220b060402070609060c080705120c1303150b130902060313 68
    0x40424885244549880c1003e03400c10707030324038016600b450484000301c04030ba00828a6001c9a030b5070040c1c01010264200c6039104080003d50143d48580340c0d6229a40b10350004501c2102d80301c0051001d50b160683c0286007059641c0100780072100c04900700b091310a401000310103100d900001c0c0000341ca404401c0f0241c0d00c440340e210308107503281400d004182034200c60f06e01d04990305031054804248410200300b040315104075000340080800b1a00c0309201c1c0c021006803a20b0030028045072141142550f50b01c448560300c10806a400080000410071460554203550384031007a09411080d691014503540b108900390b00000340681c40d00c400042c1151a41c0d0f040c0d80c00320350072200c140200b18440c01c1c5a00200103c2c08803d00081711840010b0303002d07020320116610701d4803802d400c07007817a616102d404d240342d00311070800010904c004c0f800002180c265452040050881000044c080ca071017002c0020303501718800110b080908001907000541e40302c10959601c1003c0c5007000002c002645441c031140c152907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 634020305 1250 634019055 634019069
    0xa0e10031e0b090c04030510090311030f04090c050c19030324090b09161d040218010e2b0204020c0a03120506010503040c06050a1218030315030c0302060f04 69
    0x40ca00c0010350412a4001d40b602c24015628007035103854409070000d440c4a80c0c040a0103130340c001d0803030100700d801991045e01a28007038a0002400ba0846001a0955015034a101070340400400d00f03002c41d83c4c1c244100210481036003040741c50056101902a00c2d50b080070070594900032001c1c94441418000d40010820413242c02040d030907804800c140d031107403070014014840214542078035400c050070700f080c0890040f694003451004250074400126010541d00081c40f5609405000809064031a80003402c221907454680072641c540001c00100040c000d4448148120416101103c1c0c581c0f0000300200220b180703113001c0032001480c0c00801d02900c540e1071204158400c00381060145a03100e4500018994401e5046c030140d1542c000446290000340e80c0580600700d071420400c14580203000810001303100307080542095500c118084103da01c58908510320560710703034007281055818418800d00300c9104400000a0703055032034031841c110035400000c0c022507000481c9090394141100f60341c018420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 634021555 1250 634020305 634020341
    0x106030c140c2406090624070b0a05070905100e0402041806060206150612060f03010905010c0905040207080d0b13060308130803070302060c0f0c010513020907050a0e1003 75
    0x203841c596a84404a0407958803150781440c42440c180c02851000b40100c500a0140e05e8544550702080769100c07015841518011100c1c0d2090402054031f40034282017406042080c481e4035090560000340d0303a00401420400c0034400b414000342ea81c08219075a50300c4a450072144030403c10000c0341c000d00c1203030480c00d604400300b04010401c07041504000c0a0312015401e45209032180028034920101c3d200e007540c3c0c8203000380482c80c960503901d08000c0c0c0c0003c0040c0042d8401c030f0b400c0c010a08648000c0303000d60b000d944460101e00c0064212048800400044e0b804518007000768403280c400c1c1c007840b400e2480503500c0750400086965114540b0101044c403200402141d982c80c601002c865011044442c50716120140018000c00080152808503405402514080e6200200c3d001658004900e0846440040c0010360303d84001744200e5100d0f070107103090748002072100d00400c04840d030003c0031407041040400202d0245648510400003c080948581c04c0c01e0441c044280c001e880e500e080302090f062 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 634022805 1250 634021555 634021567
    0xc08030a0213061404030f060b061201050a060c0c0e061f05040501021c080f100807030501050a0e011503110d0b070509010f0318080c12030117010615080106030c14 72
    0xc065009051040350406403401a0760349020135101c954010080c0f40c4890030500080000c5041c04594000b50342c4600800a10540544006560703078100c1503181031001603100c01031181c0d0814600360800b400c02410890501d100507507690325018000e000708400114203c0c00300f44c0b01d407242c41c0081101d40b00c2034600342071000680002041da800c103118040c0148140300b00c044008461040c004000d04069036620829501d1140103080341d0005032842c2d090388803002002600410a0050038080d41c0310302c0010803941440400003066403030790841c64440364501000d60004501000840301100d503c000d040044005400005881172201701010740050002010007500a900c074004191000b004d0f200d03035090f00c01e0b104046040310101500358008c2e81c200c2c01c101c00460907020240083c4811807040743e04540060424103515007080e0301c1208c8200703000c075413a0046402030180d003001c3c00b114544600c005483c00c50090441c2d00611032142031680c0c0302c1070404581c0c4540c0c541490550f4021420365610303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 634024055 1250 634022805 634022821
    0x201c08071e030f0e0603070305070c020a1202040605040b1f0201020d020301090914010c020613050a05030703030b1311090402090616050f1608031b07120627051b010c0803 75
    0x101d1592000c9000818038a2901115802541850080240a050941980d0f100201503004040282102e418080c2903000d0600681d1500942d10240825021800440c00c141c8180810f5540c00d0700101c0c412800c0001004180d15a240070003c525200c40240e03e101d103d851b010f07030092040000f44106280004004201c018041c0c010341d480358400c1407100103151545114600301ca141c0d41d00d5a00580050020070a070003c000c048124550248090f550b25122941d5890301e1a4880b40b81100800d440d000d068030309141c02c1414507444035a0610a011000601444500d2840f0788502c583c03045502048c140e810b502d81000350b44542c2e8826001700c00b0592241000c9a0320001c030300d14031a05101d500c1400742d051455444420458150030011402c103907170241442c2034249000303003140d550310a10000144418003100300d5076180d4003407580015104007a40040c205001456204014800c1f001f280e400000c200084e0f03e0740851903507a45500030950f1030f0040350503103000714020344120008000d000e404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 634025305 1250 634024055 634024103
    0x306050c1b0102160308061201020d14100b371211070b0c0307051e0306031203040206030411031002180a0909021c030315060c201c0807 60
    0x4046242031040e0019030700c503280c900b44d01c5400182c1030040014003044001a002d4014030350041c0e0024032048120b07030000a81030880c0c1012100444045d01c85801e0150f030007203100081e800c448106042010b680c20078004640500c2056400000f41ca0301d00f0240701031321280707500705125900c3c03817002c4600f04060000080200800214401001345024400403030800e2181c225403004d5400540c069040d9941c1e036044103103401c014914024000100f20300001500c41e940c040d00c025221515480d12420310505140c9410b11415840071420000c205020160781e50b80203407a401684040400340c542000d83c0442c1c145034035090f441c50701030300201c0d102d03490041001c0140315040003640e07462605550b56005d6003c0d0743e0f45000203900f01c1c05940e0b00c140409180d0203081d860030b0003402d02092140f00210b9000b54951203900070400600a0040f5008109200201d844642141c000c41c1c4400210500060100342da01844101c044602c016104200180718041d60041c0d9004030405000146582c003240407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 634026555 1250 634025305 634025317
    0x1e0d0905062a0d0e03070b090d0503100b07052104060e03190b04030c020d08030a0e0607080a201201051c080a050a020c0a0303031a040902100507020a0306050c 70
    0x8038001d034000507202d02c4044024030301d040d02d81c50182d4030b058500c03624059568880100c0c04841c80e1280900c07a055802000180300706407003104024050714000700c8407410103510104940401600300140007034082001921400c0c0e50f101c0c1c03e6103560b0400391814900e0001d40d842511660604907a261103031004c064043c000321465512a00601c0d03410804164440e08d42400142c2c2c07802c079030901c81003c50070803040c0d075a10610a003032001d800c2d10540c00003540500a28403c80c1e420400100300424511640540e20f2100d41041c0206840d0902c0c007000f500340304000300703003042c0340f59a81303210b84044040c03000809840d10b00d1601c607540e03200403800c8401007020034040c041c02a02144c44552076801000e00161003650481d803118103003032480303c013191680e10004441c0118417600d00c44041e96501c1c00d140307900846c4a80c6000401d04524031001445410030030100344514034028074000075072a400001d40807440b21340f80842d507511451000503e5581c00380c20280c0842d01d0442000301c84009d6000401c0303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 634027805 1250 634026555 634026563
    0x70c0605040915081015031704170a05120309030f0301080721030c110f1f080a0c0c0204230a02041e050f04110f1303170c0a081e0d09 59
    0x3c880c1030300f410481e941a2030b41c072405500b54884c0306031151030030945d40503640f070608081900c1201750366a2200403155581541106000c02e000400704607810070304038020b85802003070003e8181070313085484a54035000401c4038035159481c00000188024414011911007070500140c0540b6035840d240f50031b65402c92030040001050720b02d040000505a40081c80380f600764160748169a504c12542e230200100701d20300d209500000e0030050310105a980c103500703ca14070b0180b00740c1040380046101c024044040a02120f98503490003803c00362030303640074010364812074041d100421f00c20451600c40d00800c1d4081200e0344043c0b079a209005128209800902c00c503403140c1038119803010303407400348420380300c0911031241c1c02030f40401145280d04268004402020b0480f06c1d00b401c044c1c1c4044034000c40d80c07000b91100318030703805141c0510070044032481c405400020b00700c18608001801174925994061594050300c0c2200c089a143c03059448812007421a00b4030100d0152200d81c03116405018142c0d081e0115 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 634029055 1250 634027805 634027811
    0x1b1202030606060f0d020c0115030303050601090f0609060e031606020304031209050108070e0406080303010f08070e090613060b0307030b07031b020d0c0501140405030c0d0804111005070c06050409 86
    0x240780b40c9010029203002ca45844242c40c548510280520002e40c01900200d089540b035020703810710b114110f0f1035140114003a44020501c3e00e008800104128900e0700182c130030b401100414424182d100104e5400ea44690512030b1640c440000040c1c42e0a00a4003141505c540c0004017103447c50740440030748205ca101d1030804803600d40726501915110707124040c0500150102001403c0c6c071b48100300104502001800004d0b035140c5889481e8150b5100b60001c107005d02d1204000c1190800800031b080041038003e12110b640c1c1400b200e20b5440d1400076003551030701c4040041403010b000c550785c00b065101500a04840d1003540e2407810300c00ca100708840c0a0301192030042e407803002c8203407405c1a6030003c61a070b0180221421840040d10031a418a9080d1510b42d61040c0352204045c80b148102c1c010342c0114002c40c0c540e10480c5400303160030081010303081041901824400024610120f82d5030340c0d042210b900740f80d4141c0000c2200c4074018004040c01c02d103100340e070029020f0340000040c0b00780c0701848428 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 634030305 1250 634029055 634029061
    0xf070c05101b12050c0f1b01020c0a09050c0c0102030a09020108060415030308091f060302090606040303300911041b050d02090a03080c1609140a091b12020306 70
    0x2641e40c00082801082d441a444101c1d01c00030301148680d100c0d40110303040c11802d15001c1080f0510308040d111403213041f0b41c0042200c41c0811a65404411a00300910041200d08104d20209a01c5446031140c03240d0241c4603c00b280002d80401d041ea140c07d20b445008545a10b816080e40340a40b4076814240c0c041203d60700070034880d003414010b001c0700880e500c55001400345156811141800f008010001d5806800c400b08201d0203c1848840800030303030034010900608500402a24517130181400c0c0c852141000304000007a081034029503201110400b501e10300304030084d4100b0018204800b01d001a2405281034100801c038181442c01030340a0b2020042c42902a0007041503000f91004040403070801c0c4540d801a810a030020841004080c01c000541070f625a1904140d4200c035489000540294000c21207405400c442ca100800d00c00c07000303102c0a4020030100e689080040c01c00109903882d05110400e210b65020300c401c1d91448480c54440780c035035680000420030fa09000c2244280950703008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 634031555 1250 634030305 634030307
    0x40b0604080a02150417030319020c100f11072303041a0304020d140d0e0109120816020603090a03032a0f020f0303040309050118030c05150f070c0510 66
    0x365000e40d0151001840b00151580800461850300003415205807810000420403040d0364038090036181024004644a042c902c1140c401c0d0561014134060861040c4103460045000113440c481003c4010800140c0c82242c001070301c040c165440d12502c200b003002a4080803c28003900381d03501c001d0241101041035001752207640c1c9038030032403266113a500c84541100025141000084d41c009200a240000414030b59490100311000c1c070000002c03e800004505004a80098400340b41610900c0c15120040c2007145915002502e0440501111310124142052003050048044120b4009091341c2c0c41c0d00d4999025540c44640344411400242000b00701e40312014500b58000d9110030141c246030036012025800c458440c0d00e0400701086100e0115810909031040c401136000354080d41d9072002aa08210002d0301d84c9900b1280d1000c43c199260007000869083c2031041d06a601c05c4400030b03011031800001603120b0103031500212100c040002d0302000c11901c90340720021580141c81c00b00000561000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 634032805 1250 634031555 634031557
    0x5151f0308030a11090a12020108091203040303020c19060c0e0414011502120703020a0b1509010306021b0313030204060b032202120303070932060a0c02060a0e040b06 73
    0x100c010003624007400410b0b40d5100f1a081181a40f0020454504007aa50b10000302440400c1d03104a04960940c21b0000540d44d20010095110400c14000c2c070171b144851900d407029220060014080650200e032444052300203100907042c0041118141c5100f610134100701000700307421880040841c50158044500307060601440060518403a0241d019070f00e0f2a0040502c00c0d0300401060840c00740f00312541d107801c1150058103186000760300800b4403481910b000040704102400c0f584084400145000302c598880c165281034a90048015803151042c2814003800c03000f152481001d4000810b03140000d120000048040380d00850741400015a1900700010a10084c0c0318040c2c180700d1a0452180e03c004060403c509902c00b4180e40b0f02c224126102c1c9046800582d81c1c1000684200420012010407031900741030040302206880031041c2000180c0207100100c01841c0c0201d0001c1000013140f40240d6a0a44480d005000180c0e0b92004400c010072000008401600c40c1d0324050003c00c0c0c1d400e1042c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 634034055 1250 634032805 634032809
    0xb190611010e0a1403090a03032102030f0a0b0102120a030509011b120c2d030c0e010516080909160f09050a230a08030405010813030807050703050705151f 68
    0x14010740f0f0003160355101d541c90441040c1d4103e410340f20420003858162100a9a0001035000f0342d101840502c09103207003a07465042e80c00900b1924010f0042c85034004c1d040e03d035076811016a5200140861864005070304092144c58111030f18480410a00b0340c49405422903481108588000c02501d01c0c09090181403856207410301000445008078901c00c5d41a55001d880a0003503400d050b8500d8807424181140740a080501340303416600c10a03442001601806a40781d00e031900d003416040d83e116980020001e015402c01ca82c019000758060f202449001800c0f542010310250003540103103405000e070b0b08c1590800880700000f038800a90007140ba44111444025114000c10790b05d4030500d0044030719103c944680c000030040440e9078886200d07949550205c40200507190142d9219450100090281c6000270306c02d01d814180781c0001e00003e039115191551040d00c44c10420388801c064101100d90340a1160028810711460140b098880e4641a245104100d160391058500551485055403d0924 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 634035305 1250 634034055 634034081
    0xa03020d1b051b010f05070e0306090a0201052a010507020109050712050d120b0a0806060a060e0f0913080c06040b06010c03090515070503040b030109050c03101203030b19061101 78
    0x80c41103c1181c0f0041c482c4801e00c190320710020489a1689890700304880058504201107005440c40f50540d0a0911525600091030400303070207001d030740c0d0b0000703402c5210742050f0130300c50b40304003880910101e4007140125141d00355074001c00c000e140660029008000a4500307035401d11401704000340d01c4031444085a0016800000303000718020301d120540c0c14008410000c8803003522110400e030340b901c03400403040040c0144402040382e41086c00602282c00d4147c1c00c81002c00c060550221040e44690780480310084050f03580034011b590313681411540c50001080200200360004292001250008451b8042d6000d00848001529040010760b051420341d40c00038041400c144c4104aa0729040c43d4221300906000079551502c0c140b56115070855002d9041180700780004070040c055408a80720b91548102d60303d100920b141070421145003403660368030901541c5075580c100705040500c2504103051982010f050110303a11281003103041506040d009220004240d4064010001014040c4076000800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 634036555 1250 634035305 634035307
    0x507090b19060c03080604270c0909050304051e090c0414010c02130515060a120507020a020d0821090a050f07050f0f0619080a060b030f010b090301090501020a03020d1b05 75
    0x890340c041d40d17081e200400b0154090760b6800200a0316100401074045000d0030400003801c0001480e1154150341160000c3e1003503881e0608103000a400001120107840301107510401480c0c90280c0c503d820f040f030303c108682103405a0188032510b03007403001500513100c0c45100d0a42c050118001100c2c0d40184040c00796004d01070901c2d400350403201d0f611154104004041c0e5051103000040411020f51007000c494001071084010300d00540507610800390807964500c0505000d048540009407600a0307070b5000b800c14800041c520810456a9140c200d0148a1102d03600140c0f030a00c00c3e840d12203290400070740312405440c1c80b040c5881c00100b403540c191000144260950348400c01800300c9031000c003a00582090040095280c07048805011218010007a528100c480c904604001d007a00d1007580f100010b5902841840140c2d4031003170106064482c0c0840b001d4881c420800043c0c0900401d00c0c1c0035040b0351000400042d902c0d41a001031410741e4a280b0107001601040c0030140f8000000c8c0a0320001405c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 634037805 1250 634036555 634036577
    0xc02030f04091d03030705070c0f0e011a1e0702040c171909020307030f052104061b0c03060f0e07081902061b1615080c090d0507090b1906 61
    0x4943d4001d0942d0f0704050483c0841841c007502252a40e8029604000171540110700ca10070420400060005407243e265204202880c0c1401c668401340107026846034581c0b0456416010421542a980b203905d50b130240514542440d0b885514690205006074043c904080d0b0f2499640c0c000c44a01d80c80b42a61b010304541a030311400c0c5020319240402d2044801078595941c0d0340035941c1001444051070080006121500d0700b807414500d00f91040710620842e88911030520f034202c0c41242514103e92460600c0c0e4510003103607120740002d14071400020f1942000700404018050258890000c48044020070040c443e00e846115944004a21555000b50300111902c1c807c000c07602e0251001500c042c0001e410100d202c490b144050740745c400c41580301d03400540510f069085503c0d120008112980c4101080d40c2e05041c0103018050042c8104e025010009004e29241c03951041d03066031503080700590b4002a00da1900d00003405840c440e040c41401d141044440039604c071025035040b60b4090f2900043d0380 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 634039055 1250 634037805 634037819
    0x4020109031506030212030421030c0f0c080d08160207050307090b01110f0309041a300d050c0c010503061e040b040603080d060602070f05010537030c02030f04 70
    0x1c40040281e84039503d803000000161131344581d52900000200255031901d092000340348003d20341c3d1464030700988a68071101c0219401c0158426069041410042290300d1400c20b0180d07005260b2003c5035501c00c00c41c20009003070f0301c00200c0340204200e4950a030b0445104200300e030b4811550040681c99001440100014281350f40400d00c0703048103042c00c00036540c401c1e0703149040145035150b0a60795040090b41d8503543c03400d403042c800384a42212844001c40030000c0415500c02201d0030510035030548907143c20318550754440341e00440c10700c0d01c116a06003507281c07801071080e0441c0340d408038144900a5070807100c0d030246060701c2c03140c0d802805090743c1480c000105a100c0940b902c4158201e23036920007012940d08e80d4080d109c00765001e030600f59503880202215200725400796100b4011504000028401401e070103822404032a400d00e02070b900e51015040c07203166a650340e608400c50b01d001c00341c1c1d500b41421600344d1701a55003481d00d041050310b88002050343c49110f07103a0f040c11181c000300400d11100e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 634040305 1250 634039055 634039073
    0x30c03021510090f0b060c03070303150f050402070f120c17030f06010c0f290f0c03070e0303090d0506061f0503061210090804050f0103090812090a1e1a0402010903 72
    0x704c10740c0900480c6032041030001ca410b6500c00c0a80311003c1c0c000080c8042032507014080c840c804a07001c0c41503070070705142000c1d2542000305806094070a0350002041c900740040c1c880d04051868000b4584a92014138a0010f030031f1100c4a40212034100da454090f10b048031410b0162803040e401c80c3e61143d60350b0744a000440f5103400c028400c1361000c10443c2c0841c081407816240444240c800000c902c981c1d943c400c01c20051080003092010354000103010002c401070f541007a41c0c0c20000e24100103500e401e80c17000007829405800c50311500070b1a211089000e0110000b03001340100d01c2034503001c0706e085940300c40800c4c0301900c588031000b1500c00c001040041c00d03c2c0d054031060b0f01142c0f040e030b090507001c0711140d015564050020380324030b45e000c00c0a002519111b036440030030a0302401e003000617007200d943e0015113000b41c452164028154500095001a05010011040742c1c4182140e90b4049501441c00b0171480305c08040e684140030010803080704007808400b500035a0140c4940b40716524654403c43c1c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 634041555 1250 634040305 634040321
    0x507090b0612070504170c0a050118050d0b070f050c0c0d06020d1805160e010b03100f061814010c060e01020405040f1a03030f0414030118030c0302151009 68
    0x81400c21100280080100751240210311035613034030755210b142190f000f00f110107240c0c10002c0750300000b10104090351182d400070308980081c203001d0300e0010207642c690103840003644900e4210308401e00c010200030014510b46c2c429131460312140c0902e603a00d031044641d8046c07405250140d50080c40100c25900d420340358107131101d00c00c0101610303100322584a43c040e905d2400007001c2101803481c24408014007440030005d44011049810049860010240d080d010184525942068000f0200300303040806191100038005070442400501c1c0c0d502d0006204030f07500c03911039140c44244003000c14010080021100040c4050b03540c800b0868044e25a8801005007075203034005d0750f40c01c000c0054151520b009400565901401c0001c103540900008031124105004140c4248c204004034181d000c0b900058600703903807001507201400320302180401d00410700d003203091941441c245015070400d513100b2035a0000c0c0703100e5801d5a505000b1401d1054031520141c2d0386d5240f88060410a1011082981c000c8038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 634042805 1250 634041555 634041559
    0x3080406110a0c081b0907090501050315041509050a11030415270201080a0e030f0f0c010f020309010f0905101505090f01030302061501020307080a0e1e011205040507090b 75
    0x715081a541d541d0350410101e0f4040d4007030f45c0121102d00140e500c1d03c031402c3c0060400b40d0f48100a840c2160004042d0300c480c2c0100350601c01e010010942a840d1030500644240c0c000e08104910b5440c1000080c0280440c0f1420248904001c0050b1440320303103000d040c451040b06181282540c99030368400c041003044004404410b80e8500030001c1190f0b9808440c6003d00040da1020743d0344180b4000101030302c4004101e640c040c4c0c02c02d44c40c1000038030300108503641980034200a50700d17450500c1f0a1006031181452814640d824140728007013010706640154058101c600c020404201e40c50171107410703241c0c140c07800351140e0846100c0041c20b010702e0700441201900c4441f8104074a40f240005450f02d0010f948807508910410010f00826404224241d0407021030310801c21a50340c0400000c0d41c91042000042c658040030448908181c0928071812108100805058040020081518186000c0c160103800186218441c524511a074820980615008800b8095440c00c0c20140c030082d19266102503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 634044055 1250 634042805 634042813
    0x905040507050c100204050312070b040305070212010c05092b02011d0d110108011a09010c150f090521071b0e1503010c05040b0307030b03100f02040f0e010308040611 73
    0x40c0350380e0001d104e0951458010b800058446042500b03140c601842c0c0010744004810030001d460100e2500c0c2c00069003d640b510b85103a54000c14400700300413040d2004510380c55803d1110450103650400046c01d442c20060300c0710010740d03081810801c0381e400550a00c5481d071070009100b002552290030f940b001c44d0f1003011686031070205c180c007040700500112420368501039181650340c403540e130180d2824010a8421210034440c5296a11450b65202c1d1030f0086041c0500d06030494104072207a02100e8180d2148a0200032040d0402c82c2d0802400382c65204954a0241981400400d400748500c110103030b0914800608004840d9a8000c6260f1120301c111101c001c544800142c1c0815115010300c0b40d05240c080a2844034400e0900d401c0d80e8960b40c420041c07020511042c4040c2454a080d21b50001081c940800c0d408400c001003800e2404400f8184139007410000c2c0b550000d80c4d203030020300071500d0003480403068a81d100c1c6247c11164007804000e0400c0d80400080203042d2040c040d00a007100b03820255 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 634045305 1250 634044055 634044067
    0xb070804021908210702060d090f021f0f03021801031109041e0b0405061005031302030d050c1209010c2a0f090b03060610030c0c050a030e09090d090504050705 70
    0x12050070714481d408403085a0050102291015080c490418080c031029501401c0c07200c0b642c005880d500603203200d0b012549c0d9411755030042c0004500c00e0351629030007500b0390042c80c926800c0003000c0e400300341c0c0754400300d550858090360103031107071080359000e04000d0914055101d400004501a01c03909911000040003800350001c1555103205204910314010a54900c15649e040c0c0311003074410a400c014802d6183c541002420b48644042c1080c0600c00e01d000c0d9074903503030710200c0b121800c42c02101075018492041080d06454101d0b0003400480c0110f000c81d480076200e2913150080f1321840b05082d00281501543c507000600e0442200d141c400007246004e0b0b1005400080031700c01e07580c0e40c00000303d00d811038410042c0010360311075402600e1007500071b42010700d0118041140800d05c041404c00305555a1482c00340c442c81404085230040d806401c1e44e01c4c00e4200e0400903d520241c6d00c802d4801e01c1020003050760b1040000d20241c0017085034039040c540702c0ca4101000700a107001003e5000b440f00400407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 634046555 1250 634045305 634045339
    0x16020a060e0616030c02060103060b060c0609160e060f06030c0c0109050c09220206030a1e0c080f100b0a121503030216030206030a09050102120106090608060105070b07080402 77
    0x15070101078075008001c01c22498000c18083c0a001c2c1c4070040f5040c586800d1000d0003c9602007500341c1034a420200125041c0c03101e4010440910540c000e188150089400740540888041504401156000d0f50321100755210341e84201d00c4e400540307825900080d1221050003a042c100042c5911040380c111407800d001000398100e00f50b400021084401c0e80018559014610b40345040a401c078180d241c21809406800780c40c0e00b250188407801030f10940f404400036201846a41004003c080204180600c10141d002180c016001c180c01c201b011845190000d001d4000c0100b04608c03500c07504005c072001c0c5260000c44903141d442440e90078200201180708444144060240800d41c000c01d11204080c9407841c01c0c002d045c0001c0d0804c02c030190102c1c410030400750340c500d23003a00d0308115820b400041c2e2422900c1d04900901c244000170000c221203030000108103800c000080201c54140d10344465a9503500300441d6107100705580100000d4013400070030711075072282c1b900d5603000c0c1c070140080d8810040821 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 634047805 1250 634046555 634046561
    0xc0601051c0b010e0406060e090a1704151101110a14030a1428020a09090f180b04030f0228110316060e030c060403022701060c1b0e16020a06 62
    0x1300e5442400b8420901c002c000c104e20866004201c6243d103401c0d070342458541680c8401c0010b00c0038042d4600b0507020300c07212001c04101c4004010079180c6c0c000026034100082c011400a0203c50925460429854100c01c0c0e4042100d0030f83c4481d9548400201c80350465070250340000c1c0954110580c0d0382c0c1c441845884040b0280e00a4421446d600b206e0b0240318219514146c405100b0441c650042c044071046682051440054440800b008103120203400d03100c80050100c0c4000e08a80e01d00000c0c4903090100c6841d089004901070740d502c0d104050011420303603076100d5201c0e5000408021071035009805040264000e81148503034800300c81c02c40302d28006480d10ba68913000c1000148080010003034550803140f55501c00100754080c20100c0803003400242da6000300d200c040e02442d110241c503040e290440212000c08404c540d8068540d50f1580002440701100c000101c0c0c40d803400140310708c1c900e0606c101960844200c058101d01a44e1a164407540c014094164401544540d081c501d00040b0980 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 634049055 1250 634047805 634047809
    0x30105060d09060203190b03010e060a09030201181a01090b061b010b0411040609080f0703060e0f030c0304140108100501113306010f0207060c0c080a1203110c0601051c0b01 76
    0x446c0072000d41e400c812002e8204d03940d800e00c00d0321036850814a5a00614007042c0607a111811580002e1041458107040e80940030580c41080550354111458041002d5030452501e403800c8a0304c030300680c2e82c0b10801182211003204400e94403410500c80c07016011010101b01c40000a10300012903034a0103003021506582d1500c001110006000c50305100180c3e01201580091500e03c004000758017a03168100e48484160001400c8241c4541400d9070600e810810b0f41c406078100b1045030340e13070540840c040fa200c1d04a405003007006569048424101c0d849000b10b94042d4080b07000004150340b4250054a11071410b4681011600a11030100700c0d01560007100d0016005034106044a4440c0c0040b40c2c0d90380748020f086605216100202e2840a6070001d660340a036222810402400440e07410100703128243c641c4006050703c1411417401c10042c4980349090014090345003801240514813224899001c3c901d1b0307181e03442d84424010041d9141802d45c2e4009200b81c6000303103684900a4a6407940280b0907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 634050305 1250 634049055 634049071
    0x7060f02070f050c03031204060b22050f181b010e06220b0c06040303050c0d05070f1e050708090a0f0b0a020c24070606090e1e060402010203030105060d09060203 71
    0x20200b071105100050008100410080b4061490402c8100c00c8000191028001070401036a802c502d6031503444001d007110391625521040035400800f4503945014200843d0003500b00350f004c0d008078016240c0620000c241a84000150250342d8a100c985100c02002106240c1008000d4111443d1900c0d03107001051400504005c81c81038402038001622000740035880030340d03e6181004035226207040460381540007070341854085102d1311144210580f502806203d110040e1426051204c6290855008500340b86261186110002c002c1c2400340e03029044840d01d400300754104a05c80000d07402400800c1d409034010079003401c1a442d81c088407041202500703c40ca00180010781c42090f541c0401c56852000c808684101080c0d9860b11000025880041c011421010100380c1408201042d0800c07009040604000c00c01c8020461045a0b00c900c1403c400051003014400b0303c035114008075580d48a942c068004525503460141071148981c403c0c1c0c800301e010342d9a004a08005240b40c0000d5000c1c03400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 634051555 1250 634050305 634050323
    0x1507060b130e07050d0305120901090803070302120907030213150902040906033c11030607031a0303031605030c0c0a06050709090c0f08070c02031203041703190207060f0207 76
    0xe0500a03d103000c1c50340e00454814070300c010351080001d43c41000c5850503c40150528066200c00304200e003d001c1d510f000400c051004030410568992540c0502814a05403a050201e52940428280c550300c2d1404081d4128030398652041404c2c000e604100348076100c42d003c5a030941d5556001804a82041d0810b0030f049450381010000e1251443c07800c028000c0b0301c4881c410300740348440881a088114103082032050594078902044c0400d03546611000c040290030344140d8a004040103006100400c6040c112034205050303000726003400810b0301d204080101d041c2c40050499601604c85400c01450041403860801c100c2120741028030840d03880ba84200e50100b00341c1001c000c09040003209800501d186c62800001e07480044d400f00078150508644d0034000784903180e610007151454a2144047e400d0310410f07550b0050b20f8426001148210700910584020500303922031200c40344420b40d407084060b0308a14030380c0000b240582c02031500b103200311400070340d80c850303500000705a80103482c2c145c48202c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 634052805 1250 634051555 634051571
    0x51513020d120f050f1615090b0403080702010c0e1e060d140109020a0f0f031d1b090108061605070b0901090516050307061407060e0307140c1507060b13 67
    0xf410010f1800600b109061103070030000c0206000d5040d001d950900500321100303e49407024480082c022294074243c1c802d06100c1061281044d548510303041d0340031800140c2e60700c0040c151501c18030980242c0740c22595000d080000481c1006654280c20130310b00000c5820b00f01902d070b00e42d1690000c2203000d09180003c1007a0411034040c0907604ea0507440702c0029401041f0304013106611290003e1041024140541e40c02041c8404400609000500000e004140da001c50790302100014440c2611390103080d40045485007405102c180300c020311605039182e000c00e0104800c1250400c9041941d03009213072007801c102d02034a841d031040748142d444200b641d546011450a00c1300510002482045040410490034500008655610800e02c221030401180c003014040030f42c0004101c0b039850b5000310061104d900008038003902e036070201008603107041e00c8090020550300c02150040030dc0c20010004098084001045e80060f0301c04801125103503540c201d0040143c1e541000c0482c5500c8110340000d40360 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 634054055 1250 634052805 634052807
    0x216030909061211120a0308150109050901230604060908060a060f030b09030d0609090b09010608071811072909031804021e0301050a140307030f0f05060a0207060b0409051513020d12 80
    0x402e92710702e940d042181c800c40c1030080780c45016900d4116441022401240780103008803152240580000b142c3c003260010b40003075010b03400040101960001e03800d4484a480d44581d13001100c06621070300c000107400d0724042004c14082e1582903400019a02968504580c081200c1c0c226041a000a0340c9240c1c0e50f0004000d02107420702035603004040301d0080002904068495640f51050b02c82c08800101c140d031a03051103c05a0003142c4030741200d04441e0340307410961070407102c440c0800441000c1c1d001e8105840c4140c004940055002c0e25450300950b03c0c09101d0140306d03440030701c510340c06a0003980800c100800e6400e04010a88600c543e40e43d019200c0d4180410442c513048d06a12245a800407243c45800c10340d0040b45000403280c3c40326150314140400e00d0800d42c40b01c540710014156025440030071920600ba0340040c8a42441450104203900582040204492640c2c80c043c20325404a2001d8215480c0d81c150300d50003050100058620540a60003d00b103001104c00481741a404088614202 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 634055305 1250 634054055 634054081
    0x120c141b040b010207030b0907050910060f020d08010902070c031203091101111f110d090501150e1305010b100e09010e071b0606090216030909061211120a0308 70
    0x80c044800b80000c41c00040001e60b03400090001030b00c0c100021000c20684101003140000900f4090300d04002458840519500d402c040e1080b040428000811040396604c017041314140365055480d42c00d60f41e400d03c0305200007504a0401210088080c1d200030000c6041c055440490301c125a4001c03450062038035101c071900b1100c0038024140400c1d000850140b03807000c510022809402100c1c0300d9181620220701d4041e0110342148580580005850300a60103ea00b01d400c1c01401803000703000302c0400340c0d0101000e01180c89088090b82d1a0740c00700b0800d00070001c0c8a00101d00580001c2080c04007000001c0b0340702400c940f101d011070913584180c2da103800d2202d2900c2c010b25024800b641c0324542454003401c018004161b0031701944c10801104200300d031a50000d0041d07c2240341c11521444100c0410408844100050300440c5140358001170010541c040d01003540c40541102d02c0058655440501213400c1401e0694800c0102810150b448010070940720114025940e0021a05042d07600c4059 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 634056555 1250 634055305 634055353
    0x50a03020d1b02040504020f0a06111207030806040c020109080f090a0e1e0c120411040f060807090e28200108040b0601030b0d030207091d0703120c14 66
    0x2480002c1c80d201c0c0300c00868008020031581c0640d804507407543c480c40059401c180c5184210b600c64615a070100311180d008070203501c03071030710041141e00c01500c0702c010b90884c0c021454001c000964106c001031280c10190071043e4413021038000403800003000d0751111200c0d00107030745203e045000030950071058500000140c0c0101146040e03100345040590010444417807862140708030308462008202c00754080400c0b1140850b0141c800d01d42401c051400c0400d2180090708903210300c0c200341c11407810340302d203105490480e04440000c1c299a8501144d00700582008100c0152070700545109400000324180380010105000c0b10844404031070307180ca1207480b65240351007000b0b00c04404110260b41d030481d596a40158228882084d1039440c040102e010700b150419103900445032140000805070002032107026a94244001c0c0151418000303070340e0940000d58600d004980c00303050108081084402c00580c200124501391070f0307806158423001446010304420094030b6205804290524100040c00b8030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 634057805 1250 634056555 634056557
    0xa0f0b0709060c0b04030804031112070b22030e220207020a0b07080403020103021b0a0f12030c090b070311031606050a09200f040e010b180c03041b12050a03020d 71
    0x225401c51912802c1381d9000060008041c84649004941403500440c0e003900b000440e80201d0b1410001024030000507008150111041c900c060040b555040090001ca1040b420742c00b4100381c0498a600c0c01c4800000011010f604443d01c006088050f9682036040d104850050101596846091041c0084000954084555441d0600525001515100c11681241c0c3c0904c1d000d030301c03041500501e00454401000e00c40b990310560400504100d5602e0386030744000d00a1921a10711103c1c14416401da40070360180c4070001d60340c0380c0d081c00740300000800313003050030702078a0320780301c0e1003c08080e551840c0e2080325101134404e80e00c1700c0c07181004564020582d0004800d4014083d801260751240c0d15500300c1034ac02d5a11480d101c41d0310f499500c80514010002a00a2091040c2498158064000d00c448040d86024a02000c1b40603400401450300b20300488400b001d16245580e2601c2c1c54030746e481081d02000a14050003000038000e11074081c0c0103000e41c0034001500008000b072502a20b496400b1407502c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 634059055 1250 634057805 634057817
    0x11b08010305060a090507171e030301151107050a03050f010c020c06090d0609020310060317031e1e0709060f09030c1404021b0115120b070e030a0f0b070906 69
    0x200014a003c112150008030382c2601182d0000c1619289080040542100920303800d070580741c240c4070100203510768000314582036005c042018040d21a88900c424020031403c040c01210b800302e1a03101d4070030303120207100c01000c3e5030005848100043c5c5018284d4026590b503803007603060045800d400c1c03143cac285101e01400140b00228038103000c148207009120071948160601561002401a0f1303800000a442d4001c043e600d080c44881c98000c0205424001038520440c07100e00100b1001c026011203008801c0c207888c00315045001002c0e485281c00c0101491011003041d080103080001101180b03005051507241d040c023542c00d02c03100030b0817181081508820880042d034200045500340d80c40300c1c00d0359041fa1880901c50345070400301c0d000c0d01c284441c546001030b0085134101e81e050103600503031342d880c001001d107041c8079a90400c05103003081d4002d02829030300a101c0400c0c051405504548040603015080d610045040c0d1294098135841403804c0d0390300c2c0c0c00f00b8204851940c3c071541c440050320b4241480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 634060305 1250 634059055 634059059
    0x18030f0106051011100507020102130b04030203211309090218100e0705130b09190b270402120a0b062a030415030e0c01080c0a0e011b05011b0801 64
    0x207000c212030f494940050000d8280d40b1059030005200041e6403540d6250f05210034109510024000d5210745e11a2840c64509039004c02c070300c0005030448082b207400074010040e88042e1694800e07041e60480d200024100200000d0414281c2103c800000f081c600f5000035100c0f065005228a10b562142804003940c554405c000c090b002409120702503030748603440407501e641c0340c2c601616144200ca01c1210545080480060800380b43c00040010303240544007100303140c41a001d940000d40450240c0b50302400c0034000342105c01c003020368250005007600740e500c2d400468500800c04aa0220300c0e0003182a2001d42001341c40030f418050300c0702e041410b807000f510b001207a100e4904650300c40681c41300c1415061284c070031301d031000704140d801030060700c42d544612011a1070040c00810340c984c440f00d40387c0100d00c1d0f00e00c201c1d0300a0070340512900c0c14600780d0345050041c5808884c40c4900802a506201d6807081e00714030103000c2100c042c4098820f0f000042c0341c1000e048500c103880426200c4c00300301318880c001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 634061555 1250 634060305 634060309
    0x3130504060303051812011103190516050708040e070503041407060c0303020d0603021c03020c030d053c0711030a0807140708010c091e06080c1305040218030f010605 73
    0x40b01c5c1c004401407410311100c40204001508444041000c07515036092003202d2800c4810380009500a081001c132030740c2c10806108400c820703184201c0d210a0003101110f41e130f0b51410f000c0c2c1c00400042d031003500b102d8078003520752070b40940265060360403000003003020040000308800c4042c500706400c60f080050840f5850641e00401001c3d078550010101a000304208030701c0c00c856000000619801040c0d011961075550304160f4006101005400502c01d02c001e4058900300450280d2010070150749036841c00c14180045c60200900c0d101d00680000c4510080100002c1d8800c050310540000f1000c23035852400d030400c0035200c8085580d151080e00f00c1d050784000103800100b1200720701da011040c0c06e00d40d03903a0b0400a003030500643c880c1d0119400c0104258403982d100141c041580e052030508200144680d0040143c180341e8010100803a8514010510341c030101c1000c5c00c203031911b081c07011000075140d00100b0107982100e980750100a40105072a4524a0188200c43e014070f00d07040204119482c00b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 634062805 1250 634061555 634061557
    0x2803020d0e0319051e0c0a140907050c100905010b04141009050c040b0a020703030f050a08040803131b0503010b0118060509062701020d11100b060c06090313050406030305 75
    0x2209080403020300f83d0762040081c10302c280810700a8038103001042100a1a03655110b190b0600b11074840c200500001c40c0c07040c40c455035032100302400790a03902659150481a526a84540340d805094800c01d2101d40c1c0c0d0340340c2e81c05100c00840c440c500109a82c081101840b058030104c00700800d01c880031000700301d0420344c0100800120b460351100842d03103449600310b00b641846580c22003d048580041c02105058000540e80700b02c034441d0703548a1582d65402d03c1150580512595200002c000c00f01041c085801d09000d55003000a003824040200520f070307500d151070b10508a00304140d28008804010a140078030403034803003a0003801c054400f00c21f1a01026110a5940540028404086050001c81e11010203803510100d0303c0300d09020a080800541c4000c14156140e280148610101c000015104200c5504140c1d1800018008483e40140702000f13404042e40d03098000c2401c5c04529400078007003142c00e0203840101d015590b216403a0b000080c502210b5001507000301c0c103042e800c00c0041c0d8040c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 634064055 1250 634062805 634062823
    0xf14030c10030209032407051216090521010e010c05120703021b06040228291b06010909030c030503100f230f030607050a022803020d0e03 61
    0x200c810700041406881036000b030007003040d501d805d0310072101074107024101d4111400c2110181000c1030229916003000300d0f180d1240701c808910880c221008901c144030105d03e10616801c150408500c19030700e4a01264600d120340c00d6281800040d113088080400c420b02c11440e10500150007031182950100d00601540b0900d402100404104000640e880d803284c0d0543c0d1200c0c036070820035080700b0f02c0b0310b42095584c8000e075020792003002c070082e000c02c2041002404804102103025048034641c64550000059071029603d031406a020420f17144e49000c04400038510f000c0750512050740c40d100141c40702d107444016000a0f00461906020101281e044031a02d18466418500181d0b29611124201d916641c40c1c0d000b4580d81400c0382e03012611805549443c4290b00d62400c0c3c1c0341c3c1400c6001c04111040f280d6400558041d08540d0100c0d120901c07500003011400c0c0540111045500510050700c1402005111f6103603c00800b48490308050b0705000100716412245001000035030914002502da610b01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 634065305 1250 634064055 634064059
    0x402010206011a13090f0f06210c03172a0714010509030a12030b180103020114120a061a0c06071206080304120b061905040b01030f150f14030c 63
    0x100b0703004000c2565100c222120f642101440d01e4100707176a28607050280036942c0020401034140007100d50813442d07a214520485070b08081d40e0319150011000414010640e4070192280c070715508000c000724801525080e918880340d40201e54031082c41c218040041608110484401548020410b0150000038680241d860b00082000c40200b07040068640780324050400d5014044d205940c000d010701c0381c600c3e4007222800d8a05000307480b0b1034402c0000113107141e00c0c0c0300e600e0f0001a0050001d5441102581320480c03581052030703e420101c1c0c0310668149002c4a0040410b42c4410050060b41c0c0440300c801401c24203920158105520010481c2c0c403514024201d0f810001101400d0100031415040040140244801da90f03950341c4940c14800c000e180c02c0d4041d00d00c805510041000c9041c1440c080075140c1c0c040d02c29200b00b034200001c0001503c900c502c01410035171210718940f0311500360311410074840c49081e0b21989003890049c00448000695008400110781e00ca80d0429030788010400090408003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 634066555 1250 634065305 634065329
    0x11030f0a1e0b070201050403090510120b06040b0c07081005040f0b06060405101e090f0306020304020604030c0909020f010e100509030a06020a2106030816060615051809040201020601 80
    0x511222101007074200400ba102e0102c0e2014041810f4041d03020a02850007a0b44044241d510341c000d228842c00b00305035481c00513a4004c040ca044e51220742c024003008a0040c81280b030603070f44242485040c0c1180030300f4500e0350086d030800c00c43c01c42c04001c4140d070302d1400c0300140000d00e051784400801c240b0200d0302a20408000b4001601a92498203c5001e010020f005078100380000d28002c000d068412603200c3e407103400f1481440c9003800341a409007203591411111080c01d0940d0380e0100030b5007000d80201d030030481c2804080000340101c11480040d0005190002c3c0085541c01040203058110b03031890706000c4840c21412403616030804c01b40000e4a182086503032983c07104042450700101c0100541094400300e807540d15181d001018a405c81d80701500c21040015180207007007150043c4c8802051204100300341c4144ca51501d1045c0403a600400000404130b503601e21202c4054a0150001c1c005000001d010080700c5c040d4460300c0c0400f6040c1c5562040f40fa0036070020396100030601880c007030300305 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 634067805 1250 634066555 634066583
    0x504091106070f0803090f1513080c0102091017130c140111030705010b1011071404020d05270a0503090d081e040906060e0d060f02040302030102130311030f0a 70
    0x14811108040c04d6101901c00e559182101c2c0b041d8480d04900d0101c00746000e01107180500303c1c40c21260a0180d500007500c95009a1b49546554031a40882400341c5995000c2c80340007440d90340e012880e4002e07a21515030101c0548070350401d4064040080c0714105441e180c1a000022500075485001034400510a41c0f94245031003006135030100e8845100c10b50340c800000c00104024043d040610108801d0380c40c0118490b03428015580c0c41202d180c04640c2d40e0044004100e40504407100c03c00700c04010707000500e40050001c40009a4000b101e1106000302108081007828110030309030341540002d40060824984259a4941c40c0d114607904148290080c403448018411500212040304c0d001000e07203034440080c12403034a220303000f62090640d02d030700d46200082c0c11405131036904460b00006240020815246e95040000c1015150402c500d41d0300303200200040e14240b000700313040034802400c2c613041d030720390b04d8451550520784041502036040680085000c1c00f000840e07054075130380044240c2d0691 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 634069055 1250 634067805 634067813
    0x30b1f06030e120f040905010503030a0f0804031e020c01090f060c020405040606050307090501051503010e040f2618040c050a03050c0f04030f020a051009050103020c031201031407050409110607 85
    0x1689243c030712012032000294003844040000014411604402014801070385e03a0300070540c8034010210108089580c10801c0e6078024415494141e01510a0400321180050401c00035003003584d0982c4c1c0000359006440c10301c542c5da04070741407400038280d100d1441c070340d1810700c0b600405078609070200030b008644a5010600704040c0303402010160101500b11411300b6641c0003060003411082c03182c280280480f40ba85074011681508890682d40e000129420300e44032691143c42e02840044140c070700034502500b8041050008030b850850340c2c41241d0082d283d03c0f1600040f0b402c7c80e08100054861460044e008034040c2d040300540d801d140340d03414002400d0b503803000c0d580080d226514010000702d10014020080049103961980900d0003520056001500c0d041030206000b610080100441d26202c5d0401056209800805120b20a0016a820568600d0504100100c00e8000b00c480e000090300c07186445104210200040100f1a4244201c101d203072618415500d04801e40c50041d0300005441d0184 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 634070305 1250 634069055 634069063
    0x100203060a080f0a110402030609012105010e0d080108030a1707030f0f0603031d0622030204090f02090a050c0304030c03180906090f11030c0912030310030b1f06030e 73
    0x5000c60000c1d501101c500c1c030140c940344c0765521400c0324030441c6017182c4085400d0031b100781c0b44503000242c0321007040d034208403010402034401000307540780e801c042d0307603c10028201f03015010100c4000d8000300300000910b039002d07190400c140c010640301d510a001c1c80480c96801400150001c2c0303207103a40a27458032168001c80184c40e642c1d5240c40a242845d1000400e90f0999000c0c400312400380c1da500580308040c3c904003000700c0c09030380d180e54003000c00c1c0034038500b41d846144249003181500000006080e502d030f010405a400d60345040c4c0c3c44050035418041542000666658050000c00c0200083c0c5000840c070a84c41c007003d40042c0801242c1100c040c00c140c003620058203201c1001c443c1d040003580d50103101010341803c0c00354064a900701800100c03091140d02443d110000e06003407103421a80c0b8003034040d1080d0044180c45a00100344983d0706042503050009501a0b041150000d10b145d06509004240100c054030010a0809a1403914229240078240f00280c03069450003240500c402c0700032501d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 634071555 1250 634070305 634070309
    0x203070804081f0e070e06010e03120d3218010f0509100b030c0d0f0c030605040c17031e04080d032307090b0a09090c081b0309100203060a 61
    0x80c40100140c00320700c1040000d400510b11165981d184150901c03124500c0546100450610042c0c0c020380c0103010060070380d0605070b070009040c5410840490000c0000e0f1030503580d40d29030010071600042501084035107024951041d26000f02041e212502c0080c0700c0099200c6d001025526500c4201160160010200c10f04054803624001c0c001d0038106002c28009000540340c48025200324074026440c04014080d00c1c400400040140040400b581d00f0301680c08145403045400c0d0b0034050090000a00d40000c3c14040d50007440001010300d045d1500070002d122541144a244030b0b803240e580c911020000c222100c0d81c405036010810400860f80720300c0280250b41150784580644030801403465891f40c00a22050400d070246070b2a2000319002000c60642031f940240000c819180501c411500130b001858082028585240b1050b564000a400c40b00e1050392140024603075024003030301c409010b6403401180c0c1d03004200d51540c2080d9112035610b00505446c2c00300c2c0c0743c000c07002030003035600c0d5210040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 634072805 1250 634071555 634071563
    0x601061d0a03030e0a06030c0e040b03010b04020c03070b150d02010309050a0506090a1502090a170c030307030c1b060503061c0f0b0f07091401050d022107020f01090f0210020307 78
    0x14240c0b24900036200403000c024117401003030b5140f80000c0c0541702e40105082050641c9070001c15814010600001d8000c070190180c040d074032012180159116440103098408428002c0c1d42c6640c403625210884900250003060320300743c1d190040405a60b040e400e07200c0c103542420001480c42c2c09107030083c1050703042c2e0f00140450088504000f54100c0210300100030714401c18101c043c10309045400012030080d42803054118005010507c41194034540144d4075200e9801240d0008800d00002461940844000c6000076800c9030048200505907840401c0640035404546103981460300041060200410052207080b2600003d0340307035848000c40c0113000d1341060303a00c4105801b034141258094000c0e1402074018000c08d001600e51449451800280e40da03001380e268100d40728000454040e08507281040c54903508002000845492000d440f00030040c032800c1c4d9481e490720200103400c0c441c401c5000c10b026414106400002403154a010740d0895048550740403000c00c000c0228514002d40d18014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 634074055 1250 634072805 634072819
    0x90b0a0c050109030908010b03190b0424091e0b0c09060c060109020c1603080307121b0c030908011107021003090f03030902090c1603110c0607061401090b030601061d 73
    0x2005269001d01034509846d4058000c2c03144003d0b1609141d80c880503800e25180040e603080386040001e902c50460340d0814050707081c030088080c9280c1c00040c1201a004442041c42e03444101200300f20340002001c0b02484001c80501422105844d081c92041004100078415040090550484c0e03070303000103542d0300d80c0110b0104d038110341c1c4411200000354810030240b032042c030032501403100100812081c102030742ea0100c146821502d54503c1501d110010682c1120b05035141c050700b40030300403890b00e00b42110321550b861020000040c2400b411010041c3c102900340d03411f004085038007800c1d04045900c01d0340e040e60000d0540e040040110024041c1c850000c241c0d403400c1c1c40700c2083c55817580208912900889180a1540b03400b9003071091440b8900c2d041c25444010b4031140041b174052585110600061402d0b41c06c405412800980c2d02c1e401104111403407076a680c2c1104224041d402c0d0317140500b031a0b6108114041c28240029036902051181070108491040121036000c403813045016402409400c0e9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 634075305 1250 634074055 634074071
    0x5031209011b20030405030a06020307030f32010b04030f020d06020f030f010608040f03030506040b1003150e0c120a0b040516080f0609060d1b060e0a060f090b0a0c0501 74
    0x10009140c0c0c3c01010340003d400428107000d03400c08000c982c2180e0006000f0400541c65542d000041e400041c4040c081c140d440d41c04a80c0c07201e1601442845a0303041e140381519071550004030300040308012007100800c880100501c815140070080310f058a030044100b544a00b400d1000030807032000300d14001c11203400031400b0301c22000700703d000d180599410481805c00b82c0c4c84000480381054110f4014000c0842a042440400c0c001d038001c940041000c1e0020034040072a80c085900c44000c1428003000030354410707814450b00288480c150180048150b8447c90f41441c5030401f081d80103000120120301e8500c7e022800b00521503001b290420701c0a002403216103403000c0c60780700303810540810b11702040c050780004090204100c081842400000e02c894070a0701e5000920444074140b07e0201c450b80c40c0f01205d450581031541c0c0001c01071a01c6c0d03958511076607141c0709008401e41c030b5500c04024040100f000740e0701c043e0400c1401090f20283e110759603c0c3e42404408403020080c241e40640035510742410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 634076555 1250 634075305 634075307
    0x406020606010f0806030601060c0f0c0b0a1211040302150c0115060f081e0c0708180315010b0d11040512160f0b0d09032007180905031209011b 63
    0x10161064000b6240c841866801040c103035419002205c08580c0741d04400010b1280c40c3c064034401140f2805011032105507240b03641c0e0b101000350719800609800c40041610003546602c040c0d500030740b480319482230146c0440d4001c0b4810038041d80c0002072191400c081201c843c0f0106c23200303403201458800000c5c00100400c05540110402c030b80114800100d1780e035507900109008012640c02014801001da205400d03004034401da03054003405a00c60000708103d45004130314003a0241076407041c0c240208461203501c2c41018a8090f60b200d1890200f07900c42700400c91305150354141c40b400079a040000c00c1c01c0000e0fa4081010f40301d5a0410ba0340040546480410500c0004041c2ca210007650f9001d840552201c580c2100f046082c80b4034864081c04103c42c1c01c4000c0d1130b401091005100781400c01c03402c00c44480d00c20302041c1c0e0128070881c1d603100303d00410000d2100c440d215113042007074504100d41d10301503c8103501e0344035201c0c030300c0180248100420060304003507000f0051144045940d00e04841c0e0303400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 634077805 1250 634076555 634076563
    0x203131a011a0903031b030c07030308061c212001091a10051e150309010501060e1c052104050a090b0f0118150e03060a05010f140a0b040602 62
    0x10350310001070420b03884120700400b074100e59010a0082c0210b0828a04440040e45030744502014076160200b881030403500d56040200e50040c40c440d88440c00c0514041d000e20280c0362a0296500803034183c00c000c0c201060a62a01040d903040d0b6038680e4000149120741910404480c01c0c200401c150440360f9280072440c190300c090310082c4518490180f4000511001c82c13103600c15111000401080b20080015241200f00300300c40003100c0011448204420000071102442e903c06100c03081800810030492502c01e100b1507000d081c081c2000298125002d001c2000031487c50002c0001d0f01a80c4050401c2c00380801c14152106800e980110040314400c00185164015118040c02860090700104207541030f070150840d011009405601c450454000441703081b4203c40384466203000c040000301e00250410780445503c101c03034032a88c040ca02080c09052030087c0042182c88424984070051000f400302803080f0040700d08020f45504524200c80008100250356409108810707800200050f900c1d40200e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 634079055 1250 634077805 634077809
    0x30e1203040f03231b010c061e06030b09070e15130c0f021e060a02030615070602180d1205030c21010e09030a02150a0e0f1b040b010801090203131a01 66
    0x107281e00b0210208080801c0d66079401c6112420204d145e6a010303051035204296440d03440c0d009003030204600c1d083d10803810100b454607401401d580c2d01d0708400d00500110341c841c180c0240120b401010b119140c02802c814101010f04440c059070f05003d9418810380e1543c1c4203d689203d0200b040111051211014003a040a001c1060160142c2c44040c000c01d28280401c6d030304c183e14030000d0806541d41c891803200a41c4000e0985621000d802c06000b03082c00d000c00645150741c030500c0e00581c4d950710314241121041d0f00001480c422403c500c4400001183c1200303459050b145070604c2c0e5100e45980c104070f5840d0250340c0314900303000c0040ca05403000001c2c40c0300c0281200d00d003d5148110f92a4140450f0b101e01c5001011400750b030141d074036a030720f070b15141c0e12003548425914800504940703c0c502560425004c4910802c4e542c1c02403000326914071000f0200d0311450800c44040000840d1040043c041a0052184286003940480000c1d280c0c124041c48003940c2d036120520042620b00074000c03081c2c0350f5080c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 634080305 1250 634079055 634079093
    0x1e0d1407030e0c03030c03030a1d0a060f060b03060f010305072c04060b0708070308061908010e0601061d09060402071b140402120402121c020f19030e1203040f03 71
    0x808025503090402004444417800240051860340d030b1000b6800c9d01a000a07180010504000503d18803181001c2c0581480d107403107003501290482d01200e40382c045d900780b6006204022420000d100c95035075040c80000002c4070a007404221507a03400c4094803061200c2000d4030011080345401c0d03408034000407091780c08aa017120104001604c541c4240e03203a0240e81c80040c55031004001c4000880d0003001030700e5014100400b1a2451500c0c11164540d110701e5a22030719050791a02c40310083d001d000d102c41805030545241120202c007984010800301a007043c086809440c40d940800d2194841e034045840660304004c1c480710300c4000741c0000e10421102c4c42140204020030001843e00c1c0740500858049020011040885803a180c080160104400d02524071600c120f003044035004041c8080c407204000c05070044c6c906508075400c442d0420b000800318410141141070710030300117600440d0b106c200540507922a161300402070207107840c510660f0081c00750041035003000000c000c907064048068403a1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 634081555 1250 634080305 634080313
    0x5032a041d0a02040b090607080903010f020403290c13050402040e0105090703020304050c04020306130609062105060115090f080303040c1e0515040e0903090a0b1e0d1407030e 77
    0xb9261814101d000d10b0040070001041009141124903203030f40545201801004003600d00643c6000283c2142c07102800410490b402107030400a1062205416140100340c0c41030b018141d2600c00845441c01d8000c0a030281c01c20003240d000240c02c2480700000c0070703080191045640d15150381080100c20001d100315845074040c01d001039000ba2281c0262800360751f2000003010f00c01210010070000c0d41005180a41100c000b0004861249040c003420004000900380043d03100d090242d026405100c4180800402c01540002000503000144075811500c00307000340000001e00c05400c0b10034580e00e0744030040d0303519040720100e04c3d1400440154000e600c1100c1c103540e03050350b851518184101241c02c0c0201d080076800d04020074108424a20b4102080403003451030700d5203485c3c03000106401075404030b2607588081511080f0341898a084400381410091b0305081240111194100c00300301040380b0f1600c400410038240e14030707858000c50746035910641340319078a2521080003001050560b052480d03900c0703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 634082805 1250 634081555 634081561
    0x10e0702030a090905040f1e020102010f0b0a03140a21020c0d020603060f0105190c12020c1f03020f0d1509021908060312040303050c0f070605032a041d 67
    0x300010880d54001d81940741c0b206050f00d0300720560010703c001042920701001d200b1034080041e0034040040351150840381d41500c4480c140c0002801c58815802d40700055140c180d00700512781e5000d0480d011240d0041c13540e4030708074288101034200405e1100060003206a820740400700c0100c2824440c21440c05d03400c460b1889804010010780309581c88000e0340220081022603141c0c00d01c114006c0c042181818654a8503d560546c4402c040070f80c05c1507000200808032140800001c200103170364000c094802072440f400c8120000c2c008140308209a1501052909220f40050003501551001000c40800c280c6850800014101402c0c05c00b10402c0c004040000101d0a0350051099451034500786020042e0b100510400707558000014103055414400c0300b100300300303540340d0740000d0020b14440d0b51419141d046c080d00c440e142001d80c20035002c0c180c02076034040c04a264090140c0354400d840100b480425902440c944001550407410341014940010340465000030314a0b6400304208906260181d0355 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 634084055 1250 634082805 634082807
    0x130513050d02060a0c090b0d050916060906180807180b21060610020607030b011b1b080f0a02150d050708180303061e03030c01050703050604110901120e0f0a0506010e07 74
    0x6070503004107c801d4000b403020010540e2140d100300d0340030412504495a031149030301003103103510456000e84000f40d0341000a02240754002d41034400803e4079000c1c61009410314104a032142c2e49400354101500720080f400408c2c1010b40c00060305540d0103061000301b0744088a500c9171000c1003103202c42c0c0900c994030103d0399a007010380b040a1003040030341c05041b8903103600c90128090416507003403a040200b4803190414100400b200b8460071845103914840603e080c20250f03a43d41516884491103802201050100c2d83c0042012034040f94111008152070115642082d07403802038843d60f030550340c030700401c014801d508800310502034000c94050407040349001c00455501c1c072045612a81000c5000c403501c61440d40b40340905e98544004083e6130525158207003aa0865400b202c0c103000181c1c48000740a102e04081c070868000d6a1030505180c40c000b080400a822040d854a0001c40940c3d518944400c2090503c401582c5403a01400c0d40d001c07580c01d040c000d80d00c5e070303081c0105100200814081078000b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 634085305 1250 634084055 634084067
    0x901060c030215070e0604151404030507030204050408070b15041a18041a0c070215040302060a08060301021c021903060f06052206030903020706020c130513050d02060a0c 75
    0x1140d41503000b00b2401111207080b407070f5200d02900700c0b4144400603144088990342c40020300040c000c0010000482408800c1c02000c010f2040c6500800610400050021030408110407043d203070140c41c04100c980755840e00302490f00c42c404000d0081c4050506010000280701d044116000d8102c42c1440a03401320044124115004441d040e8000c0c017200320f410b00d2070f401041c007070b50080c01800380035440b480d568454030310355008541505287d04001a03400440c50100c440003c0c41030001141818507081d42d0210f44c0f0b4ac4a04030b081428400140005a83c40d5400d4040364580111010700000c030040081703800020b5040f41400d969013240540f00c0181440c420701c219800c69016110b40900b5a01e00701c000e0760305900c1520074910000030098401581c0c0c5001da41030300148590743e40082c0c080001c1c1002801e2103181c0d0081c000715089005520310a9031040300701411401c88440002d150340710540501018466036400030145e00030390101002041d0046116442880b81304010700050f042c481c4102d0350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 634086555 1250 634085305 634085327
    0x60612110a0b04031e210206010605180d02190b2106030a0206180a0b0406083904030506040813150215090c0d0c09110702063015090106 60
    0x85030380b080c0b104102040d94064494122030220f003468511500c107448180c114034500c01c940f500d40390380e1440407409a42c10000940181207034500b10381050301260850090003504140345103e04006d0301804159075a010900c0c80b5900c46440a041c56540e481c000f8205400110850302041031306010b003506498148440c80c8600c40c001c01901c40140702d642041055048110407060513015126014541c2e1900882d80c005859940901622240340600007060f415008007600328130b43d0000480f18818582e2050200054014900307040c00b8101035000100c0e60155510142041c42000180400e0080080c010a501344500031184521511101c2e001e04000c0f2080207680140d01007408a0400300101341c0c5903401800180907504007580100010791802c1c034403030047d40e008804039410071003001c080c0b00d81c28590340b04c0504941000c080380c00281b100d00a59030500403030702c105204207075040d07a00c1422050304010f0448811803400d04114460219500f440301d00d000380045000455228000e0f1a810340f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 634087805 1250 634086555 634086569
    0x608070504140a2c0303010905090a05150603010f02031030030516022e020d0903060509010615030c0f14070f0503090402070303050f060d050615010c060612110a 71
    0x12a0307181d01c18880000d107070807800c1e88110700d01c018084c5090189030003144020307540d038001140c41e94103110440c2c0c1111f0300500070002540c4400e1492000410200c1c2c0740380140b0a032600082c859071441c000c00c0c00f40c0304600070700b030020303100004020f00d401402c1e41d05010340d20000c00f00010b1003503941004420f40e80d10f85800f0b007490f94052400700024442e0b401071030038280210713210381c080400c3c3d40441e505200041d140440040c2c4461022141c82c21040409a50034071407005059448070712201409200040c0070280290340c461000030900d200c2504000002c0c5145048188c500c4008400240213110740c8200c3d0703001a0040407521a0184142036407600c2440c0701182920381032040c2d55251100700c00000481c0c9030b0105000e856003a95443c405080c0e018000c0d140820306181060070308038480e1000380b1991140702c42c041030802091000800a60043c0517031a504000c04c00380700103881250701000001d16807030508601266400e41d2101c6911454820325034014020740600c01c2041745415801410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 634089055 1250 634087805 634087841
    0x70602061009151701020d020705060a2f0d060509011206051e160918060f0e07170a0605191e270906140609090102030910091a09010608070504 63
    0x101206010941d251350545006000510345000314050405a800411003915660004400c0041641580c05004071901e21002c2c0c115600c0604110384c0c18120b400042003605c04004100312428112903070205002e0200101060040d40e9914200c840c0c901c908081118214208000315407042c0c0d1020302a00e1030545508009260340d50740c0e0400600000c820466000c116036071034000341204070300c0c4198580581205010400b103060a8900d03155410f150310025800c00b00008002641d640148241c00b1850050100c03032054503680404000380c1a540c01c595848411241500c41342501903a00404039800451282c1101401301c00285610310b542c03049000c4200c90755040c15449003c00c0c02c400d000c14110000041c1c1d002a510345008444250710114a526110300c00d00500d4900b840074154401c0b000c400035807861030107010454880030102c0c1c02c01c00c0e20b44c440d0002c0e010061105481c200d95a01c00d010045949060509a8042c1c000c900c5090380d240a02c0c0400309090920380200e13400d030710740b480c00c0d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 634090305 1250 634089055 634089059
    0x31050606100203071b1406040f05040b0d140607030c030c0e0439020105101d0c1b1020040b090415060e010e0f0f0d110307060206100915 60
    0xc02410800e181c00541180010010103000500e0840c00020306400c04c000c00300005c0c1045003441c1d01c102100c01d440d105000a2204000000d1a10b46a0003030710303002d0350049081401e00c1d011880501d08003000501c0d000355000030040c0840c3c0024281e01c181c2035540d0900c0040100407080c2e044800c402080c6000510716144500d6038100781d04504980070300c80741d4884a92174106030700b141c100c592110034002d000081039030621441d42402859000142425132180c00b03072400000500320810740081001d0082c0c00000507001400c2007042c0c0c1d030903c04010352034258009405000da21500241c00404c001132620303405075070300b114015240c94159080c0c51107a140078180380c4855156001209a40e40c810740715500d10f04005040000440180095110145411040e800240074001c0c541d030194001c4600080050560b03840c20010000c00030306481139500941c403800c104a0900c030722954160980b04540300000c0045e40080c0c4584191101d0f841d01d01c0c01074580c9065010703908485c460600d411545403003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 634091555 1250 634090305 634090309
    0x1302010201110f03041509030f0c020a05040e100e030406051c0b041107020307060243180506040203190b01020a020a17010509160303110304030b040606140f0a060c0c090531050606 79
    0x5400d84ac500040103491100e681c4c6000509448841e003900300305800c100c888005940d02402891103000380c80c0c0146082c9410304600030103900422406030500c004070040f20050400c3c960040c804480060001d1001c50400a5490038075808420100d010b48200200003640700d10200d001d140809401041094041c0d00401011000b003491500d007002a00c170556003000c1c1e01d400c2e01d010008041a00c61195a130100003040400c85000908041c0168010810400050900842c980c4803280e070107000160030ba510300040b4542032844400075009103100300e000c5101060a0303100116489020003e01140d600e4403c1c440d21601c0749040c1800c41c002c04801400040d0040101060405221040302d0620366640c0b265040c10b00f041d682074412658481c070034402442400ea16280780c3d2810342e802e550400001c0007203402541030b8402d0408000c01001a88104a102d411003c000c084841e03080c0040e007410400d120005660705042501d00e44a84c101008a1000344000c0d2070181d04080580025529401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 634092805 1250 634091555 634091567
    0xb030c04051009141908150402030d0306050f091e040c1802090634030e01030507020f07090b04090807110a05180708040f080a08010611151302010201110f03041509030f 74
    0x10003d0717458030300500c007080f05201040500b00720f80a280d0b81c0b4815040c2401810304001c91443c0d4240ac16003008000d20240e1580407510450400c1614100c1c1e482c0e82e4060510058812003403081a800a28428007050020540081064600b401c61501c00c00d203010040303a04a1090003042c90f00203905000720071840e01c24001188041c00c00d59400103040c0005080c820161a10702411004180c80600c14072103941c0c035200b05584400c46000030654106040401a03481e441e51041123442600c80112003030b02e8641d80c10002603c2c0d40071308510b0302c4400c545080b140845a0146123402800c20440025107440c011801d40002080e40407040141c0d19030010466550000a000b0b56a5404082c110000120380400400074010580c0d114046c55041160003450320070240303210340490307000304120580c00940d26a01604080c1044400d00604e0481c40145d001d0641c80c1040020303c5800f0494542c0b032882e00c4000e502c0745205404540800342005521070803503000f43d4000d00000e5503510500c42e0240a00f07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 634094055 1250 634092805 634092829
    0x120c250201030c210f0b06070b010f0608040b04140c1c0614060120030418020c0114070203090d020a0f03050d0807020313032a12051e0a0201180b030c0405100914 71
    0x400c2c100340506c045100c0e82e000c03803000c448080468004100341d910758030000c1d000e011240303400c000c0c5080ca9290904a110040e1000e0a140d0303600e048541c105400f0010161003901c041c100b05081510094000070300ba01c5010f0903600603040080b10030100c00203060300c61107010705031501e8442000402c007140d10b0202c80c001101003440100070110340d10180c5101c14142c1c6001e4880940c2d98050943c0c0142034654001c0c40c820300c0c01c0580d061020140d004001d40b03500c3c1006407400305222101d8000121070b041c1c2a400b074420301001c00004400d0203000b04008288200f251580100c03600d0307102c001c0342d40c0e1003059100c4c440784101440034030001c4c5482000c40e191f03104000301c5003030a0340b00466480845400c1c6d4001d0801c511003005110800201b0701944d004007056880d42100b8060300d4108984844484074028101705081d09000000c03a0a044100c2c054414400d1641e00c07403910b100c45903810750250003030510400d190f0005080741031007815140c3c203590340280c00482c00000344040c0001c500040d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 634095305 1250 634094055 634094081
    0xc060617120304050c040f0204090b0108072307081201031407060c150209040c110d08010e0109090201140d090c050306190213030b0f01030314070305120c250201030c21 74
    0x103015040c4161b075203000b035103101807a1303000041c0d840b840c5c444c05ca001c46140c5240703d03041c4094001040440c1d41c000f2014007203a0784919003546020509242e000b0180b14040004045940200c1d21242e10490606058183c81c0302e0321888501c08a403c0d100c81c0d49136660703c50840003401d841030107000500c0d5000310310342042c0340440150800005000090507211100540000540882103210620204100e04d14251060b402c205d01d455041240f1150f458205000d40c8854584031300c6e9040440e4480c101c01c07004001c1e4203030043c0e01c5044072a10503000e00340d48071043c0c81c60300c0c10000100d19840d021400901803100c018500c0c070358082d9807048002940040c0c5044130b02c11400c0c0e4000010941194071140300300d16100041d036540d811403070054036035046060803511340b550500c02080029000790840c1d5001200d9414015180e88041d110303c400d105170403d881440e41544403441841c80009410005c443c400d80b02401115040300d021101007109280740e448c1552280f405109442040e4410a106064 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 634096555 1250 634095305 634095313
    0x300f0c0f0b040b06010f0917150103060b0f010f020a0f080f040602010f110406020d0507290403031a0d081605030f0304030306060201052e030b070c06061712030405 72
    0x41a160101031192414068516081d40e40070007081000d0035025540c0028242401500b410882000501d2582240070301020f1402a400b803d0104204000804096071041c0042c0c00c29031f1a450901c001e03244200c1a14019611030b034224040d580655000b45020a00d030b40203040340010340d211845c220039282400d80300d0203030400c81442010350440003031020707050302c0d000468a54484c4889034100c0340c8409120446c80341c107220903c0800c0d8082036406104100e4035056403500510300304141c2c449414003800c44801e08050001451120700c00c2c2c158440e50280e14108140011041c040764000010b00b500d981c49403482130110001140e18024000560040e040d40200c1c5038541c1d502c1f403070355000031403078050b02e1008020802015454002d000151030680300074070085c10038600c0500b21002100c00f04e40342c94240700c9000d41c05200541080b00540c1c10400f180501c1c10416405460f01c0100c450a0310000e060600103e4044141602400341e4141c100c000c2c4101c0b11071103500c10305500068411140e42c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 634097805 1250 634096555 634096577
    0x5070905041d0c0303030603070b0a0e030a0b010323060c0a02030f04061107120b0c0d0207060c0504090f09080405010e0604031406240f01050c0a02130504300f 70
    0x72a48150715640203214850a0810400c0080d549000a1804600e21951081040005031380700801c031501142c080d504c0d041d444143e040d000741c0321445107404a5800d8800c40803000c06100510400d18100e038012000268400b9076240200d40c219140000c142103540103401240c0c0b00f100b5600280080c07803442c815070b42440c4807841c0130b0ba807603442a40700c88001201d5625940171a0001d0000d88010040540c030340c680f45c002d543c0d59041028000300004d4502310007050f2825402e03107070303011100c0300359205e0802c2058105130840a0070940041c05030840c1c2524080003690380c1c1c1028450701c070003281c01001042c18035252400444850441c49000c6800c07030414000080040c00c0b24072103100001125018103000d29003142c1d40d194103a108104460005040b0500d403085031211244482901c10a1070540d0380c071100c3c0c50311280340c8028110000d4125410b00c0700e07140d0500583c1e22650240d44207180f000e51075244850000703e44240e100b0001d59210044194458450248285075641c2d0200c2c204104568 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 634099055 1250 634097805 634097809
    0x411060d0906021815070b0601030c051b060f070908070902180306010602030711040522050f0d020c0a0608010f0e1b04230312270a030c0906060305041505070905 71
    0x180010100ca8074250801c1d004112038075105001580c01c40703925172264101251512180002d442c05800541456510200603ca040c030420813201c1340c4200c034010040588940b00895a43c3c00111010b041d0510300d00c0100f400d4a116181c20000c45181030300a002c071505241c510402940501e6640859a08840320340c00c2c3c545080c8280e6000708082c1d000345840b00c00c6810001964075540c00c1040c41245804200002e20300310701d040d000711303a40740c0140540744200303860994507006d05154001c80c94032408485140003940040ca6204808058a41040d41079403014190360900082c051030324001200c034ac00f403100f100240469640300c01440c0306600200c05001c1196410740c0580c00c0125821344207603d50251007034406620f4803a2030281c00070084111009650140c5025801624083c00c81001d1076681100081c0b14103500c4500040021001316583d1404101442c458402c0ba07505038180b520000c0c586019116061107290000c85a00038802d0758809a401032000501540601c0643c08021442d1307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 634100305 1250 634099055 634099057
    0x507031101240303090b0721020a0503042711190201180f200303030a090203030408010e07081006060e010c03031517010e0105090c0d020a080a0602210411060d090602 73
    0x20460a8050b0710050840c10001e12203540e036048500c0034031040018100040c8103981842110110300000620101d00c040102d06140000da0050b180388404140403c0202007050121014524045800c0d00d0f07103601544141a62960404c60710f000b0f00070f100d0304910b41901d001c2c0710355002d01c03031000281283e0940d1100d400145c50800554a480f080c1200b00b041120079a41118840d000b9444c803100181c2100019039244001000c210300d01e42c07903800440c2107480410540f009004020000d200905c0b00120196480e1118800c01010384070b05564a0a100740c107109900503641c079070340c918024004c1d1200646401400b0541103041584d07410b1020b2903c81c100c00b61038040d14104100c0b481849003162aa425078080d0080f06000f03074582000e208511000161081180d6801d0381d010a203240380d03000007010f8010310341c003803006400741400c80740800103658010001100c001d070054100c44640c003040e05504000301d0300140800d0314101280c40078541080501a441e0408201059000f10781d071303c0c1410303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 634101555 1250 634100305 634100351
    0x140a0b0403030806120c0907050a12110a1e020a0813230307060f02070302130b030618012306150415110c060f0403060e15130b06010503070507031101 66
    0x340303d03a403c0c000645001c4160400d440c144400410075a0700c01000070743d00031005000c1d50103205000031160340e0180503020305110404280001c00c14120507c0c041e00081d4810501d2030001044c007151040341c020136002c0401c0035003031903000f004002900c0d40e61503083d90251101401c0340e05650750001d0b400001c0325506c1d28032901600d24010a46001050500d042c030250406018402e001c840711074a960b00086400c00c0740d070100d52545889401082e404000d1524414140d090b0081c04208500700d00100500202900c039103008006600160446046101c2c246000e41071401603800411136a01d00001d203484a40074558101d0300d00fa903220a402c1b42941c0d01d000c4080490603034071090412540500c4071300e0342ca41d81075600d070703180ca0803000c005a154416030000400166403115462507007401003065070301205680845110394204034101c914418500748045407d07609000c00542654440c409407809910680c5905043c166140d80c25142440c21080c0c050482d0b5032802001c50404514184200c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 634102805 1250 634101555 634101557
    0xd0803070c03020727020f040e070906120506090c030a2403210c080c0f16090b0a2304110a08010609080705030d080a0207020d150b09090601140a0b040303 68
    0x201c801c1d20300681081002d074040e214519219450f000c0c210000070b07800e07981030b01904005955101250741170301140102d41000070a00111003c00201c184c0042c000c030709442c0c080d03e40042d01d034296016807054810480345690442803150214106a44110280d904000e8074003011407280348400150201d02000c2740300c1610b0484140703040050050200300764007a15180780340542c0310b0000c4200a840c106068000800300000010600081c2034144450007403902c0f80403d464820201710395a81c091100c50007400711141c58800604021305d0b21910320000c640303980004141c590712100d0030981070680c2c0b441c1c25401544403071007012010411001807c90b84090f07228006194103144006184034980d400076075580e813080030140080c2d9000203100a10144504d07202510765500314031070003e801a0f83e0002e4001110b50817441c10403010200800301301e05030241c10441902c4110802184501c00d54494105801c60710051010104d800c40c2c03061224400303081e20003599600d000c6042c5560003075205034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 634104055 1250 634102805 634102817
    0x41110030b01030b0a050a1a0f030702060a0e0f070b13030812041101020a0809060723010f050a02070c0e040303060509040602040e010605030103050d0f021903270308040e04020d080307 81
    0x107103582c040c441c24220340300c2a40c101041d241000d012540070042400380c881006e46440380240c1c00c10b40e0604441203840c0c6003581ca41ca80c02d100c01c0c042d5503401c0941d4404011814680d00185890f0005a0231603c0035094005141c8a890044940810380c401051000e40802211000c0040780780c00000700015103076400313489003610301820084010603a40c1202790454201c00e11031404104a403042d03072464201118801d039101007502c1d2601506822005160b8151680d2049098410f4198040703101000d05007400d20903030340e8254080c0e00328030506e180182800d144039010301040940d00c0c0140e510508c40d090018000380c888000070081da10850f001c0f1a051b40001d000d114000c03451184600400c440e0801313a044ad41142e58442d00e85100d04a40800c0049000c0c280f008603100300680c404540742c400d5111007010107401e0090039031114003400070540b9100c0c0c00e40c0f20410342d41424a1700700d0703030090b1300039050505120141d9148a00940f090764001006100c42c00801c2e81507000718092207998441e1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 634105305 1250 634104055 634104071
    0x7030210060b030c03222a0603110f0c0106050414010f05040207170a030b220b19031707150209010e0306040309050121111c06060906030504111003 65
    0x4041a81e000740c0140a88a0052043c08009810341e820740b038004181090540e180c8558401108984d10103150241681351006a404502c0d8040340301c840d00350702070004800c0d02d55141c14099068414200b000c4800350401c005002007003000002401e2010104000812001ea945c4c001800790b504011203c032070b14400c500100076250fa040207031001894103480a40c1010300588440780b0381c103444c07c40100349440006484845520135880711302c00450003061951000c6500034148148480d405814040d07a00c0c00141c0c07211460400400004410400100401c9a080d5034a40c01d62603044001c41c401e064040c406100056003403d0646203d55800780d005894907480d01c0010b000303403140700d0071500030f41094080c0404240d00c0303240c000980b0001c1c20403103041520104c0700e0325805480303141072241d030780740003818842c03000e8440003032407c40821408400300c0c10400b0518001c0f1181442024041000036108000041c025009190301c180220b0f002580c03480004041100c00041880c96000203039a5890 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 634106555 1250 634105305 634105333
    0xd0c0c020a0b09030a0501020309011b1706300c0307050405090c0409170c0a020901060e130b0a030602131a031003060b12031c06090b0319210201090b01270c1103070302 74
    0x58ce10f2100032231324140361284400c0c4140c00da07808018080c01c2c0034240c609111140103ca06200780080440c0100f039104001c5032490860315003c40c013004034071a008020000030585000d00946000d0380c4030101030511084180304100003415104c9044030900401c002d00c0905290550180c1060004080035103200101807040011200058005500340400c03c014101d4030b4907000c00340f80308152001e00014401d0031070700009520446503440140101c0c00018107008601505202d002111040d0b1010304020396100b207540042d0008407405c060500c2111400c05c0482d43c2c5070089030342078101910600111403000c5d0294103541c4108c0e10710291950005c64039047e070445200d904020b240b20f20007080000100070019880d000700e15a85520b8900790b11a403800d0102d2002c2d400d104031148808880c10315405000a4003911090400380d54034013640000203040c8014030b030f01704500518082c0303507058500c40c41040c10060403101046420485400190b0340e20120400083c60514040d070014819803e035220 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 634107805 1250 634106555 634106591
    0xc18010e010609260f010c120b040908180a05150a090b16150609050103140705030d0e091302041a0f0f0102030f070305090d06020d0c0c020a0b09030a050102030901 72
    0x300420400c10b07003a904100c45a10b01c816100d8000c031320750400904221900c84c9900e003980701c45c0404203d518140c540068107421611041034003110280a22410380c401040008682d80306030007070150351042000d00c00c540340760ba8140e001242c0003000d00200c2e03900d80303001c076090b170880280400340541c00042c0101c003542c0100d5400000c11080c51218584600c0700c021075141d4040000040c8210903900c80441350111035000480034140607007007000a981e40f07040c2180c4181004940c2025401800b80102d020700300818521248002a126442080c3c0502e0074002203010041020106003d82c03881c032001030342e0307034080d281403915002d0132080c00c50351420400420580c3e40201610a266800200d105640c01006032071051344525005500c90520b03050070b841c01d00c112850641d1000c1c148030703180e04000050b400740115a916410402c10740a001009036031b200d20f07114020f9842810f0030400c2264145840090003440c1c806016502d15a030640e4aa50a84c0c1043d04e00030010b94548160707401c0600070b50 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 634109055 1250 634107805 634107809
    0x105070f020f0109080409020a0e030609010204030308091614012f0c091b0a090308040e011805091b060909010f0501020c01020d090905061503040501090b130309050d03020c18010e01 80
    0x1800070010b025940c1d070745da110b13449144950a010b94010904954403405140d2408140002605982803890840b1505000398440c1c00f044001c02d0f100400725114150014692044000340540810001d0600d9550010414070f15515030403c600038200300c4004014114440116096811229420740304501c45818984180d130f015000715580d600300320300100e200c449034039003151448080b80d44101c181c000b100c0c102883e030030240a0503000900066032541c14860141241d00da640321160254000b01c2e444141d50059070b810350b041e401031070100780c0d0095580b08051004030082c4180e1400100d90042811180d00741c1c0003a03206c000d581010405944c041c0b0100c0500d43e82440505108048010702611240c998042d94001c607640304001500380e120340c1d070703c0c4192402e005015a02c1f840d25207090350107840112000c82e26070240c003012a403100101d00c00300402030f80c180c0340d024689007007800744126100700c484141d00318421484264650303101d84111a040d19400100c22825604204502c1801c10042e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 634110305 1250 634109055 634109083
    0x80105040516140703090b0a021011211504090506090d1701090519020316030b010905010c171b03071109150d03121b1103031e180105070f02 62
    0x80d00850040c550b001c3d03a1003040d00c0c05110100d4a0b90300d2400c086540c4410307a0400c4802c21400070b1400d80381500040c0101000712000020720540c082d209008019004454415012440c0140b4400c01d100316100040d030702c040b03910840c501c0c81c40b0300c5001074182c1304004820340b804d401001c2030014840c8180710700d05821900c1c1c100400c8444500a646800305414410600380c65514400704441584030184070100c1c010881c0b0075912030034400081c00d003118507113441c180800e203498806961035000702005002c030780c0305031100e0a04a0740341c1c0f00c4130b0a6490082c2c01c1c001c8242c0c10001c2c50101032418116002401243c40103540321245071800141c89044c010017030703224500c8001000303c0d03140400305403d80003000b80c80c00154503180303190a40d00001e20b050300c0c00d880c83c2011a00003400748071250340d400510042d601d41006903020242107440c0d01c011356081c0400c02c01d02d1032960445d007105a08540201801c0300c144410411404c0084c00c4850a544680000300458102070103980c3c10000c00e0502041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 634111555 1250 634110305 634110331
    0x4050123070b090c1e01170c030106050a0c050115030b0a0509070b0f12070305090d03060b04090e1005040c060809060702070302101106040f02030d05040e0415060306020a0801050405 80
    0xc08030495003039024042008001d0310703101001807021502400f01007900e00300648000303151101402d101c5c3c4120703900041c440c00650001c402d812001c0d0b4070000710340600780d1108154950307400c12800316129404180c0c2d030380500009003605400070b10240304100364041d015042c400a142149450003c445000e01101c400904140c140040c4600115880c0122004400c0ca2039503256001501d1145002d900c0c109111030010b401001505609038100318803404150b4240c51104213402020f0b81100d41900500300800001c0c4001c1c808940c1b03950080c0303170b507448850495409020343c13001007003a100215011603601103903d20401c101c680040d01d4030b421504175009028145800d00b0025070f190401e00c0041c0c07250002c000c101210500680005547c800c10109941d042c0c6054103180c00190810b01b0301700d0091003650803501d003079403240040d0341c25100ca8901c080640d0312240c4078500c15083c00307002258010364403c0c000000420702d00c024242010583c540c402070750b15000421045902c001c06041007065 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 634112805 1250 634111555 634111607
    0x10608070504080d181d09060123100c080f040f09060e0a110f040609150315030b0402032a10030e0a061a060a0203030924162102040501 60
    0xc5813030481202c40e0301d043c1c180752078210760f00c801003105c6034400013014a01300e0302411400507540b8030034490205034003161301030390b658081c0720030f0080d82e9180050070a030101071040303d51134000000008a41186031565000b0039a4440031802d0384007107180c200c21130000400308001d0091494240003010312a03000c0050510700f08003c1e5240d00000d00213810660f88010840721005004c042c0c503207144100e1506a11607403100c1002d40120420700035001e103444083c0c1101600792083c0501c8664080f191601e030a000d00c0c60361156610341d0003800c00c0368140503d0006940340c1800800380e1404038079903a114100c1c42240d40500c02d04901c5002108101810214541c00c0070100096901001e64421000103542c500c40c001113403c5084010305961013200000d00007500c650001c0030754014458030060300d003006060748107091030110b800354045010b91503c000610380003042045035448070850400d00a01c00640070851a410201c3c08510707042d650102e0280031700c0d64000c1000c41c3e042c900c0c0d140300f000c8003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 634114055 1250 634112805 634112819
    0x100b0f010c140a24110306030c061b1518010e210714030405010917070b07050102091002070614031302060a180f0302041802130f110d05010608070504 66
    0xc620600c1c00340000d81515a20001c4010030466201c405030442074200f03890f1101002c075400c4035201c0d018440064100554280c203d070042c2c0403203004e020010000d20005a504080c0449604115910441c040300071a00032030110041c00008100c4009e43e20520032031030003a00c1d4081041d450103d501c6075030300d02910300001c4500001d0007407000805c03810802d00210155540065841114002003d042d81d1140c5040e03c4000000940181d8401b621101440e98a40c0c0400d105c50003800f04041140d80b24000030440e801410000b41000c40c000e100251900922202103103003c3c2009a150300181c0c0002e0341001101c2e8024544101010140d00c2c0901d1810610b8240d29039070300c05200684191400901c405040307010f0140e40354161028036201100a0303841084201d0346540c0d00c01a400346050190600141c108581690f0381598010b00c11b0241c001c60041c10801048a0030308191480ea880c030311a6040401c05010b09101060700c1e50100c3c139581410780c01000c0c0c0d030018141a0030711009101c240918 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 634115305 1250 634114055 634114067
    0x60602060f0117030d1a03071a090f0103020702061c0b030304030302060402150c10090512040b030a0e03040902040306020c010b030f060a05091f02090910050d080c1c02100b0f01 78
    0x12100d1050220f440382001804500b58412000905403152500c195400d69018010394201c1ca07400840c16610010703560724140c480180c02104400d040141001244c41c01c2c50140564888020181f50050500c0703103607070103e2070303e40c490001c0f0042e06031a510341d4840da0b21076009010403144154013643c01c080ca10b980c003950301c0310041c00007445000044120580381400c035058810307030308424048480c08181004008000d041d5240e050760680506103072542c0901444048030201c4008045403403035a960452404024241100d06003880e0101300720024141609001070700c095802017500690700e00540042078210750011100d40e0081d0050160300f0180b0001080c00b0350b108400c410041690359038601807504102008800400c2004592110312040b081540034141d11031003a0740c81c01c83d685801c901d42c0ca4907806803280d41d0f889150030030312100040042d0041c0a10301a40c3c4121141cac9542159085c010391042c2003204016400318203030724405140f078028891074100903a8460203400c20f00c0c1c0001c110b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 634116555 1250 634115305 634115309
    0x914060a110f09041107020301020a0f08060901030c14040e030d23060307030f0f120509010f1707050a170a0504020a0905090a080c25080c0306010b1b03040b040e040303060602060f01 80
    0x8219920001c002c4443c2c841c170300700d80203594014000c41d9603101c000c0d030180c417504502c002c0d10005004000020040e00f450784080e8160b94003c13886500c940d01c1c110185801400841e650b903001500c442120600400400150016801c103010208086059000310001c0480019002c68140b4451041c0440d80d10f000c114101900d07009131025121861500740000b11501b1890018140380007444d00da0601c07540705016022141003682d03000e070524844a0100c8011024941c244200780c400e10210700c51358040d07030080074001098180410102c154490500031300030215030034440580c455081004524240b1383e400c01904004a040142d0b06011a01540e280302201c80180425000915540d651504100a140d400407080c940301510f0440c00307840c3c24a032828032443caa24420021030a00d103140101b09681a1180145518105400e0000001c035183e03410440c003003140010000441c2807140c481c0100060900407410031400c2c241868020205d80c803030340c00380c001c64100000344806841d41a64480c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 634117805 1250 634116555 634116559
    0x90506061c0b040f03050708070303050a0b06030906010e07210b0a170c130f09230d1209030306050a08281a090c04021803010c05070302030d0f0914060a110f09 70
    0xc0313240003440d003070300c0c0c61185000c043e100100c042042000c2582c1900000d2180c0310240003486001914814070909000640700208980c1080006124200c4e50300380a503444820b03850009140b09202d00c3c020450040b0f41c100c400240d8070780040b01900d09226181c0c2c00203200b42015a4203d0404510740340d01d41400510452013242c0c806400d403103104080c0c000050001e1080c0c01080b04400c1841c21110186281030b01c056006030340701d813101c81c050001c035a000d6140020b8843d0364207800c103402c4900003001ca50710202c042c10369031407000c12151503540d2a400a040000002e190f140030500703c001c1385400c214034115507032201d242500005084086003c151460030088001191149641e141c202081000111f422a10108e809000c00c030000301150f506402c1074008220b529602041140c081c4034424004d00543d05c104a03240b002c1d003495010085134804403400050414442d07440503d5504841c405000d1580000188000c02a2500c9241c002c44040102e032440d1201181d444c030464014650498 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 634119055 1250 634117805 634117823
    0x5040807091509020c2a010906031805060c0c121c020903011b1214090a021903120f0206070e0a0909020301061d0412030e060a0506060d090506061c0b04 67
    0x1200d003900d440b020308050106104151340b2841d860468903a1280c02d40c8440c800d4410000a020550403900755083c00703608103969405400341031440a90144c8840c0d41e05060787c0c043c4055401c0407800520546004010032080c059a503190303000c0441ca400040c0980e00710081e42044210020030a2000c030800c0800703c400056241c0b0090386c00a070042c0f0a060500c0400520030200401d46503100340b1030a0b00c015092400c00c1140c0001d20b41183c03c540c2111405002da011a0110f0050320f080040404581c0305000002c2c002901e990741d00202c9a812460403021848000d014405c10380c05100c0e4551068085c9095039400e403541000a51000062080f1140980c0c2c0d6120007056440c02e411150150460301501000200b400c01c1400d92400d0443e803c0d20300b9140303881541c2a1034407034002e940904854000800158550401c9003000300005400154003070740030001000c12188038003550100c54000c41c0030717051074646101404071060460070040e07103208501400100050702c0f42c1c00503400c641c1000c000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 634120305 1250 634119055 634119071
    0x219050f090a140903090415030f030c2612010608280204080303040f0308071d0609010314150109080f1c020a1e020103111204030c151410060504080709 67
    0x42d001010030ba021510405079040401031920f20010060045c03d5098804204140884031f50021200c0e1a00005103000790100040300070074841d1400301c10071409103060036400660f41c02c0300c04241c00d4446c0144594607010501ca070140b00041c1d000d60041c402400c000105180111483c0e40024404e0701d45018011000b1320074000f42640d038107940140400d8402c0340c2c0d40c1e00b010305101c0180c0d80b09544c21000070311040f0006680d03500c280121066840c06035408881c0d01c0c074403030030810f040c2c100410841c10950754176400344040c03400c0650203009056480c1c1c0020300c090b04c0740006110051980180c903499004400510f00e10400007600c11400d0310103110f0450b4603101070001c03810304118200140030220366108000008442000038041341303100762000c10200324100e242e440c01d80252413042010034031070000100072078056182d02107000d101303140b401508006181072100322920790035801d0002e0044010030407012441081c56014103402d081c202c2c2840c2c5001221039030346020340600b03c0416103402035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 634121555 1250 634120305 634120321
    0x3031a0907110f0a030e121203130816141b100305040f050610090e0a020d020f03100516020601090b0307120c0306060b180f090c0a0e0402070305070219050f09 70
    0x30340380b040004081540c41c9001e1a0400406441d03802c2056481050b00c40030711f1403080800a80b000c1e103911407500c0c25003140e40d44e10724480c07250301d1110143d0301024104108254514000b214200c50b0f1310030b2001f00400d1403070036403007031a114840400007051600325464000c41c2c2d40396010001030241c2c1d8034000ca600d0365549018002c00d40912001040d41c4141814131024100082140b426a00c80c00d408120300c001980049da513403007000e80081c1d04201001449000b50420498a01281c94054111080c004102800d20200e58084981c10200c5482442c0c00454917414007000d40103225042c000d100100d42a000a0b40f1111944145c2504100703510f8101e0400291068000c000c5400c401c01300710440c0d58102464095022103a032900300344040c00c400f1f100d0f1030040300000b82c9150207094252251340d80c4c8002c040300d51003c66050140401c610543c44595135600041c03c071284260f94145c1c9402e001d105008010b41c0400e2621403008a40318140131070b88a80540d484403000840d0400e0303460f159825 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 634122805 1250 634121555 634121563
    0xf0c170903030706110c0d020a0816030e0a090f0b180a09050f06040302010b0a150903030e0103290a0506030118051302040c020f06090d080105060f041e0303031a090711 74
    0x10f0010102414007000c0c560072045203010742000b86140c403c0d40d4401690040898507000c000030020300741c0c0000e210981e4000f0750360305200825031181c108196800c103188002800400c0550100810035100c44030309201e0916401051034049003a0b8020600920b1041c203100d2864000301440b01c00b030f940d0384a02c014000200411480701d60142d00303032500303428141802400303060444042405a0003c00300000c40200355041c01d880c00c8030726942c4008943c11176804a4038110420361542c101130702d540098116984c40c0340d01689c4511803200040d01004070009101414901e540320910644017070004008400c085912a01b41502d120400541c540e260400070500e04008500039404c9850403101c400803540000d12042e542ca00b486c122140f07991550180c0e0f548900f6081c103200018014001000350f420264040d02804d0a8228030a007095110580000c0c2222801c95465140544038400c10505030180725440c4920310385010804042040004035100d41c401400030020401100800392280d203081c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 634124055 1250 634122805 634122817
    0xb0306040c0e09010f0905100303050304120216090906060f120305070203150c030406050f090a020f0a0b0a02030d0b18070c0c090f0204171c080a110a09060f0c17090303 74
    0x40c10320f0603d5840c1c1780302c6202c0c07138082c0c092603003410720381004100c03590309120781c0301d0459600d9640c04c0c2c0b0310350313a41d83d41e040b00b241c174100780c4000d5119071150107d04004402808018049510000504203c607003010010b6401c07a52242030400c1ca0110b0521801002000d104180ca4050400c0d981d240c00920200e0300e410444611000407890840c28003c14040d80d50007540218001e29084c0213684641e5500e0a4034241950480701550228041d00c005040c10360801d4034100c002840c003481c1a640e191040026801401c039000181c00010f50707001026128840c0b00b80d00384041d50700e03213940d07684141c8004c00524003400c0b51044c4001c01d40c3c0342c402c0140b5510110701404043c5401c0c801380e08020444e401a41048c0621110040c00c0040319a00400000c1c02280c4003404980c84030345c4203200e100603503a0800c0582080b200541754100055081c0c104001458248516a11300c001c0030715007200100703a80c03031010f03284003004902c0b407107100401c541c240300703104600400044a554044500c0082e10390300c120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 634125305 1250 634124055 634124059
    0xc25020108061912031e0e010e1003020c010f0203010e07020c09040b060d020a0e27191506061e0f09050906031e061f0b0412140a2a0b0306040c0e 64
    0x80c010b0008055201e03601b48100b40810070920395400d94104151001041603a0350b50000d007100660309018a0b00c0d00d18910407103001e040040c03800c0506892242035402585180340c025400000411400c2011400c00798040c40b14406040c0e120300c0e0380300292a800c80600042d000c00165400b01e18282d48e885d0071740700c2143e40140308604140e5150394101c81e0610403900c100e106000d8580074010300b8003610301e00380e50031481400b40000c0c202c4019a940c29100c0a40141c071103400d4003c0c81a10f00425100300b0000d0030380c07911802041a10410b043c2d40346408501d9503c200140d40340380c426070176007011102c1e0030307200122a41480d5036100404640b81c00b1301c2c1100042082e2503100d1030844413101140780780c001c1205000714003402903494410103e000b40d0b44903419451504210401c000c051f800b03c4014404c0c450a5039203140354030084482e2a000c0141f0702584e100703007425410148440303040803410000241c00007a0200d9480c0c02c02d03c140701d0100401e194021625211045406841140824021480 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 634126555 1250 634125305 634125329
    0x307050f18031504150c0c02060304050a1506091a030c040c020f0a111e0d0b1312050c06091605190f0b130806101215050c250201080619 60
    0x5203202802124000d44003070705d10000c0e104c003c00c00b403181d03405140d100821680324803c40c0c607425401e12407941d00c0180141d405004036114080000c036190030f88001e00c1801030300030814505241480702129100322040044409800f103540060b240826543c0720680c0440d0001000030b4520000d90410724030585a100d607010700f04a000401042100c41e51144c0c4040d10300d40a0030f801615444402c086404451b684a03030404080c100103182c00c8112540700b402a05c10847c0341c4034595600c40c1c070340c00000c80c800200d00081400ba2100740304001003a4000c030a02c004004281561010910412281c0141e6028502e01e068000654101005e210020b1030000700643c030480d900c03011400306400050010b0a80c155001d8002510f8000044660154032107040080c0340c0303071808500068001d403481d02240c5041d1444000752100400b1310800b4070450700c2141c02c0b036a9481040240c0032540c480501980300700c5c0c4410117600580d900c0304039103034054420b44a801d00c05c0035202040488250f10b0b8410340400324 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 634127805 1250 634126555 634126573
    0x6060b0f0406020c03031201150c170904050a140628030605060111030a1e0e03060f0a0b030a080405040b0102190309031205091e041103040c0e0108030307050f1803 72
    0x124030080c4100c8030154250340146110000f00741c2c4034450201355106800c010001841206645181415140c1d400c0c14aa40c036001c540da6034441c14aa030f40080760046401260b104a00c0c241401120384c005490304003000180d032070140c02d044004d80503140e42c1c0510f060045500443c68049016120710349a001d42d0405d05503a4600b800260404440c0304ac0000d0540d88d001d51010400800e844149405807280400880008900600e000ca1171b0264410448280604080350f14184001402400049100c601515009038080700781d502c09441d041c000d6000d01410f001040d0040c040c1e9042d10b004583c08a044416200101d00e0485100a0303110800c4002c01103600b0140c00039800c604a900c04c080188000c004180c059034940a0405075030b40120040e03e801646c41c0810b070581e0090803000b000018507401e002c503804003540040741c0c11100b84a02c40d40078000700008085482c01096114001d515603e81004001c00c54010110045250300d004034542089500c08040b90140d03170b2026088407541c1d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 634129055 1250 634127805 634127827
    0x22030302030c1605030403140a0c06260405150601020304050303030a180b07020105071206060f111204060206010f0509060607030e0a0b0a02011e0b0105070201110f07080a060b030102121306060b 85
    0x3031b20074801103440750070310581841490400316592030090340000c0000240707440d018054444c110f2804040b518100e0465022070140b051009490041d4000c000400d8004221446030801100c0034003124199403041c0020030003aa400030440780d04c40649500800d20608009031754029050030a0001d180308030340401c10035129415889075214011550b105c907107644101200390100e6160b03020b0744000401079644034500ba07000e0307586140d20105070343c1155000500d030990340106410580000e00180c000d01c00401150a03032402c000007500088900202c1c40c10804000b6240344160f01009050290120f030445050b91214801e4000b0110001040c0e5207605190000f4020180c0000010111032180c04682c50802507100b000702d8010181c42d0030346400350f550015908000c0004414181c1d12401d03030601c548038010700c4003000500340c2c0c04c002c00502ca030030f2400000b91021008405d001e40e106219114604514004d5250481c004402c40c1000400d20b05040300940b016800402804500141450000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 634130305 1250 634129055 634129057
    0xc050d12090506092b05031c0c03110d050402190602150604020307021c03060902070308010e09011b20150103030801080631060507050c07050303120c1b0706030f0522030302030c160503 81
    0x123140e1000300400d0090324020f030200ea01c02c009a80360454140101158003003150f2107030f038000340024004444600320310032900701a25a0340050340180c124040501c4181c0341188181d400000c2101d0560031450141c034000d42c2d6840c50b01e81040600345100200708040d02030303849040a014281404d40d510b90032030402400d000e9003031040c640d0329882d10000440d014810b105141104100c02542a80126071140469036260300c40900550b09818200d4117156030f070304001c00b99403410300c490060b00a625504000c0c2c00742c1d8059000f032500750440001c001c00000300c4400d43d0900c801e61003029007611041961a6083c04141200910f031520740002c0c410220340080152603420002011a145d80b5141c00615440e80101b0884102d0000b588000c01d80400100014000d01c801e110010313080c0e403811702041864403200d988444007082c0d84088500c3c004065000e03e543c13244851600103404800400c4949644070b01986c041d041540c0070011800c919078613400c42b5202d203152503031300c64150340a06000d41c817 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 634131555 1250 634130305 634130347
    0x121050612012a0e12071e06140d06030b090a060c0906052d030a2306030307060e030d020d020c010c02070303090e040c050d12090506092b0503 63
    0x30948214488090004050280050720b5000140c452152800a03492a00d043c800e1241401401441c5004485a40b03030034503204256480b00c4010b140c0e0903c0c03d0160036a05402100101e60b11060020512201c0e4100202e10b03029807811000c980d4410180d5181e41c0107003480d4100916a59440003402044080010015032407405920200080403241c0415110240203121f410040380c01480404038659000c2d903202601c1400b03011a10701c95281043c0340e055a48112000c48615648007040404111031845a03141c80c00b07041801c620a082c034100213940c5e405800c0008185a490351090f18030b2410034400d80d500d0003440750095440308910582d010182d009400da800a0f9840e04118881755440003503201c044940603240c640700e031f0b0b050041541c44600000c209071102c2e403003281d0008060f01e0761450116058003c043c940902c04000400506010311680160300c01c134011300003292283d1703824a03010810038482d61264000010a140321b00e1042040e0340c0604a4040400e0a0200d0450b050400e04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 634132805 1250 634131555 634131559
    0x7060b0111010204150c080702030a050d080a0b0d02040b030c090907030213060e18031e071e030806011b0b0408070b16020d03230c0a0f020604120e01210506 69
    0x14161103141c41803c0340a9485152580f04840795219040c0c0e0040c403c450500d405854410310300400342c0c010a251581d00302081f00c07154003401c04014400c0e1310416142d00302040140a0025246a40006d03c1d00001c08074040d1040b0340e0b4180b03625140e541040f0720321045c0350282001040d45172003d00c00307480344003d01c41640142e00c65140e4603100300c07062103880162040070f00541c2071521000810010340c1640c0580c1440d078841082040c0d486000cc41040346504950031076695660703a546810b01038010340400f20411a040d0025040010341c001054581c4200217180010010701a8950005510719100005d40010ba040044c070041c80100002085160b000d8940c0c207201d13072209007800d01c2c0203201c00000c2005030801ca4044030042e204e41c12581210011542c001c148005800c00040005000da4054402c6400013031020b803070603086000c509050070107002801e00d07480d2585517148005401d1403000704000d0f641d80031170010385c003940c25a017003902038640d0f0368070803540c00420030002c0205454240c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 634134055 1250 634132805 634132817
    0x105040c1404020306090f0601200d0f050306030a29150f0d0f03140c0d0314090d05221e0905010509240f130b0a1d0411011407060b01 59
    0x40071420540216030103007034050002c900303d617545100e641d482c01c03015004070b040200c05846d50b6030010081000180320030000d0041c104003180001f000c1c001c1e02041c002c1e5418000d00f40304004042c0d40202c0d442d0402a00034510101d1404030800f141d4070082031184640b0b152000c2810310000340c031000080d071103d03c415184000b003000c0d55030070030015a1800400034411215510b451002a02c0f50000c001c401c020500c600f804c0a04159500e410b100c088400040000e55804020004a10b140c0380b0540003040400505001040700070010010302c5000082c001c44002c5081c441e00b8a80780b80c14071b0004100c01542e200e11ba415003021003908420303d10032500944c0c10b0000105132490b0203034441e809009413140001c42d4403102403480b021042d040e62890b6210610300c4880d50261190520309881d2a070160300000c04402c036100700800100641c100300c10074840c0c140c1040e80420420401078015401c41024500c40200300f00407a00d01c03428213400440d407007022401d60200551074100701c40004090b2903032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 634135305 1250 634134055 634134089
    0x40b0a080619030506070c02180711100501060903080f0c0a0b092a010305100b13080f0c010c0f061503060605040e0c01020606100e10180902040b18120105040c 70
    0x1080b035400103800003404030f03008800401c3d400b5004240e45400d1501c09040301020500c09462100c00717940458160f408920a401362640e403036400d0015818075184840208059410032034006d110000500004108103400a0a0116103101c04240c0b2400c20001d021203201d20131070301c1d0500030b2007000c5d9194941071089502850a400d2565072000d0410910400e552030300070a003004501501001d40112a00348061001081b104c4404008103103c0e00041c62481c802843c4c4482c4620301941c4840340144d54003d041040016a4480311203000940c01ca08050f00b01d03c2a4100000205008171186020401680d0000704019503a04448100e5504440820020713910004558031100c1d200703221801130300242c001070191b18282841204815881ca00324282e00a0580404c0c8400c0100e0144070226012003080844904622900d0010300140d80c0c3c1942080e14004208000e4042c00203030072803201c4440d0701005151212038803c04a99183d800a01650502e41032024982065025031a000d841185003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 634136555 1250 634135305 634135339
    0x10e070806070804020402070f0f06150f030510110c010e0d080903090108220602130e10030807080a1b0318050109080a02090628050a05090403050a0c020303040b0a0806 74
    0x10442c4180e00980b01c1c400c1c00d030b6455003000000d42c4a400112a5442c0c00e0003040003207010049855881c1e0310810380025204402c1102c442501c0499010b4040c480640605200040780810070016200c01c00001040074910301191040078000c0d80030002140d8602030035503000600c0012000020942c5d034545200d25207a40c4600c80c0c580c4900711603580810101404528004000315240c8480c24200d980c2d0301000d103065a400083e81c0c0300c09405440c0d00c5240307a0601c40c502c08010a80d40203881801c000c0203a61844d507171042680201c2d54040c04000003c9880900c440c016070b40701e004060701816260300000503250207080f001c01e0408484400c03a030400c006c00d07694050726003d803c0d10a4407005104400a40d07080050007140280300340d421256400091003084981c02c1c2040710306080c4090b0300f00d458100010300017442a0365024a07c41c0d8010070030b0002082d000390403910800e00c249080003c042e01800845e145200d01c1d07000c0380200340001100214903500c4084140039110450b40100b042e044508 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 634137805 1250 634136555 634136563
    0x2010e0d1e05090d0f031101020f0403020a08031204030305100f0303020a0302010b0a0602030403060f02040b1303060c0c0201050d050709150f08090c010e240f0d0c0903050705010c140609010e0708 86
    0x43c5a4001d5004106180400c060048000e8054070914001c60790450580030682a40c0240d4070b81c1241e03c0011500b8802c502d0b207003001e107010b42030b24401141044284070503039034107400240018040c55994030215a281c2d030303c1c001110103842501c01002d0b031039550340340003552560104411b500552030700b0502d06043ca0f18030511001c40c1c84660046007050304507255000281584154100078580c2000002403a40c2590050070815101d400300000180c40c42c00c00506517203c0260060400500b400c11100503a049810740340030701340002c000501951014800c0d11220b000b500902d074400003d2407020151544042d54540703071000b03039842000c0f07511540302041c1e807002e899018078040f411207001036048c0d0a20b0074200c200c0d50a480e00c5182114489040000b0f50750120000b00c0c1d9060b40051039803d034045500078000650458075000f50510b1564440b00d40300c02050040c2d40c10484514600400d0200701007540311456200000d590080c2030904681e4001e1100c00e8440c107160081400004800f44042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 634139055 1250 634137805 634137817
    0x12020f090403091e080610060807050a0504030807020d05010905101103010b2b020f37030f1409061b0705100f0e01050f06040f020702030c060a02010e0d1e05 69
    0x20f15844903e90130030038071012890300600405001042d0b0500000c52800c03c000346401800490104130b41181007001c01405404002c0c1000d040c00380803c03074003003c107034031100300c50459030840d29403512042c2c10710000300c401650150141456083c14800401d100010603015a80180c5901c100036296003000000700c03e000074440e10348441d00502c9905410b5841c42c0b0320304402806227a0380010541408803007000c80e080840b8010f6038980100b1a50165440f1030540251141d07040150004200403401b50a0191006440c1c8010141c54047c0600045941d40101001d035000600f15501c40c68003a1f032061355814100d81096954096040045020310a8001c80d08401d80080141c000301100516440140804003c800c6001d035407108604800030080c40303000d0080240700711101ca542029401c0000307840c43c40e0401d010091040200340c00580e00080c2c04c0c5641041a100c25484240003c0140d00401540000e1049801070f21384030042c259001001503a00d884d40504001c8001d038007102190580102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 634140305 1250 634139055 634139057
    0x1092d051e060904091b091109061b10020d0f050a020c07060804051e0606010f1404030b0c07021c060f090b04141e0d0905031c080c090a12020f090403 66
    0x1200d0181c40d503003000c030000c00c01c88074013400105024803e603407460111a804200d1041c0d07010441410300c02c0c1e100c1801820902e140c0b116010381090580f4001076000d01c204d240c20a03009891040005842c8018071030b035400012008401c40d08c8001081c100c1c0c020b46407a0030304081062605000031090025031080e50546882400100881410030710709541d1130704003a001380c40314440e0892601d480c00700200c42201c0485000003503d000c0c1030200025100080c4441b150040c080d4000e5540700c3c18072002c0650b1704a0780c00400813040d40e2100100c5021360310032810702035008a030000c03980d88111410a6444101c600c1000d08000e4070a0000074041250211880203103070480510110300400d64038068880300c0c40c004415181d203070150000140d030442440444140d540c10420706440200e4100c2c03001c6009000540c06403903a40c824100349225106100185414012500080b80342044140305072a81d2540c050120380c02d040e151800701c0d00031800c2d050124840c0d441d02d6070407406410000d48287c011070341 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 634141555 1250 634140305 634140349
    0x150a09050705030c07050c04050c0a1b0803070f12020a0306030320060403030203040809090403090f06140d05041b1202090a020c12030a1503080a080f0c0403020d0201092d05 76
    0x80c18444d0642039000131002d681d50301c102c41c0106460780c0c0c4c600c0b40c14011808200815611039a2a002406c000c2c4007809038001102c3c6101000045100a03048a0344203405203072000d0303d641254001d48000d0402148145030741d05c00f081851714241c0503801300c800d8034006d440b01d41508281000100d4000c5207414500060303003002c0c0119000038000c0d00038680080c800c01c503003801d2920510214001c00c070210740580005883c0242007003107860324000344d006030090345841c440c02a2010031000c050b102e400c1070345c3c2c41c0640d281c0000b800c0c04800445503d440382894044240243e942c0071030003004001c0c90060380300e103070718a02142509901e8400c8070035041c01c290142040760030107185a461600004c010843c145d44505034100c000400710500000b03903200780d00e115111005500000e007141c40c0206050050340720b55042c040681782000990301165412130b0f640462000c2c900c0122600c03082c990108040480070b510103602c1e2152070030040071491800c07003a6090580d44004200201e414070010403000d41e9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 634142805 1250 634141555 634141561
    0x120a0201080c041d010e070f08060907090e090d02100219120b03030d0203041101050429041a030a0b090c0904091b060f0201150e060907021203150a0905070503 70
    0x1020303011255018032920300742c5051607501c04401c1d60082d98160303c10038100c0d2800050280d1108004c0164000c0c0c403615102d80c0c1c0d60404c40d0050180500640110712402c0c0c0f100000f40b4061042c3c1264000c3c0c90b0712312241420f418201320b2650781d05404560071001d40078459103044070401e144240c0c0d030490302d010340030701d184084d6901c20b4800010201800d000540c44080d801c1d6985c904000403d1a004284001a641d00d000c0c1001c40d0304550400701d080c108135081008021100d090017000801d22281141800c075444413540902091145501c0007500e6010181304021481c1c4070800b81d0311408140005001c00c3c3c0064081009030b000c101c807141c440103130a001034141e078146030340300150803886413a108101e080c00c2401800b495240358044000a0601100d030074107a41d0a024001500c42c0c603d1441d03240c0d50404c060010308030300c014411401801000c000076800e83c0708100605100345000d050955a040000d0344207144003900c4015805480c100c00d000400c21120700c1101d208007600d070350b1181503803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 634144055 1250 634142805 634142807
    0x9050f190506010e060408070504140f04031d03160303021615051e0f131203080a0207111207172a030a1704090c0c120e0a08030c060411120a0201 64
    0x2000140c6507504200c13000c80003030f40b1526440c0040002e008028010700680b480c1104006c1503403600c0c48200642c0d08514144070300500e407122110707081030713260501c0700c07402808481b0640e805542407411a89032241c400c40803510308001c1aa442928029030944400004c070100ca005900190f1003213018119890f510710003250700c54800340c00c4890001403c05180c0c040140b2210b115000506580003d01d40040e1402600c4401408200104900e00032591500c03615240a40000c000926040c130450700041c4000c100005950b10000e9a80300034445420074840710b0503241c1d101068003400080b000904a14243c0003c0065440c5105030010b103085040358200013a4682d41040c0d84082d9010b02c0303041410700020310074400400a21400c07040e09500e0f5880d1007890010340e4140049202880125090100855080b02240c440749416003091034110311240041070798001c299000e40c000e800042261100b90701c001c100980154007412072203c0c0100407a040080c03449110340c400741c403507000b808404015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 634145305 1250 634144055 634144061
    0x612020f10120501030605010e06181f03081603140c07031103070305060f060112090809150d0608030d0c020606060304030f02070e090a14190209091c0909050f19 71
    0x1203407507854282150001e03501c01c2400d650003a04110359142c2c60340c006103e0b2403d40c80d010b5511050448070511012540c0c4d007541e60490020b070400303010507901d0102882c017100e0044028011503102649940d83c246419511412406d01031703045002405010984010090a1090720310848010740a840540d1856544c50105041010b000382c05020f0700c02c0c00000700781c0500c5100d12800c04c0b60029180f07850000c0c0014101d180d80d515007250036140004c0e04c0302203482c1d9029100c1151058506010303da0000d0811100ca002e10203411810354203028010400381c038040094403500b13216000500a18078102410303a115a82110050b80001040c8005008644a039a186010344000d00503030b0b001a484107280503a8100844503403205a0000c1c82d0041048040b04020100544107005071150718442c00c01418400d0851502901c5000d0003030209048441c140520a5441860214500003034014500a40910440c0c460915207501d084d0014000b15407040c4000c0c0b09001c106207000720a1100c203254001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 634146555 1250 634145305 634145329
    0x80d0e061c0e0f0f060411090c0d05040303060810060504150605030408030406061d0106080f010f050607060605130e0706020304030f02091f090f060b0c0709110d05010e0103060612020f 81
    0x2540302d10314402218080138402802c2c00540e40d03016112501d000e00308410210404610240204a444100548405c00c00b003624425800e12401260940312400c044000c0c04094008455501038080264011206940301e142214410380f814403011600d560b00e0755402c0118071407540400c008000003800a440000255801880350b0340005000d0f80b5001d0501c031800d0b0700c100c0c000240c0d004c04014440e480c0c00c86500f603803241007219850444d40c1080070b000a036070b1309807241d2070050601049010070029103410200c050400904806140412100d80d240980704d024442502801081804101107201204803015690441f4044100000c035a003400740c9401c00400c035110000030050308000a41e400d9030010010001d0304004035080d40e4448810048900b558003c0e00c0d0443c0c10480900024004100c4030126020b1400000303130081c800c20103411a01c41c807010020010718100000c102d40401f078000c1e034140c900a001c02c1000365182c1200d103a044024500180d44a81595040c05036407802c540384a0f1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 634147805 1250 634146555 634146581
    0xa0f06110705030f040e0a05042012060a1508060112261b0616080f0c040f090f051311090705190206010806150d14010b0a080d0e061c 59
    0x1240c400381d030b210541150040c2e0700c805403802000904203c210400410705030041800c080400c0581016545d11922000a0000c540c40050700040c0c141c990b600d00040180c0802d460f406c0c1e840344d28194003110014207141c480304002e00304940c4003248040700000c680381603c0e41c03070104c4011a5100d442d80368a00c10805030b42000456071641184220200300301510000c04481841c00c0120900d504190800400a0014426042440c1d131041c850f94426a01034000321014441980742c3c8451001c1c20715032040c0e41118280042400300015082d44039881000d18011380c0d034081042e601e914000030031541040001a2589130305195003403241c40c211100c150850480e0825614288040780b41a0f1240b0340b030150540507070821001006543c4c0140607160b80102c6410080000f04510b40015000200d84203001e000507202c2d0752103009090095000d901c0e2600002c10742d401281c8c1e0360031519600c0e030002d000040011400071104240d400c01406031b40030f0f01e2030246486d0305441100e166600404600100e08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 634149055 1250 634147805 634147807
    0x50d0906060504090302060a0e010e0d0c080d060e0f1b030c0d090204050112060e03030106410304120206150f0609130204060908060906070f2d09080a0f0611 69
    0xb5075a0302c6109001e41c9611903000b420385458803013a88402c0301c1e030303c050110343d0364100440e802d10144080390000e20346072541002106241c1a003800f160f580912804108400d10b45440400d50350700c0700307203803611508600c10000c0c80d943d038000d010041c240602c01c06c0700c4181424070200d4115810400a011203c0480b500080c0408442c0c000606444081e80b251f100c04001c00c52480a1124a01031007035903001000040d8a107500d000001480010101d601110400003030308200340400007400d556000da115400c1c40d00c410400b50328119026801918201ca41e04c1e084d40c3d140c40300d24004030310144201050404040214101c206000306031000083e078517400003042001d0101551450448042441424001030311241001d901800c080600d800c8621164410001c00c01c402c580041c0456001c0c10502d828001824a110250f40d154090113601054a0072802c00503c1d8404003070704c0301c4d11b40e4026900c100d4041d5550400c0c0e601c513000110040d101d042040414408a052600115402e8605030225 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 634150305 1250 634149055 634149059
    0x50108010e2802030a0b0a052103070f050d110c01090512030408010603200d0c1206060e150109120b0114010912051506040216151e0902030f030307050d090606 70
    0x1c0740007207203010100300da0b86902000780800b0308014440c41240313243c1502c0442046003040000f0f4044880650b0f80b6141c8030410228451181e0300b4400c0e219901d0784000303134190950003440d05984550000c4022000501d0703000c00e1480d20100040c81032403044045e1120b118a50400d03062102040901d21201060f1001700300000d01024244144401140554524180040c403c00c1e041c4884110800305407045c005507480d2408180002c10034002c80e54250142e28000c9140c1c17910b40060130659104001c0c0030301c0001003002e5006c0300c540b00300b0406400d83c0c4085d80176840300140385222040703500107446144444010b00681d100540c0810802105040020b0155034138090900d0b90f148070030044a40d500071046481c12111aa144150881001c0301c0641c00c040000130b2040059001007006040301502c2c14203e51003000550040000e600c010202d050307a0760003080303000050480e0000c201d0080c410340901f80700101e008020f0728001d40556849624100c8407813123003c064205c86009450b026614900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 634151555 1250 634150305 634150351
    0x120a1b0f0e031509070e0c180a0302090a021207030e1b0414010803070b55140906071b0311030a030501060305090d0801060f090e040b16020106050108010e 68
    0x2000742003480c08500d208503480c1400003e4100744030340c0e000030301e1b1844500511102155042c1a20284810340103c4000d480058000035aa84c0d500d6002940011900052102d00c1889400420a03403000d100c5da0f511a44406000300d00310340f20040510f64941080301107142c2e1001201c0440761002c001480402c134802c01c4010400740351021b0340081d07460351000640030200030910301e8240e8041d40007801e820362655070f11244500b8800b461001c0e1031540d240022540710b1a0036140f03440d80c900c0ea4902c100c1200c92120f0207000140b042d01306030507180e461103000816880c00020344038801c0003543d88480d09100700c0003080c071025405840c03c41c02c0c08003030107001103440301c100050b0440f403405541c003081c07a52400f44040d04440d8081c0400c03100360403a072205100c0d5500108800e0451f010303845c00c0d03514100d80850448042600e03800017401248010140001d1040e00840b060160752040c8001054400f103800503800c0300c0c0b041c81902d000ca01d660004010080702026025804030130441e00c4c6480110f0400c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 634152805 1250 634151555 634151563
    0x1201061707150f11031216171509060a0305030c15010b03040c03030e03010603020613090c050712080403030f090b070e03030f0909070c0f08120a1b0f0e03 68
    0x40403030003245010462062440c10030902000340080001600ca98044a5008020b8140212444244602250080c045480400489681c40500d9402c000d2500b050300600300c3ca15400c0d40000001101ca1101140e003c900d07000d014002d070100444404042030000901008070740041010f58000c00c006800404524240b000300766146044005d01800c180c60841c0b140c6030501a0440400461f080c410000003d404600c0340080d40d4240c1004010b03461041d0000e40500260340000750032007804100ca401f642c0c0d480c0a03c03815500c1102003407043c00d03480c8504030340901824901908803445200c46d5640d5501441b5116040740c000d00c3c010543c0f005100d141025500c2c440001c5171720202c0401003080c03455000381d18011110041300034600d08105089110054080c40c00c00c0351007090098041a4418000c0725480c8401d035029540009038000c60410110071b8020314110141518190001041580b140c803c0700d068211442d29100c1c440320b00003003290b11031001d2569209100640e00ba100496501300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 634154055 1250 634152805 634152809
    0x1090806010f0503191a06041d0f0c31020403061d07050f01090e06130e0f10020412030f030609050a0b030f030306010c020d06060e0703050619081209120106 69
    0x103031412040c43c0c071051603d00324100100c05440c95a10907010000741416150b510a100081d007a02150303101c10f40001c00410200c03520182041415001000400f00030600340002e051000650b16003d02c654288081800c015032210070341c030358554100640d40c03500c070541c2c00b40c41c45030807005003481d4595a0300002c40700700384400115a1120540102346030340800040000e81820340d842807207854103400107498041d0324050b8842e890b2107840020030940794250102d59901c0900028060101c48440b803e44801446a014185011b002006490401d45000f01c0701107804070800d1040071001c6445c101c0b10700c0c81300c1c402e9408040d1660800542000607025407030144860080000b10a00200d0400d480d215245010141c150005d03c204a00ba81e04054403000944d019030790085644a180f0b40b6000814040d0041c0482c1011f000501c00880c0e407560119208000c1a01e07084110646189100c00c4000148a5502181d10079182203410a0949001d40003c0300054924072008a841c0c0216096404039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 634155305 1250 634154055 634154069
    0xf03110a030e010b0a060503150102030712030b09091204090506060904090308150108060a03060207081b0105070801320310050a05060f0604061d0a0302040921030c090909020109080601 81
    0x8016042c0e03990003e10803001da642c0111000b00d81e00d85802c0c0007074003034000100f084800700150b03041004076900a00c22500020390100c207003e04d240c0c1d0f084015000344810a607040c003a00000000840b03460000840c4920340c0700300f80c40ba034206440c2ca10b43e0800362000801081d0041c0341070188103495119401403114051183c1ca481e02d0364a04998100a8102c19400719410003d040040c440b040d21103105010039a50070100150783d0782c5690400041500c01d8820480302c120880381031804108040d4043e6001d40700c2503440b46004d9a0f00d510342102d00c0c4050038800800b4041c1005021084003d80c2e00e00401c400140c140c03200401c0d012030540403030343e086030070113211603e50082220a182010b4560401c4804841581c240744c140b0320000c0280c2c03d0a950307200c074042e859003144000d603a1080560b00841c6e00800501012805140032404920400001058405403118860549010340580a41070303030f103a900c943c2c4003071400d0203020240c01001c5041e8144a280c4102013019201407202902800340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 634156555 1250 634155305 634155311
    0x4020103090f0327051c0606051206010303090b03060112240612060602010e10110f030a090201031104151227050d0e060405120c03010e151005060306010f03110a03 72
    0x10202ca0342d0b0036901c021240c00104014000107100a07950101125030001c4522680483c1c111340b450561f0040c00706420171548596509074007085440000b50160603644a5980da070b04003581c0e6800e000013800203866141c081940001c8283c00e28120340d020381c4100480d65081c01c0300ba21a0748040b5000c2c80603401c10360000e941b080800d18a081c0c01e00030440108020f1000300a441c15010b1019100c00004030812456030304e8090440f42c1c1e01400080d594602c00e541c1003665642807444402c0000d10246030120702003401e010380401410381800a41d4100c0d42c4540d0401030102e00030b54121a401d01a400d1650071a9940325055044040f80d90060a00d0a00e11032281c211101d80c04c0c0030789000c1ca14014a810413006c02a41103458680e00256800c45500b503607980c41c2d0010201c00c00c1d01300301581034500d805600c0c03e10103c89200000424800e80d0100d12040491511014100a141045809050b130080d8007000411180c0d440707030b400802c40030540d10b0000303548030004003103044903444aa4000e0010703071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 634157805 1250 634156555 634156577
    0xd020d060e0d031d0a141006090507030c080405031b15040c05010908031305060f0c010908041706061c0305071a06150c0a080c030c031b01051305030306060304020103090f03 76
    0x10f058842c25840c041c1d944080ca004800410015680780b029481c010014130301d69805004c0080d04000100f810702982c40d0500096442c0d00000f0000c080131a417a4002a00300007071020340c5401401c11a00964000d8040c618000c90f4984410007204540024856881046079041c041001c0c40b50b281d00440c401c00130044034900d084001003031450160042c202d01e40040184448840c2d060701c0080c1240c44c16100a510fa02ca290780d54500c0e4054110000955401d02d0440403c02411074020300903544002000042c0201d1040d03401d1703541c4011901c0d1038100d943d40807a850480b65908890900e0b511a00e4180d1030080103941d20203601641c000031009151040050240d14600303c3d9000c442200100758140c2014140b420325030740ca003201c40003c0c0c40c400e07002556202c0078009104540a0160400032a603545220755045840c0d0030301c2e000000041d510b094081068084070103084400d1580140065056448020405c00d03242d102a201328103069951f00030320b00140c11118200c0341c0038040d8031000940c1e8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 634159055 1250 634157805 634157807
    0x5160e0108311115121008011a03010e0f030f090f060703030c0f0c0b06010c020328060606091505131706060301050127050414062d060108060d020d060e0d 68
    0x441c40c0d15031841144822900440c0c1002c4d00203654490450045500c400e480c0d9010400d03145185410030303440b80d420980844a2440d40782e91030380b000b98054008101c1014074140c01e9844c4e80b41545d00d1441500200106002911102c0252085400c010039018007417444000040450b4007042c8120003103903d450411303541d00e030000d070b0010340c04405081000c0d8000107581d03a802c00c040000e014906200c6d0051002c000e64900f0045808190010740304c665001c1002d405465030303a03461103021603540d82420301c04034526200300000e40880d8104204c1d1424148059000e4400b904100001e00742038080040021b42940140b0411f62104914400f801e001d080c481c09060940714141c11411546007165402c160714205c40c1401120546860710020f110349480c500f214038039842c0010403e4a21903082403240803c25034460340c40480d010f00c000c00b02c02c149000d030383d0082e0b081240d8540c04160080c000810506014540c002d10920040044405400d990344110440e00b002003140d025500c070062010301a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 634160305 1250 634159055 634159073
    0x903080702070e0609010509040609021c020a080a11130207020405010603022d0d02071103060702160e010803090409050c131a030705091f0e091005160e010831 70
    0x41c1040d240e40c3c1a03030f45424004500110010f200300d90154240d4800902804226401a1003550740240700d0b50220700c2204148038440e2030000300383e208250320344002501703810000310a1042c9501c40c010f461020801070801a22220102c400103800b0740800c12400142c0e078600c15503001c0c107101d07100103071940750203088946050384e5400140b80441801314808007561100082d5100840503141c0560388848ed85444c5605030404610a40c040c4208000d0000c800c1d008120040002c0c540480101c00d6a62402c45002e03500c0203215030100c64008200c0d07031a150404c0c0e041002020701480803113101c0300b081070200d081100381600195080c0c0c1c1d0b40040071700030301801c407105680000031001065041d0030000001d900410140c1010800842e4407191204000c2400700b5000900c2c0f2554640f40914140c0c8000740c80741040c2c00c4256001e80351500007035030036035528540714000e6181d41d1403040e843d55001c01580c40101c0900340f000a04044402203508906103070210340d800b100b908a001c07a0703000781d180200030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 634161555 1250 634160305 634160309
    0x30109050112020a09020307121107170a080c070305040e070305010503100207030918060308040602031315360308040e070c03140307091a0315010806060d021309090308070207 77
    0x70440042c00103009a9a249001070035940812001a03480e281d040c0f0544865020000e00b080b814201810f0141c0204d9100c080c1039940e0150207456031b10000c40e550400b103841100d00440200703c10b1000300b01001d060b940500b00e018402d081c01b074134068403030300c802d02004402ca40d140c2c0001c0d122001031005050a001034645601c40308000d40c00c080c1d46036406080e101d0301d8001c0316071109252282e030b0324072942c40e0045801181c2000c06070b99219190302000707450b944041034401082503c3c4000040355042800c0f401500080d43c0e03101e020788070083c20389029400c843c405103042c4416100c1c2d4404140e5072442c1d950001c501c1000003e95891078001c40a00604009240c44213025111040c13002181d000421620101012010242d40c1e503988482504d580b110b64100301481e02d4000300c041c11500c0502c0085001c2c8a0501c0b1004214030742c0b0340110386100301120543d8100c9002e2041a01e40811034010701740040d480d21240c008984c0b19400801192012002540002c180308107005d200ea0701071040b100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 634162805 1250 634161555 634161569
    0x3020c0a0b0909060a12151113030201030e0c04110a1107050307060c0c122904030219030311030403090612090f02360919020d020103050402061603050301090501 71
    0x1200070301d80244884075000d4414124080e1080400142c0540d80c0c494200020b000481b20302c00d0402024240310076460100100c400c0040c0c5081d0030341d69032a058000f5140d110712030300c100740c01450441e40110050310407408407885ca80301d84510b040083c0d070b65024070500c000301c0c2c56905072205d00c2c1040042c546800701e000c12602d9003000c4014059a100465524103035401401d00b1140071856140c50100000c1c10360000c014648054845e008100c0c1c40010b100514618640000c0e91070034080403050320303c1094074000c01581c0900060045650304440c0b54000714001e040c00100c0c0b8070305110b060007a03881143c1c12400038a02c004140711003904000c1c241c00d40c0024606c02c1000c0400c5581d200c44d1030048910203441900340b10004c250401c048002c0c4450290040c25003125060100d103ea102080305441c4d0342c0032405000c83c40c60880881501c0c010076240c00070003031541088190015401020050410390f00400300304228152400740301c150030b0007039219540d0315950303600d00750a40048030f0068003d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 634164055 1250 634162805 634162819
    0x20c0106140415050a0e0603120a020313440a0501020d060602070b0904050c09040c03060512120306060d200301080d09061e0306090e060f2a0a0c0c1203020c 69
    0x449140c4410000c017059542c403c0f81c0511945640740002e203054209000c03000b200d0000558001c0482c0d010003d4200256840481c09405881c3c525261041d20140c15a404104660703941042c1805885051030803010741c60160005001c40390256810281c60340d409031856900010440c920314014882d000080109202420009040c00d9260b01540301d0513070b090344125210004a9401001c10003240e180070802001009521f803648005006400248202840f0b0492000780d4600d6860200303002c3c1c15000c584921519542c2c84608006840c0c1105039103440041d07558944015907540d01003182c1e1158840c2c801552250303d4406881d1401e004060000100302c0011000c00401d134104420322940085a060f02180308400700c0210018002d551140c5420340c102041c114101002280c2c16025981220010703100f5903645505626040359914140b4030020b010b43e04000d8003441030090409161645482210849035494040c034810f06034000740c0c00d0104030000f1004244d0104040300704003200b40d9440c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 634165305 1250 634164055 634164059
    0x316140a0f2d1118090c042703050f0c012409021206040504051f09170705030406050f070c23040b0a150504030f03050406090f0305030715020c0106140415 68
    0x5070b80e0070721203071000b03103450009081c084031555040d00500c0c045400700809210740c50440307601c507a01d42400c0e25a0f405a464a1007407059940b00306501d0f6160040c1510310205040c1a0b5400c40e084c0e4040d420010501c1c0c803e0042020303c040c28000c41010850300046c124940011644080600400340d0040044030701c1000004510b20b850501e8550040040313800103450303665810041e0030000358000c0e003150818103454001047e01c60390700c0380e580d2600488807000c0d0000008141c401d14828001c02400a40c400c1c0300820406109200800d00c1e00c010500003030811b402c4e540c80c0c0e6940d01035a04610705c81190805050840c4c6042c0c0800444540e040714140a4205500041041211140a4031542c00d502d0202c00d0305030b80c000c1c41281c0c000d540c07040000302d0005090074000c00540060260b240015800c5c00d0000310340d0403074258281541e40010207146001c0e900d0781c40c074244144980f02c06040940900c180780b2140c00070700c2084002c1c4020b21178020030f211f1001c01c0004840311040001c0c140e500c50703541 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 634166555 1250 634165305 634165373
    0x10051b030708040609060209040c05180102010501080709092a1a090d110409080c0a05060f1b0d0e0d02013309020c0109020901090b090f010303020316140a0f 69
    0x81c040e000f50f080600001d00313101d141000c50107842044030180e0818201507140300c0080d40400188403030b02d40c0340e80c034600000090004900348d600030f2048500d20360101d18107100c0e5101d036610892040d8400c4424030015602132181d40000c0c0c0380c82c440d40b801a0f03100d2008006814070402050200364081c00a0347c50001a8000035041c028031010240c450184145620301507190740d40001d01d801d4004c0b40107601c6910348100703981e40780c2e03010a0031203043c01000003140b088010101e4042c0154619560140010314010700804541c102c80e1a0280c142d0b129071900c051018203112181e00356400e80d00201d14011401400d040c441c42180746403141103101c1821001d1402200c08040c19242d00340ea0150707442c00c07948103032400b40007006400b039440b031080c000029500125500c54540940207440341141a0f48034540a90f21480901c4064090f800800c48042403102c0d2090200449102d94603440d40566200307862807030110800d4040700c100d10903072044c1c0300f0700200a0701c0980c44210500c1c503059404000d18 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 634167805 1250 634166555 634166567
    0x70b0f0606190201110409020403060b011b1202070e0109020a030606080615130e010803030f01050418020d1b06031505040615080a0b030a0c030b0a14150303040810051b0307 76
    0x1d001110085010440b044680c802e400001620b0050051651102d0300c61031801e0082d07005100440e03010b85007c140c1c03010f40d405414800680c905d040d8001000080c50345540008040c000154400c50003241001b00300c0041c49940c0720f0280c00510001602d8608040001c0d04442c040d8016606010100c4204000d6940d0700c00520185c03015040c90a450b080e01c5042081602c0140d0040c081300310202c000860009000000395101f03090420340c48480c3c0e40c2c0c5e4428001114840c1540310145480d803110b990241c2803000d400ea03e0181b14440c1c84503800c510030980c1100b840960891800030b03844684038035440c111100c4501c09440111001c218031840c0c0440524012280c10f40901844040000145107240c02d5104020400010307081c0d9801e80b94900d01403248040300d000407190050050041030541c02148100d00000041c25410782c001d0701c0300c1d500c40681000400d24190305110401002c41c4200c800e0000003174481184c0000b265a0602d0101c280b070614264921900c5a5000d00c00c201101754081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 634169055 1250 634167805 634167817
    0x20102010e0619022a03090a14091303020f1507090f051e1c0609030906050720030c130b120a03020d0e0604090c1701080109031d01050c070308070b0f0606 68
    0x80300040c5e44810072046588803400208210110000b0321152030100701003c00245100710007254040b1a81d40c80d40c01400d484614a0740840d04603880c2d10004440e82905090140168000e00440304007130740c0d0300d401c40e2400c5100d0104400021124080c40300560300104281d01900118030580c01c0c0504120100b00341442c1e0721000d0070301c2003000c1c00312a6544c56660950883d40741103103801ca0310441a0502c0741c00340400f58030890008041d03c200091040c070503c00d8506490384203241c0d8210740440d01400e005065020380e0581d0501660400010301e075105580c6244080c020b20000c1740384410300d02007141300c0e003803240103109541140440307000095012030b8046002607c0d0410065448036640814628003e03a04001c011a103410142903007903810054142c0c00003001650810303244c0e2140705090076100300303040090100c4d150168880d01c00c0c0426260b803101c4c240c1032404505090707102d000185816000c0d402654180e2001403e41d050200d01c1c4444ca0b0703c10b90190406920b410418045410352180c4c2c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 634170305 1250 634169055 634169101
    0x603040609030c021c030905040203040201020a1218170c03120403140a020618040b010908070522060605190f20070e1008010605150405150f0313020102010e06 70
    0x203480500101405a0a40c0d61826005017840c2005920340c9071941119050301c0080c1c002c9003901c900014145018002c0300d101e80d034188c0c0944403a40c219503c0442e005001020041070082c04040318180c0c5200d071910070014800251041c07940140c01c0a03441c01c111811030018000d810082030310102c03601c00e008450440c0e070300028140c1a90742050036681004110900298030040000d0544030700020b206e562401e840c8226000c1107080a070f400199406d00d1188952240b40d0040d98080200303182c0046154040621000844a2650141d0742042160f04c079030030446c081500880d40da00c083c1520b86020303409074010f082c83d4000408000016140300c4403d43d141c030700c8000b0064080300021040c00b28500404541d00240744d68100540c250711400110b0080c081c0d0343d0301c1c083d4001214905001200d5a00284410f0103140a06281c14800d248520060b61005c0000400050030002c0858000711f101344d01c090858020501d40303200080c00d482c90349000030f9a5910071230a001a04603101a035440c41100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 634171555 1250 634170305 634170311
    0x60c0a0b01080a260d05070e09150915010302040b070303091a090304030f1505090705030f07031a06120303090a11040c090e071701030b01150f0228021009032006030406 74
    0x1508090405034444c5c0c20403150003074281750500801030340084a4542e01481100d49028582e54a1840c04030041020000c40d804500740010450300c4e0483d4040c020307001d106140c094030701500c44108a04541c80780030210000b030703603038000001400550402d00400044480851403103003405030740140d40e4092804003400c0000708075000020000080007035110b140072030009010b5480c101c9100d81e251a200e101e4a4040d000b4654107e0702034601207114400c5e240e000e544c0000100d941c403070710802484c00030141d0350003101c1310b0320044113240100080d5100302650f4000701984003403450405041c1041c4030341c8600940c140140c3c8140c0c9500406210180c0d0014540245079642c0e03014210740c2514003510440c1151200f200110500c9458840c4506a03515040c845c0460039031100119002c0312028002c1005030402d000300303c00b02c26180b00d9083c03001100240001c00702255000119058241806040070440c40001002044259417407010561145420641d241d0405000724a43d8440100300a1116039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 634172661 1106 634171555 634171613
    0x314041406090d1d0105091e0312070210030f1b05030f0c030f0c07061d0a020f010f02070614210411041e050a0b060c0a0b01080a 57
    0x150a030f131480f941e5180da10484c0350701e400c8068040d0402100300209030717040d550707200c031100030094a15840ca00c901422381010b14104041256942442c0709102030400340c2d4440c0030302041a80e81c1d04000c00c02100c117141001c010700c200c142c217a100c02c0c1051448007010368402c026503c00c240d203007400a03841e20703005080100c1d80021264131a000124600180880120402038565030b44030b0707440450701505003440000b0440641400b5505036000b1032141d0306525100300400007d0a080c20301d40c2c954410501c00a481d00c0d014080c200134048850340d0300c2e4008228900700c0720204001c0d11545040020190400c0207000e044d6016a15a0110301d19952286014442c5420341111101c01414000440c502d0340301505009101d0100503075103200e40085a100c000c0100600200000074040b2032500d85011f120149040c0c00800d440e0b4840702e284000641d003422141c1201d500c240354410301170 = true := by decide +kernel

theorem cover : BRFrame.Cov 633992805 634172661 := by
  have h0 := BRFrame.cov_init 633992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 633992805 ≤ n) (h2 : n < 634172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
