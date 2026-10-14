-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1090
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:11:56.128062+00:00
-- url     : https://prove2.me/submissions/4dada86d-a91a-4a67-a238-ff47724bd342

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 195863309 ≤ n < 196043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 195864559 1250 195863309 195863321
    0xa0c1701050d06270b01050f0105090a0306020a0201020405040f0608010510030b2403060a0903090602010608060f040c0305060c03010501140a1e05090d0804050a060f0c122c090702030a02120904 85
    0xa050300c9005842d4a040c02415101e41d8100c7c0e40443d084841c01e00380384010f45460250f46145980441100c0d42000420304079002000a10050f100041c50075444e0b100140855811380d107080321642d0340b500103104102c0300744226038100c2182030301015030303501d540e444202054000f00501800d00640d501e0b400198420400c1056912004050315840e203000d81c400002425950b90640001d49032000020f02d850061065030107039914280500403554441c4241e042610700035004540d458550507001000c60f40602504e1301403a000d03003000341c0d80c3d4074000004140310707002d952185103d0b070300300030030004260482c540010014291003144a185c0980109449d14069a40c1480d00413005005c5d01d0104400c2d000100265907044900b48500d0381c0300d8404a4504030340c0300c9810f0100c0c030000307000f8001c10700b0040842c8200c88149000d59030307141203041d05126880ea0126420751030000c0001c02d01c561822016841d0b00c143c0300d200550070b000c00090700941d24071021003654501030740018241c410b0b84442c0c03c20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 195865809 1250 195864559 195864611
    0xf470a12110901030b061602010e03030708121008011a09150a080c15030403091e081603050f0d0203041a040902070f0309060e0102030901050c0f060a0c1701050d06 72
    0x70040c0c0c440e81c2a2258856020442d110b00083c0750064801c1245070003026511071011600198a0b403406a0380191b0707103505211a820740c9840140084030005074010020030724081e19004d0010079042000b00303401d444e00c5a4000c8604c0f40d05020381008035400c9009280c0108004031201c8810b82c4030240307020700042000b00005c0c0c0082c009c3c074001c00c000800140c3c0500110060700e291301e003900c01e00d900d0f95203400290340080c000340440404001c10741c1550f0080c0301c2c42480943d15460303d662016000c0ca0710f21140da0b009010700d50700c4e00070001d0100600000e100d0300b42040162100840d200c90007926885140180c01131041d40c00ea056400c0c19581c0141c40c054a440710085680e6662810074503440340c58140d013200050425070300860380d288105441d00c1d2072101038004504020402c0015242ca0308030b94131401d0710388201d85d44642e941000704802400345511410028404132070b03c030010071b038000d4440700d180122a80b400411242d02c4000e46080c54a400081c0054030007122002881101d09001030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 195867059 1250 195865809 195865811
    0xc07030215061306240822170a09061403311403250b0402090c0c0105100609140604091109030d0801090b01030b030618070f470a12 58
    0x101d500c00c001c2000c181c808410f0741031001713102d580c5282211013810444150a800c450140c41e403404010800b554024103200c2c000159a90a54207091020380d00800040c10004103c00420003503680c2044c0c1c2001c2015114060a25520300501340415018078101c07441d014200c00c0c101c00300c90050020940640750790018504c110160040d0700195280c006642c01e540015402c1d03801e82c03c80078585400303041194040a540c41994031a020414500c00090045102d4442009442c0c00c128080c869107220703012100c0ae900c0328030b003000c00c024502e21139500103602741c80c02d0501890341607031005c050b14201d403d10180030840c01400c2800b06058090841c01c60b070184100244c00d040c0c030b6003110300715058070b070060410880d49215200441c10b8071703a02c0c9005a01074015001181885003800003524808031110100e42c0407503504c00141031500c1b616403280740480c810383d01510400511340c002942c0c0350960750321340d045200010803018415841d2100016446030004203e503000f8054404c910444500c400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 195868309 1250 195867059 195867071
    0x105010f36060306081605010221130905041101030b180408071a0106020114070912061e0b130507090b1309050406020a1116090216021f080c070302150613 68
    0xb00540900f403103008408150003082000d200040d05141000d0881d40168001c20200380007840360401480301919000300c0000c204212031042c510101c84200800c0722410000d0185010704104000408170861107040500705034941d23100d0b560f10a25503000350701e0309202002d5500c0318900b50007148996900180035a05201051310000c0100c9003050403100590001d000862004018490300c0c04100c1d107010114000c4281070200e80501142001400c0c4280e0303000845c0c0c00c0c042035081c03072207050400c50b084981d11071040071010304100072406040000010280100d0821b0341c00a0a0707510240500c000300000459081d5178410003681000c001c0c070036030404201038207080c03d262019600c00401d0002040410301c244403082400261040da0715018011603080e241032a4000c00030350320243c3c9400c200f038441012117025940d10440c40d035140da014802c4c9171407424241e40140524100030041d8003039480a202140c04aa004a81060340d03080300018081c5c075a4032100083c07a8000500c080d0a00645014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 195869559 1250 195868309 195868319
    0x1a0f01110709060806070809100e01020d0603110f09010302030706082706100b030609040204240b0c0d0f02060a05040c15031a0a030305090402030c1e0a080105010f36 73
    0xd44400300703607000f004c01c0c2e075040c0c0d0b9040d4041d00c2c08801580c12000135840b4910099492840340d2100b510040100009441c242e0601070344c0d41503400982040e21034000c40e802c00c0c1030f90b203001c2c498500209415030700050a50702d141c0003e03456280c40c0c42544144440000000c0464140c24002d4840c916241c9010919921110106640f06401c6420103a101c0b21440c021032122a1481620320820303000300800e80c02d6941d5820701000d00403039032003000c01c0702c0044200b0f803101201503500e401400417a60b00913101c0102040541c98502a0744400062200300044a03040c0c55000c104190702101070440880e69468920b4444190b004551010229502d4160740d4924190301da001040f13404101c5004000344004c100400552202612004011a0080201d0501400c00741c000d0755000c02d180d1040750031700001c048a00c0ca070020f0303100003680d60741c0c000840003a5076030400c445501500d003e00c1c0101c01070b80002d034043d046824010402d20f464061540149808101401c002c19000150400500c0143e0300c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 195870809 1250 195869559 195869561
    0x30c08030f1609121b0f1410030603020108070309050a0209010e0703050106020619050a0204081207150216230d030e1e060708070509060403030804151a0f01110709 72
    0x20b4440b00c401c0c00203125140161841010b510099600406845081400ca542c030b0961041c3d90490400111003400d0700003483c001e20700c806000030000d582e10001d550004904101030021a08000c00a0516145041c40582d0784000c00035402000e074100040d8400c80750034020b140000079000254408142000072541d101c02c151954002c80054806000c1a40c0302c05003030380c98440444500000310540c140d0724420252039000039401c030350170641c0186003c0d210500c0500b462b5011994040c40c100c001414802c122400e0002c2c001004194011414000707440c4048181d181180707409840a0001c103a00135801c0035a89541042080304030460344d10014000019001d03041184c00c0284a0241c5820305880c40003041d2414200c0f046100541001e91741d00606441400d405042d01d41000b13400e00c164900da854400003070001e1800798540c800145858985000040d40030f0380a08407660410065a045184007840840141005c03a0224460000302d0012a00400c0b41e9a125280e8425640006200c84031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 195872059 1250 195870809 195870811
    0x110f0610210c030309030b06030f030a20010c020706110c1f0e04060603050901140f0408071a010602060115020f0703150b040204030f050c0d030912081c0509010b041103060409030c08030f 82
    0x810341f483c001594890040580368007d0300600b900a4104020b1000d141b40310f6010110f40c22555001141007208502d07015084841082900016034000b00d8140091500034044006815403600140703404040d8101040010302902c108a006001c5050340090050240b40b40421186000d0402c00507955104401800303840c0550f044100c40d40f81c06a9a07481d001801c404501c5190100c0f040c1180340c0b12552110300342c0d4405a4196a100b100518881000600c509500d00800e801d500829a5504284814021400c40352070382007907611a14102e0702000012500350202da400000840c8486080f5240c5030140544810881d406440000d010040048900300b01410034012011100e5103007081c0d080c4581500003040141c0840c04981007003007110080c1c0da005095510074180309003080e94030740b0801c42c0c1c880c0302b11810101c946c0f00c004002c0c1980c1c0c24483e06140c86e104403000d104058a801c4001d00b00d12000e00180d01032519001c2e0801031500070504c0784003940d80842800c1d940d1400c120408481c140c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 195873309 1250 195872059 195872063
    0x504030e01030902030a02060304050a020901170637020c030406090f0e06130509010902060a080403030b0a050a031407030503070b041b0b0f160203010c110f0610210c03030903 77
    0x1012034004503540709108004200354007400070180f607411502041504d070001070040324244034410a010058469128442c02071002200007020743c0c00150032142004001480710f02c20f00c003040c0d0159541146188404400108005c3d840f00000350004108068420882402c140b440b00290005856a0140c00d00044a60304a00030070381c4c9840d861050996101a40d00b59805042d160304880c0c1456540d1040d900300c5409000010300003d241c1c0230941c26000640707c100030810240402003455014020000d40850417113a480039182404001000580301d404040c144885403042882081d008002480242d6013260450b506c0c1c01081c0b52a882c5030104860031101d42c065100384114501b0f000440005803001c4c0d1000c5801d02d1581c00c0d814400750007054400700e0140c8401d0798440035860030320a420600d0740941d1884541004240d20f203151010b100740b83e00203503021100f0801300080078940b4101703507030740c42d4050102ca0306440e648070500d04078200d01400c8000100c0000040540003005041164 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 195874559 1250 195873309 195873317
    0x2030a020f010203010509071103090406060c0b06090f2202090903070318030210210e011d0f0d0c030203040306020a0509010306060512010302150c060a0b120d21020403050d03050403 80
    0x40c0385040749030a0340020b20809401821640100340c900703000344005c1c04080031450440e800c05507100000b0b81615103030741c004008208220044001e220081e0700c460361002040e18241410f0a020864420901c2d009005406030100000740c1210306442e08040350a040d0020320082c0281000d540351a100d41c40000118040f6400c5180780060740701d00300d00c00e81103e40050030340070b03020742c00c4900fa2500e0790081c000c503002c10421a021103000a141c410b5803484500c0000019244074000c41000c014601a07a418034264044841c602c0841800240e202c60844070b4540203440d102c10740744c2603107540180c0c0c1004100e940003003014460550f2010103003c05003400da8040c05062b580321800e4640b4801c018071081058001e1005001505190260001d07041c154080685405019280c450520f0b2080c0d454200041d2561040c08007450300601d80c20040f80928090031400065500107002d5540f45d0307505a505c80b05ea00303090b116004455040e200119001404c0c0c40210000c080024020441254110042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 195875809 1250 195874559 195874573
    0x120602031f0e010302011206170c09070203090d080f0f0d050603070f06050d050912040807030c0b09060313020310060e18340b0a050711060a050306040504020a0e010602030a02 77
    0x6240c0c641c1d00c00c4441c05641241203034216001113610396054440c15926a1315550300040b040812900c0d6000700e1300150103002400d4500b0304000003403034080e0941c81107500500050b6266505d0004502200703501032102c0b546e07440c05a01174002801414180c4510f9100865018514540f541215209400c120182c442e00c5454118005100301c160090303c0000da01444007501c0c2d0041640002e40201ca240d003204c0408440f140950301e594040c0e0030480d016040b4040070010042000400030203007010b414241d00300030704d07400418114000204000803d0328868444000c0d5102444a24030702245807100b07215180d00c84c141d5001040e800e9841d03440020421400100c0d4a0020821000c004240401070f888000b4a104001c01c240c040440b0b0908a00710040c0000c582120318003c000080503900c3c0e8507210101030800c034208101101060b8001d00d010401c10050581c40302c1182d520010844000a80c0c1d102c5001143e0519050707004035980100070b4001040c1690008040d01030341d0107a0703080f2906 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 195877059 1250 195875809 195875851
    0x4020304150c020d0507031107271a01020d0f090b070b070e01110d1107090203090f160602060a180f060e011107020d03082806032108071812060203 65
    0x80c42c00c0300005131000910a108541c0000c2c4104207480702c004030b000c21200c5e442d0b01d42c000c241d19240c0c1d03050913020852014104c4034a10381c0754020244c0c030800d5070450780f40014185c00081d403136103a40c81412003040608100700c50003074012402036015212a555a0783c44000d140b5140c04001f6040d250301010626800c11007040c0d611410440e403544102101401403c0200d8100f078410b6040342540e02041e014103c004902410644050b40c8140035050003012003860000f0480e003461030ba03660040c0c0007031004100748111342e00001c00e660810324407403002030b84002c02d01e8562400907060400800209400c12081d0600481d82c11803881c01020030000c00c60b842840d0003400140c03203281e00c002d42200003d0301c044042400340c180c0da035100c0514403440c0089a0f14503110b01c6508a2001c0c23400d841d954581d0148140440040c441c03042540e0700746802040098104043c096030380040c0700600300200d45154940000d9000702507030051103011140000a880d85c0352900203500210780c501d103080101158081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 195878309 1250 195877059 195877063
    0x1030b060702010e040527060402011808120307030608010c0f03050a0e1203060d02060d15170616020f1f140c1209190b0a05070203090609060c010b04020304150c02 72
    0x16982c2d4141c68100b40c0d0020401070002a200040900c8414081d0300c0d0714030421032001c59403c0b84000500c000d0b04451400388009088990502c29010810503403081c180070b12040014040c1c1d0f01c10100a40e19220b90715400210050000d80c0c00c40111942811440c20312107402c003103103c80c9910161000c0c00300b96545100d05003140c0304151004041d03442010101c400f0f42c0707118015a08000b0292034041c0c00c5c011600410429440544031501860b81c54888a074028017035140139024050070108001d0b1000100c1140da1b80b500040c03c0f80000150b031a15890055008108203481001c0c5541518402084061040a01101c4004003121503040c81c1151016206a9024078491800c03007201c1402d108220507048d8144200800070070b414450702c4412880c2069180c076400e01c0620441030748010303150042102c2e050700c1010304180203560040c081d46240c1d0703481400340d861f2100107072600394680c1d0443e2182c80c00b428004510781e030018400802d000c1803002c0314402508a140784d50f4280403410000804076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 195879559 1250 195878309 195878317
    0x90303061a042c1303030c02011103070806030c04060f06020c040e072705010e04050c030109030905101718070b0702060d050405030c010f0b1311040620060103030c0201030b06 77
    0x1409240381000705102c621620000101041c10560f900c01200410014500040c0310a440010700d8201203420b00c41050b500d801b03815502440c0d0710080c031140c43c41c1b00c54144280005080c22080c07100c21000150b0a442c00c1010030041c00c0020001d004850f924044418007072014011840103000300840b540c0c1da800d050003101c040c0b040b41c000408a0510380744100c0a180080c0c06010304060465800c0c1e000608039000d0035001c1c0040d04295203103820140341c00b500d0b0154550300c0600a074100300718400030a80120604044407401c1e5042e16100244100c11902442c01c000030303500551820080c0500000e2000d00064100e50010403620125121080c00c07405015003c0000d42c0203c080100c003a03403014680069400504c203804032818401c01c05509030070f40e6076080081000aa40315620320301e514003500443d90300b20040d03004012264241090520741d11450161034140007401107140901c813140c4002c0f0212a040308107541d0070b942c43e4900240081c0040d90164002428552680c80c2850914122 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 195880809 1250 195879559 195879599
    0x4060b0313080a140d02040510080f0a0209010201151d01061403010506090604031a1b04030f021509090c0403031722080c07090618061208091c050109030306 69
    0x40755081d002ea445442550001400708100304a04c41501c0e80489103001520718070014050142e116070401c41400300c42c031091440030b01086010410300845016810b0159007120500c6409644e41e02c014005038050540340846598020000a0000390101d411851022034540c09918070403a9903a0345003210310031040705e000480c0802c1000100a80c0c540100200b25048018001909055882c2c0303800d07956981c903210040310004401e0401115150040e008810003400705000d508284c03e5413151500d005601000a0040e030b85c01d0046120052140c0555a455400908240161a15501c001390300e410500c800c40214240000281d060f2581984282c0705104805c0480c20082960580c0c41160070411020b0303500800800c42d21404101c103004840103011a0007000c0760b2146080c01c200d80b00c8125040100a0514283c3d0a000f600195502c01d6040d98214800c5070310385c1c1303003400007134030301c010008118a00249000f418420054107400546c0c49601980b01080003d075504520720b100c4400c0081 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 195882059 1250 195880809 195880831
    0x3150b04180f091a1005060a0e090a0c050d05060f09100602100203150d0317070207030c0e040206091509031902040e15060402070c0f0807081b0105040e06040b09070e04060b03 77
    0x31058400320b8a04c0529805000c400c3d2020481c0d80d101c02060041d0701c2000700c07500041c548000342401d4104110340a4000c0009541080310341103241c00100766008541100480c40e0300d40340170a219031b683c040403000030080208070a566003403201e10b1502d004138071f201e1040980070300b10702c4070344041040c42664418400c3d500c0310810b2209020403c22101c210410403001e021040d141c0c800c040b46000200c0b44034034a1600100441811410022810700c242e42c4604c5108104804110040e00c0f94003c0c2c42103407005545162440d0880c40c2005814080c00c0742003909031003440c0500342d441c000300a012450500036582000007010540c500380c0c03500008040a090100a02c000c1401d50519900400340c02d4050001c4901440e20ba030000705610110798032040c880d03030010505020048090160038040c0e04c0700c03075000802c600280b0010300740d801148a420900385a01002501a840380e42110030100c10040008410741391502d0b0142010b180c0007002030140307150407000b150000c95141200d000e00c4003210303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 195883309 1250 195882059 195882083
    0xc080f040b0114040207050f06070e030f0d0c1a0a020304020405090102070c1707030b01030b0906010f08060105010e060706090c1509060206061e0a0303020106030b060a031203150b04180f09 83
    0x7110108000c0c100d0f005410503420001d5802050091215081c441c5020707000d41001d050a4000410348442c0c51080c1384030303802c0b14014003000300b00010400104042c2d0b003082410401e49003010349151214081a0700b110507042d00300141000c0036801103100c2e9108642c1002b150326030f03101807401c034000da1200a03d040821032050007100d080c038058a034007824074001c854210380c507079031184103c0400380e0040350382041610510000c03400074840c1034054001080501d010390b00c1d0010720741e9585c50612844d0706103c101d040c0000e4036102c1200312014503820040038400c0e9055490607101740e40c03641c40f8044062014200220314103125500b00c0084031015402051035403195400c00145894080d8051140d0b0510100b1030800d40f50500000c0044d0f02a400004130b852450421402d00400100501d20412100d507040c00000c6079041d5401207400c070380c42c000070324030850100c2c414a4080d5030072128800402080024190600901d125246440300c01c080c85000c2c0004103e1080e0384521100400001c0500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 195884559 1250 195883309 195883319
    0x3060608040204150819060e0f0718020403060e0c0a150914120a151404020120150a061404050103020f1509131b0c050706030209061c0c080f040b01 65
    0xd002180c02e00304000313440c140c55594481035171401e00c094a04240c52120511071106014a80c8a2403045411540140c0b20384103d040d190340d09c661860281c074240d500340324040d008440c0260b040c0c40207584c0c402d80070045040071100907541e800d210141507101d10140c20b40410f0b20044042464415507564541c1080103040078034260710004c11100d803d0304440c070900c8580358054200072008400c1e02600109001c0312440d44044203807051400c81d446c00d912035900340030050f6446a000744070709004000d80078008803503290103810034203644131445254000c482808081e12032507114204032903213000d412400401c004180301c2a039009110181d17020302c102c0300714029070806e44d0300032420300340d1403001c24600000c6030300140810010f41042d1040ea84c1c0c0d252f440c41c4d00c480e0340e0300702d03660114642070a441c00800c0e680c031140e803000e860048908250300417071400d40300c0d20780c281a24a20540003e8034020003100c40c0c00c1c40011724202d03401800185807500030941544844d803825000e01e8000043e440141c1c200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 195885809 1250 195884559 195884561
    0x16032705150c042c250f0203090d15020703091a0c0309010c03030f0501180c1805280f1a03091e0c060316030c0503010303170408070b04110a06020102090306011e050303030901020a0f03060608040204 87
    0x143c1c041e9a0244402003010bc801211710040844611039262400c185c0e0030041ca400ba01030281c070705114804000c02c000e1400600000030b8450411091030b08441c3c6a6180c41c044002d05030050308040198104000403460100405900b060415240b030200400d03905814212001029848481015901443c0a1215003085c00080c01c28210200803683c3c00c82c5590302ca00351005855112844800707031310a0034444141c4003403003869401034004049080d41421400c0c10f440e03012114941103075014603440d40560b12810310420010f0a07000304001d0304e03843e01070341d000c6000f08051001000079140c1032021400500030810313641a250107960386aaa0229140600950324002c3e0043c0c42513802403040c1c4000038030300c0c010140314911030b1908500d040d1008013800b60b00f00c1160800029a40180088103080d2000540c09044030b4400300300100540c1314030050341c550121070700400c1d05070100004001051605400410707000304a56900d0700035101140e02201203407145c2c090000050700c071101040143c030b03107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 195887059 1250 195885809 195885829
    0x150609090609040f1212060504060e060d21020a020f0a08070e090c09010b0d050604050c1c02070b0f0708010506040e16032705150c042c250f020309 65
    0x40744c000c41c0003889585c0c0340d8018140c1c2000140c8001020081d20248211481c09004014441500c2c10700c04141401400602c100000300b4050003124842051814005c88101844079150304125203124025580070007134485441e2801030340119042840072034203041401c1c1caa411514880040e0644508205010314224006420140d41d80305100024002e80e403801081740c000d001d1103810680c0d440c0d9018294090303900c002c14940c4102c1ca450100040b01e2561000c940000c41b000100c0e48000d02c2d610001c0009000e12170b40584003c0100081100a50014120038043d01c078946400c10107a036150100003c030b204034050441910020b4010450b41e0982000c86c4405805d03a0034007094008039440d9035090b03c1d401c1c03003881e42d80c00550910704041c0310042c40740d010140c02d4480e4030703050344c50b003800344802c544143c1c8146010310b00c80e458900780e800301221081c68042c0c48200f07010f000d400d080709000803540700003011800c030141c003909000203140110f0619003c191650044c7d400e1041001c200f0106001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 195888309 1250 195887059 195887063
    0x201020702040c05030f0907050a090b0102030d0c11060f160c050f1c1101050606070f1a010305010b041b020a060b010903020d080c060c0705150601030b1815060909060904 75
    0x9028026a001690b07540641111080d895885030303101e1400c80c0809070380c0c1c6009020b009003504a08400d0009450f107030302e85000e4480311080031130040315082c0107d181d071241480b07200c10f0030300c1c00344100000782c1d0010a40054001d0340e0111003071501c4a01e100451203c064440c0d02412081c0c01124020900401701d0310a018022000e5a002d000304603109418044200b8920b07101c108406a000b440c0c03500000b1034000700c50203000070003070707440d00601040da03a104448018080c29031040300c190400400c800d10141c8800e00b001c2025540d40e491030030303078041c00b407211a440c403e40c24611440300007400ca807040d2007804403e60003071040304182e0711001c000300b00402101e4100544c0d0f00c3d0103c0540c4406418500c0b5a01c40d014a650700c0c0c030b41d031303108600344bc40c090002100a00104040c80224030000b508404186500100d180c0315240c15005a00601900c20391a40244007040405050035280001600c81c400d60303408001481d113030108010799841041c0301c00740d1044480c40422180d080405100780c1c058 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 195889559 1250 195888309 195888311
    0x2040209040911090a0605151e0c010606080c0f0304022211130f030f0605060d020d030503040507092d0e011d0d08011a030921070209090c060f0a0201 66
    0x4180c80046401d035540c1d0403040c0e032510202c0c581e1540300e06081d00c40035808003800700200006801e007400907048400c0041d000c0030100e00828498120450700d482c415019040700c0f4610703961010762074024040c0c0100e204000100c0c4a510000e9441815001255550044462140c0c034554070f960801c600482c030100c00e100602000001418102035034442c02d002071080c40c5e615516038282d540300e8016218a50400c00001088060030400101001c5400c07500d40d038400350110303d507501c4d02c0c0419141c01e40d211000e0f601450450001c4180354002c030046000c0c1e800b07203040c1c2c1c0d0819180c04c040019a02103146200d8881d0500c20403c02d05081c801c0c1c000c1c031000e051f24000c521751110300d041c1c03420b45c0c01100390345100f044081740501030000f0030002c4002c208501c2c00c100c091589411601118101607680500c00c82a0010010349260320600100855525140c040075240000d41072500d415048840102e000b460310740e0106407581c0300081c003003c5545000307090a00e0314101011a5941d500403140e103100355 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 195890809 1250 195889559 195889567
    0x120918021b010c0903020901230108090a080a050a030b0f0112090201031d010203010f06020f0a0303050c070209010308090114070f060207080f0f07210c02010f05070818010905150301050904020402 86
    0x1800081c0200b0504042e82c0c4c1da0314603020300354010032504280c183c1c4440d6140349030400b52001040601d0342a0b1301c482007424149441d554244e40341d81002c520f80001801030000042100305981c101d07019146402c0c05a50420032128444280b1240b941e960710000d0103d048601121404100754000222191043c03401150228102e1050042c140a014a2000320b07500030005022074146042008010842807004100210841c20450749581600001800301070715040010500d042400464441030781c0580742800ca90307035a0a0030071043d0041c106490004120200c00d06110306000300f0741d515690051000c08003146036546140095010380da040b54031500a0040c1a1149603030000b9000c40c80e044414a6614419842c2041c0f1511100020620110404040c5040d480d817058100a16680c213007880e030340c07000501d5002d031418000c0890090110070005007000441010002c404801902038a07106078854581d420080c20b65a080c0300c5c084420380a1004020300d00d031008001ea007003400504010f00e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 195892059 1250 195890809 195890857
    0x90c030901020c0a080409050c071e080712080420031c03060503030c0604111507150b10091e2702120f04200102031c0608011812091802 60
    0x400f404c0d1102a20040000b04041000d444135020316503005261094440c07400410b9a1030750300020701d09242c60984558060800304001154046a2106400004000c8140c840d04802868510300301c4040391300b1010140e40110480000d0000d2440900c010044c14910400c0031001800c0c1b0544a4800c0401da09c9400000c1c1d961018070017008500081e80c0501050b00c2c05042c070080c00010b0640306802086e010000c025407402c09000c1d1075413698454444103c0817004034120300642603d0070344983c4000900c090340c3c545504203541d10100c1e035040310600c200c1000400c20b4100400c0fa8440d09800500400c9221a000800c0d03c1c00c01d01c14030b840000501340704c41040d140075811001c6404022000b0541c0c180b0040c4101e910300a001c004183c4c0b00c464521a49000013501c9000e103144812001246014002e440f003580d0708200e01030200c20b4020007003050380d4200d140c4080a10807064900c0c440c49045684103504c0740001e43c0664080043e107829a519440302000294045405021202c03861346144c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 195893309 1250 195892059 195892063
    0xe1c0807050a031b02100c0312050108010f0506100903032303010b090301240506070614040620030103020a050603060d0501110408010c171b0c030703121802090c030901020c 76
    0x419015200400c1c4040041c0f5000e491891468084076030413032182c4900005a0700d0100800e03500505240003007141030b561a00341c80e030800407090800720905100020030b08480551144010201110003800162100c106010f40d11a0a00c9000c0004120013014400f1030300942c0c96145410500e2102525440c41329903c01c41da800c01e81014280a00009807040685802d00441c0c00340031105014040c0600c2c0300d450b01c0d2a400c10b40c864140201c5010032264240804ca9110030034000a0700071000c214030b854940300005242380618100402c0501c02203030a4000007078290b0707040c0d90380904034110060401e0104a07064100070721083d40000c901e204000002d0003030003191100c8815100850f201e81c1400b2455003511000b10244080080c500021801e042c0b0900c65030f41c10030400072003035003084051a040c980520030000781074003610000422108242d4424002030321600990002c1160100707500d8a42c8100c40400c20203940070880ca40410107001c440e41c0110303008003118000518140100d5034480c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 195894559 1250 195893309 195893317
    0x1305030708090103050105010809100c02030d0906050610111504060e0f060702071d0105060307030228180b0a031509090b06031606020d1209080409020d0c02010209010e1c08 76
    0x15029403001c0b48010311940c050040d0760241c142400d10f03000c1850542c4519603a0002a4120245680c0702c2040c1c820040c028800c40c1c40040746010709010841441c1000740103400d0988010340540030f204640d0102612407005805580301d140040c08940404140c6102e94000141041d0b9000d55240e10310940c0344400c0041644a1906001500d001d240510340a030402000d60311840110f154450071008580302142e1260548100b1192107859480c0c010040340280107480c2c1380b40354150035901841c02c52400c0c44d1441c4501546903642075515074000c4295030201e03520b200300249000140708418086020b0740008148a070700b114840c642d0783c0d861101c1400d032007a60b28103071740010041c1c050100070b00301400f031074000c1200c030888a00040d10b003070f00003503450340c0040e0020300b00040f01c070701f2428405960f04546681c4d50030a880320348036a21280f812000358400e01400c0b02a920340f0304003a180071b0060080da200810141c50345200041c000d014407481005681d41010080000720b5140c0028503110054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 195895809 1250 195894559 195894563
    0xe0d021212041e1209140f0d080906030f0f070228061b0903050609030304030206160201020c010f1d0106050306012705070e010801060801050619021501080f072c13050307 75
    0xb070910300d0503c92000d4000071458105000f60840c45001b9052030b00c507010f104802a200340c0300c450411016090070b40383d50040c095443d51100c4004240003207032860a01580c0a00c00004400589407601c0d00182d030b4500001c080920784003110440c5504609402592210780c0c3d00074a0007160121805074542c0c1488403c00001c000300320003d0040c018410200001c950146218000b9855810a82c802a54a000c010722240304c03900401c01e0565201c4c0f003901a03400200305440284032400740314082c4005489a41a02e00100302c0b02e031607091a402c0140191000c845006c0c0192210340d08241c0c03114060140c0030807100c41c400d81d0581020302c00909208a501c2000140d603810000c040520005092000683c000790801400d000140147e0b80c0742401c448001c0c102107510f000d5624641816810b040140c0ca102c520301035000000a6000004201007802501c05030554001c29112a219039100b0054245004d500407419007010040c50082d40781c98119021641c82c1c0c420903050740d2a90300d141c0c01b821003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 195897059 1250 195895809 195895823
    0xd0f09030809010b01110307080a0519030c0e041a10020712110f0d03050904020702040e0f06011e2301020a0203030f0d05060d030c1209080706030e0d021212041e 71
    0x400100360b40a104884881c0c03001d00c0c050144500c1c81c0f50716956409034800c05010800c0c0060f0a0b880c180c0102c01300c403116603c29a85999410404d400a0020081012083c0110f105a11540400e1a1a05c10302c00300804650b4060810182d810500c1181c1d601c0381d880100358424140701041440c0391840c00081540b103200100040c0901006000c8601ca101c1c0c40c1c18000d110b504698800613400400f90790380380105031030068480b030141c000100a80082400c4107001e0040c890500f02210010a100d4141d8010041c040340f038460040b200c0480c01e0a1344242048450151810028207004060b80751015005104540c4201803640010341103a02c0424620314003400007a1640116002c1d0044c13591002007115a06480500c0ea200a42400e42084005054110014500c03861600a036004000341182004803a5450b486160240c020001c0a1100c046440762020401e05d142c80000d40c509880c01c0d114925090040c1c0f81c00380b41d42498060802c80720041007040640e0900d21101c008103590340a004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 195898309 1250 195897059 195897061
    0x360914030c1e0d020d0315120b06030f0303150105030603010f020313110102060105010c02010503062b050105010f0b19020309040f0911191e05041b08070905030a06020d0f090308 78
    0x819028601c40e680d844501c1600109005030f03041e50040340245c2d1811086c10013203445810440b014201c15102d8110f080384046200c1550140240c005400d8402c910030b404854020840c050043d17941c3c0002c071a42d1100c0c0c1d104908404c0d06510a201664115002030f0000c920794282400303200036608200e440f0210f4200118024051041d00c1e6891080008280041e0900b9418100000d00b00880090040c2c180310000000c10030070f8488075441e085100854903050888101c3e20451040c0880114098842d98240000440d2072039000504804442c14149039070b04d802c45c03800c081e040c01540c406202042d80810301c184070031078603540110281d5451055000406092a143c81c80010904412403401080c482130510300c181e002c08060b00503501248210340c41102c1c181c000182056803504031507003080c1003031420496000c24008ca0060b021003510390141507034400200700c0b0b04240c240b08041e45940041d07110030202300b2540c010300001401110200321407450410310010341e90b00c1e120842c00504640 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 195899559 1250 195898309 195898333
    0x50a030207061e08041a040302240124090305120310080d090b090604032f09160c0201030b060304050703110d05070b0d150f360914030c 60
    0x4402030307000d80410b080000050080741d150710036107144840300c84180110308000c03800b444000a10704052607000000441d00f441c042c90002d40350a0b80a9045841079445180c10b00620218940c0b50b060f01d40c54542113250806020703850301e40c1c00795840c1a1091042c00b91011010910078090b41700380c042c0700740740d00d40d0b41e007051070b07501d214001c003584520010703005240b04a143c01c0d03000e0500812113070300c98681512400c003180081c1d03052050340d000900f5092110311000c90601c80712020640c940c0e41d0350140b01e01c849002c0a10020700c4084030380c0000c49414401c0c200c11a40a121421107090040c98000381083e00355011400c00c0d030003a1025103280e80413242c20401c02c0146028000c1400c01500d246d82c1481882c2d0729991794800a00030400b241e40c020802c0b688140b8503030300c84032104410540711800075598015540345160341d0b0041c49541c1b41d16860310a900380144140d10071b901c0c0c05d42000603450503001400c1009001d004421902662650342c3d400101d002000501031003091400900020600e00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 195900809 1250 195899559 195899563
    0xa05090424061d09100f1505121e01060902030c0c0f0d021504060f02071407140918010608030f09090114060a21020d0906050604060b09130e010207050a0302 69
    0x10000040c5400d04240d418030007480c2d84610041d400a83c5801c0b01c21946540131620b00b0b0000c1021506100762a00a82e07201c3c40210b038000c62401c0c0741c07810032405029243c000b88600c0211001101c05c0a6002d042c3e014002c8003056402042d81c0d034080c000161054548003030600780e038002c2d184a5a1140040350708010b08406201c2c07103256980a100806580d0310480010392149501c0780552401c05200c0d00040c01d11620f5048007460000d041000c48d0346400d1458068503246214110342d02c01d105240c070200780906000c04503400500700501043c100e80c0d9094500c15085410002885a55284c08000a01038020000307050000b408a00e038580b91070242d030900080e0041640203c00203144203600002c151110f00072a07010051510f806040c501c00b010140320000100a419084c143c8002408c031240701c3d0036404035114604c43d001c24003150700ea8108102c240c0398140500441c05034200300307502ca14a0480300300300c90340c07084010200f0001d40c0c2c402c0c0305c0d0880e044800c003540e0307903007019041c6000c1541c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 195902059 1250 195900809 195900863
    0xb07030c02120606210102040e070f090e070e0d05030910120c0302040b0a0c03020708100203040b090609101e14010602010e150114120d09060206010614090d020a050904 74
    0x1440010810b500d00000050381c85c0e02e400700204a9905443c001c050411070a4045a0141c10112074101d65410f00e500010410125111600001180c0d4000030031071561204825011300303250b13a42c6981c012080301c100180c1d40c034020340864852008002004440e290384400c0c000d010100e440741208801d5112180d0306561b20f6920304001c049c4100800d0050306620030a44440081d02d00e85240100401d141c141c1c64101070b500040980d09c80d000103c00030751010b40007144610f210303c0502d44140c40302d00c00e007650344c00107172050a002c0d0003002004070641044c1d4807001048160780300d403540761006950f900382203c0040108401c080040c00042c00501c4c1c0900481624020001c0240042d40d510540e0124118040c01401d6400941128644060f961600c502e0151107100c000d40b09880d84003400604180e000340b061002501130b480000600ca40100c0317400100001400d20300d85850f543c8020403d6030f07103111230120780c40000c11501045940320b00c400d07548a188501404801c08100c81d1131240c50140d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 195903309 1250 195902059 195902089
    0x7121e110c030d0f06030b0115030c0309020102030d0f0209150c010b0906010c0605130b0c070b070906021b030102040b040f0602060c091e0f030316140f03040605070302070b07030c02 80
    0x1c00c02220075030030000440d4440820084005040404c1c1480b68000d403000f07601c058400d188200010400320342c4014010207000840e20104406034224100b0340035141031090182c05038105100c0401c0c46506500008401d071109a001468030000400042c045003506044140c0500d0100354415909024032804000c1c0c00115006000d81ca80003000070841000d1b018005c00d03c039120760102ea4540e0000720300360806984540c040d2214901354124142da0341100009840f06034444000c50665802001d00c40280c0d035175035010344441d041500d5100d80c2c003800d488005404d0340d8200b00004500c440300000d04098030b8004842202145840b0009180c00c03400317003080d080e0705010044001190f840c445845000c1814444820483c20540300180780c107080c1c604e00350f07010b00001071a03020440d004520b0b640403c1c41001e01142d5907403003a014503620419002c41c94641d60040100340f0010b8002c00c0608640c0b440b81c81142c4040340c8441402c08150007144045000c05d1031459403104601d03000c407400e01820 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 195904559 1250 195903309 195903341
    0xf07030201140301120f03050705120c0c0f01050d021612180918060b03101406100305040c0306180807030228112209080409180c0e07121e 61
    0x54142110210b1111902600511840000d24206c0c101801101a41c882540120030355056486112405485030700c02c484210140c01150071510042c60710402d84903908806940c2c40c0d080c60074029000b4025480840031140c0c1c2c0150404001c0000c84032520000d4100329070352400d005c0060801c0c4038884800e0760700078404860400307000000003000d03110b8110300d2030380007400480e00c905044003203400c1c59142c8610001032030a004040c10500001401c0f94054034050703c505400c0104001c2c01c60880c1c1060b6001868240182020008103005410400c600010601604c000c141955200c809035031008004501507000f8600c1c003500c2401c007540e0016405d00e1040040c2444d02c0607a6180081511a00010b1040f020028116100b604041080c082041c60040411000b480d905018006d908a48500b00e8a1402e001803c80911008030070b2000d00d503805039003040a00e040c00d034614010f003802040702c1c0030030407100050103e001c6540103808440b00044d40e002843da514540c80010b07104910000c009003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 195905809 1250 195904559 195904561
    0x2010e01090803030610050d020d06050108090312010b0c0712050705041107050a0b0901061503050402040c0c050a03030e0123100506030108070e04060209030a0c0f140f0904030c02030f070302011403 87
    0x742d03001204490307000f40110344200110416850030745103030003515103110400e031000c60022541d448035801202030700c03c00d0300c3e01c135031598854005550b68420101c1c2003d80003c03c400400c0054000e201034030f81d911424041d81c0c41c040c0c6420006411404020054800b584400c0e010007842c101841082404c28622403054030f480002c1d126255292850703c0700070604000b01c0c0002e05070b0b00c0c0a42c0484003a0800c004c0d2004c039114500303c02409032a098900ba0701c02c9140000d20a900d500404c1428020ba5000e40500400c80e030a4900f50020403040b94680059502ea000070840c46003600c83c018000e003003018004c01242801000d01c4e541c02d48075049140100010001031042c0400003c11804941c85180c800005039160b150080290081c4030a1355058840c401e080410002c042c070350704046d2500c42d0300081c822a03030344940042980460041d9600b046002d0341c2c0d91407604102c0320155215001e130604850a00095000c07900e08040340007090078030f41081c0400e108560303000300f01d045901d91b00e280c22819 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 195907059 1250 195905809 195905819
    0x11060715050a0b061902010603210201151406030a0212040c080f0607051b0f160812040b030a1802151801050405090112050f03030f01170a0f020411120c0702010e0109 73
    0x541c4510f40411280e1001c81c05d032468841d2007500040b01459124415814004500307007050701d58600c584a0030b0165003464202001c0240c0500c07504102c0b0028694a45010034080611080c0d40c000b4014184142e001c00200d54601000460140900d1080c0f001529185c0b400080700d003030549640540365190004e100707101806074001c1c00d03644140c039000b540d02c0d43c4004c0c03184442c0c544100a80940300c28007800e100c40d0060b40d0010b2b15070302114000801c1e0381c940309c01c0305213030304052150303000742015001d06001280e6031840031f40c00b5051a841003004c8070400940d0b900000c003c0d0241e1910309204201c0003481c00302c5c000d0710916802d034180c004e0910750305190030100010344040050165a6154100c8145034040c00780030020000c4208040cad042d20707070b207040c03d5000211404090050320620000d060410303441034000a24290f055411519070b4915240390f5003040040c0003040c84080c80080c00b400705000c20304004010034001c401c9410740d6075541d40d051001404403021402c52074184001035a0400c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 195908309 1250 195907059 195907069
    0x6040c09140f040e030d06122622050103111329071208100b031b04080d0801050f03010513030f12060303050304051005011a0711060715050a0b 63
    0x1040d50001c5014030714124415000c940b0035141d021003964803a040458100b8003c0c0f0110062001400d081d2060154035111a004a14090200780090800260701c0e8000755500f110004043c52441e44440c540c60040c5200c40ea8000c01d40410740c2000a640002c02040b00e5a018401c1d1401103600c00025802c20f0145031900e104e80304607201d03828070303081880c03a600e0710340100c00c114250060102d1245a12440e10303080c00a41c244540e0000380200740400040b07020005502513103011180242c403c285150385990410542c8603040e551602c00d0002440040f0f1016002e0240071120003007030f91820650f41c500020031901d030081c401e00038000d9145c041070010182d00007000ca032910383c05051a44145004a00032900c1c0380003141d800100074541000482010740c0080114000d90007441150300c001843c0310b40780d003240c90a1262400001c0c2d100d420310048020b04001d000e40600038140e40101c10750060118091350711206007243c500165400300c4410007410b101c1c0035041180d05174100324451407080868 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 195909559 1250 195908309 195908327
    0x3081c0605092211090405060f06040504020d1101020a02040218010e060f0406050a0507050307030804061a010801170304030c0b0417010e0c04090203010f0f050901140906070f050d050114040506040c 87
    0xb1110088440010007800b19242c01080944d001524030078079880c2c80d00b401a00c480e4155076200e1100c00039030200740180380600a81d8010754000f0000d4207001040d50314141e0b448041c10145040d030090311080c2c009a51544064611201d1141b03070301c0c1514482d10001001c405114010921409040c0000341411001000b030714160384039400c01e2030ba078003000e030400e0f10b09010b0740a000b4402d100c0050342c4002c150303104800e9401144a90402d110920f000500d84119014003482c7e00d0004a0310001085860016441c400c51144094141c80c50700ba00e1b84c50326449440300b50003907410b080c80080d00f009001c8802c400011006800c0f8001c01c40328001801458494035440c09817889161104180c6c010b642e000c1d805030460540040081060110040c81c04000e01800c0340c800d0703055460000d5506039a03000700300d02031060745110064506075030746040580c0c0c1000d03c020018200081800702c0c44950301c46200d201d001c1c100742020800303990340c06802c21050f40e80082c04240a1b50518074001034460b0030a50034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 195910809 1250 195909559 195909601
    0x1306050301030b0c25030302120109020304022d090114010801050307061205040305090405091e0c030601150903050d0e0301150506070609060209190504050106020127060603081c060509 81
    0x144d503032980d4100c0d43c0556809140540104215003d0401c001c041d0160300812a8207020600c2000c16a070b100c400104900045602035040082001c510082004208071803604003110558034903d046d142000c9551090241c0142c42c242403c165201c00c0d079a08080c0310360040c90114020510a810540014154481381072150480c5444001240400d4001c1050b00c4141c1c0003c0d10130041442c00344001a580c5241c0d201d42000a00c50030b9127141c0180380424110182c2c02e01500500c8203074a07101035034660600c40c00411081040070403012002841c180500480c1e240503950b04459103000408040c00c44100444281000c0c0103103008112540350401515401600408000b442c08640d003010720180c401c1208065108d25103288520340101401d0618058803400c0d10100106d0781c98400503030895215049084840c1d015180e0701010b1135202001d101342d1882010081012a981d556100b8550860440900f5040400c04003054000a500c0703074030000e0108a4482301c1d94205103a1580c0b000c3c1c030b00448 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 195912059 1250 195910809 195910831
    0x20c1e070e1b03040305091f1b141504140601030b04031815020f0c0306090307020603040c030f0f1b0e19020c07080102090a080a021c020f090a021306050301030b 71
    0xe4412441030010103624402c42442a42d68a06840c00a1003540030046061080380040c0d0100038600340f07150701c0d0340048090b03260b10b908125407182c0c100100902410032250210701d805000104131080c403801d2110720701e50700700a0080c1014039009840721b4110340c0300d030342542c0144010800f00e181e401c070035500281c15081c035018040e8807072041a4102c1ca00e030440007a54003006460301c0804c7c1d00198100c8258440400e0f60540c00f00e260030940c5480d42903508400c0340d4801c0c8102005440d2180040d50007078811004070070411340d40d5641e40d00d00c40700400309650034040c071510300c02804180400c46032011201206802c106084c107600106200d0080c049a950815000c4c0a601024030355044030420329030117040301c89a40d030f02c0f911079000c2d60103406c1e841c3c0141c1222400180402e00042c2030380321304d80e000300048960030300c1c03050303e59440980d01000c0e03a0000700800070098a49500c61185d001d40c1101c0405a44c0307042d01800341d80100071a0303010780b003001020001003010a02100950350090204c2309 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 195913309 1250 195912059 195912061
    0x203070b0a030b120601080c0402040806010e100806040305030406050612060403030c09080109140115060c030e01030b09070c05010b010f0206060405060a030b16080f040317040203011e020c1e070e 86
    0x80220b000b4411091840d42142d8503d4030b201c1c1c5140c4c0001c2c514100ca08540032140d080111a0600041c1e000d41e00c6140c01e01c0d44024018032000509540c01c6a10030000c03206195100e50f1180c04a203032180649081d400310f44000244401d114150203069402801038071480e14034412280c44c140d446000070300143c205a9904050b035000c5100d242d03c00000e10382d400c02402041c90740d0425608081c10740c480710b8038035031070400d84c40c408104144203101140c54a84558110185c03d4400741c820090841c00075042503034a4006100f156071307405070326010b007a045e40c621642005528240d400c50b000494854180070509007040100b035800a000d540c820707020b0310041515295400070903020f005070f81000707003041d990100b0403a402d450f4207080d10580c07070607075984a45521100c0c10b02c1c4030f091b01940c01800286200e10501d4208600e03104064225101400020b00030074800c0300da40032461800c83c040815500010300001412041201c2c844461600c03201e645510002070700303181e481c0c20740d108040c0c0180c4000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 195914559 1250 195913309 195913327
    0x1020307060b150a030b09060d031e140f0a17060d02300303070905010305061503040c08010e0c24160305120403080412020d14180d0803040213090203070b 68
    0x240884060700301c4040c0c0c1d41c0c4031882400c4c00341c00707803070304440d0b030350040790b10400103040e41c0760880241500580544580200c51900d110a0569104030000102400690107440496085000040c0303400a01e030780c0b106490301c145480003071080300c5086018140e100e0440074071015a94281210460a504a81301e410003142d914014019800c600c1079800e0b003060110a030800c43e04048001d6201b08540d03503a00da519911003005404580017680c402c1c7c0c0140c0e80c0c44103080036035003810046400901034810300e9503950780c510440303003036030400c01038000690441c2d40441018145001342915072a51000b5041a640f0100c5a4042e6406500600b18440c1e4030f04074040103040c0100200d9450110300a4098510b01e0302d401e0240c20400b0549048808410594119180602c0400c06802c880b1065440010310703019900003c0240d080984500d02c0f4425501c019456907071035448802800d0f03c640401c1d42c403403504d401080318080007400c102081c079061006882c0165808602c881c1510303e1000059100c0c2041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 195915809 1250 195914559 195914569
    0xc040504030f0c020f1206010302191404021b0a05030d0608150a0b0604091103040c1d04020103020a1b0f0b090706020706050310090f051602010b06040509330a0f0501020307060b 78
    0x10414640c000b00c01b00a0789502000100d01c3c50306a900035620444160b5507100c2448032241107115481144180781800f9905107410b03001005100461412040301c07031001d078400c0342000c0c0c0c2c004044546610028800c003040c80203002d01c000610090028001008100358024000381c2d0003014586000c1d6a15070f107107540c0e0380314401e0300c000c0c0c944140e08212200080501c0c9006d0303801500c09880880d80038000140281100e103032203054886240200d01143c0301e50f40150080d404c0001423000740b00c0240c042c00645c140e04140510140d000e042c1000d405685420601d81c104c2c4040d01504282d00045418040c054000400c982100c01034941983d403540d48a070301d49010303403239900310340000360030b0083d4107403000602e410081c00381c071071240144d040e00000d64040e800c0300c074942c0703040e500102d05000030040c514154407580d41c03050140b4400700c0c085164181110b002204508840b00134603049502510608011038400081c2c0038800083c04100e040900107566402801801802e07580ca5a480007519224 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 195917059 1250 195915809 195915829
    0x3050a0b0d0f0f050601080d17010302010e010e0604080118060b040e1f061211010305060a1211060d020307050408010c02120f0307090302120d0314041e05160f080c040504030f0c02 79
    0x410305032040784d40c40300b15460701c070814014623000280c02000c0d40e1455810300c0e0074640c1280d0f81610ae40503408603400056450301c1d845449580d10010a000c0010511000e015620b40c0c440c111141e002078075040d140800803100070040f03160255180000e1007089083c000351130152800c1c20351100c20710b40000c0c406800030301840d420400c00100c1c90181ca0040004000d0a015224000d0320248071a95070a010b00004030124825810042c1c1074400c14804a5580310b11005802c0c8054141d41c907081d10b209030300050764400c0e2401000203000190030031100d0800e02c2030b1243c80340340e4400b5144003401014072440d80d0141c0340b080c1000c81000004103120f0360050701c04400843d409800014100c040c0f40d44582c0740d01c441d41041c00440d003003401e009500f06039811218407071940301100160045c3d0003600c401c8640c1c246041120705108034018000c600e4a06a012801002c1c1c0e1282070b140541480c00e81400c0ca038910010350300640c10441841b0005c1d8120501d03d600315001c0ca00758403081180c0c0002021400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 195918309 1250 195917059 195917063
    0x909030c0115170d020d1103040e010b13090501050f04050a1d032101030f0b040201170f04020a0b0c0c10050f0301030602030603010b01050a02071a04080d020d03050a0b0d0f0f 77
    0x841d040411041021005142d412540c0e03101868200500b8544419259902c8001080044c0c00a00d40214685c1c050b58904a80d00003200480c1d0410791151410810400d0a0b00040100f150120724000803250f02030840b405080041e000b808607500d000003103a83c0003806040d0b03a20481d21240003038480040d07a400117032066440400c0d40709001e0526501e503100d034801c441400600581c07426003c00d90526040f007074104c947c0880c0305d03070400506864503c030102019004a040002861800d401e25041324901c03405440001d180840600f01b502c100700c000301069101c00e90504040c08024084107000c01c5c0042c1500f000c2c0c1355034803068a020000c440c00c3c0305005101c410880f0100000c0144801980074501c82c00c070030340c020010901c401c0300551302070080c0440354005a22540c802e00900a1202c007403103103400309400f0203082923103864015050030f80301445200140c1c00641c0c1943c1c2180c3c14050503800c8101481c0420a205008003c9403030880190806041c200300780c1001c104000c414440e21000607 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 195919559 1250 195918309 195918311
    0xe0f040504060504020a2106020a090b0705070602060f04110409030e03030d1d0a0c090b06090406060314060105030c0a0c0f05010608060708070215010e0a0902090112030809030a09050909030c01 85
    0x850a4506070004003c280d81c103030b01032520b00101081d207039030501c00b00400b5101403d000000900b81d603106c0300a0761041d1008400c01116402c0014400220800b40c03134514802e5020309910b0f800c0040080c5042c200078984070240c0c1070b010038800490020004100b82e01801e07a808150890203040640e0f021000840a81d054400024400c1300001c0e20751160100244010012900ca0300c0c8501441d075401d07130001e000c0c000060700042000903000650101c0e01c00c05001d04000d04200411000a04480c240d1340200c01003912803a94002a01030624107a5200209082c110304504040d03200410f64016240d0b2101485250010b05045c0007100e001d101c9040e034884024041036403140005911584142e81c1c0e08003240508002c106200d002190f503180790f2412001100c1c5913882c2c008101c18402020300b50380d01240d5900a140050380f1014071181c00303081c00304039621400b0110310700206019001028408035800a1140400003940403900741c0458901322009980c3d80c0752400c4450451140040c16a565 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 195920809 1250 195919559 195919561
    0x2411030301140a080c060a0f020f061e24010e010c0b010f0303111504021c020d03020c1002152a030403030c031b02300408010509120f0306010e0f0405 66
    0x10303440740c55a4001020035a070202d81944d0790030030540e6809540c1e8005d07a10003014400049802d11810040075180d14500c101c8040c3d101910b202030418500390f8102015034000341300c0b1a0f803c03008910b0b807500020b1895000300d000480c2c040805408105959884c100a01d51608081682c4500f400380c0b04950880d01400082d603550075034a04803081c1e844100c001ca00402c40c0f414091101180040708610040c4a42c03910b0b40c2c883d800c100445c40d1000030036030440455403c0740e0250701d030f220050401a120750000c1c0700385002c440412200060191408003154000710000840788001e0b02d240342c0295889110000f9010075401d41d407d400e2140e00368580b0910040208002e055040c2c20032030b050511900d04100c1c01c0328520b075030718080d840e4109003000340c2c0c4401c00345441061a00b41d4047d030903040440250001000d44506a034a03805030703014050f43d039110341c2403100e00c0c0820b001d00540c03040c500102e50f15140310301c0d00722000e502004107154144a412442c11079242c07a003000e030940554001384100700c1c0e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 195922059 1250 195920809 195920819
    0x192010090315060b2823030c0409020a03090b010512120d06050d0303060504140f0f0604020d06080105061519111905061504020301050307050405191104030302162411030301 76
    0x6140e0031100c0c0c41c00444086070160081c07805138848005150310403503240502d000110300b084040c7e00181001c0c811034020000029032200510103490094000e690109110416050103800c0c00c030180c2025218442040e1240210403001507c0407100307521540c00784d21400c22030601401451160f008a4002d21008503400405034540e01071015540e04480410456040000c2c0c4078414800302d0700a4003010039070011488544e40c0000c1280d003c1002480507107000c081e9840b80003550026403043c00180c1d1558284206442c16912a0840b891180013103802c0c44990f03100c1c88000318014034a10b0070300400d600c00c0907016109004441207048501210801d602040c40c1c01a81c8100484581309036000f010041c00c0c49103401c0c000c8034103ced00028010034025040108100007803034003401005034800240300303114026505020b107803c0303054103401103a283c074a5406c0c082d007880f40c29826180380c40764203c0c06100701c0314002c0008400c3c43c0c02c2e4030b15403520a43d80d00161170b50200810307616070381d100c044000a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 195923309 1250 195922059 195922087
    0x60307020604060e030a054503060603030c0319020304050a0e07020c0a03030909020a1701030506010518040c0e06030307050714030705010503010f0509040203192010090315060b 78
    0x40120f12840c020019050f0f140481522400b81c1228080041d070b08020501d1003001688140e922681c0020700074142d2007010b052503022000000064803400d1000c04034101c5480d040c088154041d4058000d1071510401080f625124071590042020b040e503108010741c1100d20800c00c1d103010f0300c405090703038810603200c6502000c0c4203400c07a0301d84018030400d56500326900b403541d2218200d03030b4103844011a480c10500c00b0703030203500038682c20001c000070100049100c100c444160b50096010300041c0045e9414082400324540c4450184844810610140800541c000b0301c00b000300c0d804d00c446001c0303a0300c0b4100001d0442c400c01d84043e120384034210020400002c0d02081030600c2d0421402c58038150740d940019202c1d07010901c15200340960a103002c010078102440e106520078801800d403400e030105200c0e00b94190a40c01001e41d905080401d107078071040c002c110851a0072104a42c0c00c0e60748140b025000b080001240001420100315541d0b981444405030802d00c00762a0503504030b500d44004230242c007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 195924559 1250 195923309 195923311
    0x2b15050a06230a06051e13030201020610080307060506011b0b070f0201060612020a030e070603020d0612080d0b120a0305070b0c13030f020303120a0f060522090609020603070206 78
    0x3800c103207400340c00a01c40c09100c1c082c1900c90640075044282c0140b604a056a941c0c120158200e940c100c03039400c040f20004032400902d50b4007821560150141e0850000914117200213100185446a2650a1200050004c00c0c0c5040590051011a103030780c2c4c0e00d004031102503205440000c02800000b0306400c1040d205080c0f4861803e95490100c40b40c9540002c07402d9a806100300c20114070120300c02114800542c000b0700c400841c0b404c02103400d00c03c040c403140c0390009c0c60b0300c40c50000707502140307621241200f400781074018007054174020400c4c407054030303007001c64850309120262144d13699040c0c0040b521881c4180c20038004000a4075031200c0c8508001d030159110600c111000740e807910015600901082c2510414044d80040543d5a030455032101000a105038050364148800d1002c0c5410407200e981541c445d02000e4404682045207039a414180c1e100d1750003907441600d104000d0286070503034550510342e40c0c40c242d001050b12021070500d00000c1c062290042e412601c000108401250009a05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 195925809 1250 195924559 195924569
    0xc0b150102060906150415051005120108073008040b070b0a0608070510050d050709091d030306010315030b04061401060206090c10030e010903020f0c2b15050a06 71
    0xe902181d89003102141c1301c00044501d030038450b05a58800382103040030351010203a0403a180c0c0320a2000e4407a800543c00030603501c103080009400090358250808103404590040001c100184022400c00c0010341482e041d030ba05404503901e24105440250500b01c0c0c0c00b06c51660032025860b0355076100c60748444190b000c200195802d5108002049481c0034a2159104507281800039000c00d60900081000746400e21140c20200942407040340c80c040d819118117400346100f600d45903a080c0c40d000710001603c82c9600000310030303a5000c1030340c09115004804c40e9841402413030009440c0041865200c28880c3d145c0024048114032070802c810000582c1c450030b0111002406119580e076680c004a98517281103600c14410380102c0071310082820030b0403402900c803405040c00f00740405224176080c2102c0b00d4010940040e070059050301c48030901806450610b00c2d040c1ea03004a09030034000e606007085901c02500b02c400f000b403c952014041120b01d401c000b80c802076000d11550a04a6508015085901030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 195927059 1250 195925809 195925813
    0x3180307020a03060e24010b090d0b0906060111061509070c05030f120606040b0702040915051f150c290406150905040201080712060b0409050109060501020304081209010c0b150102 79
    0x701018807489a82c0030586d02107940c41c40e0b050780e0a00115045940001030840d4100d0741d8044c2034800a84100c00c0c2a10600440740100158070703001e400108010041485031001c1e40110040c44205c060b45c40e140190000d0076500e0211039220440e080782d01c140d540c0ca0141160002007084841c00c0030820040c0103840d000400c203c4c0a4480c98208034481c81903210f8620100800c201c05030060902c0e4201c040c00d10301580300b550780c0d400d07030485803405c1e15400c64a0503005003201541c0036001c1403840c401ca000e0710003580005400303c1e10150151011603c400b02400002c980340d126242003201c820202e10300680f6041e11926401c20b403400e5000781064240750301c002ca16140011031602c100740304242c03203590141d640d00b02a88805005841200c41c0043c501d04180d1240704c082540070070030300100001e00c070300840001e8540c5003005410071505e20780c10a41c11034000300410405854005081c0b012182840d0b15650f8a41c200300c0103031500f600141c0018220518070781040288005001c115840200c03c0c0c003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 195928309 1250 195927059 195927073
    0x22021c0b0339040207061b110c060d06030c0b0301090f050c030f130605010b090a120309032901090920010516060207060905070501020d1403180307020a03060e 70
    0x81056103604461100d00329000411404071070354411030000606034190003070742a05541082d0003050507079203c0c40090f145030741c88005080030750b0402d8140010322030303003850b103e408103800d682340b41d48074003a2068040c031842010940ba4245421b80d84410000d5500000e445841a03550325100c1a030f80003481601007003403400d003540c92075005500443d4441e0322000b00651455440f041c10304542000509200c003a9880e00d03803000c0000301c40c3d21801340a8904c240c1e1064540c007040081045990382608542d401c0394500d4040c200180d00721140c1c07003d0700c2c0c1c019000401d141d030460f2081081010b086c150883c0d03e007142c00000310301e5110b5104102e014003481281001481c05400350307a07203a00944444d400a60104841c0300d442480d0381246c03108a00c221009454041142c0340e98041e0f07002e203581514542c205400400040d0380401008540c01610306000400343d0b040003120900c3c0c08010b14200c100e52a200e142d561114042c13017190b1038241c1c024007618109440f41014030050140003405180c03885605 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 195929559 1250 195928309 195928331
    0x3090312030c0206060d0f02090903090f0a12031115040f02012c060904090f0803090c030703030c060b040b1012060b0c0a06020901090302090405060f010e0403020c22021c 75
    0x401504041d550b03503002404182c5401c4140566a240400151541e54030902101c00503a00c15000302c0c040c603d058000c1d81c89060450400c2100d1240e030b601244030b0b1168040c100a81c0b208280e43c1400c41d40c060030321038883e07624500c1c90350901400c1410030010100c0e1000b00310420090001c02e400a9000381d039482c0701c45104000c9100b198200c41d045040c2c6500c82920000b0303a250240040c084100e018001013243c80d1142d60780120141c03100f10407a0001000320030003481240400c8145614070301100241241881c585028109000365640503200c40e8440c00c02080c00e03165a080261001c4001e01b2303500b03003280007410041000e035000700d6a2151501348407000884c4200441916403c00300780e40548018072041c1d031000b00035440201e80c24140002e4120000144e0b6a00d84590710481c0550003402c2240b410fa2994290020140c02c4060300540308400c0c000030030b40c00100d01c41d81030010307217010704011005d0003810b0151036980b0b101c402c06030001600c0000314854030680c0c404808a180309002000042c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 195930809 1250 195929559 195929561
    0x204021b0a0312021602090a0e010204080307020f0405160305090312010305010c0215330603070507030305070503040804090f06050310020a1407120f03090c09050105190e0c0f090a030309031203 85
    0x28150314542140300117010340545005c546c82030700003158440015086071341c090554260b0300103a0040010b43c2020842e141542448191618980c3c0c0446041065281c01480d4016001010340341c901010f41c1c4500007a44120200b0480d0314080c1943c203045615070f034a00d40305000e00302e1440170310014050f40320a003250110b4110250300441c85038005410307140050007601000c0409000206502c10008424115502c41800440c0914800d030388a40d56070504e800c000d025100d0203060901000000c0040101150300542510706450f0200d1022038255212091140644000d400c011ba050003000440c0701a900c1d20f1b4000d0207020354613110b42421001c01807010a20f4002e81c1e9010304010902c465620758640b06c2e45072025001801d0130001091070103074032288680103413a084841d0056440005002d40c2c6049054885820003080300303084050b044c1400c1c6860840040c01410b4914404520000c40204c00016195403d00c05011801c20340e0356030a008101004900c026141d850a441540d02c0c501d1007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 195932059 1250 195930809 195930817
    0x40501150f090e2a0324101403070317070507060e0a0f0302091303090e1003030813050c011202090603090a0c1203090302010e011103030f01090c050405010210090204021b0a031202 79
    0x43c40d5210410615010000c6801d944150400c1d45c14041e4000e21802e0301c1080082410f0b40f803039150700c0304840c0b0b03040d804541d41c29034581224140e02c160881d41c03626560f0000e042030569a22104040a4ac0900c65003400d042c06810350041c018003030640c004c03840e82da00840c0040030510031240440c1c202d030b032f820361600e942909010180d0860803080024003040e20842416450621901d080603559a44040c2e10210f4503065900440401121500b08145036100344101e811450802016804015981d01c80ea0b40b18600900306045c00900c00c2c0040e800c450ba82d041d60308640d4083c203004d035685408469240c95100c8840c0440b03200c82c0d0748102166010f5031007038103110658075031102c0003c0ba00b10b40054640041c0d54007070504008000208404444048c4050360042c0a1805440f0055040c034070900d09a40200c5410310070480e0038401004030380e038006680707030440103800d40000d440703145800881d0180c0f041044020220018038841342c1c0c880320015040140301c0c000c2d51010844048042c6481c107900c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 195933309 1250 195932059 195932083
    0x151f0c0201111005100b04031112071508041109070509040510080a0303020c15061e0402041205010504050f190b100b0a05033102010e03010e2505040203071403040501150f090e 77
    0xa4030b0441c0240c81e082c00800380c608598ad20048440701a903840f02c2d0307002d10f000900081c0c0010041c0c0c09210400903110a500d6145408641583c0d240c50307d5200104103000e0740c04250b2041d40c5401c041010003140242c0c0001038441001620048442400c0c043c1c040e602416203142c1d10310401c444940404205910b035030090900402c04110311140c00c40d842c1110841d076401a5119500304000515003280540003810144503400124551409041c00c509289120f141019150020140d210340040107144001d40280e1020446145403600c50505028000580148554210014042c004c0c25000300146100321900640780b1002e0505e820141442d41c0348040490600c601e104803840198040c8070300801991024000280c14051040d017035140094407030003503d451000811141d0080143d1600d4030140100340c2d4150319504142e5401804880c200341003511614000c030108041060039000704281c0b0416541466445031501c0d07150655094611941d010300c0d140c5050303400c24107400308170007003200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 195934559 1250 195933309 195933323
    0x905210609120331060603060c0804080a111c20010c090e15090a06050406050d12030c0504080111030a1817031504090506151f0c0201111005100b0403 66
    0x525003d12032961440e0700d036000e8400201041c0500d00c00ca0300304c0001c091850080501041582c0b071814080d04030340e522100703c0104140d10b410007000c5403140003107030081d82d500c0c6000280c1c8d5650300059814042c43c01c254400403500e441407206c59941c0444014041444000c1d03010104010414290880d40d190740040d010650398041000b04008407143c1541c0124010700c2c1d4010502e40c1d9001038220030f4101c50010181d540c44505000302c0c100781c403038403001e400151000140c1160701d46415103c40c400340400010951648041d042d40c5109406032001851220b000b03211000745044a900b46400407030751460614039040c0180c1d100f05c5d05101c005c004030f03081250860010705408089900c3d41c4010302442004401c420100c00503283ca124145101e070050018080c241040701d41d212007614001c00c00703840354414082808a000280707100d03030405c0ca5a800c01e88002c4c441ca10068912160f0000110114020809a84208003840c0c1105116031a200510015151109003c404a01503400042c00322 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 195935809 1250 195934559 195934561
    0xa150c0f020703030315050301020d06090612031d0109080f01050402040b0609130b010516052a03070905040515040f0c0f150e06121e0f190c09052106091203 69
    0x480d0080d0706c00c0c000c03180c1800d070000140352114042400e80e840a01c09141e25551040c0802840c0324600c101d0b00a0310104030384a01440c8a030710000c04919003114460a129511201058a0ba00942c80e1070000d000030310036203240f114603020352402020100e5040c1e0040b0300701071854006d07140c114100ca04283c00202018140c00c0700817000e0008100100541c0c1c1840010004d001c082c9585040c01410039115400901a074010340c44503840c01400da010404041c014504030350410f98000c1810310aa92a284000800d90f440c1c0c2070042c03500034000c00c00d4031234100c000103210034001410381180ca40d40c0036910b2103000e1a0742c0c5008001c20642071080c4514103240794000c064840c49176001e00c181c040010081e0303080070440820313450f280a0641d2001c00700001c003060300c0150160070401651054042007a80c106292500c000c07000031644585014406985280712046c26028203402030142402401d000450000800ca0b004940f12403003e1410742d2094000103040340c03000080b030880045c11000d03110b0035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 195937059 1250 195935809 195935813
    0x506060d0b0406081f11041d1317041a0304030c1b030807060b01110d0e0d0201020c0316210209010504020304020415080d0201111303110607050d0f1e0f0806120a150c0f020703 77
    0x423041c4090b050004102001c0700d03075000f040b41c40119034680480500c600c0e030354138600440390310712499080d28200320303020a1042101103504049800b00031074100500340710510b80c4807001c9840b18155040284001c0000c1034039024807080354840c7d400c030b040c00e807101d00110584282c6a40c1c0c615054010400080d44010000940d042c24502103241c14418011626250101e900107410301c0054a2403c44020400c00301f0028500c1003030081100900c04110088030031901e801060a40105000e003500513034000000c9030442d00e5640c8100c1c1c00300140c40f015410940c80d032440035107d600b481682d000542c2020703078000303d02d000c01c81229580701901c0c044c1c00c901491079880061171090540c00a51001041c82104042981403240d54203014031f0344c1d102c1c5006c0c0c01c94a009019540604404940c0d1600c4c1d11071242c20760b8008460b561502e09906000030260340d48400a1020342a100c0441210302404a0078401c12008400c1618a08002d550500002201020403149820b0300c003030b07000050f4824002040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 195938309 1250 195937059 195937109
    0x308070c060c0b011a09130903090b0a0512070507080d06030501050a0209090a0f020702100c03080f010e0a0e070f030506040c051f0507060609091b0602010506060d0b0406081f1104 79
    0x1040c05e0304003d03090070803600c0001c880c0c030a88603551a8080c1c075050504c0401d6405032aa0004d005d5000c0c5840c1015010b12006020b03010306212803032000c0c00f03003000c036651078051426030703543d107900102c01a07582101c1403d040141c8007500c4100d40940c20b001c04580c0c2101d0030300a4031072851000d0401c03540ea58030195000c2c042c0040118181060350700b00141e1002d0b8550a0702e14880c0380c40c58a410301d40b60000d01e0001c201c40c0c2d00501140c0c082c9a0b24006101c1c843d43c040c0160b4005203505001f0400308406142e5904251155220840c500282d900c00130400c02c0119480d03104500808240f410b5030b954000b4402c1c070160301c010400b5100c0b031054a0361a92405a00500300c0300c2d0045200007005a1204c0e8904111031404e001030701c60300c481e11000e1540ca40c43c4140613010b000144024022400c140b408100700b402000301c800006510366004403c1d03038071541c0c0010000e0130508200c030240b81000e0703c0040f00010b41c1d0303001c1480ea802d01d200c08403218003407001c4a08441401c6040d40c204140c69160b41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 195939559 1250 195938309 195938339
    0x6050a03150906080703110f06090108060a05040516080903041406031008010207080705100b09190f0c0309050d0201020f0a0518030a0b07020d0801080c010c1b0308070c060c0b01 78
    0x10511451414010424603800c2c0f1440b00074002c0c0c070000300250750550a180e10360680790189544241825100c4401035140c200c2641c0c20310303000b800c000c80745484400006030300007202d81000c4e0700240f0b44010004d21110079240f001c204040c2d521072001544620f1740a58807031145000b100d03121001021400702d1030030910f00a40c0e010203842c28102040f81c40c0d504140c00d9a0000e40b094079a20400318108090103000c0c46900354489070b20702c00b0000860240c005c10b005040040400d0300d0b040c150004100c12085a03000460a080e03405002c00c8082181ca0010700203040182040d6044c1c130038107c1d80d4035201d00520071114400d401000c0503052076120701d0203c0341d55016003605060100d40c14451401c41d00c040102401091295000c50b040d46082907000345031055907048581002440340c01002600800305000048400070301e0040c168011900345210031030810554036513000205c000000501179281c000c0d1013201d100300d411700981656250212200044440081c0c14141c00600400444040003040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 195940809 1250 195939559 195939581
    0x50d0b1008100b1e13020a0c020405091b1503010e0402010516150b03030a080f090703020a0608010e0a050f0a091704090b03010b010912080903070b030a0e06090706050a03 75
    0x610585901d070307a20103003001000040d200e09142c40304030365481460050048050382c6000e441202c0000e006000141e1440b800a000b007600990014041c0c0381140700340b004002054014100384420304113000c2699031500c0310400d5200015440a4465240c500f0284c101032041d110004542964207160404e01000e8015008034148001040040800c0b0140c049200750103000d440e86403444011848440c4c196500701c0101e074844d0704200141480650040b40351030f0450601500e180c501d50b21a40420310b090701c16000a5031001a21400080080c1d02961481c10303103400b580040100d4485410100a90f00141e5007940c42141003070000d00c10002c03580c05580c003540611503000070142c204800303030143e0b0300981001101d0b070f4540c0300780d0107142424003c03c01c0100084ca8800d0b0660314091b0800060300c041c4d02d0041c501600007a01d44130903501088003c02a120f5010b01c659a030030400040d0009080f00d07120440070340a01c04c001281c2e40c9010031140b04903a9143c88051030820038120460003881c44c2400c1e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 195942059 1250 195940809 195940831
    0x1d06180907030c090b01030b01020705030a110609060c030d15030f110109090c0315050618090a0905120705060a05010803040b0f04230117070c020402070201270915050d0b 75
    0x30114128080e004002c1c5004c0388006041c0001c14001030985504550b10b40c10344d84511002c01003030301d00051345549240c0149101804640743c20005d01c50748149032440350701001c00310b44500006004030060407411240c602c20003620042138020581070301d1520000e450754090543d02008561200d50003d82a10145096203400361628840c4044800540402c40013a41d6549189810031142501c200500421152039040c20240212791156a811a1025004e400e42c038011504000c025040701043c59801401d842d9880502201000b039a000b440090b18540300b088049012201280301d482d0580d4902d60140d45482e04081141800b54011000803840803010000024080d4140000030a0000b9464049168000e1040010031707080809800f00c08041d111000d019403a07401080e2040d100d607050301d01580b039900c0341c00180d03038103164040820450f44440e0508103400405e440c0313076030682c0e03036043d4100540ca00444906c2000303c00384c007425400200c00800480070072030304218903070700602090b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 195943309 1250 195942059 195942073
    0x1503070302070c080606190b031302010c0b041109011205100507020f150708010806070e1c020d0b040516030f0602070c0b040f1406070809010f02100e071d061809 71
    0x50340d4508003100358000b06140e00701031700384816858800c200e010203484100c601000305003010700f002e0042c070000e8110320456001090702400c690041c00c59030001c0d9040b1040079000d06e46810305c0e9818440501c1700904c0b4000c03120001c107039031412a40d102c40c4103402c070004090796941c81209400416010300501d042d0300c5000801e020034007080011800d252140b0051410505100b00c01401d007040c1a0030801143c1c20040800c10b000f0f51000c009110f00c0006c03100300b0082050741258100c1c00c44803c8000e074010a400e4640d40501250341140360003a84a08101c8408421a0401c60030740c041d9400010154089141060302060103600908034590040b01d010355855540c6071001c1043d0b0050340204683c080012042100380701e494201c1e07550100c291550340c90514284d4540d5101d208a6040d01d040c00100c0443c1180706108100c034505001001c0410842420610105980d0b002144120006000c10114220888024070440340c05540040c02d0160201d458510030400400c00812003200d03889824 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 195944559 1250 195943309 195943313
    0x60f060b070804090c050306030a0b04170c0303072705061b0a1b080c09070c031101020406090807080123040305190503090c0a1a090613060315060e150307030207 71
    0x300400300c00e40b01d0003605076074504d060240c605641d00440000140b00702401001f045450114050310030650190030400c0d130381d545150019861010719504520072101142c1d03071016007800001103005480f140c0714040c101038600600e00400000320000082201440420003144c1045005040e03102c5030358080ca0701d0380304500d04140c5084400301e01a100c4112034061032540c480d40300b10725030160100301c2c040c02008201002081302107030080d003984100710040d100d020600d88240c4002d4201c0c1540c0d0020356646540e0400204018498020b0800e98018104002410001403003102c54898103442080050101000300500302c1a00400a0b002d00c041006912806202c0d04414501100700d5118a40c40703041c00401240742601c004102801001f400005225400b120300c07071002c07000c40400ca881c0c0c3e41c40095010400f00d024030000307d00050414a00030030300a4240c4c206014852014407402d035042d030b4811003100c01d00d03694084a500025110000c003200c00510000319031010761410302520740710041e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 195945809 1250 195944559 195944579
    0xc040515130b2808010c051803010b1807030e190f0203073809030c09090f0a0f0314160b1b07060e0d180e04030e09150f1507060f06 58
    0x1011003245109483c0f6403203c8141c0365110303080181c045180200210060310358064494810003101041407011a906000d00f40d60942081e8011880a004110b5400180410341e88200c0c003610702c10040b0303084c1180401100800a18041400882600d40300c103144507480c0d880340c1480b991802d90f05400b402202160b504800302c0300301c454620455880c0790703000e00c240ca5080c1101c2060881820210304024407407644c5c3c2c000a004120420403910701c4035030348503044464608695044644410b0060300002001d10102e241d00c0b1031510b0084e00c0d008040075850a54203141e11078030040c0d54030112000201c00c00f242c030988001c0d41c4800f00050915030450071080c01c001c1608002d4080318819111440c07017032074610906c18a101001c1c1401e01d103e4019806000d101001882d026141c0184d20344c200280078944255100c0b03003144406400849541810061003003200403071a2031901030504030003d0701a40c146450003042d08034042c1040341c24100580e880c500604100d05159180940300e200c0442c0306651 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 195947059 1250 195945809 195945829
    0x6060714030304060609060803180604090e01020c061501140703050409050411030d09050a03060506040204030b04030f1830020a150801051c15020f0a110c040515130b 73
    0x590001c40e01c030326107803403c9030070b80e15550451082c40317080541c104011a800070680d54100c40e10121303401d49440d24004140b8501907540001001c505040c1901c1d404003041d4020981087c20348140d40060340c41e03070b40c4542504155100c0d81e001070400e02c440034003010a10041e02c4054805d16110b403800d0f50b0740c0c46201c00c0c0c49064809403a0164106d40c0c02c03095260030050844004001c4c141124013515000000b40c080c101d620020706440d07200c00005102e6650f5604031409146d0152801c0120b0400741070080904989002c48d0003c1030380c05a10f00178080000c9682030440c0e1164410764036420901000991164a4280100c4d401600340c41d0b50700140d46450010b4064060f80b403019403002c9800707200401e10700069000c903019003400010070b1055200c1c02150b0b080e40e60002c0281002c40c000207039250080c0b103400c1c003000780000081502e418456001103110010030f0300030221640c02400c441000700701c603000d5071088402c02400240c100da030b042140b01680c13107240c04200040c0580703140c0045940600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 195948309 1250 195947059 195947093
    0x1401060215090109050a0b06120c01080a020a02070504090b060a0e280b09040605100b0304050a0807020d060204090b12030910110f0a0c0801110a020c0105070c1203031b02031e03060607 81
    0x30447c10002e25007045015001c0c00d400b00741c01030074503071b0714a0b00182580c1c1000c2c4c80314155640001d54040310328001c02c1400c00601000c0c008011411650802c40001903059659906c10300107840001110601140201d0144030703000910714400000d52502c1c040401c5d00d264480101d51600c4800d4055521280b03090310460040301d001c00d40d403525605111655505401c00c03102c400d002d02c144408168002462015203a1100510303565401c207000280d010441c95000900d5a400060007280b00c001c1a04544c0380180162003030707078043c40c00000032038890180004554001c0030150404444610800d15034003400b4008081c4c4418120360036000d4184507813038009840860402400300030b82c010034410080c07030b018041d44079810100c2092009489188101c5850304026000c600c07441030120f080d500740000c00313054010b400ca050561401034080c6c080941498030544104d00008041c50012045410a003011005170054001510420b42c958001030b11aa4015600380442c0b0002508400b40144100f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 195949559 1250 195948309 195948323
    0xf0406090b0412030b0103090305120c1201060c12050f09090601030609020c0a110102030306370603051005060301050a050405090f030714070801110301141f0507061401060215090109050a 82
    0x10304034001030140c17040401550304051401c1003081c0880e0b8001c0030340c0e2a080140c0c20380442034851141e1401c0034098141d540004268081c000114a07401018074240c2d64450445e000101c0c400550a44050041e840c030035014400c100518291881c00c0f01a080c1d200c041410000b07411915011114200e03000740035002415130201c4030400501006504002e4114001d100551031460583d001c10409554254640d092280e161010752004062020fa0741e103000000302d4010040340da031500280940015282030b803885d0300300c2c01d000c2102c0c04c090b41128144d84020703201e0500b5510b040c1c14000100740003460100c66000c0c00c003418040704000e100402102c0d000d43c1c00c40d529a07000c204007034100959a884404d03240c1c07401c2d40d016801289242079a0448482c40703408241c04407000d02061050b142d90721200051490b402844940b11740007400b400909000b0703141000341c04261503528003289030038041c603009a4458103104100880504800703a02201810001c184400b403540c9480c508000d100c800c8841c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 195950809 1250 195949559 195949583
    0x320090a030b190e010902010e060705011b0302031906031101050d140405030903060a0b090106030c02150103080d06050d0f06200f0a1106130209090a05060f061008040b0f0406090b04 80
    0x7020302d000d804c1e0f0000814000b0050a0b840358000f03081c00e07038007092140c0100c8020964a040c000298000f0160903028001a2056100b602004000303600c01c03201c62817003010601d560303881c40c1c0d2a44290300907250b114040000305041c960041d2000c2d000211030301210380c3c81e415602c0c0c102d44040865030055110303600440c3c680280808144c1040d04c010b00c1092418a025001c000682d5602507150454450781400030b1440741310f000890420104e0a1041b0709070000c03000000c2003100c610006d0405000003101005000c1d21503041103e01100d40c0300150071204010f0700040440e580b40c0c0076880c0c828a004100c40d01d40340d0a051450a034202d40d5110103102000300385003004a402040288551040001800c000e10300f458483d2203141d10031790082d0050680b900054500304007085a59515a0043c1c200c0b4801e2500300c01000312405d0864a4078090081000a406071500a00b0b0702d80c052544910b141c0c80079504c041e0912540c14000308203540c1075407102403080c0820121505180114001c0681e0a00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 195952059 1250 195950809 195950851
    0x1060314010501080d080c070215030f1005010f050706020c0313060e040b04020408030714031c05060a0b070b1603140a201905070203010902030115150320090a030b 72
    0x21168140d200c01c96175000500101328095102c0480c55000d04032960351620381519001203031141009404d601070111300001401030904190740c403184039803407505107050860b0700d80c3c004540c80803401c400f01c800b00d903081c8031110000311907401070300d465040403044030b0504842c0c40114101c8102d0b5400300010a60801070043c160900340114034425100380c90070f528251130581000c0c2e0b01e108681e406131004150f83e1540c42c44280034401c0f218072003041090014031411200d03849000745000d803000f0f84030718044000026400c1c0c002d0250768000d504180414420f80e1880c0210310032140507113a5800301a80c03003505184150241582c070740030b900a00000142640f048905c801450840003402c20303102020b0011401c07001d00307121042d600c4d4003a842d10781d440342100e1010030301400035420002d5165007800d8001c01c54074000d03401c20040f520810004c210340700504205404944800b441b000d500803005000038402c119260061680342c102828904075030340c0e6a103483d103030b003402a00e46c1001151601440c0c1c407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 195953309 1250 195952059 195952061
    0x41e0b090d050a05220306050108070512010e031e0403021009080d020a0503030c0703110609012003010501090308070201110607090824011205070b0a08071b050c04021305030106031401 81
    0x10030142074141145461110b0030003401314019040c1000200780001c403007016101c02c883d034540045a111805002658582c40c07040c1d101c40302c41c09074500502030105503040d040414061400b00200300005903240ca8291040b221024200c50740020209008000002c01a212040e0010401486660300f001d07003070911780e000b41003006082c072003011940015809404a50040116900182c9507900e1641d02d03040ba203019505a07514030101c4400d4003600d4100507081c40190483c0000300e00003141462600b00c901c00c580703a0f80c0428001c83d030015207201010300015585d20003c047d03c500504003071040c203038118000c0f4605001100c2c120000b41c8140010400560100001388032400189007920900d80f88400c800345805d014400c0c080019800400070050110a002040262003d01c0d45150345081c0100041e000300e00954840d40022110b141d141e8100010103210000f8652041c05888012210401c1202075080000710280c414406400003559039404d200da1001540308484907980024064280c40c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 195954559 1250 195953309 195953323
    0x12080406080609071403150307030c0603290d110613030308070c080d050a020c060406050f01050405041e050f07170601090c020604030311070b0c0d0f061508041e0b09 73
    0x15003d0b08052050002d142d0300219070b169003540351903486490740e90751071640159046400c056501070180072030120030300100350000d40545919440500c6907550340c00c030a092801e00d40d4203800c00c0c901402848075003071030b01101001e2502d010b6010619195100000684d15078031080e100914644030842c20800c05811003442540200c00e42407425444800380c80f01d8000d880303003c000001003582c0d1341c0001c60600c03941d41a03c0c00c4036050011540203142c1490076500402d000d07250300d0511041500002a21324080c02500d2180360300410828500c1d0150b401c40a00c0e004150040701c550250000110551008000c2000140016450840c0c031000010000c0d04002040e00401c000b14107043e1030720622600020455046130345490000740038040f45550090340c0c05684001003401c0014824050008426006410240400c5400b0041c0810f001c841da41107900768440e490140c1c8601112003c040e0140c860700740e105014840442003c0f590007940304010800d840708807003140c01181031140c02c450030041c40c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 195955809 1250 195954559 195954571
    0x3060e16020d0509030d030518011118060a05040b09012d03230c0a0314010b0304050d18050f030111030f040308071805040c022d01180b0402060906041208040608 71
    0x5134900000400465241c17100c00a012050584400200e840c9145d00105200140d40c501c00800a00e02242c620162603401207031178885a0300850780500141c030b0403504888480072140c0316286458900741613044d0b9a040031000700d0511440d80ca03050705480c50b40e5029180d107112801507501000215030081d084480303004480c410130740d1410312844844a22020141c000c1c0107014000c0e02ca100c120005c4024295104100d40b03110f5802c800000d0f004200e801031030140344941c05864010030200760444820101000344141c202a10104000c2401c003500650030024024002180251034904420003552090b500300001c4c0c8005401c01041c154440003041d0008241d14005080c0890760414000000c4907015242c0b1582d03985000d40c0c241c85c020818816201c0b0040551011610700072090320895a1407419840079501740302c00ea0b196404009015080603901c080680500d031034503001e0054981140c3c49141c1c002408000c0407801070000000710224511640c0920350b5607040260080c0007200142070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 195957059 1250 195955809 195955817
    0x50720101119020d0c031217100e0c09090405030a030b0307151209240c050406120b010224190506060313020102011b0203040e0f070207060c0303060e16020d 69
    0x441040074001c034940e4082c2840c844002c0001d80715000240400888142c020080480d10078000b080200354400544051869110142c2c40c89000c441140c500d80110380006500f0007450062204040c407a064030340021000030304070705040f00c2c1e20210b1100c800a55060711668000b180901001d5854000d90f208140150701034952113140903181360f0428040329a0f101880360340245418480c98035800301401941080c000020722400d50303200e00516851001807280340341007090042403c1d002d0421103040350020341d40e4500504080703001c01c0042c841080ca0b281180103100714241c01c1618541c440d02c0440005004036480e040c000360f00000c145001c2080a1030f41e0900f010000950303501c07419030303a004200ca40c6419500f0201d10040b4014070030100344080301703a1100260f103841c0e0360000182c000c0c0c6a20000c4003880e41c5582c4000e02aa032421991000180c0c00b12105200c6031b4402c008003d84a80b007414003050440d21075540b219007080031103444041c4c0c40c03803100d10004290b0420101000b803680d424 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 195958309 1250 195957059 195957077
    0xf03020607200a030803180106120f0812010e090d170103020127080f060604111e0f04090207030807390f0305041e05030304060305060105072010 64
    0x101055040c05107420190007603039801d5401154001d4285099031010700100101c07011501ca2600e8940d54200740c441141140c40f104600c103081c0414420501507400200020200041c6542c41c800c444a0004080316083e0007808211400c2d25600f0303d241c043c00303401d40400d505280c9244403501e410701905d003c00410007102c880d06005c620310198681034076028a4060342c0100541400340054506000b07092541c8803415000a00c80000324003907400414040c140c80780c0c0e0300c802c0200002c1e81d0700340c0c1804e02000410000021800310100c40ca40a1215407030906041030321910080005411a42c13203d061980c00040c4102010b40c0710401e03030382c88201c43c02c107404440110b11032800d24412504100884407a039060201c0004904690030f0780c02a40940c44184200c03443c50000c0082d081440341c0f42d4000089140c418080d50b625911000340d8901800860800303141000490150402814035810b110782086901d012032465900703408480300b50003000380800800c40502c11605031440c2080c040094402d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 195959559 1250 195958309 195958313
    0x111160608090d0806010c03031b030b04140c03070305190e030d060b16030f0e0a0315050c1e0d0b0d030305150105040308160203150103050c090705090d02012a03030608070f03 77
    0x116415004807003031030418015141f61800750005c090800748140d200442d24080d4500c143d15401c40c20f10400162418030001203c0980090b02d80300543d400c7c0ea252605100042c0d80a201c0d0740b29540c00b901806508804000d016546812900c1c8101f05620795003002030710322000030203800303500004c1101240380c07480d0003050715284004d00c0355031324000c08000050ba10640e40c070b4030603e03046040000003081250190f50702c1c03500c41000340401ca00034007424184000140d91a038101c0544a075840202c15548001090786204503003030740070318004e00e4490b0341c4030a02d100b9905c4d2521402c82c00d621039100040c207428402400300ca010000c940403410414100010320014104505844400c0b840e182072083d0b200b00d500c0082d003040042c0309286804001c000002040c003400180880d009101520302c00296150501c0403550b503c141c000c0b20f40c01c030845003035040041d4840c3d030540e016141010b000314921500784400c420b40c0c03071460340243c0020341ca982040c0140c803820300108000780f2a80303c04124047c03541e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 195960809 1250 195959559 195959567
    0x9010c0e09070f05040b180a0608010e010b030402040617010e0715020703020d0c09020703020a1205070c120c03080a110606030307050a03081003020a12110a0b03150111160608090d 79
    0x60000081003d04082c100d80c4030300844c1030320301034445141c0c1a071700c4940c8500700220701c1d0402030f02e042c400c1a20420000c0c549008401580c1a01d4100e4181011a07003041c05400c9164006070003280c00c15500c090014541d0f503509040d1400702c09150000c0381500c00f4150f60740c6081901e4018522211552911210040e00003810b141103e90590b9076180401e0745041414070900c495018418981c00007030b0310700c109580031030b01c1501c641c8280315107001d2220100b8101e03164000e00c240249100600541401100c501140a150452140ca001d001140c0c43e559032003029001030f03651102045644032204a03840b01806803c0c4d11410560080d41010344035281c855039150903006c058144a5290081030308444018110710140d500581181a69540c403040700c56819400001070300c0c0d444070510152300c64a4018040800c55420100c0711b1b0035a150132044c2110b03c420003503d14140950040710200110040c8400245000e0103000003e21600e85070004e409254010322841c02c1e50041c0309451041500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 195962059 1250 195960809 195960811
    0x303090b092e02090d030e0112021303020d08090a0f0f05091501050c16030309030b0601030c0e060c0102040e09030403020a0b0703050406081009020309011d01090b060d020612010e09010c0e09 84
    0x108000b081d040b9005012444028400c2c0800039030805c1a072030b6030703c05160b0040b0702d1120041003a40c1d0303841551a112500340c201d005010b016010240b08190070005480c10303d4030144040d0094103085d1902a000b00003460501c1e16074005101c20040d104204549445494014014082520211101c0c41c05426145440c21041d201906101d00450140200d04082101781688000104030520480c0c0740e04001c2c22075401480300700c80356040c0708006103180d40300b4025840c11030aa9113924040ea1500010024280c010f4101200599400d000c00903064001c2003007030340140d0549024560b05c038218010b20895051940007000001130030044180080e6220049034111061460440140e0b01c0d6032040d641c00296030b5000417203d900100c188a034004040d0301c190007144112105481e0b2009560365582a28030812010f0101e12b10040082da540c00e040d403031003040d14402000319141441e5014602803044082c0c0040c0540501202001a61402403055180d4001c0b076080180420f806100000c801d030750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 195963309 1250 195962059 195962113
    0x1403070315060503060108030c010c0e06070b0711010207060f06060903020a090c0c020d030302090901140112150302030d0207030c0605090603180f10090519050c1216030303090b09 79
    0x24064440101d60a01c40d07000c80b001d004010b050f24210350351f03004200c0e900d402003190304800c0e505c2c1c4160b05210900990000181170f9010384410300f08142900c0302100c0c204020840400c0c81160701900807050f10a00c01031003518800d000000300b46440c562018200e03070b070a800000c01e001d807038101130001da601d140c00002200d0001c000401e00055950084840000700103001390000b00903100e82041540617000303440b401c08103407494501c40e03a07114421301ea94280c00c800107000c520181c0d00c8181c0d80041e500000b501101d0303040c120341202c2e030301da01183c604a070045070a00160003005c0c003801000100920300d402003406203011803c0ca030310000000c05611003d80001d03940107003108007140d8900c06000b17280032908140c2c00e4585280c80000420060030405100325035034040c0c0985402440d00da4a074a020040d002402080b45881c10310501c2404006605120414881c01c00d003c45000603205001c0080d41c400e950202d101c0c001440e01042d404809811a16280c01c404204c01d10594202504030000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 195964559 1250 195963309 195963323
    0x1706010e040816020603040b0412090302060906071e031806031a0907021011090a210f1401050a0b010e030c012304030b100509100303021f2d0614030703 67
    0x154101c01c40410f06841d5040082d000200403081105005800c50401e20440c00b48184201e15640301c54101c03032210003404029441304003030002002a050500113498014460841200204a803900c400f4001e030b580d45044000500034195154074819030005207009112500301401214809480d102d0014185400755018400d5400000d041d90b01c2040303012210013908400f0441214181d0b150780d401d902c0f10b000f49020b018094030018164429070b40b14005813082c1e40d051080005e0356a52030300c1522541c2000da50046238814040001c034001c2c0308690142c642d0034000100d840f00e040002d82180c02c18a0310304d00c650014140201030b40d03040b05035064100b0980d03104490801c0105154405030103650000f802c046240070030410000d0700343d07011400b600e40c103c2702902a585d0305040804000b6803030000a00580040c42d4026200d40c2a07032003080703a51016200440c268900c8180320400c000c3c50740c841d01d01c0030107841142c00724400300c0c400c00b0081c011051600051040070000710303948899a10000b4000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 195965809 1250 195964559 195964567
    0x90f060109231e091005011d0d0f0501021b071d010b070b0c040f03060621120e0310050a0b101d010c0512030718050303090915120607091706010e0408 66
    0x940410741043e203020001400c09046040002c2034070b4686041703018041c0403881c680c0d00e82d09140d010403842100794000401d566401d000d507540310080c5104030780080301c56640a00201c11124141c2c10b45a46008880005100191030181140342e4000b00991085004200c000103110088403c0e08441e08603400c280c81200b5622113081000c1c0c10f1055034880600e42e10075817404010405560420000c89041c6213642124441c000581c00006441203801000e041c502800d1880c418025400e03041c1c040f60040c00d90700321a40e401c03850015a01c04032400c146440c0c5d603004011075860021a060884002490160400c030900710355070306060716512109051100b0709811a0411004200f20018400c100d40c156031a0304106401030500507201020308850041590042303180d0400000b0f88918002c000c105000a4460b03041ea0200340c60240c0800350002c0d1000c00b030580c18001042881c0c05100503030355840c1050f20f4002c1000340412800f030060303c1900010010000282d02d800c2c13050300560080419070352 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 195967059 1250 195965809 195965839
    0xc07020103090218012601021312051f0c080a05041101140903010212060a120c03080d0b0405152716110607030f0b010c0c0306020309070302090f06010923 68
    0x85002d6000d80000d10700d481400456484030b58101d0186c0701d40e80b400c0341e95248849802141c02c0c3d01504900d4800c3ca8941002000000300382c081041c0040d000b04181c0e0048074480309581452040c0181c20500b140c2c40b0718a5a0903590322006455111590786000c000f1410203503500c5030a04411405030307040000300e01100124000141c01c813101e24000030000c43d6541c0b808055a03084407800c8400a115482c9998009044008046081c600c0ca900c000e0301c0743d0360b038155a144503594108041d0b01070300da81c2d1000502c142e6240c0b485164000e10712841140711b141e00010030041e0508440c8000702920344118092880e44010384101600840810003e1607045490314040fa6043c0c1c407440554594800d10090041030340e003640c460b00d82400d000c10f0521802000c00c005580403400014000c01d1480501c0040001c80c11681c0a5a049038003401511065940c0743c0010b00307041d90a8032035504442c24201031017106e40c3c101300c04100903d4014048100503841d12103000c0301c010441b070410300800c05070b007008131 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 195968309 1250 195967059 195967069
    0x20a11030705060708130c0306020f0702060a0e1009030c12020103090209040309061b230c0301020711040506090105010813061b02060a0e011a040908070c06080417030c070201030902 80
    0x9006050001125201c04080c02c1c0565540401d40d039250206000b0800714000304486a4490946a0025541c1103c1da2655840e00000e6000c4403048844110900c100c00042e580e91000381008603d503138410742c100864004000c1c011206034000c074248010150204002410101c50408035003400242c4211006640010f8010341181000254441c0407a0304000c105604101e0a400381d420a44d031f00022100c070010380381f080615a000c003406013003200d004c0300d58580b405a10003084440450544802e40c8502c000319003a600300c0300c022240c45001030303503000c510700f0540f05441e80100b08a440070030551400c000038002c000d0280174100d00030300010002080c00015000b40300c0c852490301801005c2d05070a08001c0d11358409488906901e8242407201700382207014000c000014001c48480d2840c940e008080100520102c04100c0b0510424820309002c106050080c000400c166240d40807a403074645010f56022581c5850114000320038004d01c04850341070801d0300c120550a00300080c02d00d8403400095 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 195969559 1250 195968309 195968327
    0x100209060f03010b030a05010e1302100909050106020f250312110d0e0405060d0c0b0d0608161505040b030109110c010e0c040c031a01082701330306020a 67
    0xe00c0800000000542203444e10000c41c4240c108900401850342c0310211080014000d032420b01a1300040b080b0840035103000084c540708100c15080022010340e0b070380000c80a44000340e020001680281404400c0084148140c500344804e80a09a619034008015500b128021b408054006101c070010361520f9401044a0021180e4000480340f52080a103401411041e00005450059040802280340e43c2811009958126480243c00e801d4a040c203641d03a41d02d800c4038a0a0a0b07141d2140c50001e0000c070180003004041c03071959000000301c0d05003c07a900c440c50740340300078030b0070040b04000030004001c1130b10560781926107804010034040303006a2400d400740504801d01e90154030b80540940304050024041c41e18600540e41400450665401503040f03c003042250f001d00741c9840160840756102c3d00c2e266501c0030824100d40741040043e0501070119200360313840703402e580d990303118025894807031421064204030b0320704840380d0000c00c0200741c044034401d448000c200300c0d00480ca054165008924078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 195970809 1250 195969559 195969577
    0xf0406200708100c0516080c010f0203090d0e01050316031503020405130606080309010507020904020d0f030509090c0c0a0f26040f1719020d02130504060b010305070210020906 77
    0x20749105807500125502c071034011601d4103e0b1450041c0401c0c5850291707050380c841070540144800ca40300b980e25201801e51081c2c03511182c6540e174941c4800440d840b0303c080c5000d4464880100340d60104054090940e050100081c1d06002d0103100b08903407000b01c0810b0319040002890f000c900d4100c04905810140c0e80d82d08000e6106040c5400c004603c1d04a90301c07201c0c414054803042c407140d80d603503000c15107074403481c2c4e034103070011f0b01c10000c1c5005410046e02c80e64000b0b102420081d82111030380c6030020803408244040740000c000189000c5c092904c5840550801e45441019240c4034412171610b946142c0410018951003920301d240b824441c241e4004056040b17504207811441903442d2010300320390f000d03005c0e589a1000c80c070408100c03041c00e43c0070a844000301400400d21a442c442e14440c0700c910004040744e100c1920081b48006886d04a6400c407903030450000803d950030545802010b075840c5601440c105468041004411070f4009041000d00903e5040181da030152080400d46c0d900c10800e00b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 195972059 1250 195970809 195970813
    0x30705040f0e011b0c0321090305040627030b060d05061003020406150206010b07061107030e040e0a0209280203011e0e0c040302060322080c0706050f040620 69
    0x40700c06007595900161012074a09000b0080c0002c154283c40d00008003013040800900388581100000e0b0040305440e4041e85a0000042d401000040600603111080300c1180040c1c1d0114007044855040f15007420400345886005000007a0541540da9442a602c400707071151090501003121074862040000c01260000240c81c0145040d01c5a20002c00c804d110480c021440c0181c000f600d08000107176968000b480703901421075a40b8141c3c00c00c02d190803281b0159403283c0e0312107a15640c1d13000000105012440303070702ca81c0e503d03086032002c1000b12081c0c1d105048064108500e1a401a500d810916901c039921003491115000100c5036001822100c0300c07500d00030743c40040085080740e00700869003000f50348400881441500d4911b400c6100030251030395600184103000034401443c00d8006168400212006102080941d04109601078040d0070700340ea41c884002040c030349480003444258007034045800c0c0240740940001102146204a103c0c0b0800c100b00440f11118500100682c4044518000d003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 195973309 1250 195972059 195972071
    0xb030f040303020c0d021e01020f040b0906040801020d140a050403120e0705030105010f0e0702031603140c010f060503100b0f06030711150a0606090308072a030807120206190b03070504 81
    0x210296541141f2031044101d150b8585100c00d10120500072500003c0006140c6400c203440cac00d89041d81500b140c4266079008205210114080030248040c040301aa404808141c94640103903e5890354800303030880c6007050400d010440403d800c811001c90450f252000000c2e03803000c1100709401c2110640083d81c2c19400d00d0000600c102701c45407404103944112607004480c0d100c0540c00e0ba5648214410780c80d0a4000c0200300d0f004c41e00503d2484242b10306101503500d02442208010708460009080208145e0b54540501883c10108042d250b55940e4003410844810a01c0000340c10240c0c504d105807007610300000003110304d403090211040b0f24000c481101ca101c5c00c02c18074410b00c40011203c0d60481ca1510400140d110b1003460b801e41103a4100c0710007481d00503a600d0300020240c20880c00108020220b1254415065a0300c1201c015405401c0c4a610360220b481c090b6076800e035150745c203c110740c40310301444000d020030744023031017a62801800003407030314510b4021900303004039030f03015550080c5424 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 195974559 1250 195973309 195973333
    0x2030304020f060304030f051303060e03130b04050d11060906040e0403080f0f070c032001020d0f23070201060e0c030108060708010308180f100203130e010b030f040303020c 76
    0x166024034401c54414080c9000c09080c41194041110054002150300114010040c010f034000c0c80c0d50350425101203445d41c1c0f41d480c0c4101ba1809291802c0c0e8941c000a24014180e00c2c4800d10300181c40743c2d41480780b0303103403900c00024641c00400c00042c1c01c0307050030114500a41d840b4800c80ba1802c4000d4080340d26565200554010101c040b6016008988141e002403042548885214802e1080890074081f0340c41d24281101d1800302c0c40d20480178080307000c100082409000f42440c0c561203100c070002d40c1d13902050f41ca032400d0711102c00d0750480c3d0314180001d540301150026494020b04c00015091015035071240f00803405002036900c1044070344200700074030a50b100070f0001507050300e8448048440c03544910204960494003440080c0080100b44030322403000950380d0501c850040000c00106000140c030000403507140c00c403414000543e00c001001d15034150030100101c02880140c000014070b45c5001c14030318551000508444c0c0c25440c0c0c00c001403c050080d41925400c0c0b42600498640c68419 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 195975809 1250 195974559 195974563
    0x50106050418050108070b092d13060e010515210f090f0a03030f110c01020301030b0711070608042306010509010b0c2d0f1005011a0909070504080d02 66
    0x290060b00c40c241d040d0700e914102e061690003104d04880e1880c00400c90940f42c4800d4000e1600442180740e40944d07100c80c16510b009003424410a68183c1c03010719104081e51004001844c440340c20500001030501004020715011007034014115841545c943c04d41c6009040041510b1141040150428400d41d000400d1010140001442440c0540c10282c80d912401009561348041c0f0000c100194820324104000a210f500441101c0d9030f6400c011034260364640d61440c1580266004007410780d8007000400501c050307140c3e12900700c10f060801c1042007020b2080a500d803002d038060a01480741040101c3d00b00300b10122120000610a8410300362562214403035502c2e8107081c80303254030910000001161424000742280c640340042c0c4000d2606542203e18042451140f10490a684424040c00351400c0380900050b0907082825015000c801141c08104040750301c1a00007a13051707102200c601c0480b2040d0000c9540601040781c040031070350380c0c41404503450b104a400c000001e0288110b00000a900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 195977059 1250 195975809 195975817
    0xe030a0e012a11040605030a06090b150102030f030702031c021305011404030f15020304080406080f04020d060f09120203090405011406070210030f090308070e01110615011205010605 80
    0xda030303202091440703000c1c00c0080d00380b50000608500001400e03140020705400f01e00040701005080880c180e50b079400040d0402d00c82c00816500c403138950f002181000005d0303203a21380c0700c0c64030441201e840c0800360000b5030341e01170015103c0300c001000000c280818000c1080c3ca00c0c08d4050401141c01c268044c203054040d4110080d0281d8007a42c100001c00d0641c01521400404500d81d40030300e05041c515142c0c501c020485110a40306c500800d40282d1151b05d0f140002d511442c0107100c450b0387c46150840082c0000740c010b02d202c01d40b50442c814440140d0362010303d01105a008000803902d802d0292010f03000309000d10b0010300d00d082c04074011030100c0c3c010019001404040b00c04100c142c0e601e0505868100c403075103103a540040100201c00061400d06440f803010711503450700080f1078404507108421100340507803c2c0e01080000c0100301196601c50700450b030454080c0f9088605114000d10141d035244050300c0702050000c14001c00302d25074071900f0704140c1c0c060b040c0d1040c030455a45020240072030740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 195978309 1250 195977059 195977087
    0x5070f12051c06081b010e060307030204031506080d0c032f0d080402033d05010311011d011b1502030708060604080624040903020615030c030a12030e030a 68
    0x700201060428500c41c0b107042c044811313141c00b03032009540800c070100c8111200b60000341804002000c0500302d0701e801c0c02640c8103a000380c0b40180d80302e04504004583c00c2202e001d8801c2c00f0704200003485640e10108150f4007006c518200307904640701a24084d1889800c8060400741c3c003010341c041c0c8441441c07036594242c424442c3d000780c40a0189407801242e2060301224081c1d0141d000550810788400310900c240c84074a45244014201c098000c03201e040515000b603201c13541a22030b8010300503c42e0b200407501003074030309081060142110700e01005c505000d8071141414040b80358140b8084a00c0d45240c00380301d552140100890001392000c04000b904265244400201c0082c00a02281800000c0b20142c40c94800102000d5a401030700510300507440340070701c480c0d50110910440c3c40c2c072507020b0032100307500c039801402c8149000704180340e82c101102340c0c0034030a50018038010103680340410101c013541c0e0462021500e03482c020b04c0907806400d000340a0101440002002c6a2695000c4040c04080e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 195979559 1250 195978309 195978337
    0xd080712140115020c09010b07020f090730090609060c020f0a0b1b0706020a0f0e060904050402061b0f06060a0b040905060a090507020d1107060507020105070f1205 72
    0x18100a26000c11039000003540e080c0c25614900510899068584207401c3e4881803044542c0402510702007240c01d00283c1c090000000c000c1400300451030200100080000143e81041d09803410000003800302896090b141000c21003941000103102448602c1c0f800342c080d0305028010b14002c0d01d03006008140d04141502c455151458245c051840803d1704514000e13000000c3c000008070b03494032000700c0f40180c04420a0301503000c0c04540e504580000c0c10905002c0c580058558143c10400307010504080603590810000c01910103040d6101015615095000e440c0020a580c0701e02c0865035500c82c03014a44a8000b13000003900280000140103060545100c040d07900c10348588040c404410800d0183d5030398001c0030310081c85600300f2540150b6203c41c00414202c002540c5802086c01c65500b56180f100580010300204c411541040041111100c000024070207649800c20041c02d50040c5c0100178104007000131140180440c080e8102040c1d50000912440c0c4030360001d020b410350340042c4984001c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 195980809 1250 195979559 195979577
    0x316050601120503030c030a060806070903050c01140a0f02070509100819050601060807180b0c0106050d0822080709020a0f02031201060e030111030a020c0f0712080f0403050d0807 79
    0x1c1c2d44000d01d0884101c0c2e00000550940d11285c61903407040e0001003e002031140e1701c00f40069410000c220607406211941c13a14540182182009820500c9180845041c09920110013036400382650440c0c1c40440300b440d185a806100c01400c0382042681d9002e0f6a110720050240841d048510b94440b04440c1d140007251216088900c4030320000d4107000006d04190055001040b6180c0140d103502e070b000516140424103c07130814002406409550004030981e103021580421b0076500340f01e03510181108031600082c858091303031180c1342403080e40680622014584555400c0c0401108480007410481d000d640c40030b17880f044464000d40000903040c000600d0056030000b40c0d40040110354070201c0b00302e00c08016030b08004081d212403c1c01c1001c20382640d41d03020340c09841490440954090b80b407202d005641c50709800b40d00d51512074030040051240e081030404100400c000c01070041e06503071003107169403120341112040140740102c0d40041e009001c0d9086041032545d2103281584100c11a4031503500e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 195982059 1250 195980809 195980819
    0x3160906021203010e070c051e120c060109020904060305120702040f110306040c0e180108060a020a052205090901021b070501050703030209061b0a120e1c0f02030316050601 76
    0x51002a0b100e15400b202080006100d900b2018100b00d038024a94280032540340741c250b41e51460700c078881c10103202c0002c1c80700400000c1a003d0241e5491420305c0c061980c02d01a10306842d507110300041c80341c4c090023580040d10441548968120304015034001050366030302c0c00031101031042644404412445240361000303000f13188a0a101d030201c134070402003c180c1036540310002e010051404618003403d200265940040e41d0780c0c0c102003111030f200d030640b0003119540b42240103072400c900500b020105500600c0320b411140e5005082d40c000b01d0150461004555903491089040d28a9800a035000f0000b20100101104150000c3c41506980e079a11080040d01d100d8280d15a90b16000700c9000620802c48240440c2c469000341555450080143d4908000d90203894586000c015145455400209101081c07111800203050f00b00c0e898100200d032480ca4400185580d0141d265030f0b001850008015014080e454401044d0b8035400b030b041b01d56412416601c4d910b61000404215603c1c8660000411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 195983309 1250 195982059 195982063
    0x708030a2c0a08063115061a040302030f060903031315140610030902060301060c020a05130b120c300d0201020c16050901060305060d05060411090a090b060907050c030316090602 78
    0x10000c2c0761210745d240020340a9940617100c110108140c524603442c2d06021511000b0881200f103520440d94406a451f440c510505007482001e80683c05160010400c001c2d40703040c007004403035000c011002c0d400529007913850308001c000c00342c0c41600505480c0a01c1c11513004030301c1c0c0460b40030740c00450321584e88003081c400440035120b03030314402900240c052004106640c004c4a8090290f88020980c5d580d00c0d49440204181d1040043c203a1103142d194011250b45061040c08102d01e241c3d2540900009424000461699001c00003120781101600e18540741e000c2078061402900c005140c2035a80c1031485c1c1034028043c6d0403041e0140b20901505070350b8009c0c070060b01904000c50300d0142912609a181400c154002c5c68010300803030308600448940d00018105024043c8624401c814406110200c08107015001e00010500c9034914544250301c00881c500322078860f80280211050912562002000c85641c040d815003483c9070303c000310a000d80792015030592506d541c80b503515080900d0350b9140880e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 195984559 1250 195983309 195983371
    0x305010f0b031003140a0609060501030606050108090a152a020c010201020c07170f03041e090b18040201020106050a0b030f09010c050a031505060403030c050708030a2c0a0806 77
    0x1800f000d10070602040001c3c00d002c030070100005c0c0c12094030781c2100300e41c0b540002c0e99041c02e411200d81c1d58510042c0100a2148070b4100500000e190441c45450300d0805903540d01c0302010050160481c1c606070b8005a8819001035412048841440c0302a44103014407045802c2004042005806101c0c040301043d4070500c00d54150300c50307050040c5149440e2240c09440400320407501e00180c01001740d10040207078100300803c000d0203851200070340c51820b908000d0219026800022095080c90f00c003d03001d030b032401c4061070306e226240c5a40281e9116480141d0041c01503038090364004655400000d0360400501c06540704100800d00001542d4030f038120305003216904003814020420500c00100824841d901405a03401002c840d894890303140c90000f096900180d10440c001500910b2410800c03609104850040c15664010740c24170300a5407000c0c04107107410083c0030648000840104000c0000202d0600a5070041e00c2d280c4000e4a0351071a80d02d96600700d4546800020080c5501040d940c545200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 195985809 1250 195984559 195984571
    0x90406050402161e060203090607030c0e0d020f0103090b09010209010e040c0819061a0408010f05070f030f11070b07171509040302160f14030303150616050303070305010f0b03 77
    0x188655100f0750746480c081d680303030850b580c0c03414400c0000100180051008601032481d171001000c440c034151800409444030003031644c0801100040b8010141c403080380c4d0807101c5504507465039860401d0001200103010010307024002207841e809200400c0c00650080000910aa0b204121075651006000541c0d1055000300300060507400040c40c0c4800d1925800700e1002d1400d00402c1a5a0f54505000c8010708885203170361001c000101085112000d104141791081c00700814003280c54004000f5004080d0500f02c0020306454003446081030019030b00a6000a02111403e0340701c014a050950000000700c40381c6012071002040a88000c51007461240700e602880b0881c40780d0003020081c4100c20b03201402c101e0941c8650140714100c2c8202d07503000c40c0074041c2008440700740d601d4200060524402d07007540da40281c10400c1845006000c450078884d400c1829601c859841c641d4400050514404410103800c40c0000710600c0059039042d00074a0480b42209891006c0c82e8403902814a50f2109482c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 195987059 1250 195985809 195985837
    0x20130e06030c060304080c060907060806031c05090402040302030a08070c051e010509061b0a0302060703060e0103021c080703270e070f02010e0d1808070506040b0c01060b040b090406050402 83
    0xc1a18503e040c600540c2e0280c0300d03481d518140010011881d1078181c09a4030980e035504130410a0046ca44d02042580e8052f8007100100342c10300342c00305078951000c5c00c03290410402000003207081068a503034044500955010f000c492b001c24040c2000310b0f65800019084030100c9541c2c4000075646000722001e8940e548003102144608044001540c0a505c800045504003400740065107941080404202d0a96044d2000e0003100032189070003814074800501c00340902d03103084800e025500c4406081c9049d203074195400c407121030590102092100e00f420000b0318025000580404160b03101040d0f645065600d500e1004081c42c040d00c85011400500481205207604800580c409210f0103403803403528298000007c030300c0b03501e0b8103d9042441c40c050300c10100b10041c820028008071020440001c101d000d02500b501030800e40050b20600c503038464012000f4000c9141b40090400f07621480c02400c1c2c0700d1015540340d079140d8040c10142c10116136148203519151740000c050406000f220303100501110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 195988309 1250 195987059 195987073
    0x50a1a0901060f090308040b030f09010c020c0906031c05040f06090302090a02031806180f0115060f02070806101805060109090908160803060a060c03020a08030a20130e0603 76
    0x103021074410f440521010300704880d2102c00008a25140d000340060300000c101d00b030b580c1c58445030ba0f02038000082d0102e0100d030f160840c180d01c03084e070114850320008012100c420a90f10f411000038540204070b0100e13002c3d8111030342404076190304100140300b01d40d05881241480c940d1030313000742c820121601c006034120031a1000905044d005034011544402404a560f0380708281c001c000b0703e840380403100314000880c0b281c1c4080c100d0404210340007094840a00030b0080d410301e800f05e00e0a484151150b441400064952003910130b0081c001c52001e800000101c3e041403030a41c04055280380140b2a1100c440918210480211540e004003441048107031110b69800e4a050221000ac1804120a0700c03500d100f44682080c0e00c584407414480103018044203a00c0382012001c01810080c2640400c00380030105028074002a00411448083d0b0740051503a601da82d541c004450107040e007081114400c42441050035a003890850190601003c0401c00540707a0b900e4201d01c0d42071803070546070716078541c0c0700d10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 195989559 1250 195988309 195988319
    0x601031a0a0906060b04260706200d08060a0602030316110c0d140c01051e030a0b09040606060f230d091703061503060d032a06050a1a0901 61
    0xc14519000800c9038000600c0ca0a141c82d484125403007a0130a69040d5800142008200c000c040e03101000c922440c10a00001900c810280d661021480385809201d042010000c4007241c0075030180d08480d0050039112a0201c0007070091151030100e6509100380741e2900c020840600c0041580d105042c031840b0a940440220720a4030680070ba03055a0b8241e03c00c1241200792038031082c0f8200307481c0380701d000c03528080042124000e041180c1010824100203091100c4d084031130070174500e0103034442d070444410f5581d11428460345c00f400280e841c3da0b4102014206010410402c2da21400443d041540c0d81c00d103c0383c4040781200d41c1103480e42c10b045214452030380c055030070011000a010700d4410381400500d4000310b07900d900703101403807003484054400d0120401c04141040040c0e034064142d4208854138514000001a140d65410000a410468203174111714844004946020498451002c00c1c2c0314040707140ba004001d031604413100d0301c40d20300780081201e03440c5c548110484404030081910310180c0c01c3c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 195990809 1250 195989559 195989603
    0x10210020c0d2001060608041101020a0b010303050d180308041110050702060f04091b020f06070c29161409030d080a06051e030c0a08060604110c01051314060103 71
    0x1044a0f080000002500c82000c803d1207220014403c0b503e40010f903151078182410308058074042581950002040c4000060007100e40300c2c15680c1c1401d02e42d458044005428000708684000f1504c00d41804044009058020011a221750303c62030f49028007140075400d01c80103114200142001c280c0900c5184014a0608041c0c90304104070a46181001d540c1e07100c0d00c05035203043c0c41000911041d640f4a00206074107001c5000d0f4010b03480002c000c2e81c1045540140b90444640d030250904800090b2041088855140115006054404803d0700c1c100081017003d1280007070282c0c7d002c07e11190b0b00d11440c80158080e5005080001c015080c103a200c5e1000b550401401084e840d04546e840901049a035112501c1710300c030031600001e1070908850f500a2519101c64209614443d00b6201c00411031a400015581c1c1e000e103082c3e40c081281400c404007040d690007005032801c010f5003020300304110350b101c0385114102d041c010180c5218660f0012440e42c0c40e60b0082c00040c00b41c21400c1e51414103d184 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 195992059 1250 195990809 195990827
    0x50d020c0307050703081314030a0305160215030a0b0102070509040308060307030b070503180105060f06090102030904093009060e150a09080f0c03070302040b01030603150b010210020c0d 82
    0x8104152031800103207a50383c9042240e1a00b045a441e0000314000e03800c140c2440b41d4a001d04403c44000c03010312551000079545da20f89110050801c48001004042810030305411020941d002e412240303028601810b904441d0800c403000040c5920700007100024ad8400500e000c22204090800911a219034030200c616002c0106855018444d599000000034a80074486209900d150307034040d201d0a1000808520300620742e44926a83c2c1043c05101c465a111140d100b111503003241c1d0690ba615040d00145d082d405920169580545030142600602c20368036a032040100350640a81a0103885034500180c035007259000070005a108001440180e004404010411100401201c9055504801c86c60b03035174002101000080e10002003000407140401c100302c0c01d660203c01030006280d14030b0100340d8030113507444064407543d12441d0f54501e5900940c080d40195800c880040c284001043d1400d02600d0000741d00c1d0f00511401140310500042c1d8030a45040400000141007020b014207021240f400f2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 195993309 1250 195992059 195992077
    0xb0402090c16200a05030d08100801090c050f0103050f0a0903020709020d1b0f020d0e1203040b130603020306090a0207062405011407030f0507050a0503070b18010606050d02 76
    0x2204114404108411000510b2164860b03050040d90386034040c2e05550050741104081c2c01845454014015541d01190070f40b0031484500e041d8a1541e54048110709030700c8240c3c4008084d5192604c2c130024011a002c8e0380c025904141c0302d43c100b640d00d0000450498104884c013801c040e0654011a042e0702c00398014400c007900900c11500a551030300c2030102281d01c040c24241d00c09a0740c51078510140184800c01d07100c41e03080c0c100301c000300780320301c1000e511090300030f0b100c40802a45020414403613451052200c1100c003404220ee443d291903202c0445503500c52030000c541400f102c41c001580301d10031b0089a02c03a00c4098255449a150000110041d41000b0411a02c003501c074001062403071b00402c8041a84000c00c50103003d540d24107000580100310760f00300401e8600c003c03c00e000200c1c2d0400ca4000c841d44880c90426529029420070604015034400010603d010005060082c061108841401014240ba04004000440000380d08039201ca200b4000031808c24000c1d0100395455a0140491f40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 195994559 1250 195993309 195993331
    0x306090613020c060a0203091b0f210610080f06090a030804030c1b171603021519020709063311010e0601080d0f14030402040207120207140d0b040209 66
    0x382d012540d0741e04220085517031a2101d0f81c00b1080020900c801c20a018001a0207144a509c0b00d90040c0840c2c0e10b50304200000740100740c801c1c41012481041c8880d42e04140042d82601c0603030900062440106016209401191042c800102241000816042c1c02506401c0041101c0701165506490b4003400a0007503040c072848982210101d1100030f081e18035180765107229081741b404c1c0802400c029500342080d0405620140c04001e01700c20111030709060301d4048442c1390880c00b004010022030301c01d140701250f507840d80318000c00d101034000a41d4402e45242c0d1405011036a02c58001203054101c40e0007240c841c030310b190583c1c248420050304142d00d030781c502c1c54900d1406c0200342c03100342512807070070548040398000801041210005d000c4603e411601e4984400d130543c40000081030308030600c070846541013001020404541c3d5035811200301a9020254040201d501035001c0d413100124840c0244000c020405e640c0c00c1d00d403070140c05440640c407054a1100341c0b0b5a409200511038000d02c2030001e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 195995809 1250 195994559 195994567
    0x50a23030d02150a0f020a11060c1e0702060906070501020d05130302030d0e0705030102120108010c080603100c03020d09060b0109060206010807060513120c03030e040605090a0222060f03050c030609061302 90
    0x3000301800184047d113841d0710707a01018054100c20501d010002402c40c49404424040a0081c03890154500441c0b41220303076030340d00d80900380000b4180d88283e8440c5580305d00000740b00b0381041010f40290082c1c4800090410059036003181121484000c0c80005005030030800104115400c254003080100300407a04aa0103244c48c0c802082c01ca82c030001d1203400b0f00c05500d00401802e602401400c43d80f01c65883c04100d1414140007103696190720102d02c08889407165440b803140b40c8a613064495101e5207450070b1050300e21600b07140300201a00c4001c0ea00082229801040c85400014440e0407508407200030105c20707241107411220703038000c8a00994082c1103c140040c0c130068400b081c0b8900c5010360300300e840d01c81c607602d0040d00c18201c003009540100e08054042080b640d96440080c1d0080c11110096a202e035400400601c1e00850400031810500d020b2700400c1255111080300209800c6843c1001941c03150030b04c21500307000442e4500d41c4002800b00041140c14147d4580d13002c0c400c034050160034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 195997059 1250 195995809 195995831
    0x7030911091005060c0a06150b070212120f0a0f020c01120905030702100e030715050f07030c0b0a02190302120103111201050c09040614030601030219050a23030d02150a 74
    0x321740c0b10041c5070700140c1c4203004050074010107104410303124101d59056072059241080803000340c002d83c4c01c0644a00c00885900c0c8040f07005009502d1402d80c9404420340d60451000c00400c542c00005040d00000c0400240d140004e0000450340c0503800140c41d5550940344034915000a0b100d910801c4a6a000038020540187c0740d40c410254117a0703040e2200c0c1c0740e10040a00b4540761030070a81c407400c5803040043c9140541900700b0301302c1d200d80410041d015030303d0455007000c0ea0382e80e000040040550300b080d401c003c3da0f8801e96001c3c180182d161400c207407229441000c201c059002d072441c41e912083c0b8810041000400d600c0e441081d16a0203010b2034520402c22840303c0c01c642d41101c052419a10018030410f141c60b15104040c05000c00701d0b401e41030080d8500100faa41c00050000034002d0320405010600303006040c18100080c600200a02445074941071942e0140060906c40504d548850f00441031360b150210b408811b507815035006210303160300c1501203180c020000c1e0440c1040c42c0e840e8000e101c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 195998309 1250 195997059 195997069
    0x160818060918060607150c0806060a051801050f130e06040207080d0c0201150f0e0c070b07030e0f0106060903020a0504050403080406020729040b0901050907260106030c03050607030911091005 84
    0x5a007800b0b906c00070b00a81c0d0b040e0090302035500109440d2003003d08002d00c0c0c5609400c0000d6899400302c000042c24004241c0006a030584100118800610320100d025201d03907020701010010b80e2001d03910303c1d81544848003030000380e0281580041441000380b001c0c20310f46106600581645600b40300200d03000800000d580507400f03142d04200780d5030041120078400e50043c05080c0d41c0140e130f036002140c40c01d20703540c030303403440c000c501520741c00c10180c641c030300212080c104121955104000074002c0041c00d5a5450107000300069202c1207029950f4032000245c546403510426100b030ba010b4403031000d0741e41c0319074940c0c0c002c1d40541001c5a9030081300c42030b00002031105d031241e0fa5075031542e903600320070b0b041034245800b240b04010040c13180c42e0304240400030420000b01c2d40c0c41c200c508981003141c81c400303210071145004401c003400001035840c04a00000303014105298204490081d8150384442c1c4a04404400380c07131150034007800d1041030350342101c1e840c2030403d032440c0e0140521241040940d01ca4000031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 195999559 1250 195998309 195998333
    0xc040905010314010b030a2111060702030909010b0a14130308030109060501081609060507030306030618032c010e0d0501090605060307080a020a0504020f160818060918060607 77
    0x154048401121494040100f44503440707605d030b0101e0080006030103a5039010016000d6030021011041da09030000182c6018406407508005503601307964040ca08244000c0d50790300329404081c80749a4401c00019540070880840300009403d5440c1390015200f41a2400715611030f0407003002e150042c000c0000480c0d03502000d98003030324904001041440c0b07480001040d042000c1d000000b4100000c5080c0c45141e04000c48808560007810801c1e2500c3c02402c00b50010b01581d44081c01301c5040030317030401e8018001c0c0a2450614881d4440000c40c00306030b400110b6907030313003c0c4d11000c0803500711469440329070241881d80c440500040051640c0d0610307035101400c1d9440c8103000c990f166122400e100c074071719040c400c1c103000c0c10b203580081c680a0000d800061251002d88120340c002e56001071000c0300700300e00308125088400d0080c091201368805d4540680103070b00080d082811407071500022255840c100045070704500c402010726480080519a03502d441c0c9010b402641d0003501000000b0001e00562282 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 196000809 1250 195999559 195999563
    0x3050102040e07080f0703051b0304050a0311071d2203031e0902090a050402011b0b09060c03070519020709150f080303060904081e0403060c02010b0102030c070e0c0409050103 77
    0x9a201e91920b02044516040901100300303101c050420413454032400c81000390f0000c400c4c6008656501c0e551081c0c62000b41008080e95100000010002031107400502815103030300c030303945d08070355100040c022984655490081d94111440400400b1100010703c42d5690031404000e810343c0782046106420007050402c141c02c40119465400004012031030700001540c0482c3d800003840107006e0359000444285000381a0090355958002040a692113a514240c41d0590f40111200d40f10071810181501002124128098456980002c6481140c001aa409001d060322214204102071aa05481a40c0810403031304501c11007900240005072401418420051060503209040c10b002800307101901135045543c9a51081080c400707143c50700c2075040c1e84540c0140c126919440066014001c00d4a420310b001c010320f20104020003400900d910075480490302d900200040e40040b07006903124051514800d03004d030040142000400700c0c805005900c1981d00e07080d18074181e00c0e07841040c00ca8100b83c1017 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 196002059 1250 196000809 196000811
    0x110409050702100509160503010b2407080408070305330613050a060501171b0c03040b0703080612070e16050f04120b100506071101031b0206060316080303010911070c030501 76
    0xf1b00f901140e2400c1c08502500c0180c0c02070109841070408602c0e1007885e10a80b26283c004259900d00502d810380980ba00030303500164041d078599076020784aa40741000e00080c1c80b82e010f010002c84110305140710078281c2455071000c220041159034950203482100400083e000305d503144841c021091144a810305c9414404e0b40044d40b1800d0100040c440ba901a2180d034010200c8800d20094250101171501c0c0c030900a40042c2d034034000401d08030700310b000d0b99104800d139030400f05040c002c268100341ca4030b11a4034180c40101801401d611201d81c0c42040d40324220041c480840420b840c10b07001c2d0070441d124103040c01e101e4034040c050801c2d0a181d61107036110512030700320380c030401e0b040042800f041e603049980700d0920300419007003800158041c0314020008210306008104000b4071703406078200144452030308244401c86548000042e4135210203c2e401c511a006401304060700c030301101a024217584401000798110303800c046443c0001c1c407829a01018031101446468001036100115101842c82000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 196003309 1250 196002059 196002073
    0x306072a03020d021e03120c071202010603060f090b0c030702072106060617070f0c051005060a090903050d0f0608030f040608070f1d22140a110409050702100509 71
    0x1038005c1c1000d041052000001d1100301141c000b401d80007040e1004408045c444c43d1541e255a40f0031b902a20402d40001d0600c1a10500600d9140d0198440c0007101e01850007800001000711408003201c42c000b80c024145400d441c0868911007001000d1940b00c1038600480340003d841d01c441c500b10141420580340a0100281c040e400c010240c00b59400070000350800050b8170440c403039038210103900200748104010944035450b01d120f224401d510403071074001c1c081d00c00200c840c980400c00780500311801c0380202c00500303001940d8141c4e40304804031550160360351800e0221510030790001d418000c070381000c0203407652004100310800340020401400c40000b6640c0e40c51800001604150300204030a048c4501a040d240c5a190000718042010082580103010750300d070749000503006201c007645a101c2c5100b01c07a061221216941c800d4440da0b800340107051081d0740302d14844056441c40040501c3d00c0e6030a2000300103210075500b0858208070940181c580345a0094134010444030202c0d914855540b00d20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 196004559 1250 196003309 196003333
    0x80f0a021302030f04080307020a12030203090d14090418060e0303040606080703030804080c1f02091c0c030f03020c030114041a010f2303070e07090e0103020306072a0302 75
    0x34854515003181d085065046103002d400d402c1d04101e004001600510000001603a0103100748094004c195001801c111403c05d050f0b0001d009420480e04402d072445040a1a03a1440c081e845024030242280b540c2440c4c90740900622000d8441e21a2010508942d00c4603800011800d004080c984401c0000658a0b481d090610134250b5103503074885000b60308041f009102003548140155449a00810101d80d41c02c80040001d00e8145030301003029041c1542c3d81545405200c0c0c0c0c0003003000104c2111200361070005940b003400d52220f40c4400a01c1541e103070a0400024500d07901e110040c0c0c1c001d0069032217144003400484c0c00d44a69500310f1501e01140300403c0104000e0b0701443c01d00780da40080103000c940c107005500c00301202d18010701015020b0701c04509468404801101c1c1c4040001e410b464203980d64480da03a48100e42584c424020880f121004101e0300d40090310380307048a400070002d013880d03110701c00300346c1e028102c0403a01c120a42d92180c1d101c02d0710198045080070588a0340c01040410286 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 196005809 1250 196004559 196004569
    0x12010902090f04260c01051f060201060503030703030b1f1206060201090b0609090a02032d0a0804050103050606090d0b0a0c2d0c02030a0812220308070504080f0a02 72
    0x2e0562100c0c040305424000464414540350000d1020061400080e020090240344940a107540c041611b40c2400c0c10000c0070309454143c00c01c000801030030400815200c1c80243c1c240c0b892030040c0c1c0e400d54003c3c060f5a0119110390040104100080c0c41501090401c0407040075000d185082c54001c5610070342c0c10540c0090305e210300e0000b040c2c0c504c005c104038416036a41010b00d600140c0b50b64030401c882000315011800501607480034079402000c90b91240e408410524440703c820781800b2000000c1850075441c1400401c0c1e80b100a540108a07c0c42c050420f00190014140540f50780e80042d410700c9010440d480311008100f03a507026540240382484c090301000c0076501c203100140100306a1075030007080814504404803a50744a0340083c103480a003000c0c126444003c84d8000b0350705201741101501484003183c0206001d407104a640001651280e20101c891032030103624413800c100c100d0255010078415130005403c240c03580340451510380c2d1031042a00c1c081c1c00302c0c00300d10741e0740000b00c19404500c0c007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 196007059 1250 196005809 196005811
    0x2040503070f03050c190503030d14060a0e0a020711040905030d0c02070f0b07080d020a050304050c06160b1810020909130503070f03020f010c091d010803030106030e0a021201090209 80
    0xa0910254142c5040d41c2e202a103949040003c2070103130070002102007814120400c00c0c0050940941101e0703c6542c82803010b03016203800c00004410224a00200742681450880030381074504082e29520340fa00d902a24000070350200000f501d4135444d01c0212800380c2e44030f004148526029400440d06c03120055405e0003119032282c150003d65112003020041c3e8803446150030304031446940310503103841280c00e2800c0706100b8104083d02140c4001484505242c001c40594001e41c0600120782110b2442e20500c8074a205640300b0811544030b500f4100c00141607901d0031340c0d00440710070203141008d903c030080c01d140c1018007844084054000c12030100c0b5051003002c2903401401030009148804031074581c951a40719080c4003400132280c0c0c040040500d8001c00c0fa1009807040780000b023208910841d001841da9183d4010003009207003119142a00000440220b0705a408020180d482c3da4a4020180c009154403814a1140d009206042e405030fa42c5081c480c102038600d100216034103440b40704001c20008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 196008309 1250 196007059 196007069
    0x3807050114070e040c020f07031b0e04030c02060a1e020615090618220b150303090a060e0d0605040b092802010f05040801050405010e0c01030e1c0306030b09010204050307 75
    0x44040820442d55032015034450080d00076030700098841c03840701040f424040540c100c0060f500c03510400004000482c014040d0640941d407203080702c65100c100401a00d0800e0301c001d00001c01069901d000f51604100810f2803006500f060072800b417210310520700d101d60340c044140c056040a4200149240d8202036080304220803100c201c02342c60840009034444411a035902d44100d4000b001a6030038802112205408490074001e5980d061307545048280b03440211200c800224920f021071100c0e040000c140d94160000401c218080d505240080714008440d00f001da5018070400c1c40640450300700d00c980c034001da01882520000f03203043d0324031031324000c5410314042c24252902a41045000545100c0c13425560900e00b070784824191050841e014090350b0880d600c103500c0c04d000c0c401001415844202c0300484442541c150f2050000150101c602014003001eaa401003090401006007200c0705d54940300ca5410002803103910b81d19407290040b802c80340301000742e60003e4240320780e00c4d040040c1c1d40100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 196009559 1250 196008309 196008341
    0x12050d06030203060a0c08131a04060b06030a0b0a060c0812090304090e0703020f060c0d0503070e0618010806062703010f020301170c0a0f0b07021f03060f050306010f38070501 77
    0x2d02c09a0314444841032550302008a1849e440229040102c40c0d0801000300d2340081c101516400c001542c00c004140700011107205131b800080024510303005d815040c0110790840001414904c18204031031300160003d001903214001003001086045a92003580c1200380e049005140060852050107800842d1014161080b0424800200c00303660000780380170304100714601030784c89465100d81a5901c0101c115215071100c1e006c544600d02c9024468846c00944099a515000e81c54410502803a440341e0810030140d8403c40310b600c41180840d0b00007540100f005000000e1141403007280d50300300c0e0003c1c0c20228940940e50f0b50303801040001c100c00030303d40d24115804074070f0303601d403030300c00300c17681085100b410380030040411142c0039583c63f00c0c000d07001c003c1913804901f4969005900100202068051810305007d244c42c0450603084c0011110306035400c00c0c41c3e481c029803c0012a0a44228401004a0408a11848100b90084039a544104041030f0303120b191a280c551810500f0b48010500340c000ba6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 196010809 1250 196009559 196009591
    0x30a0c0f05191410020a0b0705030925150c020916090605030f010302090c120103110a0609080613080f0a050703030506100c02122505010e03030712050d06030203060a0c08 75
    0x141094007000b40d90f81022a26581c84074030b440b009030b062000000e400740200f541c0108001a094001000794400c0003601c00343c496503003109604a5400c2d90402100d6402c240000043c45601d050403104000c10740d2034141403200742d5041d0700180c85040d0403950148107206d21200070604d40d030000308900c050320050230090b040d440d05181103588400e0510000e4030075281c00002c40c6006854000b00d03030a03060040e000c4242580c40c3e0a02c200c45106032208a401034082c0780c80040c00c2841150b0384400d9540000c0603240380e4403103410481000680c90b40c00d0f102d030401000300744046c01032240140600e106589034140c60341d040741009401c41d000245018040d01d00314031180e0103164800c400015482d4111031400c190301074524160315082081650744482032003003204a200c488815011300403a1026a28840703582c40003018551a8000d03e04001c1402c2030a1054040c6c80307014601901951602580005003113070f607500041d14000301501e0700e2aa8036a501502d2200c50f6000b810650f0007024814007401c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 196012059 1250 196010809 196010819
    0x304030b010f1a0f09030a140f0705130b0109050a1202010201060501090b12091f09020f03030708031305010b04020a0509090603010b0105040e0a0906050705030f0f0f0a0b030a0c0f0519 81
    0x48103410f8102040803000160002d18038021020348000d5200581200c5c0811602e143c04503035a00b0040d10b40701da0b881804034a001031000003540e0000c0d104060980e201c6d1105032203445018002c250481418041c0d0319030003080b04e88a1240a038028044030001b186005860b000180c00c50b40c480d000075040006070322060001c61511001c07100c084000100c1000b0f580c2d90340d00801d0800c01c0b540210341d0a4040c00310101e400c6d2115400c0003954034021681300d421040c55204155803403140103c000c091607000d0001400d243d6051488084460050002281d96003c1d280004c0403a4004001180800e502144d06903540c00c0009400358046c809900070401810042c0c000f030b10714052403103051000f45171400003072450a07440d080312050301d5012500b4002400e0200d400350803901b00b00c414131400480c20000441d0450300c0714100340956071804802c2c035251160b000c2030340a0003140d001182c1610405030300c000000c00f601c102000511541014586950601c401c002e00d1500000000b41904d06c00001401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 196013309 1250 196012059 196012079
    0x2010c050a050703020a0606080717030306031513020405040b1602010905030f07020609030a080a08070215041101030213090c030f0506062d032508040c030204020a0201020f0301080304030b010f 85
    0xc0e140307030700703081035500c0e6082841c0c100e00e04010030500600240c01c0c84030019015200007059025900d1404620354060790581ca07a65480c0400c03240554143e0019507070104000c280c010351a00404040030f0100e2404094010405032401544c1c200c4000307464804010050040030201d2100107880c0c4005c1c0f00151003511307103980d07078004c02c0300700903440c0d1002842d202196945001c6581c81c01c0007900390750a40d0200d0070180c1c8250040c24a5802050844000506031880410180c0d19801111f03200300c09a16141c8413802c95812900210741815800c001c211002803800c091007004014520003c0340c0d0300354190004089c0c0300640024040700d03003040c09000700c90b5610010f441207012070b14070318115040420641007511070115a10514210000b052111910317415400300d100f060300324131214170751110351012205032204440c00b80014000700340c18401441c058005010694280c0300150030011520041301203913000783d20254982e031000030104104200086040d00510f40003144c3c1240350302c0e011400e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 196014559 1250 196013309 196013317
    0x3061806011706010203070c0f0312090b071104020705100605011202040e150d1502090a0b0a02030706090602090a1403070e010509071419050304060b03010501080a02010c0533010602010c05 83
    0xc1e10382e44941c000550680d00c02c20946004c50f0700b0000c40f6040720340d40c2d44506159140390009031142403020082d0841c190280d000380d8201d03001c0c421440d2500341d454480c9885c1070784692440340c0c807580030000c01011580c1000041c0c80340d5541a400070304545820b0016001c64044007980b0700c024014007081014124800d0708070fa100071200e903810284544034000444d0340c003104400410b040c49040402203c1d14280d4060880118281e80c50540180c54801078403241c0525106180164820800381c0c00241c5190003080c4168412000035044c103440c080001c0c400d15a43d002a0b0360192200c040300c94500e41000b9950092003001084040c030b505002c0070606128000748602e00340709607018841d19820000c41141d810743c220744104070742030300c004800910310742c81640c2c107480d400e0509a0101c1c4600e01031190320704030b940b52401000560402d070f0041d10006440401581d1ba8010440c808107144e41c101900441006040c215031446801c6a11807115000e041c2c0102045a02d0650406121a0044112 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 196015809 1250 196014559 196014587
    0x30606010e151e0d060b120403032003070203071e0b06010f090902040b0c0d0206092a0307060c2001020703021e040911040c020114161101110306180601 67
    0x100b6804040d908010100d2160310f0504070056103082026075648800780c0a040f1003580e00354140070341a600c0e4481c81700e81c06010100c090b0940310340007160001e8042e5012001c1c000c41c410404041c021092000c8c0c46030f03003049811901680001a03c80c041082d00502c400b00440701010b440080000d545652415080050003141403100355480c2c004258007800c59200100f2441b43c05554554642d108001150480203940340c0500c42d15821002181c008941d491041c0c0c0048014a100c2094904000d240e0340785460b03c2c1000f24251042d2052914184051000b500741e42e2601d0491a5035482d00c81d04890303a00506800c0f0341e80031507400c40144e074080381900450790100c849810700c4204d8080041030303010b8060070550182c07401e4130150803c889405a40009039040320f00f0401207815580590a8940c400300600a465a00380000c00c00300900780103020301c141c9440e1940c1c0e0140c20031481c5003101c008c6802c0c003148113804030410100d40303840c01d00038900c0380e040010100141045000038200700c28ae0300e07407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 196017059 1250 196015809 196015819
    0x50607050c01050903101505010e01051806090f060f03010e1006090303030b27161b14070503030a05090a050103060e0411040e160f060f270f090e0606030606010e 71
    0x13440e04c80c0ea010080404281040b1030b08100c0e2508200707211000c2c003594810349001c40c5240c81d15600302c0d80100c051320000424000d5041c43c4a110070100049640f00c0c0003242c2e804a24954246159100e10015203820600e21110710f43d65410a00c160104c0440104500355649440c041403241544c44015207007180d901d810046400f0a41c00c000940705010248911124000500e1030024107190b8941c40780568500707440c402c600c0d540040300311040d65164a0341003000306903101041c005214541920111030400b8155620543c6400c0003900310b86c070085441000500108001c051817600302c61840042c182400c040040c41e01d03041e0020200c0300010300c05050810785c6402041261240e40149035050070300025250208815010003070000c03920302606600d18030010300822010301406040c009136249880f030340c10000000d4201c903040d5000180116800c0039201000508810b041601e4016190812012807407400c0091240d2600380000c00251103030744441c051180a98020480702c45d94441991 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 196018309 1250 196017059 196017067
    0xf0e0604290a0314150601020d0c1112010e1c091202041a03030d0e010e0c0901031202070506030703090b0a0614040b06162d03020717010b0a0e0907050607050c0105 72
    0x1000411840090b031026001010940341110b01544c00710701c8007142070991a00c0404c68944e034004a9440c0c08185580010894003001080030a02801c000c02c001800100115000c00184c001d090035609000104500d40e8854040103240d0f0291030303a01e40c1d280c0001e26003240d9003480e002915000c90744003c0702a000c0c503079a16010740082c400d25611510a50043c00b2a1b07036070002121f101c002000914603d416551820031030390328028010130b0302c0c0180b050040600b00e00c1c2c0d09541b11440b507101046040020351043c940d00240d00d403901c0000c0d42c810b11054800042801217800d01080b00c2c0707401010054035900e400000e10128035042160000b10750240c500007201c01811010440500c6031019040310701050b50180c07800c108150743d40300c00506030103d850729a446501c0c42c401030040e601800402603044210180200d04078041c080441a030600000f160860180340407507643c92903500901442d500e11402c100540b1000c01c20340e80102002d0b034005241020944610752564018020b140c1003081c000307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 196019559 1250 196018309 196018391
    0x30504030c02090708010f09020301050607110303041e030b090606100302161a1807060c021003060314010903030b01050406051206030c1302070b07030c120b060d060f0e0604 76
    0x30744054007556018080f580d1030300f40201d002e0000d410074480e01c1c152510000703020a5024090007624100c600203070000f400c1107841d82d140340650014540715a0184028000010304810040a030000080a90300e00e4a80d47d0a509250300983c03070060451040b079001d1403e0001680300e0f840d04a00c0900c0610300103880c1d41100031403441140006a002d40b1120540c05051810000718045c50702548c4800c404106d910400c005c025141c0110780320380f401280c040c00d890009403c0c00c20003000c01010b9071800080c4a43c42e60303105090507104c00b5180c0354681d500d1080404054040c890700c031043c2c00074204a4201464804020107521a0f141c0e440b42000d03d42e0f000c103083e52003c000b905600c210040030302c100741c0c0c42241164000e422800f0290782c003080000c00304010b54000d100d104185070441c0d03901000341201c00d10641c041c0c4106100990405010400c00380c01e80580d1040c034001d400f414000e05403542c0361041544680c980601014419031911110102019030244c00c0c05030100b03c1c5502c0d50f807144101c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 196020809 1250 196019559 196019567
    0x7030e1014040b03091b061b0a06020d0b01120e0a02220e0a050106050103020f0301050f1503090a021203040521030702040c03061509081e0a02100807020709110a03050403 75
    0x126a01c49101007010401140c0844901e028510a079901c00440f0520005141e40003481c0d0000000e9680081003045561000300d40c00e641c41c0540089081220002055036684c0c100700d03800711050b504880e13618004040340e984d01000703601120761040c405000e0f208151203030390344507082010028894064447c2104200300406520381c21007007071150130000740d000c2900080d11028080c50883d09946000b1000c00d0a40c064825113014034441540542168280020702c8502484d102c0d00551101100001200d102c180c80c00842c481c000c030501a0024a80750710503c909036406090303007455500203200510158546401403d6240c0200c00c80c940b24080a204060a512034441c000e50040e050940464030250141c2007402254007940890000c00742904044900e00c0140c092406d094100c070751000d101c0418102440d00b1000c10000340c8104114660015048030b503414048400300b821001003015017901444284001e01814900344800e6030442003581e1203210720703868442070607900c03000310b0245489 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 196022059 1250 196020809 196020827
    0x50c090d020d02040e0c0a0f060905040e010e0a060b0a090b030a080a110607091401080603150613020403051005090a0b1f0b07061a0a0501051801031e0b040b010507030e10 75
    0x28004000c2c5c45a101091a19004042d01e450b006003000580010341c44c1c110003c200455000342d441e58803440c140700801014000e009260000c0d0f40d01c4800c503134030000d41400f42e4420140b040e640000e00201e030a0a200710501d10703030b00c003d86080c43c00c040b424407510301040d20b00c86254864002503803a90a40d2042c0d904201185c281d000310b2180000304003086130840d000b03005481c0c071409403107840d40c2003600441c3d80010484040c0c0d01a000490b205c1e0030b103007180511640140c001041c2e400c007200b04249140482c0c000c0e03401542c40e60300c0322000e00740c4205988a016081481e20014180440c182e0b200d01c1054140a00b0403041d048c40411200b84141520198001500c0d8600c02669101840d00b4404054014500702c0304581e02248030710030341e51426003403180c00c84806071034040c18080d44034618000e00b820141c100341859100d910b4000c0f62025660f28410582c00180300040da103400105002c01c407420200b140c2e050100800000c00030a40060454416484c100d810020300c80000104580c07000c1c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 196023309 1250 196022059 196022063
    0x90a260f030f2212030c03081b09011220071205032707090203040b0702010c05041a1812151b040504050a0f0e010b0102060c1801110a1709090901050c090d020d 70
    0xd9a84e080504040d44103a40c0c0003114020303501c2846544405145110320000003600c12098003082040d006a54007801094000d050182c200003100030552000035048034000e56800a2540002040010070921003c15841d901e000d1070140d0131032810000c120a0f04100924031251900181c4a9000c99032041143c10054a6400740139912424280740180c5031a4050701c020001d0f50920f205100414401d000f51811298003810318181402400904d0314298403090800e1214120004070440075164518510103444100c002000200f111030849140e4030b00c0500b45100d42c2d14070458802c02a8032140903101034685c01c0340c001403a5180c0c1144c00000b03055108641ea54281000e0201400303010643c0407800c0b0460a0b0291845030b9140700180d000c501caa05400c1e5901004400000242d52099003034001108000040300d581d1141a251aaa5818503000302021554001280d8100d802e201c0c3c0030641051036107009016906051081d020305004107441640039070310340e1100d5000d650b91110301c042074607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 196024559 1250 196023309 196023329
    0x17031e090415051305060105030604021b06041a16020c040b28060e030f1b06040902041e1d04060528020301060806010c0b040305090a260f030f22 64
    0x800d000903100700120b01e481240d00c100340c40140c420110303c282c004c1502c24403059549600d10343e1036400708030013500715804075000703403100c80e01c0041d0311042040b446002c2c2d8000d00740c0c5c0007406c1160314409201c4400a03c03860301240c030703001c14899042d0000f50050340414111000724011001502248041001040350000765000200100d40c662000d8480001d0780d941d0360307a02504040010a0541da1f00c0c000f94141541e501203039089a1068184180c081c03401d200502c05ca02c2c3c640e03110341c40800c4e600a600705d14a00d215140001c2c14202c0b11001440c005c103440074894048503018411074848000003030000d031a00380c45800081100320700c031b5100f4400e615026210308940406010040007500300340a8040840c06040104a580d80500627160a00e41c1c8508214010768881d07a0845054000910b0300c0c0d000b41200801044025500340010420300c0001030070403004c00c9661907a403600c0750f04e401482d41900f04202600b4018a00e004440d020764121604030760105180c1c1240b5800002da900902c015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 196025809 1250 196024559 196024571
    0xd0c050c0607030e0120030103020628182c06011407060b0a05090903040b0a02010908030f040b100602030a031109060316030f0b0109050f01180b1317031e0904 70
    0x40d41c040d03102c00c004c9401800204065082450f519007191032011a20100e034106000400061a00c100203005010140c1d000013043c00c030481c0c004a2090022104101240204101614400e0014852801044401c40813400c2c10754403120340400d80c0340442d00c0400c10800742e00154169000c0c50311250440320111324550b46181c203043c844e00030003403400340c3c0344290250540068030b850305074041402583e45801451600e07162020b4400300d9446060218255521100d0060205050b80b015512410326171615141c0c0c0d2516240a04120800070058070380c0c00c00f510750a2024690000c00d803a060714441c1030006244100110038481401503600c583d03401000041003208400c100b0040c8034a007200c5480501012144001c42c0d41564551050780380000c8040400300618500703041160034164060400003503588081e20041000c1c00c0c150001c07090440300142c074a00301301910744810700a1034030303800082c030100400210545a00c41c11034824284105a00040f00b2a10300f00d0444034121001003040060b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 196027059 1250 196025809 196025821
    0x30c031e0608010e0102030c0a230313051908090d11030d0e0909031606020304020f0a0f080f07030f03200601080703170901170a020d0906020d0606140d0c050c06 71
    0x140c80320b030041c44541d508212a804030701c00140240d0380654051200c1a083c44080c0a040364964041e1382d6400e401000084400000741c050320003103006212042c0c5c0990b041c400d904040340b4008510010341c141425110300d074030100d03142c00c2c1070314116403080b5103510080e01c460a2060038023808190703c0e5814040c1103803181007940c01001210315110103a4042629903103801d81143c030380c080c1c00328400383c01d00300400c007200207012a07008581c0b01d0303c01005d0840c10403805010409914298002d000303841080e000034040700000700b0059003000302c1c60700200b0155055603211201050005001424803a66044014291407521079008a00c0e2010381112749542e52440704a640707403ea80700c00e550207444064000740e10100441150146030042e103900324081303000d0900c0305401c0d030014a10800c041d42884800c1034120a8010b0007482409100007589079008002c0c450200c4d00254400b00c00d00080e0310042000881c2038080e240030145c0800000340c3c20501baa001d0380c0398411103024a10a0045504001c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 196028309 1250 196027059 196027061
    0x617063604020319050a120302070f140c04090809041a120607090b0406081303020f010f09060608010204030c09181a07110c030307140709020a05030108010e030316030c031e 76
    0x3104034001c60413a4410207a0b080d200a003101886805400b981005120001150055850080e5141c081c5030062501c841502c1c1c13a8480d400340c0e10101c4610950002d00d83c07611400708030900c0750300c40446040240b8040c55031000494030410f1b90f02c0380115140c0008000592503041c544d0b51001003d08107400c0250020620f58852808403065000329a1030000400c0030540c480c00d98054520949540c2c615480d070001d03014200749001001c03011882041c640340c5440f8003e01500752504d80c2864007091040d018034006040c2c50017900310400c582c3c4140310400c04034400c0516401140c03074800740001c0f809284c148030b920569641c8000f400070152034040302824498040071600c108883d6490f0611003511824031912070064818044c0e26a1003170041d80081024203009580312449001240d69080c0d0341d001c00c0c0143d81010060300d0100f000400108440203081c00dc8059822400d00a14614a088441207102016900710740040541c0e9150030f00c0c19034040d5000b102c413134280e2151400c0040030807044070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 196029559 1250 196028309 196028311
    0x10c0809040219080f16180302040e010c020606060a0801030233040e090f0c060d1401060207031a07020a03050c030c07030510060501140702060a1e0f030606170636 72
    0xf800180514005076400e00b120880d40d02405500b09a8041e088010f001181c03c8180010250030107084070700000010f83c0c46201d0416014003610002c95140004000030303052490080242d80640300c108001500b050f4080b042a055960440d524181408010910007440900b8100c421780203015a00e00c445410139040540110359001c0992000d66a805082649608038000280b000358403c80c0c80050030314088002e0304080744503d4002803040c0195118400311b007001c6e80300c00c2c05600401001d00a004c60660a504030748040700c00c40040b401d007071b48000d42c0c50f4004000078081220100700310355614014411228402e500d101120b030800d860b801d08c00e450308854904601c110b483d08500242d0355006000b440c08100c4500011806c000d003a40034001503900900f00d03401000b079400100f00c2d41d810880320300c1c1c02e800442e84c1c0748461070300510006000c44603950088030038040c02d9041c6501290807004c1c269403005086e112019000488106c0c203007204c01040c150081c0b200080d00500301d9605a41c005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 196030809 1250 196029559 196029607
    0x307060f0b090a150e131509110303040f0918120e01080105150904150e0106051c0b0616030228110a03030813030e060703050a08010f0f05010c08090402 67
    0x9150240c943e03d88540413514010150051442141001c0100320b0742c2c0448142c0c402d0100e40000d901581940e40d00000c8810301087c0003c81e0f030750302c607131070240084030440e480f010304198021441d1504055940540f81e0051060780c0348251900c0c0c028450f0051a4466504640e0256082408007807000300601580100c0d0060f0380000c20340c3c030000070145451101022040c010070203662601c41042c003400701030102c4121304895082c01c1c201c006004402c0041c0f0394000d03e203a5982c240c0350b900f054000c94284603030300b2150340c0c0907092940c04002503079184100c0d855080e800d0b000d040703107000a2900b6428030309080124006604140402d110b1110b440c80c01799440b038070406c040310313100850200b080900380e5180806030016842c50001240c0c859040002c010890003401c2100c07420310084001031056101c039404030006040031601d10b0409801c120b15502609007244007030b0180b4100142c13000104045c0c0318080c108a0b000c9035003003e00c45468122090208081c00a5551301d4464030001c00084040d0300d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 196032059 1250 196030809 196030819
    0x614060310020f09060904060b0c03030a0e0102030114060a0311040f05030c090405060714090d0312050a06031e031103040f0513090b060d03050904140a06060e0d140307060f0b 77
    0x5031000c0007a00c0d01c01c95400808600340c150610941c20148801500104081e64200b503440d08046580f001040203060050568001035030f403403908000440540741011044d41490380184014000d000c18a9405050f00c0d405403072690b05d802120340c1c110060060008299115040000c2c0031482c6005013840d00196034060b07080300c1096501c04c003400040c14040340c0c00340c25a0400008200d10074462403003194101d0711b681c00d075802d00094500252205c0a0b4590441c0403c213602d110400700e000c2e82c0903080e4406860031040010b1072442c3c90700000d0111404160881d00c1f050102c840401d0b0080c032159401001c2c81c02125216030300c40142e001c5401e042d000b060301c201055190b4100f800018010810940d03131190004249460b10700a100031250124012400d0000500040889440b83d114890106101d01e00311002414001c0d208001c40710f031900a102007042e0b40740b50700e65540b5281d5040d843c00e40c6c0182125410318002c21014154001c0100c000e0805042a03000d4140755200c0c4c00241c0925000c0354 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 196033309 1250 196032059 196032073
    0x6040b070e04090b090f2425020102090909060405100c020304030605130b09030a02030a0e04091209030b01060c1112070e01060504030302070e16080a110d020309190b040f020a0306140603 82
    0x80e005586401408040920301400c7c000b0b80b108440046d06603801c40c0b80b000349200c10b01c42e0345010140107419040e0000042c0c0d8086a00070f0b0300d24041c5149a00138501e071010344054102501e51507224200c82d204d07040d800e51612a00441c6030310801c1154029a00103074200300700c7c02c00c802812400b03941084245c038001c0301d440101e19a00c1010040700c840034001e4004600d88015000c0c1500c0c5900824011540660b44a2000002c5924841201c0352021035039220680241189451204e50f0010b8016404000700304000d580080c220b518a03a094520413200351502c140f41000c1d4030301d00021078000030b0250641300c000040301900440940250303132181c0c099401c0652150305952045c0d20031117406502c9078a0b5500001c076039010700c07a080d4101c0c0c0901c0000c40c42e20303c1e551288210340c1c880e00f80208c81907400001c02c808007405001400c0c02c810702440481c11424103466820b2030040251000d8041c42d25400d41c1402c540d1112800c00c0110b070700060074401302e0141c0b001407403481022100d890090140d42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 196034559 1250 196033309 196033333
    0x12060a0c08130b0c1b010903111605130f0c0c11041407030c030e030315011403070503010b0c01021c020c060702070305100209040f060e061801030506040b070e04090b09 74
    0x11105202c0d00440d05100072940094640d5072001c0c00203400402640700030030060340003500031a000751140c20420004183c21000b440c00805007440a03902c4020390f0010042c8402121000d074180f0300700d410459013006407074200360b00800100300c120780400b0900c0c0340c5500c24031840e4100c01c0b46160540208a440740f9950020203000a07140b01c03100e50f01c0300d201000000703074005020f94842d00180500345000580e992220440e6442c0d0340c01980c0c030281e050800555542b40b5079004000d01d910400c0080a5415400d00c0303900a01540418040d428130480082203075285401c003581a903070b00c0840305280c46042045521080000e40c0710f02d00c45405402440b0002d84130900004074141225800002080c1904000c00054000c2d0044101903a00c140c83d0640e8048060301401080041c0a40c5403a90003e82005410008079442c0807100c9880d40503440010808240c021441980c40368111003002150707039448030304070b03080d41803503108941c0186868807503414003680f0240140b10f10403032012114004410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 196035809 1250 196034559 196034567
    0x80d03050f0f060306010303141201030c09240b0702030a120e04050a0c0c0602090a080a050601080f0f25121214120604110405090108030319020f09100e12060a0c 71
    0x303c941641540c060401080040c0c4101d044040741c105010700c3c541440f41809180e881c0003030a80c4140d81c1e91514003802e0044044910881c664204080305d100210819494a1031440f84544180081e0b00008110402951010700500b031580d58042d4000510003009030b4050308102c080480303580528500400210700f031a50748112050703402c0d1522038106400c1169240c1c00a548110801a0418000180021030400405c0000d078418400e030050005581407640e0039240c440c02c00310003145d17503000640c144c03480d9030701040141407540742020400300c03002c2190095020800550042c3d080f600c2e48042d07030041c00918450b18040c0c0c035050303641c030f800141d079a0480c40f5035000e240c0d500c460b62040c0c81c2c0450320515050740b002250200907502e0505042e503c1e00000c0890100740e006401c0e0740c20010400004000c40c000900785010034110071410590035400d21a82400b42c00d00c028007440f07062640300c0960380503006408150038001c103042641030880f40d9482d1208016640804a2400d00d9071042c40b030341c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 196037059 1250 196035809 196035811
    0x40c0b0a0e040509010b040905010b09090c060a08090c1003021801021f0207020d0f0309090b060f030c03060301061502010902091003080702011407060612030e040c0e0f0406080d03050f0f 82
    0x40c59a521800312068001c00c4010080a0f010040d02c3d907840710030b060141c81d2801010f1480780640000680720010100b403200000c40101840c2003a00311410030400b995500c800d03140c1c0403807075180191240da83c0d0302000340b400c00c640c08182c0d44030402940c04c0e100140c0c190000c05103d204402010905690000103903070321a10140d10280f045920801402c03241d516a002d072010f13900007400480d540e0410344800400841c2c54a090b400280b1560b03041c84111000d010b43c0382c035400240c85c064a0300d0003440e02c448481c000544045803143d00000450f18507682500414080e001014010a8000d003548010f40241440c0302c040780104090000a100c1d81440401c1c403085a0300250410b14040d4168011a044107210b1140820b0b020b00f4800d40c80070503030754840c00c0040e250341d2850141c02d2100c0d08004d08480030986038240700e01c3c2003050070310800d640000101304002090b50b000c01e90070b0b01100010050005034001d61018407591456407015641074212500681042c0c001042c2502d07000e05210b8840c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 196038309 1250 196037059 196037077
    0xa1119050a060e130609021207080105010c15140c03100504051006030908071b030201032403030806032a120a0f0305030721050a0c090f0b09030f070608040c0b 70
    0x18800710104601c50246240703034403c2000600c0d08049646012050381110415082014856404140341c1d070320f4200c801e006500b00501c0e0801040561601d0002825210f00002c01804407a10140c2c89074000003a400951a48d04200c045059520b020314402d03075550401c494029085420302c0000403242850b02c18140a00200c1048490b802d040600c25405400c846108a8013583e08118610100c0c3d03210060700c0c1e0801140094000c0a0318600005050f5140041c50300c0c5040c5459170f00a018608840500302181e515041160940c0e071201c0000c2d00740302d0440300c10450300705500c40d592010526400c055020100449500000c9903021001c03694800022000030070b82081240f2100101e401880039540c0681107140c0303003010700c260030008062004290400c0b01c0c01600d4005000c02c82c035040c0100c0c0b4034480945428400c8518180d00284040c0180c440e070240d14000046011080d00c00380701d45014216414201c1c0d80580e81d54200030001702048605440c100c66000c0e01051040c0c0b88801c48070110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 196039559 1250 196038309 196038319
    0x2e0804021c150507020f07080322061b02060f0a090503071e060516020a090e0601090209060f090f0613030314071104021c1b09050303090d030815030a111905 69
    0x1103401c0c690005001c00741901c0c00358446d551448150801c1002403001410034000999201c244142c092165a22a0700c09020b03500b1280409000b26a0303c08102c2030303803900346140103204103c0c030700126909200c3c0001e003000c900b000007128052240c01c04a0b1204454080d0201c1d034860395640c1c046181d1a031611944009007a80240c1007008921800c0948116440a10030030f600300810b60000c1c0c41610694030010071161a0700004610380d105112841c01095000c7c001d51405240d4400a0380900c42e1620000c0400c00124001e4041d889204240450080c090285035894880001e840700400b803e01c4114000348089986808400d94101901e440c103512008030300000c04130004000c0a50402c0300a2403101c1c1c19450044107003055409441c4079510220161455030007125002807000b00542c10441c002d0740b0810000d201511060444003446426144c5281240c881071203d14030303180180203840e40b502c80e1090001c2800f20702c0200d98903501c01140c003010081b80148020200c1c4100e40301e41a400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 196040809 1250 196039559 196039583
    0x30b0903092d030303043e0409170d05010810020f0d0c0c050d08150103021603051c060e190506030a14030f0d0501060306120b062e0804021c 62
    0x103100d2580004500d5101041c0c04100600040102e899500111000d8801f0b8445201d112500429032102c4040100341006810580784840d54240c206d0541000b160300580e500c0c5809411300c10a540c0c01001200b48008050303942046002c0701020703040078014002d2500030703440e01e440d50710b9480c0300721400d0b11000e01041c3c4c10b0402d001c01d01c400804101108005204910041a001900038001c45468229580302e0340c0c0d584c1812140340804007075481d0401d040c14410002c0d450804001211803a200e41d0625140760f48a2481d00c2c00000c0c2d100244e054031507641000300c00304442e00302a50703039440b0b0404051602203500c4680d0104041d103005990036509508100c9115001c04c004000060110308410126894041c03c200f03d03030869888044410a4203940d80c4c01400000d034580a95001055030a80d40c138442e00d0341c0e4680e0181c140740a004584034075086241c4101040c91b02104c1c060100d080c01e0300c110008541640a800e0000072a0200d1290384808602118a0000881240321503001008480b103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 196042059 1250 196040809 196040839
    0x92d0b060f010c02030f0601030c06050a02060a110403150203010305010b0a034b02030606030a1e0302011103130c05091e0402030109020901030c031203020313150f020a09030b090309 80
    0x9651041e918860400001001c0c00015031000c10000c0303441d035580002440c0700e40c0755042c20600c0340380030741100b400c0100400484e600079a0014540e600032100e9003000a0780007011000220030300c40d560008000302c1c001c00c02110181c1280d405541224000e40091180740d403080200426001507010080c64409110440000244448590304500259080304c40d0745c1e071600e111001c05030400c00c0e01e140f001034507201c3c50070441c24140030994200d4801e4004100403900f0340e56400799498503100015502c80042158030906200b5009449079105039078400b980c0781415126481c1440e8215400c0c4c03603d49529200141c503050010043d4403c4a06c6541c000d5034542c108010f50000c0d01c0079000b80d9143d920743e5888c1000d0392b18202040d00843c82101040481e6140d80380c11404036403540d150070103152050042003c1880c0511010041e06c0d445501c6901c0c49000d0302e410401094003000503d031300c2d880803c07601607641d0005032000c142d9010340d802d540e155948901880d664440d41113a9a00f0103920603440b14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 196043165 1106 196042059 196042069
    0xf050d2007032703030f1202030a05090105100305060c07080423010f0504030c053c0406141507080c12090f042d0f092d0b06 55
    0xc51800c0003e00c891002014800a4180070480d401d55100c0c41c85800c484900e1480722404649030305007904108024141203030600070540c42c10303012841200d00715040d40d041300c0d481401401181d4a400001c000394100c884100d4400c0340901021902480324041401403401e00b88015001c1c000030000101407526103040101800b50030041407001c551354250b182e0903540180d4407148600140040d500c0c205014600c010001c1001c81c800e244030f80340511030320448043c22241804000d07103840051800c0b200c6c41d1100c0743d100507000c125241c03034014200035050b03013400f5403059401c00307500401c1c490800304414110718082c2c50015980c426840d14880f03501d640c00342618204030241b294000022805c1845c03102101c4400d450b00c0255003156190440303400b15910800900030f600c030310b10f00303150f205405000e000c04404030740380300c1600005810305091805801400744a06600d400342880 = true := by decide +kernel

theorem cover : BRFrame.Cov 195863309 196043165 := by
  have h0 := BRFrame.cov_init 195863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 195863309 ≤ n) (h2 : n < 196043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
