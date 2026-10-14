-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0652
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:56:35.353989+00:00
-- url     : https://prove2.me/submissions/da2a91bb-1988-4550-9e42-c37857bcd1ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 117086330 ≤ n < 117266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 117087580 1250 117086330 117086393
    0x303090610030f0b07110f070f090e1e0a1b1502010606020d0e0301060302270f04120e040b180a0c02030910050a02030c0a0b0f0c090d03030b04110304 66
    0x401d103418480202010200e0382c96800051050a450ba8040d0551402811508030080c0541c5004449080c49480390403040052141c01d021065103009082181f0083c08240140b00d10140e5540d000000c03031240302412042c04040c80710511185901d11381004040561494041109201302028480c55141100c0c210301d0340007140c01805403601300e403c0307a0043c0520514500301a20601d41c071080c02907255503207180101c0141d0f0b80103012200f00c41401c0f0820900403509401c10341c00f40e40604680b2945c1a00410040080d58241041c2c0c0c2000c0d00b403a080c94581c0605001c103002e80f104240c0260301000c42c11400c050300003611001c0d48146072048041c40410f10104040c0e03202d116520f41a90403000000c1da10b24100d02030f0380209407685151040300d00e4220b00d841080d04101d0908400c4a4900c640d0090100108110010503006080c0360040e51030b014010b80010301c0042903480c01803d06495100ca03244669999125030807606904034015501c3c0740902e48480110310480103c003c5100c44548046d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 117088830 1250 117087580 117087601
    0x2011803050304180e060f06130e0c03060702070f060507020406030f030201051b0a08132d0201021002040612050a020c0a050a02120616030e01021e09040501050103020a050405060d0209090903030906 87
    0x5d980c144100a004c2a45501c0200c0d00c2044000340802e41000c6040c002c00000180c622559410359445000b40c04044004420142840e0006c6d1201e01150311030901440300c0e82c00748040f001218202d00b442c50b5200018030225024140c1588003820066440f4091000c1c107030107402c00d40c41105e1000c000c480303541851b070481516002d101403407000121641c0c001170032020407070003031000c041c0910240d91818400212907030481400000021080b20ba510b601c00031560108000300c18507211f20000c4d42084d01f8848010460480002c620801c9070301d403004258038180b0b6a0444000700110b00a80e51815468205255511151581207003d101d00c030340300420485010a0391030003242e01d0f01d00035404900307000b41200600307050030621415542c20840c1c1080c0c072215070480d0798100d241c80000c9460380c00702010072040f200c05038011414503004105401003658080111420340d036080700e40c15162600150004020301410040680004203c4103101d6050b00010285d48903c1c0300508031511075442c2407400c3c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 117090080 1250 117088830 117088841
    0x10f090b0f01051903141009050703050c0607240618060e0a05130314160b07080a2c0703020607060e06010f05010203030c0a1b060507020705010e06040308070201180305030418 77
    0x10b6000c084c10420f00c0040d543c0495180080c00c1241110b20191081d03040c07400f1550b1607a021202a800081d040040003c02e00c6110003a001c12140582450310700d44506240c15801d00c4401d030680c4408681550004090340321501804044801005036400c0e049000b008010a00a0b20010701e1007000041e070707406903070240030701c110710030a0401001c00f0703c0d80e401c0e01c101594a1032030780c12510a11010700910f45025419000b28020340d1440800d0801c5032000c2c1901078064101c900c05420940c2603e1049490108110078881c10340c124a0390001c1e8506e441d04003425900025800000011200140503642d0000403006c0d0441c01a607d00d640d9400235410320074200d2040741d001d41c006000085908244001a2043c0c0b034560400c806c841000b810380444184030008202c510381d84d580305005000358108041d0b8080c02007802d08000403140000010514029448000c0041b03a000030000110b9100b0012180000d40588103105d4980d22450a96140d03080341c000c80c0403240c10186801c5c2c0c42c807042d0040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 117091330 1250 117090080 117090109
    0xf0f0f050d29070302030a0c0c0b06150403050111040915031122020d0c030b040c0203030408070503120406090b0f0708060906030321010305070510050d050702010f090b0f0105 77
    0x54010440d155212030b286902100d0401c18110a240056081010765800718070406081d580103989284c0201c1c020201c4410110030300410603e4119000061a100001500302e002160982d00c03002141d00628800e12513508024055403c002154020810803000360041d80c1003460144102406c0850480301c0412520000d043d107111030b0b1110b04582050202c00661500043d11614280c0311048800103981c40348050394034043d40c60740c00600c07140c4e05105030764506508403010b200d02e4420100096881c0800380014121400c002171440c2000010022100906030307501005a0701e29041c2050001080c2700b140c191080f1940174000340c9141c040310402841504d160325100001e44403c0c05100341220002d1403950540300c104505954042913040500c240340002000e212507604628001b8102074150f03012500898000e10300c84100c1c0d41003070644d4071101c403042c0300048550354400100d02404107110901d45003440e080c810380030700c0400718400f031107801740b210071345880d036130310010b2100740d40c0030161 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 117092580 1250 117091330 117091339
    0xc04110301060c030c0b0705071b0501051b010f050103030203041e0f030816081c060f0302030303131e08030411090114010f0302120108060601020f0a050d0f0c0c0f0f0f05 75
    0x42c8880c0740661010780071207000e07180c0b040740c1c04900d9030307000c02203d002d8400d07002054003c43c5c0c44040200c07072500c00d6298401003a5061400303207003c0c0003074118029480e00c610500407840040040450952000c0ca1010540c82e0600c0296500e09000e0344903440781c000c6640460000c00308025049511a4660072a45c408000f041c500f0304d903480d8400c00380c0001100140341404900000c0101d4400c1c00648001025030594200f01500341b600390342218070b6640310b0007420340703030190800250340e020054a901c00c081080f80200d10100d85800c801d2808420644445000503242034000d001c6021b002e0f5101c0c0f171090300c23030381800c0b01068204100c0761002d100341c4442c103d95440001c070170352249824550512786400c02504190404814141b104426005114140e0040040003115a03041005100e8031700070b1405031070b15041c01d455003520741400307451903c01d0040d001840c0004504c034074001d40c0b60f1b6801c005424401615041c40d08540780c4544156082c0ca5000c410209100180d03d190078103d880082 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 117093830 1250 117092580 117092587
    0x2061b0c060f01180507022e060602010c11070f030321020a03050f06031c030e030f0d020c011808030109090804050301140403080702150f0a0b060703020601080105280e030c030d0605030c0411 84
    0x440000003110081c81d0040061581231190f0000003841c018a00a05920340001c40c4448540900034038512480c00369540c164041c00007000a0305808126006807901494201d220303049607011f02c0b02c20045001d1003186c80d88000b503112a00c4d645940114040d944170419a0182c2c0c450b0000c143e40c8080229000c48900b071003d1030300c84d071907010742d00120140c4070720015642440a00c0208e41181d030040c5682204403a000940341000c104d0a1003002800c210b0b02d59805080c80340350311401442d000502035082e05035039030181c5d00b0a018059042e20000c00000380280f00362074900484d241c01803802e03601140030a4083c408255054000301d1004007030204405000c0c044c0d0354078090004000409009600500c4c1c0e119100181030321150010b014660094000b01080d5142c0301c800342c21624005d00384070451000d441d20941702c0301c12400160008180400c0400c0c034101c641c0041c0d00314466681c040c81c0921002406401180c0300d5000701c000c070365044041c0c4100c0c1e500d80c002d01080e100e6500401e4401031042 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 117095080 1250 117093830 117093853
    0x30408030708180106030803010e0702030412084e0105030307110406050d0305041401020303010b04030206070611040906180209010c030f02190606050405070e0102061b0c060f0118050702 82
    0x240c110035405000f000054032a43d0020b400d05003110010741054420810000051007038010039402c107a0080030900c011441e1a140c0344105202044030300c40140281400252001c04805118403120143c1803512240344595049545c10141602074288110350340c5a03000742c0d8000c4040342546812548060702662600001d40e0b01c1d0104905401c0200354415521040842c0c59101d58018807400c3e446619840d6503542130402e2810014034040b50141158800c20051002c9941d00003614101c07603041d94400d84804c8545001c201030000c25040c1103000002003030000784541e45400401c101c0c4d40e034408072404018407240c0034060784a4940c010380440c416440c13900009110b4061110340048a205460088040701c0b0250000c00f04401c050b01c04907298881030110340381520076603800c801c0d5820007101c10455000083d4841d4801089030209500c802c201c00c80d2039102c14200d96446501900f0740d600342c03408051300c2c502c0500a0240c0903005040f2003009820314124070030540587e802c0c0d001041541a075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 117096330 1250 117095080 117095087
    0x302010f09170d090602160b16140f09030f070906051e0d080c03033d0e07090b0c0f0d080c04050409020f03010f1b030911060304050712030203030a050c0304080307 72
    0x1100d241502136a03852180042202803029050485603082003c00454003400d0000c01d510010300111210a039800e0502c002c150464681c0088200c1140b45079140c2c011840b040130303075018048895800d4000d4103041c0301650004600ba10035140c12000c10008140c0719414006070305c10008030310105410102200d1407500e054510343c00d010740308035492841c1203c0e601800e81550000d540d90802100402d8901c085481090b80c0c3c24141c1c4041040c8550034070b03000342d1910320b0440522400d040458428045500c4a20645500016212813041550355601e0462019070b9540e40140d4070b03250703025410044882503c107410076406000303035840c1f041c2401d0801080000402c036500c012a40990001140303050350b02e080c02a1561001d5468001906854503c00800009411800d0f03100301407a040300d0b040007aa9401d038241c1036000c280c54607505c82d0796038507145143c0340b50781c0c0042c1103400f10301094100b0154000000c5100703c0e40d41c5e40505c4942c0758840d80360594081541e004102d4035040c000158894803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 117097580 1250 117096330 117096337
    0xc030213091a06040f15030903051207090b04080610050303030103030f0302091c0501090302070e0723040306020408060702012d0209010e09010f1412071e090501060c0302010f0917 79
    0x145079030b04141001960028156620070f6014651034503e6400800c003060340c04003409015600c5050900241003690b40040041c4500c0d582c0040d126005408160b149204400d0b0a025080c4151200c2e0740380c0d00c0f015880c1d07035540207c40382d00c0b064201c1c40c00811a42004000d0364101ca40c1a11740c1c0305901e841c00015800380d0000c41003203801034001c41e551412240b03200d2408107041d00841c000281000b00e810003e06040447e000101d400800c001403115203540541c40d140e2000300491081500d01c0c2c03058001c411071180358001f601160002c40d0110300c20a0201d06640205043c3d0000c1050318038000b03d00080b1503042032640c00010203040c0c000c60841c100c4d0002d1a41001c1490082d5840142200040b8584030a8000d9102108103c3c03042c8411112480042071080048035919098004446c40c41d40d5a43d150086200201a412070102c403079040036000e102038500f00e03005005941e1560b8004095952001c4158010740c00c1a180d10300c0e0300e08611400b400c0d550010002910705208010342d42d0b940d403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 117098830 1250 117097580 117097601
    0x40605030a020d0510030b07020c0915010c05151f03050a03050c0307060c050307030b0108090304030f030c0f111503090c06030601020a05061f0506030705070b072f010c03021309 78
    0x42e000c000d41e000032540d038401d89200f118241648440941542000d0090301001061207040d907000168640444e950850003641c080f000c030b003040d00c0014110700102c1d5102ca00181c006c1061007070102c0000c500f812079041520801083d5005e01c0f03000703a07a45424060b00c0941c80060201d411107004100404e2003400180304108d418001c80c0e00e01012a5039120444009510620000c0c03c0402801240c5034503000d1204424401d10f07003801141040030f8416104c0c0304d0352000524541c0719501000405000765024440c0b82d401c626000704110503810400951400c021200b03128004a1103500c80394004813003030345d000741149030040c0340c0c01c403040c01400a80c0c0d10252107181903100e85400030780000c00c02c20a1034440c0052107c000000840e1101c19228007200c2e400c1780707100d010180108041c041d800400d4400d81604038881c0b8815803108802035542a030b50f400580f00c2c802403003800b00c618442e1401514901c0c45000700812101510701d00c100c049004d41e203204801c811038000100407214041d00540c40c1417 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 117100080 1250 117098830 117098851
    0x1032307140925020708010e0106030503040504051e0108010209010905090408070b10080708010608010506010e10030525031d0105060d14160e19090b010b07061104140a050f0604060503 81
    0x1c3d01002411101a101c01c8610001a805401c00f80403840007030003051900c00701c0c00001c5c06040c1c21943c07019180e00460007014040d0b0b1740d40340007840308005100340c003030407409290302c0b01c0f00c0b0350719120124043c1d8400200e00340415487c0070000f41e6410605040ca20540c0c01210705400c189041c0c2d5881103219006d448400021172540000c200c00c0010300c500c90042c100800000b603103a1038650f016080d00c42c020311141c1440410700c0d1600c4030352110944160400100d00e0000b4840e42c0702c040c06001c0b881c10b50112104d10301501408190507401d50710005200c00b40c1c007800e40c11400301408c003e00342d5904680c01e80c1c0101c0c2800c0c2c00d5001940b2081c0008080a60400740c03402d00d82c0b61400101804826402410440903600c10b020f1111070b811209040320074548000d00169045458036049518180310f4152a000d00090800610101d0b50000d0b4103e07826a11031691699a4000906007180c81d19040d849503ca035600051145800d06210341e0684d005070885052900d0100103070340503000100a8a5803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 117101330 1250 117100080 117100111
    0x32203090506220b09030a170c03040b040305010f050c2706030702010516020307050d050a0e130605120a0b0c0a0c120c0c080d080a18020405010323071409 68
    0x2107641c0d01016003a210303002a40f0890007094070314081c40d0041c0c0c55000440940082000c810180c5011400005450304810050341160250b50854000d200c0c442619007180404607000c900420726500600459005a00030b00480c894442141d0403a20240d0341042ca00700104104000d115005901d0321060140708001500418050f000c11915801150320100603591142000300d0309880d880c8031403e16585100541c00c1003141e40d40c0c10b036280d01400c050014010046a0400301d0f6205202c461941d4402402c81d42c80360b2440310409000c1c1c403890041e58451091800314880507240080c500440c2a007140054490381c4844030051101e034400d01c030031010407000e030f02c5003008103800300c20039081904190344030b64003140e05007002c2c0e120442c86d800034144c42c0c00c26512964410f40c03004007503800420b501b030700281d01c492464411000c20000c0f0002034106040a00000070322401608020210140b240f68840c899810490940c955619001c2c2800080002400303051504000c4c0e9140e62100035110b004a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 117102580 1250 117101330 117101339
    0x3031b0f0905040c030b0d050319080705040e0c090d0308070e0f0603040b060a0503030c0607030f0b030604150617030c01060518041b0314010b030d0819021c1e0c020303220309 77
    0x241440030b00c401d407009da00000d146d44030b05402c1130850700c04000a14011209003807a803401030542c469442402400c0300860007003201c80c0401001c1311103401d402460210500403618001d003a2030030440e2000003086815041c1c140504120400d440091300003001c1525641d51350347c2d5220400b8020380304580100b111703040406c075900c0400041580102582c028001840e062000134155510701c0a010b40c02c6051100c1482c40341c43c00110036802c207030310180760f501803465020043d00401e43e5603c00700b0000b600e00d41c40348081c0d6003c0000d003000b0b00c0c600000d0204640310030a104005520340202c0c2e020011610024011074981d12000e4a00800c00c3d5140802c0c0c1d5a907151310022a00519441100f40d41d203c00c00701051404110040e800405400c0c0b1500307928040e00c440c000b403643d5003c00e481540c0c0014010821984803105034400444180741081090310b1b191480e00116207109810680601d0803180d90301041c0004140c81c4110141c280e48400f4802c04142d41d24a8400e402d0300300c052140d00301300803c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 117103830 1250 117102580 117102589
    0x3110607092d06120b010e13092a141504051002010603050321090c0102061302030a0f050c13110f0a03090c0308030a0f0504050d180e0403031b0f0905040c030b 70
    0x4004107099540c0c41c1070000385a030700b10205c8200d01c80944c103011086e0740860140d1158448200d401152041c00a1030380000d05202d002c1022160300d0340300c0e101604158212901141c00f541b408d545020100740c0055015030300b4041c00820080000060050500c0104040d1034a000d01e00003e840d41c0c400410070035580e03600d080c80c42c0c00c1070750600070740140c061041a42c49500c030001c660144c1060300419052030322500203074031028041c007541d02c1c07140004a0343c42036480402c48d543c0e6450780f145400000f00c2d6503080458580010b80030640c41080a4162040307540342c14050300600070070810070207142a4410b5000c411aa01c80c1151100341516022694080703144a240000114000d04089541c1e180c1000480c0072a03d801c407030204981d1405c010320003c03071070000c0c4007089005141400d0300d41c5000d840d070552200d0710540c061004104480100010150300d900190511242c50a10700c40000b980d05054600d025000d003003800048484800700024074140d0401c2501007117900300007501e92050400b05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 117105080 1250 117103830 117103919
    0x7140303040e07120507020309090c030720010507030c170c0d140f04060c03021305040504060209030f010b0307050109050904033b12061009022a01090311060709 71
    0x18080740c0c0303820382e03074195078405e0082d96030040031172000e1460b04143d8000a00456405010480e030b81ca008000101c1082c007480c180103400d01c03c00581440304c00741900003030103000b0441c0d9000000303060061544000d40910032100a83c85000201c2c60580e070703103c004190030780108000c0e6003025280e04800c254072428003000ca0044204400040c46c1703103840e0808006540111056808040c030407c80b1803001c400b0501031500b50344084070f01207810344503401d040000c0e0069200e126498000c1d04250315015005500c025540c0c1c6065080d176040694074401074580780b5680c85019088031000f40000d00091180015843c40c540c03e103229058045401944404804413105a00c101407145640c1354841c07808010310a8544240d5008009503e499070710309410401500c1a032781e8064000c54011a0a240c1c00c07141d9150540c2e881e088007185908442807806840c007043c00b0350120302c80c036065210202000c505544640000d807502c51481c0c0c504001d4801c46419040d144084058585089220841c840c3e1031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 117106330 1250 117105080 117105091
    0xb04051c02010e1c05090402030a060335040506030106030c18141206072102090409060b040b030d0f18030803070f0f020705100c05030d0914010b06070507140303040e 73
    0x1550848000c0f6091814070f50640c41050180c0c200321000d1400d52003401c42d1245901a5000741c0c981d19400300740300142445803c01011110103c3c01588000301e5008401d503181c0031040c140038141019070081103588268090b25401c03100400060150741d01035000100d40802034509910002c284a402c0e084003500c5030840003206000040302084d518000c2c04c0c840d803005d20403018141c142084000544640703003102010b010b0705007601c0003c405c2c60b2594180c9103a0b02001e00144100c1c0440d1400c44014030755441d42901c542e00e4008081000e00b40080d0300c240001d4543c40d100d05240399490191881e03c01d0128004c4950f840d0400880011020005140116560780715401c1c04941000094060000c03511074000319030190500b00069541c2514000560040d03090a2461113490b003400390940c13298244422119042008120400034138080c640c00001c445c04c0200030400000c801c100d814400c11030090166405004140464440d0074444c640026005049a240030b64410012200d400111303607 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 117107580 1250 117106330 117106333
    0x19060905091302150d0c0306120320010509101d0c0f04060512010209101b02060d24030b01050d0206040306181211010c1e03050903040b04090501080d1b0b04051c02 72
    0x1c1c41c01001015009031003131000b86c0e08003030286c07500344076221301050700f240d0000d0108140300201d81041d00554840d02509a4102e009200340e03d0004900e40e03403000405a52350341c440ca00a0781400c00d0804d1850000c20b00f00d200013403c6103030600307400c2069a149d03d81703130254413503507410740040c4070762750200e07070784002c1c1c01e16800580c03918403d50801c10300441168004091242c00d074514075450f204d584884007140d87c1220015210880c0450328002052004c0203600c40c020030203100d40511441000c0003045078400d82c0900e030702c0e80e00e03101400110611000001d402040520090000900a4110119031402d007010031071a1560381d26010740d2401d0f254054008101d20f102c0c0b422102902703010b0044a01c202d4140111019826001410340c1424142d0407420580d0324004154210814000c840060000c0b80b010390b1129262555000240020310611800e40704100e591b0100501600d0030f051000300c038250b081090052a1100101010001c00440342d80c055250148030b64001da8404201c900c0c1c16a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 117108830 1250 117107580 117107587
    0x40204080d0305190209030a0b040c05040501080a0510020a02030f09030f070620120306040b04090506010f0f0806010308090108100b13090b030a020a15050c06040503091906090509130215 82
    0x1072144c80310340c40b031809082055004100c8040c0e507460010b022464640d104030007200ca0b03500c5081003400400160032166010b410100001070502002030316140c0103000d841510040c0c00c102c0d1040c2c0480c030580c007a00c009a08140074614114048602400282d04064240c2e1483c3340340102c0242003401a41001000c500700080d5606a51018004c180722f030b40440d0010a46040301c82c02d18840340c0070082c40700d440b0b20f450340e000a0a6844542140e03004039800011a1025615190b40b0400e208150040c0303402c070043c0090024504d20001041c1c0e0407170b41c0028506280c4240280115001c0340010b00002c6482c01090001444498900041c40382c815002102c200351420805000141da0003120110311a91003000b411001da03452400120803604401000d54205010f0704040e01c140c01103240500990040c40c042001b0311034084010039840390126154a42107000404611b134251076806500001003221205203c2c50400d25842600004404070150398201c41d64000380364102c04500e9080210b2010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 117110080 1250 117108830 117108841
    0xe12070e101e0819141c030e0c0a03020922080a0e0315010b030702010b2205010b1617040503031309050c04051302070204110d050f0a09030503060f040204080d0305 72
    0x150348100c1490b990035441103031545491079056450b203140a810140c500f01c442ca03001007040d400c0340030340c1c2440d41d04103840c0c6151114840e9551100040c42403000700e03007070141400e03129030b000ca4013080b90800203000001a5086801340f00c0808401001a4851001300b0f004001c1900c6041c2c4000c0442d01c101c038160303075418400c0c0004040e0782c1282e015a010740c3c0401c01020071918803090080c1511044181c00e034803583d075000b049000d403451148180c0c112070a50b806a0540c1c0945252110f0300385c141605024999a545400d9124070461843c00510440e074884800020940b4890500d0f10800070821824251250006429903002060000080000d0901000340320211301a559001c0300e000b01c81030800d071a000106810b03400020201001c1940010351000b195940d5128030800054805010344031070307580f20580c0061505071040c1c40b02c0141c0390700042f80d4208500641c680c059150b0b980b00e003161124028001908818050194481c3c0c003800042140c41042000150a0300b5a0b078000c101030812 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 117111330 1250 117110080 117110099
    0x131206090c0f062613030207090f0203040501110708031305070302090a02180306100306051902120f06040c1d01090803031006090f0f0b030c0c0607050918070e12070e10 74
    0x103061841040c01d40701c11390208030302c10312030541c0d2004041c0c0000c0429409454201e0410900303402c40c05d4001c0c0b501a50301850043c56024501c960b10a90080100c4848a50141e101d401000c0c0002d003802c2007000025a00d0740041c0640f00154420b0044038541601c035400101d42910807542d80201e44c0d80850034016031042d00d010404d0f1040c040d40a4111401c008e0a800105142c9000140040361101c0104005403050500c01845400c0c4400440d110054003002100c2c1110540d11310300c6490001005c95803a14140c400d04d031090140c1d4642c414080c1c02c0007002000207458482c01e906000d00036400051800b028401580f1641c1b585000169040c10010003500646146e08600e02000c2c0c001c0342481426a182071240655040d00c0d9099140d0307a038460909441d02c98034980640fa405148180049141c20001078000c95034202c800744c6003243c040c141c0d0710040301c0440304100020582012602541441c1000910340c0420754265000d440e26400ca1859981c030584402d100c00445480070041080b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 117112580 1250 117111330 117111347
    0xb0f0c100b01051902031903020901080c1309050402030319020c011d091b0f040609090f05100e060f06220609031110030b091003030311131206090c0f06 67
    0x104888100803100c41c8000081c0280241c030501081c07500b01041400318140204103a030141841f1050404000d603403030400402079001842d0190101c0c41100c082144500300500791703090b045030200c800c00d40c20b03c0d0030102c40c040c12029005070b1301404200082c0d442d03000c60106490f43e002d415001030181c10356a000061401d08911524501610032a40d40a80c6070380b100201500201680381c03141110141d103030008800d10414441d480a07080c00903000550b00e0300424801c4c01c440145204101a0905c0a065000d4900842ea000c407070816100c024809003240c402680e070001c0380500103026184180c07011821642c0440190f0f2070340e9100c10b041c1d5540428104c095801f620039890903010b85482c40d5240301c0084940c0d143c40c4d00c248010f1041c0401107200e036004002c4e0b1030004248203110705016203030700b205542e2400705500003810a484860078100e00d1044407601140641010324141ca0040914207004503414103d80e03880d150202d487c049036484040002402540546081e040e160a0b400380c41c0c1c0b403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 117113830 1250 117112580 117112603
    0x1170f040510060605030406020903010e0703121d010c02090403030f022206020a0b040f0f0c14030f070b0a0302180406030c091b140702010908010e01020d060806040c120c0b0f0c 78
    0x83c00d0000c14032415030710a040c0e079001988607078003580325884000005d0241c012100c0e03200c118420030600000384284421a0012180d844c0c803894512a01c9601f42911210540c0c800390100f1a1440101c00500702160031070381c82406481d0024400f040f0b4480d0070f0980e1700441112691136141c1380c00440148198130714030002c10301400203007403210050fa0b4007500404004d1001d030501403510381c0c01081c400002040843c1c0e5501055111504c0e0711748520715030980407500750031300a11844603228985800040c582007079802100926061909081c0118080d502581c0300401d080100380c000c0c1071503200c60082002543c882d820106da01e43c1001121021502007041c1d240d00d0700400004400382c3d85d003001840745c3c80019807a4480da62403c0b0300040e50000c41c0f0341d222144035882c1c060b0f0110105411741c054103000c0e00d46401400503542c0e9251840d95800b042d2000f5161701c1201108000c8081500d08030420180b040d91810151681c074560198076400a6011a41541c0002034440564206018051003070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 117115080 1250 117113830 117113863
    0x3080603030304110d03020c03010531020a090c0c05010608060618040b07081f03230609030d020306180112020406090c020c0f1c29010b160201170f0405 67
    0x43c40c050311100c546440f00440c0034001c04842c030049003407500c207001c1660742c1c002c050000c1c4600e06100105040b034604962014001c070460f05600410307558081c40c0340d0511a00280b03003050003401c0c00030780e100502c0c5030781054040c0403018100b04005042802014002d02d0320501030162498200d090140c1155900030400900030340303070b040000040f5560b06054112009107041c01c199602c10082440344521030010350101500d070100001040030344002103a000d0254114818109404a02035076540d9059890040d990003d2203d01010b007850381c041e5902c81402055003054940c140f0700090703c4002a0032245450840c44100025420180522700050410400801c840e1a40b034500070340f134110001c107071407203181e0124201d190350790b404140c0700c01a14003502007420355a45180007914254440700c4145c00744dc3e0010b003182c00c4000c840c200c034101c0c0e520f01396146c44d0144d41190302001e0380400404a050110345440d404100082d81c0c161071045505210603540c0b030030207040292411902607101c054070b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 117116330 1250 117115080 117115087
    0xa03060b0a1202311502010c02030706150e070215180c0d15020a02010204051008010614030c120a09020406050301050907091806050f0f100303050a0503072001090308060303 76
    0xc07580c002141403040351840e40040c1c88107850300f850440e0400f00c03446803002e111410300d002a003c01001c40d48003210300602c0380d4614042c121000b40d013078400c24030005015800a1225401183d4243c000b8884c01c844d488254106a865441c40907213000140c1d003810059004c2d8561043d10040c1d240000d401c40c07003d528040f2803085848000340d541501a06641c0282240e50100c000c00154084191940c080344900355140c2c0340c030103c024000c1d00548510b610803980600b144000074020480700c0d043c0d650a0707558005a8010a00c00003107644040c000c002000000c001000e01c00c084410f1a40c040c401313102c004542014180100b005035169038000038440e902d8803090040e1002d00041410132600164000320b075000c01c000100d4140d9030103040181041c1c0c1400200480c000d10ec00034103208103c01119104582c84074166540614020b0000602049040110355000c41c01003018613442205031801040007013803e102e1008103010760141c0d400507912081c803041055007001000ea4402011b070004c508 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 117117580 1250 117116330 117116347
    0x1b1c0206181f020c0f030d0e0114010302100c11210f06010b04060f11060106020102070311010509060c030a021902030d0c020c0906010c050304080102070b0118020a080a0218030709020a03060b 84
    0xd0ba4600c2503106044140c2c00100f03035000c1c0e0002c1c07042d4000302204806403600e030310340c080b1200040d12010030442d0141d440c000800b080c0d8250207581505817600549900d0f494950200c0030f556074110010151503002071007440d445142da1302403420100000107550701d1030003010280b0345840c0c1800103e40149640046005110160405081c0c80807180a49030078142685035500540742201c0c04c850304400c9001d5000041803054054000b081c41910a544e080c07800c0411900c1d460884105459000c074940003400801c1c00c840b5130401950704a100140010720b409441c85504c504500e02c00c2c0a000585c00205034859602050310918030401c0b1103001031f040b1408610000394903560010180c906004a4041003030600c0000c10a41d00500b2403003000710750b640e206040c09502c0c403d09228501701501c802c1481c220144090083d071715074140310f44801802d80c1764104503c01a4006210405044074020b402c142d06650402041005142480006a84548040e402801d4404980008074240002c0103400c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 117118830 1250 117117580 117117613
    0x319050609130210181d0907140d030e03060403020a03020c03210703030603050708010203010f050105191d03150402190f0303031512080d0506010f051b1c020618 71
    0x603180c0e42d0407030703080b514001c4d605010388922a050346131401c1e1404681d008a090800703840a900e050389111054186da540d061496940c540032400760300f8034145d00717030035a8007281083c1414004030707840307803d00034038a240e130702c000c240b6000c2c0499040c2d0044c1e04c0010007000381a018444000080b80c260050070740c48598041c54105040c0c5468040300e003240c0015003c0a145c071991201c00515480015907101da80d0f0f03008600d010390400e01a40d00b91113110f90001550350300400842d0310610b03503c480114500b1b01c1001c01d42e40c3c0c1c3c1c00500402c1187e659105d0201007540c040c080442680c2c0c01c0e07685e4075214101401030104c40540c41800c21790500385400c06212041c0200310607811242e05107400b0034000700c104060005a65160b019403004103c45103200200491140034000783d00d145030b410400c1d035039090700441302e840004e5003c0011500412039018007015000714510f841042908070742c0180541800520707400008420100160055004d010a06c1c11107401052289178510041290080100011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 117120080 1250 117118830 117118861
    0x6090a06210609080412110a0e060409020f031603031103040e16021c0e01020d0305160509031606030608100509060a020c0a0b040b0108010b060f0a0c020102120319050609 75
    0x101e8001e001c641d5290304204082c1c004103441588522200e40316a40c0b01d056841007850f013101104c401c001c80400925500303182502504581540391001c045448480c1881f00420b9880c0c0706036008181111644a02c0c4c5081180001014000c964103400c03034a1410020441c1060541c00c0c00c040d08100000c0100044015003560000c0303030030030b1041c4004ca02c4401030385000c2d44000350036031445d40e07403504500050300941c045000c2e40080c0c0a46030701c2e100501040302110f0085a00da404000e1010b2981c00c2284110064141d1080c081d044500004203410404e0706410140e1000b00025210002484150710a001442c0c0c1c41850403000d0000d4240009402d85582008007034510056010400d201d185808010655569070400441030715820681844080c2c80c909016044540d800c06402c801c6904221003200c07140d500000b480d40c03d0008408048441100f09007040c3e0440c81980b0401e14442403480003580951400c1d5041503400800790703049810f803400180014406e009040421114010b5216403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 117121330 1250 117120080 117120119
    0x30a0b0106050901090914060f0909060c090102010204090227061603030213051215010f0303020a0f110a090912050403030e040b040f090609020a0b210702030403020607080306090a06 80
    0x50f8954102000499a2402c035501a1b04006d09008013520710003090103000c1c0c080c483c03e48540d541400d90409111000364156400925035000d8000201c0c20386040d006001044c60500c000b5240903504c1000c1800d0341c100000008503010542400e50709002820340c0544030346030070354170079003800030305081050749001c503004c003030305160300060343d50581c07242880700c3c10180c100140185418260b20b800d980d0b5501c3c021180c0340015204000101d03012101c014804112545a402010701c585190707280c06002c04410b1003101d200f9569401032006a890341403107800341c0500400084c09440c94104100a0a60f2088000c01e00070104028000f2941c0180c1c40c41104000342c80215101d4104001b0400410b003a140307980c60a4a0152500104800c130b41003050140d0088039054103090302d4082074a114401c1c4584002c0c40f201c02440d0f07812034031904504652140041c010340b42420366940200d981035010721f02c111100e0f54004100031042c500843c001c0c1d004201180100040d82c1080100104203903001e54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 117122580 1250 117121330 117121337
    0xa0806010e04061d01080303060307031506080a080703021c080601030c300b09010b12090a0c0e010306050f0114060f040314031c0513031103070c061d030a0b0106 71
    0x22040d901504100c040038801400401c2a107549502c0c84030b044080d92401c2d207135103203000000070740c0c1140002a41e010300c0000b00030305840703840c541c1c4862181c4403080c40040316686a0100281562040c0000804103000300c107029940c658914009050020485480d1492502c1c0400191001e0b423061085a0200c000c0c00c0000382820098801da4105074500600b4941c900e0f0544411000300d100070a9030040c03041c04001740500e24282c0c0800100034424041e0340ca16040c107214250026407016101c58122030000d0980701c160110352969800c00f40390750860540c60341c1c04401001004458407a082d170203e0105900d04655042100c0e101c1c0325500d500703500b44070722401300e0341c82d206080ca24219801140d01041c0d500c00c011a001f009a03c03604205000b80d49040c03d1515914008000e0145611070410040c030704070b00c0c440554043c0d403800c10071403110315070348001d21201d0000340e81411409c003d00f01507150a6000b10b022140c010440328107910250007508003150080c001111485258151102c500703 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 117123830 1250 117122580 117122597
    0x30209101806080703092a0806011505220816080a0b061203090901080109060606140d050403030204030b0708160203040b0403120203070203070b1e0903030d0b04230603060603120a 79
    0x84c03040700601803003840908200041c1c044940170b80f1350802401c1911008580003031100b07583d101c0300c42d11400d01f445801c02c241c007800d8950030018400c9000781084003c0e43ca20300d50781c0c3d000e54081c54540c03c80d80c010200940c00040701d0390072240c0b150044002440c0304002898280c01c0d5540d01c0840600141c01240110800310034040002401e00a4400e8014068040103044d80e44680c0280031306034014007901c13614a40040403413000c1c41845e0300154100f001039003e203056405060607004040040c002c1e41095400c0c0300c04000580c85620513030064806607a81d07081402c03c41590f2800300100c1d4240010365000304000c0240c80d04420996044941283c020704640c44644010303400d511681e54020f50600502d1404900c40d082c44010342850701004008450208441c06210040d1041c800c00d44c0e4075071b00500000361400f4494110b403600da00042c001050400d15071300d0a418010f108280540244003802c20054141410044c0990100c01200103080c2070780000b070b80c000345101d1032050008011428 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 117125080 1250 117123830 117123841
    0x1e050303091210090b01150519050d0f020f12070908100e15010f150c02150306010905040509010c170705090d03090807090506030f28060b0a0603020910180608 70
    0x3e01c0b56400010303a14005104030782051400c054030070024002c40c0112040c0c017012203a0030f88540261122408800802070300d40311200c1c4140d6403504080308242c00c09803100e100555081590026001c20300401001d980c40b0022140141c0e2004001004801040280c0344104010040015020603104118000054088801c66482d0030a102d01d05504e10a0a001c3c000103140c01d4003503003100c01c0b500004d0202c803001c0142034080341c200c0340b0b080005c0d43c0b00c01800c1c00100d0307041762240119000301050500313281e03e5940350b01250599a0484800381e0f030ba55160040b02a86800042c22003086900c42220016840c02d00c0c00501280070700060740780200c5c410700302c0e00c00b00b40c09010f0000152409000729040680c0d5103207046c014000c108e13070441c041e0043c0ca01c0054a01c800203031541001c540f24810301d51502d41408012f200850b01c030400d84460340c90b80845025500c503051008060413003a500540d0b5404400306020761180b44a142c42c0030824580e128102c0405003a91043c10349800381307010803061311503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 117126330 1250 117125080 117125083
    0x1120f0204050d030e010f02010b030304062109030e1302030103080f070c080109050c12060415020d0f060e070e190b030a1e0b090a022a07080d05041e0503030912 71
    0x1c0342c00407600021100129014560840d0551800010903a80c4100304061007100f2400d0300d2501030f0580c1c140e40180020301110b40901e00303031020980505440d019a0501c0c03054941078802c0d07400203401103000311907140032030b00300b16000e14030200ca46082945154915500e04415100e41d445140c4081404500c070000c2120301030604006124101c0240591011420020303111920208114800c9038101140c6041a40109049100d030760041d403209800d03004000540d000c3d6026402040c0802d80d0b5104004c0100d51511030400900384007002c90480d45807404014100c0945504c0303280c4201c00360303052403100c1c02e6030b8001442500c01710003844da1691200100c490241c4140c2000c07032070040c0d0908800002c1d040c5a8069800304808581e10081c1e9103c07803804200f00e00c02c52038802098121300c0252100c0501103001410791803440012607080d56961141d40703082c26691030011000642c002010460340c40e90080c5040c0c00c0340c0c4500800240b9107004006070f501e2080c178029030302841140da140540c2440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 117127580 1250 117126330 117126337
    0x60408070c120803060307091406010815060408070806010602010b240409060308030708010e090705012f03120705040506041404060e090703061104080601180f0612060b010e01120f02 80
    0x10915400254240c15207020301c0c0f90340040300e0090280c411038000081c0704180b40519189800001d00502050700c4010044805240041c00b80f1250f50b440038003500552a50305c002c0000300070b0640a800c0c03c9003001c102c00d04001b01a880300003161304202c0c403441141d441c801e1000100958540704103400c044502c00071268040c0d6442140314600d0024001305101c03182d00298400e645669a221840e13032100c00c0c0b45c0b50200203a990420f0707944040410300903540144142d0802ca040005a200300c0c001f220410142155110090a101d40010408110440782c020340b0b00d4004001742400c50506003803070007045403801140304441ca400040c80005419445940c0418007514005401507440d00d45541ea49948520501c070860305180b60508d69040b41c02c2040c00e46d825509182c0c0130f00881d920700030891448090101611140c01c0e03031401c1c111086005c1e03220b0140200b180115100e02a0124240b6008a8041c052024140044030040403171503070b031040d92a005205000c0b4005111942d04003d03c00070300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 117128830 1250 117127580 117127589
    0x4060c0c0503190312060b2b050a020424050f0306040f0f1b091a0717030a05040209060103231e0907091b0203070f1a13031e02060408070c 61
    0xe04250300b50040c160300340050f0740300d009440c0c02040340440c0d00113404031001c6100b400046101403151081c0310400c02423551030900303400806506452900c2c00c01c0d00f00c94003a030b1322094269000070108040381d21002c10200c0c034900b5040805040b000704401034a54030a10504444400c2c00200003401581e587c0d1000d00301e211500b0080040c0c080203000100107183c0501c092085601591205802911030348054090f9400c0180c9036100e014130318074841c0d41380c01107041202c4c64046e40c0050140d452410000e58484c80c141900415603003070034014001d034404040c225504140c1018600901080d2800b500c014840d05581008910750352a000c0800040d0000402c0e8800300e40c00042c8045034400081d031030180c03101180208842c11898801614289411203186c2c0542c10034401080420180354022a400d40034031184030300744405070400702c588001100c03030034004400c04201e43d00385a40a02d43d80040c1d500c0550703201403200141000795a440001340000c04141d00041c1581c20804032950035401030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 117130080 1250 117128830 117128833
    0x1e0901140a12201602030114101802070201020303130201050c030706050603010f060510140904050c1b0c181b030106020703140a02060f09121b04050604090804060c0c0503 75
    0x41c41020001030600b15001d5040150070b0800203490500009080344401404800382079520b004840311208200c200e030004103036499565210034458500000030382910507230450880423122070a0040300b4141503d6190300c543c20b148180b00400060740c00000f00ca4100014030b0710022141800c0c401241d5a00c1188980302403400049a0001003022a0304204d001302001c50080c801c2040e0b0308802c06c00c030303a00b07489545e0b0b02400131445444a40c0c080e03545410650a1103e0340c44c42c09403900007042c2a02c4041e06d003004510400901c480304000101c400f0121012107070040c15a02c42e440c00010911031288244400305681500801c0e41c1c100320304854540220942d454640301e42e0344c0d101c042d40301c19140c441525900040600325035416008904010711560041103c0d041c100c9100e901c3e481501304800d03858001614150490b0088403c100100715414111000b50015a00708144015144041c0c25940918209001d450003e44543c040d103003036413014581400190f546007400c18805006a015a030107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 117131330 1250 117130080 117130087
    0x627040f090b010e0c07150b04090308010311010c05030910020f010e07030507060305070210020a0e0a090b04140f01170312011203030c050c1b0111011104030c0b1e090114 75
    0x80a0440c1c00024405018040c0380d45a6a6248810154010101c1d00080d26800800c001340000708450303107091004c4822080003802421401c08102203402d9a60b0a8011a10000c0108100603040f54070703001110b0280307854180e03030034a69266030345c034092040404c0c401e502c100c070b135911498402c21558000c4e12518009111295455205e95100c86042c0811398560041c4180030410f140240605800391036030f13600512186565503040d40086d08840150400c011300c154220508c0d60399400e9003070181c0a01c2c0400145540d1200c100000c8501c1d2550300035943e04440c0c10807280c041e40c1244503044804a01101d04c129080700902411480788000c0c00c1c900b854020004184402c002054510b014800d403010411040c40107410ba8090148030303042c50300c65001250711005184400224513590b103040c1400900c29140d21602400d50300709508440e039841010404006000b0b0000c1180700a04c0d20031030309442d214200c895458042240c172001c8000c65800a83c3c4042030b4421040d42002c00c80082582e6203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 117132580 1250 117131330 117131351
    0x90a05120c0d080301030303180503191106090c04051e06041a1302180d020904020f0406080f0c180702060703090203100507170a0b01050a031d07080708011802062704 73
    0x10f80e820a01065002928085d0754820380310340c1ea42858602034010780118106a2405540c5059981c0840c900d410000c2d03d801461014a0030071100d8045c141c52006003500050241c14030007103c00c020310022180101780107401c50302c1c50f00c4c108103030010002d5a002c0343e80414003060603a0081c201c205547c07c9145400d681b200180a5070141a50f60710720000d001000489404000c103200a41a01039803080780c82d004540140341403429400042d40c060808590b50340c0d10150241409040038101c2901d40142e01c050100f80380107407a00c00048820a10381e4054149140300a40d01c00c8010201000c2c559142c00160556808200c01380c038a2201c2d882c10b00642c600442c0c01010000030541003010b0480365404509040c0c000d0040c21500c00c0306030364013403c180c5c05070402ca019004801500c6990849800480304850082c0040340c054001170004028442ca8848803d003120900c071013624043c04034090180060341c0302401c4800540314081240d0017520300c1c00105041500304da89003075000d460074a000b607 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 117133830 1250 117132580 117132593
    0x20a03140c2d0a030506150f0d0b0105040b04170109050d09140301050921090901090603020f030d050307360302120601050a14010e0a030b060406060e03060403200a0308010317090a05120c0d 83
    0x460f48510360418007545404ac40195200e0086008030540e408050000b840070aa001b42c6200f5240e00303440001c070b405501901c0f4203040030440c072500c400103504200c050000703c60243c42c0e47c05404003503000700458034000000940b00e050402114074000311342d42c000700d024001c050a0b280008401042c800c403e5a5407c0030100502c00f81c4412401008004240200c0c0c0c980480d039807580c00e8454551600d1540da03504205d440241007000010340005011021005040c42c00c3c685000640613450144100e00754010840da00b465007120302e60540c0000700500013900d4124459089500485000c041182c1d0b045c0180d0306401c42e500c000e5005640c082c400000d004010351890f015103000e1360100001501d4441c22241c000c14032812a0705940712401060000c1d00c03c03038511450711502c8241d0801076000c28a030030b007080c1c903034030003900020032640041c010301c80c0c201800d41c030542c002d0114625009005010039041c05061051030320482e562045c046114500340100380074083c000f030500e0b0041c5c00d90f15105 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 117135080 1250 117133830 117133837
    0x10519031407020d171009050a020702040b0a0f15140a030b040b0109210602040806040302030d050114090601030905030f0706020712030501050d06020a03140c2d0a030506150f 77
    0x10702240c004000070032180c500116600b00310400390350342c10b0149100780e03103180c000342d4016084903d02c5400280010340c41c20603104040c02074403601d101503500c4506004100a449032408060302c2031100c20810001e82d40e441320510111444064080300388004030f0815680543c074146500069800007480c111003941c903900c03600d026403007107404100003408180115203400c3d441c058407003401000541c0b2000003160a01c0900b095216040c01f501e8103449014141c1400e0742075070118056400858940e440444900400c1e02403c1c01da078161090300322201c001840c1080242002e414555503426100074000c041c021540b40c1075521020035a01d400c06d15081c0000d50042200f550041c00c141d09601c43c0d20301c240034031030481d00010981901203000b030f141c00f402940305140007000c1c150307a0741000c280080c0800f89948100d9014035031540b1040301c0100d59a42c000200001030310310221000c0c000040d00c00388155000500c46d40b0300010300d40c0c0c648011a8480b80104000030f441140070515400c80380015009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 117136330 1250 117135080 117135101
    0x9180c06082512020d15030515010509100b28020304032603012102040903090e060d02211603050106171603020d050c0415080106051e0f01051903 64
    0x41d0100e000c07011070341e4010450380c421003400102407090803903008030f107500503005161604800094120fa03104c4007404c1000d030b035401104e403a080041e142c2c1d1b1030a0006450790040c402034420304880d140c41000a454004103004030001e1281c00b040d060303500304c80710586090082101000c0c90090b504650080c0d40e07600584001c40702d0450f2190700700400c6c5090092010340c20907041402d420b603400c0000764641c90001031802c000c400024007203100583c2e00c0d40180c028050203070701e03070200d240c3c2072460107001031600401c0c240c00b0380211340318000182c4034204090f020b40e004134000803242a50108140c02c08007410b210801452103520003005001c41035000e2800c541c81c5039140c02600c502e0543d000c0e02c41c0c14a011904c0002c3c14098100098180300380c1107030445101c5c03400e598207907090714005070440d0448040801c04500301c120520451800340b0814020349400c4440745881000010404201d5145501c1103026031340d0801c144140e0790255003641d042c10009000740d800745d604024010000c0140200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 117137580 1250 117136330 117136351
    0x3030b030d091707050a03021c0b070801050f010206100e100801110c06010f0e0a020d02090306070201060503010605011b15090b04030c020a0b19030e0304051507060c1809180c0608 79
    0x1400903c810300003808800b252809015040001e00c0c58081011101c81ca1400c1040c0340100140c9030001102d102640c1c0c400c40c0d02d034030303548210750600040c004440c0385901c0d40360548d80003505108600307202e03140d11400c40f400704080324003541e10b40e400e01d610001a031380500740075030801c1314121402ea6084050f013107440924040740d0180e81d881c0c2e051a6842e01c6841b9440d04c40003a200401c840100366002085a02c901c00400f520b45902040424078000301182d005006035550078090256140030f00411004000900e02100084c1c40c541001403074801c001001402c1d4400c110804000a00755006036a55a4020b240c2403081e00c6c041c200a42107003d10300c0d04074414441046d000c11002e4811b01074400301c800c3d00800d02310751600f58200340c1c0208007540303001d11640300a00000869698803021a0041d0a905c4481c54443d00366103001415188071201140902c58481810302c4006001060701040304c00032000030484088490748000308014002e0060300c10741e003004011804a4102d005d0a01603a450103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 117138830 1250 117137580 117137609
    0xd0204140402030705190923090a0203061012060f06081e01031a06010903020307060309050f07051c1104050f0402010f030507020d140c07031b0b040308030c0703030b030d09 76
    0x302008220f100840360748003c100244614611956514400381c0c090f10503051400c0c480d030b2586018503039540540c45042081884180e2040b032801c184d01002d4100701494000e60a5080003800945030b2500500b400b4200034140408031071004090700002c0c02010b0442d0181c0d8400e444020041580c501144c42c581e801e24142203411034204001d04a43c100ca40113880740200012003135101051440c050903141c100b15448a020002d80e03018070916006020070380340000c071440d0304e280050515288118840040d000070104000d030381c031026190064070200700000e000d02c07215440d19107000079420290a802510300300c10080d80c40044644c01e40200e000762a01550000d142804a040d10411100d1030016000f0088800d0210702030312216016040c21480b03141080c110201c014981034041d80306503504244e004006000e12a4060a400508021150340746403074150f49840a840c44064070b143d0880c4400600e407414140710345c1c0207241034100102035404440200f24010000c10b81402031042c1c021480 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 117140080 1250 117138830 117138869
    0xa09060206041e0f0c1e05040501030209040b1f0b1201090213090507020307051902040c020a0507030830070201050a061202060c03070804030308011404111813020d0204 74
    0x81d410702c41c561041407415110084482502862014142120207a2440190500140d04503054401410222481c042c0a0504001a181a1002d54002c60159280100500150301c034203007013640c0103420150b025a251500d00d100549030102140c0a280740e01d15440108840450100505170004000d20920840e40c03608041c20481c17040520714880031070644000c2200c40107d410442c0d0110450040c0c80c1406041e4a95509011480014005040e100c20320a003c52a191203524004102c0b84000d05c642c401d20f0303480a030341d02d210303004c0a49040b82c081a05020840380754080e00c40341c400000c5800303070b40000032514550103c080d0351000140d42030800140540c402e6114000464030340104500c0310007102e4092104c258001d0b81c40c02d410b03000070090a00400d458600500040d1b100381d4910f01d0301d62512104520703622031481c6c140c1c032031801c02c200c0d01c10043c0d03110700341c4070b8011003009040da4489801000444450034085038030022070010030722541e03044003640500b0854121408100c22070185 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 117141330 1250 117140080 117140083
    0x3010618120f031e030207051209030a060905011107241a0904020a0b0318010e0309060d050618150a0503010b0603010e0406020c01050c0702030d0201060501210f0606050a090602 78
    0x5000e000450254000c90201082c84848000c1240d802410500b11450301004110724854089800c2404240c0004a5030304104c003c06c0b06d050011540f00c122814003290000107500e540003036001400094603000d0307602c18000c003980501c1d04c280c4021401c40d0307104854504000040300000d601104400342038452103050510303000d640c140906200782480d44980c850100443d40c0700c00b400c00d9801072144e0b880410300754080e0006500a080c0d445595107c40d80d028412030948003561652603007a0028054a031031034136070b4001d42d10103640300c15010035150b407164042020041d002c960f550011710608140300d61506c000c49505c01c00034066034600c0c4969111002d1500366012058155004601000100403100c2c0103481150000e2286102616048284032400c0c06d5440907900344035034000024008046150070403c105411000f40001c0c4007082c03410740082c103c402c403181094140f0502d03c0c5100a52090f541c443c051417500100c0800c0f94949400c1c004065410001820020440012003c5a000d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 117142580 1250 117141330 117141377
    0x60902030f0610050103020a03060812041e0509041103011b08010501170108060117070306020c03090a05040b030c150d050f0103020a08061b1312051006050a080c0607080c070b030106 80
    0x14445600c22143d07140400443c000c0d8001c4689400305941c451000c0f601074400e0250b41c486840b0802d11645550402d40000b10f5038400c50743d40301c04100300810800c00790300d0300300310607621a400049030254900990007190251900d84d0030740210507208140c0b00050340e0403143c1d03e4180d4100380e071a02e002c0ba50003101517103524400e00500556500c114010821280c2d0040e0840200d0030041c1a40c10455030303650313900166002892628099040407403a0901810310205a01c010142164140595001003021940301c0c10320303000690184c8e41918180754450480302c1121040160480100180e14005001204154007800101e03c01e00d403200c00040d40c0d20780068440d018640c00c00171170000948640b100e2045a0150705c0842c24002c050800285c4d1108469412089500510150440c410794032800000c450864101a1140805403810302c0f20044c00501f18a40c1901a00c506940f11401e041138001c034007810b40e81c83c240388105a0b01042094036940658105c07982900c0d18035181440c1868004410b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 117143830 1250 117142580 117142591
    0x2060c0a0c140f18070201231509040f0f05121c060509040803150a1701020c070f060c02010305041a010f060e090112020d021807020a021201061d090712060902030f06 73
    0x5880013040c140c00c0c0d0007100000c3d041007440c000019122020541c800321700c0181c031403055100070000200000d503466142c05803100c078021034101d802813500303a890003481c0c0280c103400b4201040803a0407004012041241c0c0d0809800143c2044e10346900345040d403030100c1d1101d41c02610600703086000500342404103005014070352000845007581e81d55402e10031a0001103a0540e031041e0072400002c2c160300c40c100ea01c2125900c007000943e07100c00003400c0d6460580d0940c886000002d8481e01000b41c3c5a01039258550680d0911b4003040a0303c40d8200b260b4002c4c10300c075210280313440203800010076a980110002c01c442e0a500c3d40c0b0803c4d4014400c200c004103007489203080b41c0c9556684070005161405110325858801001002286280d5080915a450403104180560f0002c0403110070b610704050328903800304000009000e918205100070340000e80e10a4454400402e19010441c3c240c018401d10001d010700c80e80c803203400460741c00c107140070b400580c2c4264000d0080344614896400d0100380c103480b90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 117145080 1250 117143830 117143839
    0x30e090106050304020d0302031606020a030b010810091508010c1e0903020d02040b010528120e07060e0607170a1115010e060324010e010b0307090302010c02060c0a0c140f 75
    0x141c4e2544c00f0b00405240081d0120110b00041045c02002203030002e5078810540142401030302d8000156000d8215502c0952050500c0380001c10003080c5d64800d601d03031094410461020804c50179044900c062400e45410036a159402d00400302c85c030035030100f2441041c1d040c48403031400d180600752080c0c0302810700b400080d401440d10700201e40541095040301001c158180b401c03a2800da801481994000007114400110f210500c1000080562200404084c410054020001c0c64441d5612554038140d0384140800d02110424001003039845030140c1d15040e4000325a0022201d4804d41d80200b035000c901c103c1c000c40d00303001d48920030000026103c2c4841c00005031655031a42411050004954001d00c503d078140320340c4409880c21750006400c0d40c8144001c1240d00f00c0c0e03504280841c100d600b016003015817290028030402050640c071291035405c4a8080c246600c00156500114405104428450616100c1c1c2c100345410401802504001c1b03c0074801c1c10501d52070f0310020170048110610080790301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 117146330 1250 117145080 117145087
    0x703200d0806010504030b0414100b09010509100806090606150901020a03080402040204080f0f0607050901090b07061d0309180601020a1e020405010e0a0606030c090e180304080a030e09010605 84
    0x2802420800d401400505004d801c0c240d40c0c3d6601c0714204821141100d01d280224a8418454030410844010031402c0c10103104046907031000c02d04141051041d039204101311030200d511101420a03600c054038004003940d18074a403043c2e07003035550342c41a1005401090004003020854102c0421748040c041d0580c06441c0c802f0941c3c030200d400c8080a84140e901c554200800107a41d001005003a51800e2098007811500341c0300100d050801780010310490900800f0460940c0030381c0d02950718015240c12003d003030b458881c1410614000c0540301111811500d16209a10340070100001510101e9001c50310f50b1a6020740b032400b46d8500d5000d603041409a401808841c000a0307156048800f003180c1d4030301d9140c0008661700020103a800a0b88054004280c65040c4004503d09000b40c1000d800f942c201071000002c3c840b0020300c000c10900c2502401030911000c580f82d80d0034101544070120785e5104803030b00c541d1110049600c850785000102c3c0072500307a10314103810b800c00041d0281242c207107465031800c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 117147580 1250 117146330 117146353
    0x7030f09060804350d061805062101020903030406030504020306090d08070e01021207060b191508070e0301060609090c08010f21060515040c0201020c0a02010e041401080102070320 79
    0x1011259040712061007001c00d00948000e441310014000001403040085042840c10032282003c0c5803100d140741441d0304141c208406510f0302035141c3d004007842e8200f06000c48140c07030820300901a104010394036000002d4000b483c20303499000540694002c900fa02e00c0c981310b103440103540785141c4541d5804986e052000031151401181100004030040c0143d40d8840301ea890f04d60b9442c0e0000d001140c22a03601c0700b88001c0d03428041350324105200285c410081d401e0500c4094a00450445003040402c40741e800000c41080c41b440900e51545030190003807080a84821020b00008240c1c01484100c80c60302480c48031030b0b07118a0142d1b040f120480700c2103881c24180b025220341003482144403403800f002d502084c00003507000e00c01d40344203003600140c0e1951410718000308800c2d110f514800e03c007160300500a0404401c40420035006140c0c1c2402c001045508860100d0003400f08074800b0052102d140d80000740281041d001041d8180c0b00c1c0d582c0819a00d1042e01c0c10400c0103428000f0746159200d0303040e050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 117148830 1250 117147580 117147623
    0x3090a1103060405061f1703030f0c0403080f030406180c090506101b0201050c0f060910020a270503191104090c03030c061e09020108010e01231507030f09060804 71
    0x81d012021600c5112180b47c0f64800032013400380d03032806003d080e480002040506020945000d412040c8003882d18500341c9591221029801061a54240130100001081c00c10009900a00140807102c86941c0329074854140075050350454820b03400c10908103400205646080004144001c020b900c0d805084245110415000040100c0072030600a041041c40b040c000100841e800c008254401003a461408039052801d110742019920100d6005001b0850b035940c000b15003003802621710000300c10344014080c8128910030290321583d05402201c0c12800c501d058604000b11150007442000e0040c03040806000494040603c09052080440d40c10300000384502081c1c4242c0e03000b4400440c10700ba0032031009000c1c4a54212100109035100d45031811540c108131010b006241c420003c181e0b40d80340401d18500b0ba408a0300c00035020184484401d180c2e1349203109590305000145004c0d0b01d81e4141c4c5005026003440d41c0d41c03100401c5004400045103407080341910710448e40302894400190403a007600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 117150080 1250 117148830 117148861
    0x90307060503150913110a06050f0a02012022030215130f0f08060718090f06080102030a06080f030403050d050a020c13150503031303020d021503090a110306040506 72
    0x1030015124a82c0490740c4d16902d003140a00403041401755031101d18a001c0b1805408040c40c00d00a4071250b50401c202c64010f015a0083c140001c0030a58410210346c00300e0041c8a07070780d01401c0e176a4203030720100180d442c01c03809403a001070f40040580812404a0b01e0500c5030301a80704c003c1d803002c180100c2080c4101c540c4064200218820f5404401d640c4880d000c130301000d01c0380c210000c0d154215a0805c10f00600b00880d540102103800c0c003500b01040c1e5519000f1180703507800b4440600d0b4552414503000827841d030090004202c580021034990414070107940141c50548211511881007402070035454502208886c11030764098001d01e0312500d0460280c23400d0b04101c0300308041d8014194030090030f860710060420601d48200c40003034a010903a80c8640302608581140340658400c0c40083c000384484000701080e40e404462000540000340300095841e01c01d00c140040141000c41802008000000c4200e0111301c43d1140325552426a4141a0740b440b044402902651141d00400c3d1407141e80079a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 117151330 1250 117150080 117150091
    0x6080102040f060507080708040e07030b041803080903070605010905150303040609050f0f030f1e0f120d020903070609081902011b0507210c05030d050409050907030c09051b090307060503 82
    0x505040c0701d85606d51400d81c1d041942b012843e100350004120820b07516218a440c84241140c2c20001c1851000075100d5280c50001c004051000c0080410702411040099804281c2d01440c28001581c40c0e580180c05040141e40c0a0403c09110101c010245404000e4406070350903983d802040074a444100400c407400b0308411904080303401c0c21820076480c00d02c21079000301500d4004104440201040c085481a6001038280c0d541014000c100451000710760b04e2203694032081d501d5100c0301c00e101054000d01c104110141d2501c07504000240448d08440c0c00d800300ea4600d4140c4500b2030041502c9141c008941d80c000303001418482d07200034180c490318201084140280119902184c0f02e41c8501c0c0401c54950740d100c4402c0104100a080001080414002e4802940a001161005400500a4000c43c0500e001842d10740300050b030a100204012001940c011101055940c1c0d030b0348081e00181b1742651901c001283c55000903d10207260801c5a9220601a004042440c134042045800d0b8101514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 117152580 1250 117151330 117151343
    0x110312060604030807060203180c01020d140405030d0f110c010509060a030b03030f09130b060a0c06091514100b0405150904020c010203070912021f0e1201060906080102040f060507 79
    0x400f2000c280100003403c856440fa1b03200690340d04148107444d2180022080700d00d0181d20207000160b450761f000c81d12000c5003446060014800655524000140c0075a03003180c1d425200301031209142c240e110b81a00720304a0148c035007610039200c0b001020f4030303440c40d00052400701d4400c003c0e4003e00d0034880300030f0040c0c420b94030780021407100d00f40000b400c40c2d0014110fa02c0c82d42002c168007817185000806292800508082000110120760115015024090555060011f0090400103000068002d810201e500c40c0c0042d05032a1244c065500800700300c80b4042a00840360001810907031240845000d9a0b04882c1e80c40c02d103860401000059038801c1c0075202d4441c0f00b4014105551030b140081c100b0801101d002603200e10744104000c1640640e0303809a445e10303045078100c2001d03071503407090036900c200c03540024840d034400c410003078555007800007c0d141c002850903032402c0104c3c7c1c198052001e48003854000e1060642c3c550f2030b64241c0c002c0d40100c282d5001c10002c1040b519001300010015180f007070a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 117153830 1250 117152580 117152587
    0x11010203071a15040911123d0b1f0504240f020a0b010317070b07020a020901050f0102030409020c0f0703061e1a210f01090507061103120606 62
    0x541ea0302c580d03035100c001091400c282205206003406106901d081420f020350b41000021156292a40c4080051035000c0c09080f06441080003110b041c040c855000340b13210751124211a01103003544007400c3c2d00c014102102110748805011410600441012110003841840000c158201c1201c25603070244d69a000d01004020000d600d13a01d15016499000c10b481610341e4805099401034454045851004210742240d4007540010740301031112415030b9084144040810100c0555002d584902c480181c001e42c000b8042200c0c803035000500c0b00c02d03184295228400c990341c41042c041496814038056026070006d000074042d90140d507000d41540f006140455980d15014a4079034184440741e08160340c010744a0300d20b0340812403000343c1c10480842c455410031200702c240110442e10207150721303524072603014a071050038aa6030301316540c1152000d0100b600c7d40c107140c3d81c06260003005444ea0889503070142040c0000c0c014001c41034103041606000c00b40d80780c141207c05211245d0390007045150b00800c00d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 117155080 1250 117153830 117153833
    0x601020118080c010c030c09060f02151906050402091005031e01030309061407030906030e010b060408010c1707090302090408070f0803010611012a0311070501090b0a05070207031101020307 83
    0x410008851405804010f0342e40300b160200d2802e4941e400c2c03440d003c0c141011140f04000b5030280c410011030f403251a00019a1002c15800c034140744580702040180c44102c420301440f1000c200c184d4241c240400000c000d41d0303550700300348400d0340174400000c2e03070262120440c52980c501031030040d5485214490402c580300071b03074240c0740c180486c2031700305600007a00000140419504820324071941c81260701c5c00d504003040390b40d00070805441d80c0140c2d030403da111170b40ca014510094019001007080180a69161078a82805c46e0081c080131503a00009940600e107242078503103460707500d40207510030341c2da000a403401c0d90280010420040d0044400503002c02403100842c0c42031844c4102c2078131580308190b8a5140081c0101500d440842060311a4588542007400040319000c0c1040000302034024145280c00b61030a4000300740c540c5a500f0701d8800040e82c1010458194003c0b40b99078070402a402d40780d1240804d80045035011500da10160344400000e00100e121444860800d040520413a441c02005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 117156330 1250 117155080 117155111
    0x9030a0b04210306120204021810110c010306050f0402070507080a030f030b01050306030a030e030109061401030c06050315130b120a1104110301050411071239060506010201 76
    0x2107800740c42d00001011100e52102902611200002292405010a03410940c1460140c0003082c0c0081c42107500040d84114082c071816038516600c0010500c0d40d451344103020180c40c0546a1105820074001c002806071250301038440d80c2c081d6040500741500721501401800000d42c03003218240c400c2d200c1c4840024001c0420805030f40514480d607074018000724204009026100c003e581a414404148200640c680b000100216015010704e443c200803d01900481e0042c1898140a0031003800c242501410060449070303141200e1061503142202565048221030502040c2c1c2c102e40c03100c00f0740840a55910f02040d2544180c03140d000005030344070b118000a5107055420040c603400d5001150f5560a00207140e841140c001d0058406020032444416126200d1105000b0240f081d03a41d075120501c0288202d003036070200c580c40150103c04481c1d611004d090347c400500740b09600c00010004c10098401d000000100c00c0706903081030b118282c0d84e541c2e0805803000524050466680c0c2440c646142d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 117157580 1250 117156330 117156353
    0x12091a0103210516140a0c05030606091e1519140604030c030f020a09090b181f1104080105090f0601120f02040b0d170c01050a0b01020606010c050a061103070216030206030c09030a 79
    0x451030b250b4201a01d011f0504ac10400c1c010701403403040d2400d804000d08150100c04504404201a00320400c564036800303008002c9601030702e08c1c0d4200b9a94241c0000030000f0f2100402992030b0700350320070180c03001c40e000c01c001131040f0700000f40310100ca076004200080c40e4030034071001d5901c0207140c82206900e079455602201c822040540d1030100e160240305516007584902c603509400040980481c05442e00724402e40ea907052083c1144035900c0080a400051700be00b62005031003100d00070320007030514450740d40e0f131045441903180782802428000104694115244c20015a000c052a0203c0d01550204002003400b421501e8000042540400000b80e100e0525004210003400081c1c41b2031039451071f542101c50060280c101c40749441c504020b56a0001507a40d84040240b8241500c000603180a82c03e0003000500142401e0900825030303071426100707024600c43c0e03e1a42c01c907000c07004032000d201c003040c05a1102940000c001c002060014401c0402480d81500140882c0c28454003941c83e40301001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 117158830 1250 117157580 117157583
    0x50d0c08011a1002121e040b0703020a02010212040f0b09010315030510270b1b030a050103030e0613050f28030201090b070c0612091a0103210516140a 66
    0x300c0e6124011294a0040720080c1901c3d4548010b0883c50411503031300030b9600c0351442000c00550701028400c02d4480c62011600a064107a1103940c552025140c061f680310010481240903000e40000e01101d201400d090740c0866a10034001c0d4851841e191400807181e000d8004a410540c0755505d403c105190240800000c6100e40d006110690b010380300d2100b11800b171600c4000c10451038031a0100c1e62600350b0031110b19074010081d80c0ba42e8544116462408030806408050b030003010080000ca02c81030fa11460490340039803280300c41300210f802004818846c68440e0422250f50001c244083c1c24048803030606030f8000b8002207071b00c4882c00c005818510140c0015480b00312596070600c215688008044000c042244d0082c0c01e01311140c0d90f45a101e5501d024920801140541100740c8410301d030010b42035950040c4d01041e02c0d6051090a0441c5a0700340003c1d180c21355000d005c82d4090030081c60070381000095076241c6040c842d07402c041e0703c2c2c0030b007403144251401126002d01100e441401d03c510305045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 117160080 1250 117158830 117158861
    0xb0307111c02070b03060a0e13050c010c020607230109080310090603030207090c14040e0702010e210d0e010e03190c020d0f050a0c09150504060609050d0c0801 70
    0x8411160180c5452950700c80310400d0700301c1410300010140c0019499069a5009070344544a9171a0804185103918944c44000c00038241b4007880140411054a24442c80c025020745600c078903480d0040d1242c45a0100007074000d0400c02c03c16001c641c4074030141d01072400d0b0004415800140c10103a0b4292014910141c40c98003000091106c8405500794000080009080500c503091550710065101c0341075100c0d0080e81030301d44840607601445644060840078042c0d42141e112070711071121030040042200e6550240d86403046a8000000006146081e20506a60301010002e25000c10360240c028548046500b921404910b10300d50081c01103800b00e0701600000c5803507000450821880040e1200a4001e1000c00c43e203030390250b21003100480c16550032000302490b9103100d1610919004001c10701400c440e1250380042210451a0400014000002650106a40c66804210413240a40305420200f0704c1b84504110606081d049002c840b805100002141e0f0703030b42d0866609440000c031130103068 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 117161330 1250 117160080 117160097
    0x109080307050909060a030201090303050a11240609010b041a1306320901050f070b1512010b061b19080a0801270e0703150509071508040f0c0b0307 65
    0x4c0c20721414855000400b115440b0180b850740d000603000400c2d50002400b002000039030407416034000c0084c48030301180041103650102c51600d520101c04405032161172103079662b001054051601e81c10340c07416261a1000217140030710300517a441c02d990300c40500c1800c1201c1805950880384103044800001e00079500d803603051070084207034500010785e0303603614685034002172016180040544041d103640f00001c2c01c0282d80c9681d800c69009007406a59401170004c0d44080801000105000d1106000403090342c2480301c0c804100d9000303081c0c40c8920600758120005114502540c50f48480300161b103400501030b2003190f0740c0007040d454805149601036802200000b020a0510340c4001d205004020a403940044048100b0165002001d05016100303425100e44612521304410721004000791351240340308a006007204040b0020708803c640c0c40d000e07405403074800505240b45411004e502c0c1000da40301c016a54543e03403040103842d8450010b4901c00d041031130100c0e4000401c00150700504035902c0c0c0240e07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 117162580 1250 117161330 117161347
    0xe0402040f0e0f070806010e0a030503030907080111040b03060907030e0d0f0e01091211030f0f010f06090b090103141002031f050a14040e0c040c17010501050301030b0414010908030705 81
    0x48401c040c14110f0038010000400032001e610001a5812900074030301014003100080c00a0f00d5985d003500003070801d0000005111500c2000644003040340e200800034889030845164102203405a4456a1406002000000c8251929601881d44040c643c20002402c64081c0b2140e840d0016210359800402d11919030aa039068000c0c17100b440b031510034603186e072650382081800100c0300120034000b04182410400003006640c24440b84040050410846908450040003140a01800c00081104500c2c01601103142c8442d0300a903241c0c1c1c48050a51640390b407a6545982c19008590300042c001d00030300004241900b403500085019043c9550b40010144003100c4600550b10164001c5218014840b02082041c103015102868401c044900256a841c0400003e06045540c056180c2c010714041c60641c3da203811402200c2c01422846281000303a0701d80c00155040d100078000036080c00002d03000600012403004c500039200c0ca070940042005c100664940c1a2904251144000314601044268 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 117163830 1250 117162580 117162599
    0x10090f05010b040b0d0f0204110a2003030106020712140a0312181509030c0501110703020d0207060206061302070204111b0120091206090109060b030604021e010e0402040f 75
    0x1100d00004903000c0107541e071013400056800740c10038001000c0c0318107140340c0c03000d540c0e80343e01c40e250300480c0d07a420382da5800741d51100803c120032000000c045104551200c944071200001501d05945036a0020400d0301d05180300303001c6000c00050708840c215260380950003800e07801e010000c60248a511908441074162414800340d400c0005501110120b4042c9540401d1010340343c2c4a660440200c002070807880c6060413507503201d002c0c001800700d40c04c002500d40404040c10040090390301a03420345a54480c0c20342c0c02c0340c07120028440e40307006034450808034805141000700960107407030100d001881c0100766408036040d40c02484034035400c03041c00304071400c44a80165000b035280c0e43c584000c03c41052400c0b0024194111040c45035407848000c00c2215407603d80e8a5588022003220040703494070300d08200e0041c040e0501c0e040843e450307410710340e02104178103000890a00565006010026101c11020710301115030320244a0b03410003c0b850b1085900d82c80b24402003028040500441076100d0400c0d5946 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 117165080 1250 117163830 117163841
    0x20706050123010e040209130203100504052a0307050408160302010f0203040605070f0c050901030f020102010c0f1b0c050d08070c0b040e0c0c0a060e0c0102061005030706080910090f0501 82
    0x650800201002c1442d0301c0e070b40040b9014809a040718016191041000401c1d842015140034594840c40007040c03161400000780c140c0704072901240c00b13100541c2d40040b0382042d500c03c81483c50545104540302c145040386074025503841005132610500b03242c1d0341c0b0819031500c1c000102800c1e211030354590600030755911000304c2c0da42e501180001c41c5410300c2d10303000030400d01c81e848001d0440c0001003420420407803d01400310041400070100300065842c1c1c100541c140c540e02c8022400741d86420303491541103016022100e0281a6a00c0340040c1c000044030381405000c00400499070b211701075602042c203aa800703008000150103032242c81e40b0707030b0b034540790180340022190840481030314180420000700c19981c41c9990710260a550403920f0b184c403c41c000740b42c55820b44008041d0782c1001c201864500c40000c03100c803012400d03070885d40c8039100e0000409031007000340509605600700c00c00a202c410300440801c2d800030328280c111004205001320760411202800000ca580405400403034060103000d0184 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 117166330 1250 117165080 117165119
    0xa0b0f0d0b070e030304081b0d02190f0806010f030b06180c0c010f05060d0215040f060e03060a0c050f07020109051f09080d090303030b03031309060501030c0806030d1107090207060501 81
    0x5c515040c100744005589804100e8044c526489059050300b85031a070500c1da000c2640c0c040e06407042039582c60002981091540100807035a01c0e107013400100140e0016105c0e0481e80204074180c020390a540382c103140300800038182500032454900f003094411241d4001d6100f40e00c038240d207584401205552509682e011019200c1050800040c0a00d40c0c0d0748550440340198102c2e9030340f084a019403c000d8050003a0b50210540c0404420001282d0b504060b59509600e0f048050f506540d031036404403401c0706c20010500002400600a80704001d10000081420600504120424aa075a40052004c030403039101c0c80c040791505420740c044030f0741004040c0c01600310315011340680304881000038805056403001804154a5070300d078080f592420710407901094a4240c80c1e0844036281c9140c00e01500b4a8800c00d8002460003020907203c9114121050240740e0040c054084021403076412129613881c68078000700c9000300080090001228402000703524452200419558540009d0001440700c8444 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 117167580 1250 117166330 117166333
    0x11b020a050601050d05070308040602060a180507051e0a1401020d0801080c0d0317070c03020d02030708070f06110c0f011b121122080d030905060a0b0f0d0b070e03 72
    0x461000007900032802a05651003618004002805802d026140034000d90000c2c3c040c40000401207072259020a9141c86664100e01c103021010000340d0500994904841c00b41c5250401d1600788881c0c500401c00700f03150600d011080c00d00e481d44c003000030303100316140d8420f2903100c06c12807903910710b5601803001c0303041c021041c03c107a81250315280466888a445045044c41040b1040821003051700403d01c0d81342c014004110f080e00f51030080c0002c0d1903491000c405070054400c10611841580c4000112100d40340e004807940d042c044c280c0c0c1c40b0500c1048a80302240c0c101e03150700c0d0303031036204040c072000d040b103d0034a000500305051340d40030003421219800c503901906d01141340e1004486070000c01c11841040702440003e101201e04140b195180a901e00710300c55140b8248150a407071400b44401e40039503c40c3e01c2503c1e00c1c101c6450055048406e1607100400c41d4100300000f896070030325a400601c0c9444040d1403410400c0c0c0c840b00080b404410141c045a8020100091090032607001201400f903060540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 117168830 1250 117167580 117167593
    0x611030402030d0806130603030824101101180803040b010f0608130203071503090302070b0a09030b2206021206030c0a091a0402030703020406020f1501060e011808011b02 75
    0x4001c00d40f0b4100f07900d031450500c001140440c805450322802c0503004034400e00200440ba441c1d00d0020203403401a104211b11583e9100d484581010178a10f1010131000109101c007201e229100c140c444480e41041038280d13542e1401107004a10400040004480c440ea41c51552468549407041c80000c044c3c100192000f40c01c4410701c280c0d50414202c540041d82d000340491409c580d840024a0b2101c1e54002640440d07000c202d0715030f13403070f01600000100c510035001d8a00c01d03510340007100420f000310300c0614002204c020081000c11112400543c000c2c10001d61310726200703000003180b000100c1040c02252200e40c0041c94110300b4070104002d64100d030044010b491040c0c4d070140003a100c0c2e14107020303c03034040d640d0b40e01007003070440c80e41341186100801810a54a074036001c032002c0c009400501c10200580111802c10901c200c0105442c2c0e016540c81400c0003650f404d020f0120b80c824a1240014107004100140c5100a00c0010b40c820050141e6030000c106c14014042c44800b01480c081824103640c00138 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 117170080 1250 117168830 117168833
    0x20708060c0306040e0a051f0c0e030703020d0c0906060203070c0509040b0406110403170405010e0105070c060f0e130615030b0603010b0307020c0d0b0708010e1501140d11030406110304 81
    0x140202e9402c0710003140d001c10304094690066007041a40800203103103204403070240c5400c02d4540c51000410900e002e080000078a0b4440c1506c04000d13036885140d00d50080710080c0014500084a10080e501450b6002121501c5210400442c3d8003034200e00003607030001c289001040120291600036080c19113180c6c946061030756a2a4960201900013080c1e00d8403242c0ca9229001d540040d41c00035500f203403902c16501645c4050050541c028020940011200c040100181d4016000c0703d1019600c005604882482c2040455008800c000b414081000d21008040141c2d1500303a8441911018040001c5003890501542c0400388406c4e020002d00d400c000342e11089680d040240d03411038090030140d40c0c0e680ea6044089051442940c0a1640541030813000c0c0c0c2400f24031146140b00d0301040d1925031080c3d0b00c07030301000c1044008940e0703511141071440030b4170400e5228080c07545e0422110300b11281400c001c403c003c02612101c540708070424101004000a001142c01031110120503440040c1c80c50409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 117171330 1250 117170080 117170101
    0x1801090c090e0a0e1609020403021003050f0a02031b0d1a0109060212030a0204050910090c030b2d0303040602100b19051504050d0303051807050a06180b0f03060102070806 75
    0x70703c500410790fa2803001e422010300c1031005c6001028807090560296031509800700003034110b40420703801501d146d9a680245030091290038000e2078001810388465540c41080006540002d14101c0800c2031440c0142807621008050011500325240200d0b58644200b180c00208400b0301810341000701e030480030400c890b004510070708886400c80d40d1341d960780e82c0c1e91419030207845194401c84d0824648010094040f1040e81340c0c4066684003030046c05003040e50902103013510b01a0241a5210103103c0048000c1c0c0d1001801030380380c44500c00d41483e6103a02200103415508240d00503c0541c000c0c83c2299580d0000b4030851074000e0080b0740c24504400380302450100000d15008460194002e178005681041c02c0c681a14001e040044c0000f00304003a500d030007005000e041e610003207612140b21110010420200782ca4003950000790210507100d15200c1c0031150141c108074030100349000f5a2000c28082c44400083c4100c410300b4190300d40d86c0c01c245000900c4c1c01d0003540701905580002c81800b410804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 117172580 1250 117171330 117171359
    0x21005070f03090827100504031110260916030f0b0c27130513061a03030429030106080703051503010903030b120d020a0b0405010204051801090c09 65
    0x6852a001411580a04d0f19192500c107200c00800000c0350100ca084815101034401d50341d17503000342c44d001580c4403090410f645a010b10b00004155200500303038507003542095102d0020521061500c54013034954002410001d440c10080958030100388020083c0326001009840700f581008000fa141c81851a1a1081e0f4011440340003000c0102c00c034041038500007400c00355100d081c2090705005070800030b103400c0070842c4844100c1601400c800480c000c1300350401d11809204105002400a00c241c03d40e840c407008001040100398841c0c03448511a85545081028001800c50080150450400080c28854624803c041420445001c000521005500c0303403080c0c1d082081400e0100e065140c1c600e02d000c800c203004100642541c0b80449910034590300d904600d0a1020030b81c3ca500d01480b003a01319a446944143d589270159010000c04d000107618912680e40c418020030005041a445100041e2001d100c40340e0034107004001c00061245001e0b6200302020700843c6d00300342c0c0c140c42c41c010380f086d11080c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 117173830 1250 117172580 117172607
    0x905070306090c0c020916140a0504030b010905040807060b010201110c0304050a0503010203070c0f050307150f050702011104060e060c0a050304030b090303040b0402060a180f0801060512280503040e060102100507 93
    0x200203030031987c81e0500418a40740700c1c0d03030b8001109071140030031b450040140d00603200550b8444100800050102180c0c820070b80902d400c44580c903c0e05009417100c0d4081d0080d40c041d07504541d6500340a140b418038004c064104000c2d40009169114035000c00c00c510803105420540c801c0c3d1040050010103500300c4941c08110303511800030b583c088124202035045005840000e803123410795400d0107500ca642036104840100c0841c0c0200140c0d15605c008900300c1b058000d44982d0000c041005103c03c90248a440d261000b00400c01450b104c8480c5803e82003440c0040c04842540c8003050520811840319041540103500710000c60440c5003d032601c014a00e00a04040d015850000d0036041d030511801080d44002c05600702c508040c4d959207081300041d2110700c24111954a0200003007164503010f801040c8128802004001d15210101113545104070400381e0341d5140d0744041e01100140c814409003000b0304100035072a48501c0c0101c006810044c40503101c4410500e070204020b1045d40040d605030214 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 117175080 1250 117173830 117173851
    0x190606050a261902160c091b050a0e03010f020c01090510150b160c0f18110301090b01050d0e010c030614030a0822030516080d08040204150905070306090c0c0209 71
    0x10f000071221036000b0311a85840c4a83d644c00382400034180010b5901e8102214a000c5c410048401e22844032805600c1c0d40340e820700000e90420422071035034802c04410f00e446a008000080340e4046c003081800300d0b48050800c0741182d44680440e82404418401c40549008180040c00395000d0280403030b9000c1c10601800c4505071001c6660b4882200e00c40120b8482640b004600b00b006454240304d0319040220300c40ea07014207884600313a0f02c44c10418040c0056488002e0401e03400c503401e0540c0200a001ca26162504104041c490003030010018011196504400000000c0802c96850300070183c89240d000850601c100c040c94959680300010700b8400c03641c0010229844000d105842038043d40201059100725a4070300020050100c08108900009605490822210380c1d03002c1903a141c8862075810004134140d9000200942025086400959082c0b513042c00310b0758032101080f00300d03041641c0d4000080d03a140024014100c10744600b1135403082c1c50400c0b0040020715400990344100041090010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 117176330 1250 117175080 117175111
    0x709110a02030d02130e0411090109110415020c03060c03100b090105070f060e010603050f0606030601050d17070803010b030403031406150f04050d1217040f020603190606050a26 78
    0x40a0740e20030100b01030300900c1b800d0003040c201400c102412180d0708c81554400c0918400000f486409803244108501d5010005400d1600d0070075080010146c1c0318910f01507020780d00030003855a8052180700e200c0c141d4440069242d080100048480300c6d0070780c002851075601005001c100341c0c0c0100683e218294021725030040b090051504001806d08040490b0761907007024408404c01c88080385007042c8260740300854165985400c02c05644070002e00c503442d01f2000d82854170005c0352a407042c10040c0c501c60602c05213400c00c00c0c1c0d11003415038000d80c05000386650200038072040503898002c800c160016903c0c0866241084000200d290005101c6081050b1000510268512000c0305540050000400c025010f901600b000c80c10402e890030407000054010035041d0000c00b062212500036500442c698650680541c01e003c030703a900182281c40d21034015030404070090024001c42c0b019101c40e039103554517010740300d00207040707003241c218080703040c04031401044404484e000d51030703074010308802d641c042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 117177580 1250 117176330 117176347
    0x70621050a06030206040f050f06190503070c02030a0308180a0b150d0618030809060705030a0b010203090301110c0f06060d060c050c032212110402031e090709110a02030d02 76
    0xb010654002508200c0106001a19448a0183d40200c4905440031146070194500b002174a01c5607800c24018000520024800b107403046002e181c2c0b203142800c0c02c0c01b24480a80010742380101200045002034040e01c104062100016450400b40640000030b00106509564614164100400102e00d0b0083c80012402c10781d1500780010704690011000c025115002500000340032a1a0301900428441e5000c100329070300c00500300d80f040d010303035842c1400c47e201d580f1420007502c1400c104034110b2200b404041110b550a10074800042c1110702055a12031402079a141051001c0011400f142c10010802c00b40b0f48907880d18825495200c0000240c614480d041525540140203241405110100c1c00c0f404ca042c42e05540b4040c4109040d88510103640c82d042448540d00c403240c0148001300d41c590181d184e0034990003030f40d00308855590051701030400d00d07601c0304194421070309101291302041040041540500c240340b0000388052000307140040703407600a5580e12034054044402c0c0d6000036481d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 117178830 1250 117177580 117177601
    0x3091c0504030b0901050108250b3001091a0a0b03070309050303070306060215010503030a120204090903030b210a20040f02090a0608010609030206030a09050303041407062105 77
    0x38041c40c3d210401ca078483c105030103903e00130542401191020b20412141d100c10b441ca100c5c400c81c520600a501400150405d22802e5054000031a00c81100d495420041c035034155652034004a1301a461400d105c40d07140000801c203841c074020801e00600204042021103442c1c2409040a5402007203005903203864801046000700500d181c00b4003940004810301c52030540c550050002c80b20181d003200c0c20000c19850f10751802c1d100703224242d490f80c010013038001441d004100c403c0e011019420b00500703080d907400640b001d854001c0b81c1140083c0d603401c3d8041c59490082003080150024015846105901548296880d4841c1201811002c15100a501e83c8034850f03030710204041c8042c10600a03501c43d41100710182d000081024420301c8000c401080300e508c5022801d048481a40e150f6200501e10380078400d40394400b030100ca401a858801c10000b0035030400056000c0c0d07115210140006078039401403814180726401000801031150140d003005d6040d820343c107012044480c000262602d6442c103a8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 117180080 1250 117178830 117178837
    0x50604050123070c0602150705040e040c05031b04050a05040309120f05011503120f020705040c0512040309030215030f070f0c021807090f050d1113060806011a03091c05 74
    0x2142c00b240000c0c04404002524451004884864003144c50104076040800c002d604121240000034405100402020340c0e080036149d0040c5c022070220019684860210313080017041c42d441d41144c01d0088030305400381800d01c01e96500c1a00b0305020041800c05640043c01c042e00c5100740b405000002403c0000d018107101c00e031600390343c060020071201c006144420098166072005944c9400400740b100e030b625004400c0c0659604944e070240c03800c50f0600041000030000050200200201400700a032000e91200d0060700542c001c1e100e81d09a00d14500c1040410b50740e62403042000e4009005010343c40701407000c0703150458120b00b810140d280003984200d402c44160300029600100803484441c8568a1001300f50042c045a47d840c2d1034152941c13001024400c1c1486840c1e08118260b91101c04600480c51412185000501c5000c000c0030100d21001510102c1c0c000c3d200541145004020560300741c00114903481c071240006003149029413240e500c03949444155420005150182d00b19140701d032044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 117181330 1250 117180080 117180137
    0x20f01080627040308070201020307082805090303042105030a3b0712030804020405180601080d080a060b030a0e2104080c011106011e0315050601020c06040506040501 73
    0x1405030301071042c0ca07003010307400355410340124040c000422109031041c021030744102000c0d21030f00c0b91500c0703003201078201d840082206407054401c1002060048000e006607401402d81d2401141c41c1e0a083c1010840d0800e00e140004243c2510700e81d4000d42c50f000010b80c0c2e40b21948480001d810f61490000390a100141040114004038503494a805080540b00001c8040789030700813100c10540b03801d40d01c0341c980703404480500418418400200145042d41005500454141107500300f112035a9034076283c80400c0c1c21410603900154200c0208907805075049034021100758007806100d140c010070640c1403201410010020b0746800541000003401c1288890401c8210303840400381000804141e96500b040c01018024081c2c40c107003140795842440868610f0310400094080c6900c1c3c0014001c1c0701080b400804442d101e40c000000109404004054609444400c042403c6c13409100090404180722110707481000b061109004948039a81a103090752028203082a001a000c8000490704114004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 117182580 1250 117181330 117181369
    0x608150a0602011a06160b04020303040801060e09161809020d0b070c11100e2e050301031506081c021501030c03150203090616110a03050301080709020403020f010806 73
    0x140021010b50560107400500090281c2d03100c004440000c0100d18070a0901003d600e200043c80180071428000c515508503200808803807030b141d5254101400c1d40d04d154803036920400032104003c6090010f2004c007c5840007102c40074079031070410b4190201c100e0154501040240d5a0048404540720b11881c10b010503006008940384d8503041900403c4613580700012a40c19411070603000e140d08010104040e401d500b41c0f218980304020074144900d981084a9611840a06280039408151040c210040303000715075807425a4ad60442c04c02901e103585400240c0c42503480e0150810000c0404281c03085034030405103c05000b0010b206c0d040b1f20b00420200580c030b0182002d4000800c10421004100c00c883c440d00304000003600040254040b40030458006259401030301c0005c0790744e495140d005200c4945070500040340300d007608a040c64050200d0f0f00300c000c98000030050040901c200003800080a24290940c5024110b601045040c5107030b089003414803903100701044650b0307901c1e007284016004030175 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 117183830 1250 117182580 117182599
    0x4061b020339010207031109040203030f03010b090901080f150c04050916090b160b0a06090203070905010305060a051e010905120615060712080a0f06120507051009060815 75
    0x2409105500c82c140c0402412520b0340c0b01e5030815500100700705044940048103075481c1c0b031011042c4040610000d004176031500080091101d03041412000d1400f0b03060341c085081c2c03141c60890512040c400180c0151030207a028039048041c1c03c0c80003e0407030151a410b02d0740c3c0708540310150041a64010b54016650101051040180114403000402650342c02503980c1684945e4906c580d00d003500c5038020805151013038185101c0815401403280ba009281040c2c00101183d544051200301d0b00700b50f40440004103041800c205540e8940903040e0044804c96201d0545450200041ca130310402d20794010858034201007070302d02ca03070181080070300820019211807020650080e00680780c1d01e00301c86030b12000d1010180c036145400d0a6055800080c0c0c80f220071084010042029280c009000340340880807034441c0625140c8901e00d01415000b410300890003858078141e85441c2d41000215005140540300c1301705001413123540804030404aa40f141003861080e02d03100406100e0040d405042070304240003c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 117185080 1250 117183830 117183883
    0xa05010b07151d1f050c0a0203041512020a180e19090c0503121b03090a050d06060f1401020601051e1002073c030b0c2808040b090304061b0203 63
    0x4007075400c0c0d0064070b9020045d40d42c032042c0c1e90380103005005040f070040e401403109200e08807200081285500c114100f500c00340b0b44100d05a001c1c0ea010114060004640c6145009525030303c000c4c000150400d60180d1015150041e03281903010100d0310942c00345910f40c02400b00b402900900c44000c1c0c04054182d03410f8169500010019521042c40300e42c80c100c402114600400c0b0100595110038002011400054600380401c07d002c0e123188000e60b101580c0345c0300026000c607981d64840082c21001980807035150f641c800642004c005078070150140a0342e1201c084440108414100c50400c1110502a020b00c4080128a811060340284a0781f0805450700c20700040700d2004c2d81d4865503002501c0310000020705003141000348500c4018040e03100c01021900610110010b0485000744c203d451410448a40b40e00e14a050300200c86000f00c0c41c41b40c140814804404c94503a404036206008524191404500800c3c0700c0742d0980b9003002601900da06011541c09012032101e0a110400e060f81c5180c11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 117186330 1250 117185080 117185113
    0x2040b0a080114011b03030e0a0501240e04061503050d020318010c03020d0311130e0601270e0a0e0d0f1209030905040b0d0f06050a05010b07151d 64
    0x3240d822808580300c2400011241541480354282c1181a034640c500d1403001c4035010300701c2ea003846048051646858181c0b00c1c03039404000c07a008070b60080c1d00102d401e01101c180701180c80c1c0c400000302d580c1e440d800818449440b08441c11130b0060b07400500018510b43c034108480c040c2c000e6404c002c0850041c07810708030903198000b000c0d00c3c20b641105214980c035144400107443c5080c04413070040141c0c11000c8105c1c1c100b400303a440491080c6613032026524000040403410701030481031b000280625040700500445513480f0080d1907148241040031105402c5d0401501100c4549215405440700c10074001044001540c210b0f031090500300c0c08440a041c10350001408010307480b00c00314001042940d581248070300c40d0203801d0015425448200380c86080105002c054040103c80e103070400e00b81c280c1d039000608550903404c10a4007a4100042506054a118095801c1030303101b4044681c09202800111781681003500c181c1c000c1030700011b041d0505070248210b4014114948803540290408a03070706110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 117187580 1250 117186330 117186337
    0x20301090c0902040e060f0d03030e07081204030605060103020304051002070203010b040203012301020607170907050d0c0602071a090d0c050a0b040315020307170705040b031003060e0a1106070204020c0102040b 92
    0x403005e4100c1c035983d0390403003409100890403403401c4d402101218140d0120f402540700b003220300d071080103541d6840d85600d076043c54030340c810140140500e400a0104188100b0f0b00c9450b0f048042440c00354614100f98032010394071035090300f041101a074000b038440b007103540c250b0003200c000d10080c1c81552650b96541480940300200460180602200807052026620128a9520174005900c5240d9030784003a960500c54041e004107141041d00c50407002184c160f0351412400da01921440740140345038201400282800c2081c1d00448a4a411a0010012030050400d44411260955200c040c0914504258047c03d031140d02890704030383c00d40004a143e401d00001131058030b009072180a082c5011036021070403803008503028070000d1490b2180340a013418550840780c02015a180c018207080d02c503803100200354015600f02444100d04c0604004110032030044192080c0c4003000b5028130300a40c0c0b03502e80000101e50102e132040000052500c21075445a05855041e4101c10085480355215201e03d40d0503030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 117188830 1250 117187580 117187589
    0xa0804050301050717011e03050a060605120c152b0507090f0e0a020304141c0f0315090e01090b010b0a09051219022d130605010219020301090c090204 66
    0x1424a40020002c41c003400c105c200303075481e5036440c0207079a29000f4041c1080c0c900004c58082d802c0101070000c08100208040d550700c500035140020420715200400c881104d0003c000c070001c6d08001e80381c98180d9180b0045184801080b540036541d00710000400c01100308000c00c101d001254110182c0407400c040d0b0040b80b05130a19200c83c942c968407950300d100bd041840c4212441030056100040e43d91480d900919041480f0700c0741812031000900341c1c80c0c24042c444034081000310550b5075014005e90300c50785d540750b844140c0c10704000c680c5040c03803421203112480c020205800d031a0605003440000951000e20350030b800003942206540c43e124407038600d60003403025030000350503404041403502d00001518400b0a0150040050050000000c0e00380002400140d07404007001c070080303500320661042180351045680400350f40c40308101c10060301c2401200612021450000d0911060340c0000da21440c1e00095049404440d0303161001030f000d4120140c2c000c04a1003801b41c00100c0745203c0c0c02a01c20344 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 117190080 1250 117188830 117188833
    0x5031c110c0106090c0513050d020409150c0207050409020603060409081608120c040605040e040c05150c010c090812030a02040f060f030b010201020a0906030203180708030a121506140c0a08040503 86
    0x171200300d004a031107010b55002d4030005084400d00f0080c0c0d00e0102c40d81085144060800b10300d507161920b612507014400c0080c042901c3d140c600c90f103041c95040c015980a44012201080703141d2203a0042041ca000003004140260fa07180849010b01c0a000282c03044d080d00c0507104142040c071131401080b590445424001115240404142440100420b89054800c00c0da14a400c00740307070074407604503444060407c1c2e07042d081d00e95010078a901c0314001c541e000350904003011382d18000740c2840340c21503903010102810805054070610007028080b41100151480e8080759880781c6500c04207800078862640160101581d592000500a4100403448148030090b00c003000140c0002c00164241e00c201d407028000a811003806100c00c40c026800340d50058020031400f80c180c016008034610381a01600602100e0788041848041d03079512030b08404080b0004102842901d91054400e06602451f008034400e02040c0350144496052410990790003d2100040300c1c7c1e0071465040601ca5036101e801514040d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 117191330 1250 117190080 117190091
    0x40b04060b131401170d120609020a030e0c09040209161403090c10020708070501050a020c032e06080d0807051201030b060405070305071e03020f1c0c0c05031c110c010609 75
    0x10a8503080944500c4103503e0302406c038040d034103001200c01c1043c030071000076015a00c1b40c0128900906202070080c0013040d0f01c000441c000d1010480389003a05845d90280705039a03500400006864400d001031f0030640120072294030300c405200c00d030350200c0380c000c460007101c6020003003000c080400505060309a03800c2c2d4030040b61038415041280c40d840c1a02800c030007680b107164104a09e520500042c41480141d10603038441c0c40a807400642042e1031240c10032441001d03405602449140d46130000018500ac10003000410b01c0c00210315220b0f442541e4042c00c1c01050000140c4060243c002c0b540c2584c1c0d00b040800300703913071285000c0c01d48003015205140680d186c500004d500500901c1464051400b5866039a509607420300c62079401c0203400c00301000c0503024071075011300c95585800307001c160000d00380650b1048400102d4104a9400712400010071000e26200d1010810200c11210101d400d806a40b2844141a05d6400600174070a000e503501c6000003200c0d942c0340819480300341900c10301c4000740007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 117192580 1250 117191330 117191339
    0xa02040e0f0f09060c03010303200f0705040c0f270807030602220501170714040e06030c09010f030605060409080a020a0501140603030426060103030504090606030501030308040b04060b131401 84
    0xb6101300032182500360080400c0140302080c0960700c1070341003542511003a0f001d43c01c2d070040303070341802e44544120883c0e62003401d040c0114901400340002d809664940007000344c0ba98080209141545042e0400c00c008810341c124401c6080303203922010345042c0c0102d4680507aa4642500254020481c042485424030b10303c50010341b49141c1d402c11600142e55811115064a9802e661600050208414070050624034034800d0081c0c005000144101c1c2c0d000b034100d140003002c4c1800c2ca0220b00c00709100d0001d003c0140300e00e40b810002340040e29002a00021580d64400100f0000d12103403401400e0854007003a459032a0f0342c005060003010344030f20001d2040380c51400c2a088200d00590780da81e0715070018001405080d5002101c03412801d0052452900c0c60a4204154240b60084c0c2050f00041d00000d01408107032214000c00c001040c0790300e001c002c2907256450003803403408050802082d411001e004101480f07902d40000c0c86c44c0d9002400d100c0007210042d0300d00000c04c01c4640e020b500c02c03036030b000008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 117193830 1250 117192580 117192583
    0x207081210120602031806090a0506011205060c031909080301090b0d020f010e031009030c02100206010b07061d0d030605030f010b091305070b0c010603031d0d0b0a02040e0f0f09 78
    0x82119501280c0b03003140380d00d42e65100082d40004144000c2c40d0701175664140c140302c04000c2ca03030184213200d02070060340d025400d009041010513046052000604030b21140000c2d40000c9c5a680450b00030003d035141d4940c1115401d02800503854100000d00f444450410b10906030011412078001c1007042185041d100709111800e4480744001e54810b907a005080d43d15405042a640e50703090080541d45011810035803407003100d00c1658203800203459041e090045040203181002c2440c80ca000178480c542c03501c11590200d05c14560300418071a00c03640084802408400c03c0c4489240500c1641e6012031000e100400910301c61141303621030311402008200d03451040c071500d04d12400240141081e41d45034001c840340029217880444207441801b80010b550303080c070380c0034003482c1d40a403001103021031a40c200200450115802104075059460880b4000e80d504010369614070790183d03850210b90340c0e03100c86800a018541c0300c42c4143c00404100a0004010580d03244140c0c1111034140c1c0c15103a0143c41e6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 117195080 1250 117193830 117193861
    0xc0c020f040f020f0309010b10110c0d020a08030a02011a060a0c0209060303040e0f040b0f0108061801060915170613081806120907080c01090b0d090602070812 70
    0x280d002000c28490040c0d905042e00400d2004482040152404031046400c48075a8130440348580703540d64401c8a1020342ca00f001070303801c40b16076900d000786006c0d107955a441e4030b5051071034065100d50034a094980031901d075042458002c08548090340e8540d580241e01901a01c800200c80c1c0314511034401c80c01452034020180d80e400d60040d940d03031540100c01e50a01840800261500b94988402c0c003000840d2907040441c01e1054401b401c40d09a6828580307040307001400c0180807900d400855000500c40c41900040756a486044e05040080c0b005c002c4461500502c41c5801c8162124101820000705211540d0602d08135005c0c1d1100c20725104500c0c4c4003a80b00e42c815a8500410780a0103240c2c80480d003000040d1401419500b0901c0091800320b001460507800300601c52158000c1300708201e1058070610000c00144440005041d441c0001400286040c805024603041d40341c001c02c1d02c01c9004801d034019001207600542c01c5541d01c419040c030b41c04d1504918401003032042140c00054049001c0c00b5034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 117196330 1250 117195080 117195083
    0xb07090f0b030a02070f030c03090807050607030c060e010608030919050303040b0c120301170d090303020c4507021f0c05070c09021b03030c0306010305040f081c0c0c 73
    0x220036140e0502004041d10380c009000c24030155001d0240380046031965240d101254425244c0d41114095441c000d8601c050344c0d800f00c074a40c3c01c1007400f00480d0715680121030791264980782190101066240c15001031074110300c48801980b0740280400d40801c004000c00903840304960417032007503805504608003100c031406070a4268009000420090031a040501056000e51055910360300f1650f04000054200340d01607805d4240c040160140d074042800030b8003001c1110700c0c158503013a00b90744000e9501d84400d0b4080b402a100040c5880324090750b0443c01e4a0040c10410300c02c181000ba5203000f014140800c800c0c110441d0202c0422412070000a941a603204a00903041c132054950003001c00510750031170001c1c1480001c000c04c3c00041c40c00c28200380a403049050042e11241100c1001502c1c0200104160450340700300306005600d40200c083d00e40c044000d190203c1c480d615841c100542003070f00d003001441ea070750105203420b400c213400c8080010b40000304400c004005042200705c6501060480 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 117197580 1250 117196330 117196349
    0xb061306020d120b0a030f0c080d0909060b310f090b01081006080a05041403070c0812092d0303070506010306180f060c2708060a020702090112051203010806040b0709 73
    0xd0406c001000c086000700c0090142200c030780082c0e030354680e281c205942c0884110000e10030040510403441c3e1803150300090004e1406a0b41080000c03014080b22100107441d80f4030500303030204072002d02c49511180201900701d00e100040c907540c0e243c141c0740250109580c51030214402200003031070781103030b00d02c58000c0358115524484561104144400106005401510110f01003400240c03400400c10040c00d9140c8601d020030513062030903031101c3c1044069056229060420084104180c0d1004e0741c40e0184601c03100d11500b0f54024620441c605c44103000125054000881d02d802840310115080e030499004210a2040000e0700044803211605801c006010303110380348407080400c00a40c080d09010400341041c031070410b01c21744003219034036a9000c09041c002d00100f0070b0001020034081580c004d11030600550401c80f0f50303400268407450501402110301c98100c089001e100d07003000100d4071041c2503100c640d9a035071a0000e482c0c8078a01101d05039580540c14011541c01c0784100c0500044401005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 117198830 1250 117197580 117197599
    0x8030705061303120e0a0204060806090c011101020c072304020403020d080d110c0109030207080c030c09070903020904060615080c0a0f0c02060d0e060c0405130b061306020d120b 78
    0x520102c980d40c1c807000c080c1c04110540d50400304214861142a16080586000301000e060501c1004203a640b6500001d049803c40f00c14040008400246e003e4001d6003400e002d07030071462040d9494024041ca03c3c3d170300307100e12400d0f074000b070008c0314038101100e000c0070919015a00b030403180c28030069100c5c6100080d004403c0080041c0481c0451018042c20310300d5100108140c402400c0050342a0002d40001407030380d48d18001030f000c15030100504c500400030100541200703406800020307256000803583d14000d440710710005414030301c41e1100310051503008190b440710341094280382000380030718040c10300306820400a8595240c014800c040c4202009000140392102d03081c8200c07898404481c41d4410f2000110707100d401603643e80041e00070810394001c00076034108600544c616005000e0b101d9900d00324208814041926407c101418504028001042c100c043da0085034452064402c0900940b07107511011070620707030100b22800720001355554a258a51611403110840340c0d8044255403154040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 117200080 1250 117198830 117198841
    0x1030b0a0902040f090506060f0103060503060601080c0c10020711091005040e03070b04051011071205031012030206010501021e03030609060315010e1e190b040f060e010306060803070506 82
    0x160090300007284042c001081050b1205246400d40c1c880301404c032181e0300654108221401e02c40c0d81486501b509180610441d8070b8403002c2911b46c1e4024111604002ea07150000b180e00e02e0010480d00c0b00242c49046620f8100e003220800001e40292000b11030045c0319580184031440c210110f00c2c01000c40100320724a242c81c000801c0000d19140d0010250303030205004020125268000d01841030b8010400340140002e015114001c5607414601c03c0782e0a07038148254404145114010131502030f03541005960380c0c072410300158441712960300c07484804a09481030301c101a80403030b00034102e41c1c00f83c0844d54202800c0740d040502a01405607a41140e0080c00095802c1c50031041094002d070b8080c080e1034400184920a10031540701343c100040d0090700da01800490f15042c958285200350007802c070092414030442c0440c1e1900060300d50070f821a2a01c03038001d50341d900d1364018100f11807003000400c8200c1d070311280c0d410101e40901c81a10294905000018051404011520110385c004003420065903030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 117201330 1250 117200080 117200101
    0xb040509130c0b0a03060815070c030e030c060d020a0909060501120207080906120f01050108070c030309150203280b06030112030509180402040b01030912050a050d050708090d020601030b 82
    0x90500c1035440a4902c400096048442d4001344003145141d03402141c0703281442e00f81e074a0440c008a00c000783c41d0f005410807030f1880d40011260021645407030f1502202c911580041c1c0b400342c1511403d03a000b113001501d03c0c0101c5441d030052241c103040f42c4900c1941959200d4000c02c440040c8912404114104042900503455500a141f4540b0810ba400d081031810004642c2c2604204000b0b8542c44e0300c0d00c280b01c10100502c1c002d60041000b41781082c00d40c83c2c0701100800c6c40016440041c04d040d2111407900401041c2c10a0040001600304115180d00e040403a20b444843c099409898101407841841c0c5e0b460340300e000d2840c2c00c502c0503107034900e0340c0d18051070b00000071080401601040340c2404503468030340e030740503004a40c41c0381441148402c1c00d080c0100800c840710005564181882d00c0304030070006040b0300c000150011581401c0f0340340d003858101695140303d03503451000c04c14644420040519048011140141c403900c003196403a131050f00c41641c1e150000e000c050215200c0c0c10015001c1010b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 117202580 1250 117201330 117201361
    0xf0911010806060928060306051206010321170f1005010c08030c0309100f020306040f0e06010312030b19060816090e22030e1c08030a050c190e01090b040509 69
    0xb01c04103001980c5c000040500108000380e0840c100083e01c2c1e4800f04514034200715803107800c0b071540002d046654510740d108104106410455040c0d29551188655074601030f01c142c004603a0f5400244d1400d15152550b005401c004991060702c5800301a4041425407181c54507000a950000038075195445d0303100a1001500000d01c0c84115200b1401c3c210002d0880780280c07050600100000358070b1342030250420040d50321140a103010140340c0b803904100d000d80024020304594020359010040700c00940201d0240c102c941c2c62035000042c1c90b5140d4892700b407011001c005c544440e500c171001c6445041924022a400c000020000361628000340000f6003440107a070340068060094400120110042000020101d201a00405c0c00c42c14000d400e4104500d8141c0306144c4419810741c0981d0340d5807004014000501705160700780c1c1d030710000b99800011408031202c00c003000300034204006c01d505004142c0c0c41c0001d5584e00240030302200040654186041d03c0690380c004080e1100703035481d52280d2803850b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 117203830 1250 117202580 117202609
    0xa0503040206160f14060a05040f020915120303100602240c070b09010c080a0e0a03050702060d060b0301081501150c020103110307200304030b0408031302040f09110108060609 77
    0x40011420b400140041080c2000c0b5403103885e8503d43c10803070100071030070410002c02041381e29007080c0400000403145800c81c814103a04a0306400c1c1900c03031b040300042000c00788500c04d400a0001403121038860000020358414400a002031440984545003281c5605680d038018540013507801c985044002c1e603801240d44400d901c40c101c0d0030200705032940034540c40180e4a41c841a59608041880181d002c0034644d8401c004580074031061701ca9094086d91246016009030402c1004102881150380e601c0481d0100c1c840310740c0520007c1d480d5482521b0356442846400c0c0a80f0401c1c1805030344c010706c072116038101e40583e003046000c0202c0c40300c03e07140c03100f6000e4202d04069aa0040c280c141011501540c003515490340c4100201141100c4d1800220041c4200c50082d402800100006075440e41391079440341e0b020491540b00d49800851981c0c6601a003c02540207017801c04c401c507482030395405040120f0094414507210751048005544200782030321550b810407000c000582c407a0901444981c0d041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 117205080 1250 117203830 117203857
    0x18080f120a02121501020d051308100507080703050f060d020d02030709050601090602010213090209010207180c030b0f01080106050f0705010905030306090c0f0703030c09080d031d01020a0503040206 87
    0x310461240c0025110119440290300768085022031001455141d060303072000643c406040c0c0d10303540100203541c50480101d194100680001ca0b0007440c020142e0103c0100f83e507008070f40b00c0343c0c8148000310240c04120b64000000e0f0601000840e661300c64001e4600482d8410181f0036280c03030b0401070001040c0041e500745d0300001c0e1b001c45030340113840400c0108020040c07101d0018480c20301100050045040758402c0d0b04580c014006460305070a00c045603400c445a2110040c1d441c40f045c2c006030305089050b8030510841c80aa0041c1d141c0c0d05031900b14014000700313079400b0060700c40040100403204246c260080d00140300302c0010f02c0b40e01d000b04002c02e101d540d24581b103400c0400982d542c1d0f00f5030750b460f0411a0150004018050b0701d04146024070341003001030030120300700100f0301c9844c0264064076101400300746e200c5001d010341030302501c600005450201d00740e821f41d452032400600500113031100d401d120500c0e05080c1d40051018800d03910494030903603440346035448503020004203410200301c0c003004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 117206330 1250 117205080 117205087
    0xb100603050714070f0c260609031c0b0d0506070f0e1203120a110c030415030c1e20061501030c12090809060406020f010b030a0f060e010b0301020a031401050418080f 73
    0xf01d03151001c0024101f82c403000f600c0e400b240458407003420818090701c11700b0540d0040c081104281090100c402d815002d4a0300001ea806507000050350411650801402c0750190400b44448280c1c0001e000300010101c3d190f5109a541d10401d220001e11020211509600b0a0000700300d001d2005c518260060b052210201d207146d500c90360303030360b0982c814000c1b103039254000102003047c142c0c1c604903540b04c0b8840d410200018040e064014240c0c0d80e10741d907500380310340c0c101600c048000e00070447d100c00c03101d064441002004005001d155078031001d03a0000c040c0c1a406451259940c0f0038011644902d00660b1045868840c032201040500101c26044802c01c0b024003051416454102c0580002d1000764000d095410700b50704e0140c21030303101090480c002d80100c41135001082c032141c6031a0082c1d82c4840c00080002d6a603104600500c02c40c0e05403a41940001000d070281a499084050b2500c4441c000b40304a0340d84104200807210b50030a02c0b4070111a502c40d074004116044084c006001551481074038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 117207580 1250 117206330 117206339
    0x12090d0b13080a0203070204060b0c07060f1e11060a05162f030a090801061202011103070f0b01062706110f03070303090c0605030411040b030a0b100603050714070f0c 73
    0x38180c1101541c3e000507440032408070290f2400340660340050602004040c50144180b00158075881c0718012345042c400c031480162001d80c03007103841e034034004943c8a1002480071403100040c00d050418610403d203100d01c0c0082400c03410640f0915002d081150b04200c104821480c0a03144011801c00ca00c4140180400d08032a14011220a83c3e0b0743c0110790195035034101c590340c041c180c11841d07001503210341c1c5046010310071845644000c822007602424404428802d0380800392451041860081481120010910800038a1609541a85c1079525802007121450000c0e9003501c2030f10000001c01c481d1090200030300b90080c1c1c0207240c2e070549802503620890789040f0316403440d40019000c0b0002662102128281305800380004050517580c81c24030f10b5402d1030386441043e0f56005070141c1c8103554071402402d4580c0d0030402c10720410b03840041e6401c1445d02d10032030314910600e4811000400d00700f00000b204948951034007034031030100c0070030b01e41030817003a454800a07629416001c5800520b6a0070218 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 117208830 1250 117207580 117207593
    0x1030303060905060a06140f0c060f0112050a080f0403060e070e1812030702120414030c04110a080603030c0106060e0406080a02010c080a02010f0908070c0f1208090f060a0c0512090d0b13 82
    0x49d9034000359008140504040402c3c0c0c2c22601c4c140e000e0b1035104860340f079110001c1c0300411101d5106070018661515100141d401c1011031180f944002c14207890311310110751000780403c129003100c60301d00009020760b48111303074240c0f0303101d100d00c030344050303801012303503c194440760501079900641a81b04441615842d6005001e19a11035049006260b03c40c108008a5240800c4440054402510140000300e1401c0d01544070380280d11401045c8140e07800011001d841c10000e0310240001340009200700b681da1080a0800700d00f840000d402541008004256100f0000c0e5444485606a448194225040e105d120031a007003d6085e000715520781d403003801c011840c0e014101c0120b0041d000107961720100e181001e4000c84652200e543c680345100d0410242c035214070700e014000c2c2c05c000b042c1d641e10f20020000b030004802d10010b0340e00007000700e0707210201e560010740340e480ca80c0b00700100c2e110000f80003070900c0300d4000c001302603501644003110040001c1000c17031030980012800d210180720f403001d40d0780c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 117210080 1250 117208830 117208837
    0x1a0c03070c08061008070614071a13060b060c2d06190c080c0405040207060908070b0f0a0b030d1101150902031501050702130c12050c0301030303060905060a06140f 72
    0x400742c03a444074060104030000d01e019080240300120080c42a00d04c1e0440140c00d40c080c80d000e02c034003020080360301824400e820b40b90228400004818002c1460840c44d4950030303c0b583e04059501d2031601d038011100d4140141141e9000d15000e0040c00101c00c41c0c52040060340d0040514100d01100c900e40c030600c00820000340e0300075001001100e030b4502204841c01c3c100c460580000f0200031021007408030455403002101c0c159001540c0c05a910080c504100c07028006403a001820b01400140030404d00c00401c40c003a0041c4011000c01130940c8414480400380c804c9d1941040d899000020b10b0302110317000c0c0c0300c250b4212090b8030011421415040880c10800b401e1f910088209400104002303001055030802040b0036401d00b011406c00b4400d8010840958011401c802c010b03941c1c0c0d8008180601807162240c00c45400e40c001e00031440c201250041c640c00c28401140482e040c00000b155100c102e0140520618010300f60b001d00300e141003c2241c41949001c92100c02e00410400c0b00600c00424004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 117211330 1250 117210080 117210089
    0x2150f0304081c02121b130807031a0103080a0e0f120604030806030a031704170f071e030c110103060b0a03290d0303020c03090a03050f07050a1a0c03070c 68
    0xc0c3c1c507648a24080c040380c00a4040101c1c4044c8100012111545c03038002580e0400f5040441c90004c0300e000000210314403030340d41c02c200400d2044200141a00300024404103680c800d956000c007403e210459003441040070300006140c00b10512580c01c1d4107200f0482000384100c014103619450b8038203c00318501c04240c08120215400140402c0241034122920700c0e00100280e0040440f112540c42c014444105c031008000350705920340120341409503070549007640464682005513240e100f620090800e50008400f1103041203040c0701d404201501d6404a0011605902c44440c03601c0700e40c0c0c0301c080c00900850b4030750526a49a0b0045070419441d4090b000d170f12032940b00000c0403001c079514003d070f02d1040712400310b586031545102e20003921050210b0f1400342e4941005070b112145800a1825030103030a14480d0000c4080b0300000c00c0c0030f000101080d00c104a0700a44a44c0c50b1a207042c064081d50303a0090941d01d1040b4403410000c25018002400c10f902c036032083e2428450190b03628040480207520 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 117212580 1250 117211330 117211343
    0x70203070c080c060d0b0301021b06010f090b0f040b030a200307090c05190c0b1003110306040206040621020706060609080c030a0b041506060f0306050303070203060402150f0304 78
    0x2030200c00c00c2081100c00001e81504801000c000382c248000400b01d200e210f096110359034032229115095182501928290242003012041580a40b2441541c840c400d02c61340c030300d6146510700000e507142d09116081d41e140f80600403011680052080c00050700076100c0e000c4d0188503401111021545080810848485900f6240d1600480904162804040e50400680180740120004182e80c0000403145030410040c9010310540c4110800d495001c043c580c0130b0501d915030302c00c0050600200160000340c901c20001c0c01e44401c15101450750710f0b0700403600250021810002480340300c1c01500c07603051181d54995103075480b60480c0d030b041c42a0380198404841c000c0c1c5030107081c820a6000205140030f02000e80040c041041043d002070313950100181d001c1c4c40c03801a00040340034401c418580e00d40000507e40280200c0c0d03543c0030020306000300b10210b500000d15183d404030b000e18000c400c43d100740e40c0040c01804079850f00c1d000c02c0b07603501c00346d000c001c1000e40400c0800b800800c00e6018501c40c03801910b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 117213830 1250 117212580 117212587
    0xa02030108070501050405090609040c0305010203010303050d1a03061f09020c030a030b0105031504020d0f05040b0403021603050622020d080915030405030a140d060f050a05030d02120d0b09070203 86
    0x1000710700d044001c2c0c0101e410f02009100a02840c2c9030038114a41c0801c00303c1d07100d9802e4495040c0703d12881015000505154000030005c01810340080040406040c1a4010000c1e400d401c01d14800044141407107503803540288000c07441400b0326000380c4440b8580d40100034501e559031404003080780d11040022031180c01c0860140c0d00ca94040c49441100d200a090151651504010120030000d02008040c4100e5000ca0041121500d80d4000c60480310404820011410203007083c094800c4d045401320014401d03040b000450b1600c0c40700d01400c5a510000400c5039407120044491040383c4440c401041c075010395800306c05a40c0356000202c40030f0044064550fa802c1d08000c4c00b15070160600c41d020101410014003001071400802c036030301400c4d02c0c40d084111a00c0d5000e04ca2481c0708805011140300c0c1040300100b20352490741070100c00c881007140d440220035643c100389074403100101c50030300158211000a10980c420240100a0041803100001d840c1e10003100042d10354034141c41070b800503480803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 117215080 1250 117213830 117213839
    0xd0e0c0301060806070807050d18110f0a12020906030c100504090b0306011419091d1911091003060504080d05060a0503101e060303020307031701060e0906010c0b0a020301 75
    0xc2c8141809010400081c140d545000080648006005020340d0b0030480700203030b5160050b105a00000343e0700c806140d801c41070241070602009401000d05c00d41e115004005500405141055070b1004030341e619111064400a507030200000b0500c01015241c140c003465112900c0fa644d43c070000d204800c02c4d40c0710f5544607414061440c0464030740318003050103940014014000c1d40034400124003060f40c121100d00703a403031ba810300d1300c140e07914194030807a101803d10b00d6408900c0072513588a6882a1024125149030303a928a181d0321050300213202508000100c00d04011900b40340d1740b4140d119281921b0b0303080301030752666100304a5900b05c60682e2400d01c0400d903180b10404134020203030400300454a81c0d400c20704290000c3e0301c1d444405059940b440d580c040e003104c1c0286d4000700000000c000501001140e903079003400303526a401120114002140d1713004c540084a030354050281640d48644c3d0303803038813002c00e081480124030020742510b0521400c10040c4001841c40c400680c81510038510140c0c44c1e5141 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 117216330 1250 117215080 117215083
    0xb04061208121605031602101118010206061c03210903080c0717030a06030501090f0c061103030103061d0607030915020717070c0b03040308060a0905091c050d0e0c03 73
    0x3c1c000c0120481c2c400c00c4000b07101d0740841500e40050b41a10105012482000c060b441e04241c8040f12012070b050146041c0b00044a0001d440e0030882c1c004401c05210300c40c0700482c2c03105005c88006612006012403503261107150120000c2c0c041c800c1c02c0828a40d0a900c00f0f80349401c403114000a0350b035884514200c100340e401900c1940000840a0385410150b04d66038240340050381c5118415603400200004042c002e06420040045030088000c100c00640c3e800c000c1c680c4840054181c0d0824480e4100091482c81411aa481482c200018505503404c60740d868000d441100030710f2411140c642d502140c428400e00c28140200c2007078070005592000c1e80b0703140017010504c03000e424246205000ca0030114102d8400303e030814030344281040e83d82d0040d28040c514911250025030440344040b0800c400c02d80c000c01c81a0090704202c9854209550790390800f0161402103441e0540e90300f011503d500c284c004407201e2029444141440e5090a9451000c03c085a14010b14820181c0c40400b419502d800c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 117217580 1250 117216330 117216367
    0x40e0408130f03020d060b04110703020708060f01031e02130f021902010507052a0303071d10050405061813021806030402091303030e03030f090f0604050c040b04061208 74
    0x90b8031000d10300e0ba1031600000d60b072a4041c1e5001e0300700d035100d20412145e50f44542c00b030341c000001c02d041d25407035501c00d05000b0b41d2200503001d20850b9108140101e04070056131a0003d0403a5440303102010510ba2100456801030b01d072a004a070041c10b400e071184c1d21422030380110f5000b034200382e034010303240d4070104100450040700c42e0822040d64546010301c50016806001c03541e6840c20500300d0710666001458a40d10040c071042200c0b0903000100901502650009655000c940c45410301c420b9086500700300607509941d010b410010840401017000141003400140001071018000802051140c40214480e186610240d80c450348d0b001440c803483c0e081c0d400303241c9040c90090b00d400d4110314095001c90035460020780401c014503100007034842014443e0b009038a545c50360f1001c1e03d44900300350a40b008494005d40d4a01140d001782c900128110400090340b5104507041030041a60070b402c2800d110050103017203881a006a21a48042a003089000184502c0d130710440c0c0c03050384d503029080304260705038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 117218830 1250 117217580 117217589
    0x30201050a110906070227090f0c0a060e130c0807030f140126010e07060e0619050f0c0115090b0603010f0e151008070f030c0c060c020102040e040813 66
    0x3407820900c020107a0320041511000f5100340c450513601e000c14000103182040b00942809980b003030306450702d8581041030390b03e070140b42640c0413100080032010b0443c1d1285000000d0316000000a0820040d440c4140070403085810064186220491400c0c0d03e8025a07040245070070101e0384000911561651501c9040700b0b401101c5030401031140c860366882440302c01849000b020380d000184240c01100e510030924495407201008201080002401c603890342014070401e00032400e468003801c400d0810800320f4108075005940c8180d40ca0450106030384981010b00b10300394044082c07220804a000900c1100065850269030300401d40c5030958201c1a181140d072898001c0005000401042c1003000540c0d040d5045d5040000c503640d6400e000c00303021400c1c04403d550004070302504185035500a03160ba400b4176080d03034400b4804016180e080d010b4443d0201c4017000190354400300c03070100c0c1d2680d02541007240c41e0300c005840d2591b00c03900600005000c1d9015202c6c1d020000f01892105106207121000b0b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 117220080 1250 117218830 117218851
    0x30c03020d050703140a02030f12010312050f0306370807090204080d0305040f0206030703090b06041803052206020f0d030506060307050903070302060d0b010801080f03071401060e07030903020105 86
    0x43d1595030024450704d002078001c0b9400d04041015100f00d80240140c0b00c0c0d200000c406076456041945499106980c01c1c4400e0354070380d640c0403070b4605c440d104204072020701c40c0c00794030286981c480c042440810b502d4559820910840e04581c502e94540c0700c0c9100b594858000c088606203420b1080150409280394800040c49104110070018060040340d5049a011a420b00161070ba65509000b800c80074107460080d8004000000c1080b06501684403200c4603010300b40486050b9540c201b03100c11203c8070310914a18456403034040c00001c1c841c000402180c0400c442e40398015114641c2031100d048a13410103c003580002111142c040000c00400c0802281450b090129007082c5020850a200c0a41100d04001d400514108161000c0007038000460b0b01074a00e550b00c80240750084018240c802202c1d000403070b00e000000b9140030010b0720800c03c0030400091850f200580e950700b15000414008103d0f1035407620800510758110314842886444903490109605200349802400c4810041000409 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 117221330 1250 117220080 117220087
    0x14010f050a030308090708010f0203071d03060a18020402030708040510090803071202090a08010203060a1a1603110f030a17091221011202030d0f02032a0a030c03020d05 74
    0xc6644114030802129050b00f49401c0d151500f0300910b0400003250808140d560800080c4101c041d02580154410280780e03850050710030101100c10054420890070302e505503c04030116501407516032080000140410200242c0610380e0301290a07a0022580d070f501050601017000305220091080c0407220380d20020070481c601d0b0356914204180030190441080148101e003500c2d00802c10b60407618000c00013844210200d40c1c0700200c5000c1c0d030045031074900680c070701c01d0001000402050000d40c01e803c50b20040303003000b101001340d048036000040b06404111118504410b203030010f0004c0f4004149800c0915910140d084000d05200c4180491406510401040150031400400c3e00c84075505603108080d41c40c90110f505030884002e81200030550620b10b4000644140440c1d82d901c0d9042c402e03025140c88030340b119000d8400880250b80c84016070801c21200301c10109003a01d41c0002c895a0786400c00d100d0340c4414a0746803032101c4a0887c0810114460802819010000a4801e64480c40d00d54034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 117222580 1250 117221330 117221339
    0x905100602340b0310080d09030f0b06061c02070302010b06030919060e0106080102040314060105060f0903071203020f01050615040b070c08010509070e0c0906030f09070302040e0114010f 82
    0xc0314014070755100180c064524609400305a807200c0d0070010240764440a4807070030010840009401c0600c202012481f4510b8050000b50281c1201c3c01241d40103c5c0350445104562030f40c0402860003020964403103000c0014691440c3c100c40b41e0903074984010340068442c022071034080e017160301800050f0301c544018000c110718134038001410b42e0100c1410300021694451441c1c01c0000c0c00044210b90555400c000e0041003000c0c0550241c822640030713429100120302080c0e80240c07202400e00550360405000c2064400910541c0700500c01080081c08817406903940740a048200040510110300503042000e82400c0380d5024010a038200b801102d28800d650a8203c9242e20b9100d04d11031f41f0400c42002c03a0900520424801c200b00814400c8000c0c4000d07d80142655160079480c0910054034014901180715003040388140c50100303001401d21859501d403900840d901c00c900411422040c0309001c000300050710341c1d00030a88070781e881c440045500e8200c100b00c4654244140c00c20618201031800421 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 117223830 1250 117222580 117222613
    0x1e06030605090601110c0a060f02120403030f0f050c2a030105060105041802040e09030703080c03060f013e010606021506060c070f030503041403010c09060e0a0509010905100602 78
    0x2c3d00f20b4405d0811050425041800794186035032104d03030a60040b0000800651550807641d002d80103807980c0e094a8003210a40c500310114010f5000150000c0c103003403104c05005016200f01141038045050403410041e241c00c03482e01d00058104008804140712140c1003107011a11540030354418100d00030701840c609400000c1c82c90281d48618030240c01c0007240e8810291480e03048501902c0b800311240510319000351860b07900d074014078048002400c2c00c000540621907a5003543d0151400a02124440e140040111450b03d40c10281c0001c642c001d00c80c040501d4a0003007454200308003000c11740700c5540d66500f25400c551140d4003920540d0002103004000300b040f90002640200301f29020f45d29140b80c10b405070b1600303070341d600700d810b03c440e441402000380030340000a8400c88070b4550048022141040c145070984509417220700119100c030f0820b220702801403050340791200000d825100f24039034400000301004401e9009910880d5184141711504419071541c0d009072860740010059290595142d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 117225080 1250 117223830 117223849
    0x1180c1b030305060d08030103080309060612060718210c05030a0c0b2b021306030903120c030e241303051c060e04060507080603070b040306020306060c071e06030605 73
    0x1800c0550300c00000e00030340e549280c0385d030b43c19400076080c0352a0b44c0c40c1d26150020b58416034070715489200b240001502450041551154485940054030040d1100b00003900e440c1352800c400c1c0003410b0909004680d020070000601c40704113107401041c800b1511801d140d0103410b103507000b0300c0c02034014240600120762000d0745801111009044c03e0350303402c51036065038924480104c00301e4141150984040622607650080d040c45640d1000305100142d40e1602542100c0140c04020003040004030041140d0b039099020b070b0480403140c00d012841c0c50a190815003444030680c02d6201000500c1d041540d61a084021640e00840c1444040900e00300c90b180617006001c1c03080025051202418450f40342c09454010b00000e01d80090400d080d424245800c03c0a08000c6a00b07000003584040050300501d40044d0a02c100c41460304803515240c01d42e2601c401a51009003115040601082210b0b400381042058000800900300b000765014a082c0400d03a40c0000ea5002d00304050600205021030750715143e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 117226330 1250 117225080 117225083
    0xc0d05030603160305060a0b100801030803060f0301061701061a070f1e060905010506010e09061c05030403030906080c090f061606110310050d05060a09050304080601180c1b 76
    0x10a0326a0307694800a0301c3c0c00c0010806510f481c1542000004202000515a0190806800502480318510103020600169036501b2000514400040010404020082da000382c0050804845421400080390948000d07502c00c6646207022001e20300c42141c280f150704060601100082c82c2d002280c51201280d0080900c0545031292011140081284100d0350f00f2010f034a80198401042003030174010024408180d06441a500300303400601d940d88034114424482200900200158440c0010300c0a01e02002404007030030921283c941c80492401c0003c3c00c0258400d54a24030000e04000e8024180300340a42042420001844810000d079500359610105013425500c0036111140c0c940314007000c515920003d007007a490184045248895040203502c2110380b54218940b403503036103050081145d210000034056801ca10007240c0404070700d403c1950080e002d1000c82e414240c81d050440c0c14801c007a03111a1144003d8083d20a19000e2030140c4114004281011070b440c2c0304030318150b543c50852840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 117227580 1250 117226330 117226337
    0xe0a02091b1e090f06030402030d0503100b0304050a03030b010206010803032d0907050118050913060b06030702030a020d36090f06050301140105130b04090204020c0a02090604020c0d 80
    0x10390000310110301c0c1a610400098481c40390924140c03003000426901c0284440d0080c000301c0354140301401c200b41168090307503000e40103100800300c0c2041103401d80c1000d1311840080121005c0041e001d40d607400590300550150026210310784080ca000740031079410f690114195004440100015080403060317940c4200076082c1d00700c400c0030514008080c11845e52694130081c0b10b0070188001c41a00207940b0040e5402a02c43c550f49003500c0702d00c00300030455841659030020314400001c1c0601902890002203d200d681701081c070f0889000000d40c19001100c3c0c2070010b030301c0800c1c1c001d12554108640c082565041c10414801e61454041041c0070660b21945207001200e000085070445940c500f060042188010411030340c0c0820f0301c010064240d07403003060b03c00c2d800e0802c0d142200300645a00380c100c80c0010482d06c414403120901201600e0443c6019500a50702d440c510f0150325035000a00780c0e10480405840044005d104010140c074010700600d026510510204071031072000200e100911a4904 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 117228830 1250 117227580 117227611
    0x4060306140405091903090909080706051503120706020412080304060501060306060e04020a111920030c0909100f2a1b05031c0b0a0b0703090b03040f050d11010e0a0209 74
    0x781940c01e07d4442c1c0c00940368034034048610003400702c140043c2092500c944010721441d00c8009015000074600048036501d030b005040102020700d9410010159281b003201c000d82042d030341c0da14054400752a40360a50700a00f0002c20401081140d102c0c440c007600e0a801c0030403115040000041034016151b0295000781d500054258295001e00700100c034070300b05034080360106003800081440080e210501165040c207495881c03a50501070407206610118082d0041050555140400c550014042c002100742c0c080c510301e6842460b001c1c0a100c480104200703020840002c0388504411f50061043c4141041410280000c3c00c2e642c1302080003c500d0350780c41c1600001c0700380d0070b080e404c520554107034100d07901e451568442030300e086401ca03401d81c010483d1092402c5688000403112449440400ac0000d000c1000c20300c0048003003005580c00c20b0103071f400768101000958a0f9850100e58a61142c085408044546e02c2d4180900030008080c03410f002805400d070050f40801e60084000e00100b60361072046 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 117230080 1250 117228830 117228833
    0x140d1a1e0c040b1602040501030318050301182d0501090b1e150402040824010f06091514130e010f180f0e070303030608190305031501020304050303040603061404050919 74
    0x880c0c4d50291103070018400c0240d540c1da890050b00c8002c0c02c0c80000462404020700090030324043c4100004203000503481c1c2c0300c08642d030f600c0b0308485110342e002c010680f00807154414520320040821840621907000007640245074285120312441c0105042000000c40d00b0300003518007403251b8142c108444140390145048a480028040d004a070403807011486050302000203408400441011401c98081c821050b980f42c5042600c21241c078061500400d109240c1005110016100b886810340d0500e40341d4a82076441c40c0f0080c40d43e018801014900022150901500500c0703100d035801083c4200002800615000f40400c081c2d2f406941c00d0322a030b0780c1e8003d280ca050030b81d8101030070302040300c2c6c20345007019144c4ca405001050180255040c80c8240041100e0307503540311106d01c0040e50140c850030300303580d01c00d03004070110713540345440c0781c11400244000950f40d00d08102401c0a040c45850129800e1304103e02e5446401c540c4850920441c00c0c201070145c140b50108901c070601c04800c0350081a66090f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 117231330 1250 117230080 117230107
    0x906080309120c1512060a0b0f031b04080607030c0e01200a020406122f0d02010c060e0c04150311100e030d090305010b0108060a140d1a1e0c040b 64
    0xa441010707130062003242c004400c110300240200304001c0300c3e25001c5406e80380c4800340001040ca034091426a000e0801016181012040145034420044075078001d1464484003420a0303504154806001580201c01f406400c0390140500000d0101c5803400409945201000809801a1403040c510900c400d8001c0102541c0503c203440c07010341c0203481070050503980c1c0180303ca50503c03004203a07041d881c0a2807104240125400c1d03100542d1a084805940c0f08010082249084840030f089042c064107840c0c0c3c6002803d10700a54220815103409032490a0864082c401a500d11b01407070200d8500360101480002c1d550078190071504030546000c492140030606c04e070360301d00103d16150350501c9207a00c07000c8002c0d480720802e0306032032043d0024402d803100c3e94019103c510b01540c400c0c3e44183c1161043c8009070300f4210100c9000c0004240340d80098081d1911810501e80000d03d120003803001e0104a50503940f20703d004404080006244010b1524210340c217042d0040d03004216030060001109030b424545c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 117232580 1250 117231330 117231343
    0x50d020405060406020313060302070c15050903011406100504051305190f0902010e0d0213050606070c0305070f060807050f030c040810060302041503030c0221070807050109090608030912 82
    0x1c06091140e6403916024065940c1d04000450504043c0341a400701e00c0d85d1103030081d92380e241c3e840039100d0803050400c400c40c02c0011940e1484000c00009125036540382d5003d01a03100368400b40445488a82030003828402000c4070500400d0500c2410801008a81c64110320428104090100040d441c0c072502a40c83c10720400b84038681c1c841d810705280e00c92000c80780c0d1242ca0300324400d80300c0440155106060240d801c03400d040c060b40c441c1e030018a0380750a1129030071241e0300c98001490030b032908400341d071988120582d5400696440e401403000b4810500300380003000c0509524280510b10b45000d010061992081e00e09101f501100400401c0c00303111004280c0300900200810f691456030410300c101d005006030f00c4103920441c01d10400101c07107548000d005003681d03003554070741c4082a819000e0104030605192501140303412402d408050b9201809a24050070030200500001c61800b0001096015a9000080450310b8031808103c1c849002044820040c01900d80c0b10245000903c014205103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 117233830 1250 117232580 117232589
    0x6090616020a170f0709060810090201021015050406051503010306090c0302060c0c010e0f0d020d111c03020c01181e090f020406020f0604171b0d050307022b050d0204 73
    0x41c0a90740f00c202c9102c041540d103021400b00b001c803541103a48030039020565000f44500750107070308181781c802c1c10071038a03420582c0244d00600403034200401c840406403c80b00c80078000080246c003000d0a20991403e07004840042404030340b8400c2c0f125242c16088402d10040c40020180d940d22880b8070204544540310400450300103040d00d07103401d03440442a864407184022580081c04141040c02e15140c2284845000803000d400c49a98003100e9082c00000007000806541c04403220018048690f03451051030f0f40c1c48200d088281e00044285006448c140031400c1c1c09050080c401011039007a1111140c0100311909d0200c3d440718000303101e090545882d031641119030414103088034180780d01001e40041088601d103a00f01c0300048a02818aa255403055030300501200071881100d000d1850180a801aa18030700545080304c248131404e64a0040d0240c0e001005c20004010000f001d074040c00b140d41c80c400b091240c1002604c000104600702a800c0101c40140080400c00310448011603040c0c60140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 117235080 1250 117233830 117233849
    0x4060f0c05090909150c0d09080c012c031213050106170d0203030405031e0d140604050901020304030c0b150d0f0b011e060c02040219030e0c06090616020a 68
    0x10140c2000040081e40709505180c01a801c08004c5154600300040707144018503130080c03000e07650300c1c0c100158105038083c41c0910005500e46c500c80021488010040400301143e500026000310030343c4006011079180c00c440c00e0000c0340c440b2240310703280001c411a0710350320300340110011039542c031b0312140500c0303800c6c03000546150320f0400b0101d031700c001c40301907505030b0450386003211038001d190720b0f08907a40c0c8002c440050842d04103006040d1281d8403410700c0b200020324440344a08042d44022204121844a01341c0e606110003841809240d05244c490344d86c01102c000d000703524610f05900d000d80206040c2c00020070aa410030f0005014000c62030500c000c0d42801010568981d44506102248281c81401900c020f002c0400000c2c104030000c44180354000a805200e4107289003c0e010f4030001c814042c203903041502000203a001d080c0714095000c02000b1900c0020340d4106010540340740420051201e40100700c1001250b0855507910143c07401c280c00007130091a041814070128542c021941c0c42820392 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 117236330 1250 117235080 117235091
    0x30109052d0406180b04030206091605040c0203070510020a03050105010f08060d0318091d07030201171e01080f0c101706210d0f02060103080406050c012711060405061204060f 77
    0x40101c40072174680950300940c22074103291600b515a540764040403c61401c244d1700c041c02007010342015007115409005600561f0f0424103070361036190510110f03c08c800c40c001e600140c41c628294151050320f01504080ca072503440d40180e511301404040002d00306a12405a5201c10000c044c800ca110305d015200d99100d035107029684049a8020744101a90400b140e00c2c0c04126802981000031071000310f940580d51a0390000c1310201194081001420400c0032501c040d886104e5464082c4095000300400340c0100541d00703030408402d0805040c0c083c080e219007500b03148403007100d5114202d40d03c02c000c403040034950f07038641e000000d00740100f11200f419a54080f8088051110002c00c8a0851228a88640c1858509a0022a00c803102404010320024051200b441860300c600c000e0201142d0040000801c145164090041a60800d02403610b006000e0382c1c400410001c2c0141c6030b0031441c00c1d2125400e0505260004095004022501c8284151400003c1c140141500b000c0701c901c2c81103808208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 117237580 1250 117236330 117236333
    0x3050d0906020f0a031a090402120a0503121f0305071a0c010c050714060601050d05130219050102010e0102030c03070c0201090915031e050a0206030723030109052d040618 75
    0x305030450354242010900c0d20003603a84084800406286106c0010304c4112030b6a629801c014000c000404960002d2040c3e4101e20001002000180801035500d518a0140d1401e20280c00a0158140081d52a4000b4201c100001900014034200390b640c00b202ca280c00120070009144e05004800843c1031560030540b8500a80b608a0028040d99004411181c0440c0e5500d2240342e44c1c0c442502d0050001c1c0e001c1160300591001c6910183c1c0003c1c13510980c0c0c0740146c05400164083c5e000c14100d04405000c00000c2109603024070411607440b0790700c4025170462620303034010310b0b007400018849401e2101c034051020440e8400d4180d071000d8038002d201006102100d80040000c0c0307106000440f0900d040841c0043d00e80b0208800d00300d01d80d8803000410001c0e03950340c28403110750000b44c05c100502101c880702e01020034208641c000d038080804000354403076141c500c600050741c41c043d111500d44000b544081d10343c0a010703148105801c248a010354020340b15850024014030b0f01d04018224000c00c81140c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 117238830 1250 117237580 117237607
    0x1e08070b0f0106050a020601030206030601030207020d030e040f0b0a0b0903070803030108010903030f060b0702150c0109080d06050f0a09021e1b010b0102060114130b0d15050c0703090303050d090602 87
    0x1405000750401c0d100c0786030789030141030300c0c140708070009a00503074456401000145071440c0116408181803602500300200f40d40450b01c0352154000803004a6000e01001986080034071070b01203120070685090108000c0c00c40031501000301c41c0594a0001000100c07148180c174100700030002402803804a903940e69644032514001c100b02c0ea000c50019042c0030b4184191069405040c040e50f410070301462400c00c09908110700e01194161544c1401d50501100c440f0318802e20824000d6805100c1c401d5540d5050b5070180111181174200501c078031854030380c0710360540302d240c2c055050b517030010710059540a8107011078254a04203000e190041200082d0b16203920242c001e51000c0a85800081c4403180b101d0f001a61114000d00440c420a00c8030702d0020710301e00d4010981c40b01e040b000308000405805040c04903003e420391200984032580314181034140301e2541c2c410964441e030025081d50811030715540c024138900d201c1c400501008008030345503c4a03011035111001c2c1550290003199030303403074071038442 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 117240080 1250 117238830 117238853
    0x5031207020a0b0606070c0506160602040f140303030103030c080715060303050d0c17070e12060705070210080112021314092512080f120906010329041e0807 69
    0x219003c2140501207800380c03c00a0554035003e0f4015074851009080405000140c0c01c20850784e1011000c00528002040c55403001b000a801c0d42c104d60a26182401c074101c0c290403a5a2405000741e00802c01003002c00d6000761443c61641d484803080e81c0e1848035041144000c019512054148e9140500020030950080010030f00940721034414400680c01c44001d0f6448020304c420295040090070000c1c0c205842208000343c0050002c1140340c47d003c0800c00a86000421110000420800220342c0f0035441d1001007a0200246440d003a04558100b510140030992a294003d0142800c0b001c600005001ea4000008080200003c2100da14180f100950380d2005500481800700e44c81c0c0782c0c7c0455058800755a825152400c0e1404941c652994603880306502400324042d61010a20401084032076171940c2601411250340205010350541c10040d040f540030701441074103907007860031400ca41180c840310242e0160f04200c181c3c023a4851412005505844003400620a1a0004a1f80c080004132000e8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 117241330 1250 117240080 117240083
    0x8010507030f090506060f0a08070b07031b0302030a03090c05030303040501050703150f12030e090a0e1c1707050f120a0c0206091c030b06040b090102060c0f0409050405031207020a 79
    0x1408046001e0b2200c000300c0b540c140014045400c07020009170903083c112040c80c01d610024148000035690350322100d0038500385c0d030030400c03aa100c009800c03803e065008070f03088a140701d4141c0b020307640d0946075000784d0b49218640b90303c424551548135000030f200c0c102d540e44009210140941c2d6907440c040c0750550080034121040e102091425001d11b03606140c0340005420381e5038140d24100e10301c0c1484a03142000700b04a40840412a200b2103003804e907100d42001d87d0280301e087c14041f50281404200b1401c191041c1e03102200703081c003440000d042039031103030141d2030a03406403006a016869403d0216040d10400c408120b010000003001607102c02e00940c03191282e0003d01c3c007006412400b150403600d4117000d8031f0988103a4042d03511550000452003580a0b03c0000c0e040c0056440c07015000300c0c6058119030b1001a500d140443e5112165070140141a03101c2011421036150452110415100c1d024900524400a6a03000020100b0104004581a06c64914400000c9160130380000b0358840f0074a40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 117242580 1250 117241330 117241337
    0x4061d0901090f240b0102121b0a031e0f050301030809010e0901180e03031b03090106030507030f03033603170a0c02070e06010906080705070c030c080f0c1e060c0708010507 76
    0x19030700e00f1403162050500988051f406000003008900281c00d41c0e40017502c800d00d140560b02a42c8411040400640c8081d612944600e981d8095044141c41002e91188084090103008001646030b594400100c07415a0740c0f01c4040d07501c6a02082c0101c90f40220050f945800c80d800d00c0000c0368146000003140074009242c44140300c1e0808001500703499010035a4185510b04441403c1d00001d41440d01460384400001c0000070a943d0b00d40700c45142003295802a1070201c207001018051640c540151500704414401d000e00d41d02010180300d241011071580301a2254921021400b058401d0b070080c0e08021405112041c64100681560010308078001c411000d841081070014003c03410000b818407941050310b90030310141c948503003a14000c2c402131807a8100078041107200c1c002a8003d4050700614040e801c4403e00380d08003c0b00e24a054021112081280c2c860320001d002550784000e5514000940c0e904442c01d441b01d00e02044050003101e400c01c080e4054840f020031301400540c000c03841707a641c903135 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 117243830 1250 117242580 117242633
    0xc0b070c151b050c0a0f02060c0105010605070c060c02010c0308091e07050a0e0709030602030c091002011406060708030c0a020c030708010f0c11060601140d020414090604061d0901090f 81
    0xc2c4181c6652189440c280000c3d0002d034136000101d000303200c403040541e00140102d03203001144e03443c01e401c5510981043e00440c101280e4202404884c0c851140076200d035050684410f81550000780401d0000c5a0041c1000701c0000003036014503051206500b0180780040139a03424291141c00307916040c2c1070180d14003403200048001001810049034034020701c415219020040e0440e1030300f4000e940010100402c0311410000c0030b81549541002c0303007000d05954000680c2002810340051038800280025100311011f0041002140320700e81165009244a01c106640c0d0381d1011080c1c0c03c9c4000c03210b44603414040d0b40320029107164107420000c02001c010408100e4205040343c1500d9a034440c280c0d040d11684200e0008200e540541700f005002042140300d54188000d42d800c0c0f4060742e00980044194904101c0740d103c030740c141500300642044080710f00b440b03440e00348820000a1078007a10041c004d5412440401c41042d029440b4048080e04081d00c85050051070816202d0540030b000da0f01e40060405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 117245080 1250 117243830 117243881
    0x424050d0c2003090d060c020a020a030b040c080c030d0507050f0d170108010c0c020d0c05120c0301060902030609060d1103030409140601090b040b210429070c0b070c15 74
    0x10040790100c60000300030b07280e4003c20f52600340c0141500c7c02074006521800d054400903955680c41c40c0011417103910007088070310300361501d0400c0780d940780d01c120110b61048101510a0f500860844243c80082c1782558413800d02e820010f207010248403c0d0072080c0920101c0490342e51384803031403140b008a04034145a5a981e11071605080701c5840700301200094403920014018a4000c000c00500c0380180c94401102d621000022000c015001d041d40da581e01081241c0c0a906081c040e84009000c2289d00318114501040411840b50008141910644078241d2540400c03103075020404144402800b1070761034a454501803001400910320220b601e071128000610250f01c6440520162001100d0050500b0324041014045420064050844505107024450f0001c104541c65100c2c0b13000780c001c260755034a2650880240c0300142c1d98001602614005c001055130000c4001c004c441e0301c075015092641d58004111041c1802c13a00080075142c1e00c402e481c0202083e5000301c1c20080d031008002c001107583e07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 117246330 1250 117245080 117245083
    0x60902030f0c0303030402040c17161803020a120c080d0302280207090b040f02070c0f0b030c03070503060d2f040e060c030601050903100606030b04020424050d0c20 72
    0x2202c18075a419031003040010300505181d041007000c514030307041c02c180e6850b060f810100031031000c07518400c07030005400100e80c1c10341c0e01400f400311008103060320001940c01c54000c85e526400500070211160303000300d5120108902c41209800600b02038041d1840c4d20400c10008000e50311010f80c0102220009685060a40710f03134044003805130640d001044a40d1921200101421845e103105500070362b82c4c1c44200c043c80407400208100b501c507980400c6081d0801c6400c20522201d03070003071151a0401c0c0100840303008107004881e0004030f14201240c40b660313018001691920407203c010204d2180c010300c0302e070350f404072520707610018030404001c803c080c0901c00b40f000311940c00950b48030030b6000300045032000315840015500300d041890064a4440d910012900d4200302200110803641c1e581d00030044a079040c0311300104c2f02c0007202d003546098982030803409244806913900199403880d200b4815854001c104032030420b10030707500c1031024100703010b0b001e00140a4004107100c045c2c1840c400b042200c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 117247580 1250 117246330 117246343
    0x414030106091803121b0801030b0901090c03320d020c09090a030c020d1202060a060f0b0702040f091205090f0301060602071208360a080c0411070c03060902030f 71
    0x2514503014400e01135282241c42c1078140d0154120980d403803106080701c000e600c41d589046060b980b42d04045500d0f51400c2d444000c00104654426450001000300141010351501c0403282c120700c402c075038000c003c16101148071682e070091010404015586142602c0402d042c98040d050fa02540d00e407981c44010302c04892411191582030b608176040b5000001c0c000d5001290090010304152103440082d503822794250740f40f0400074091707804a8100405204036019810107030800c07151480383e1910b00b0381202990300400383c0c000e200c1c0e034481d807401800c541d842d40b2603600543c10081e1a94040c0114001500a0380002115400740d03070958020070003410140070340c0084030380550003000213600d0940347c1c00a0b01050302c4203d800c03c0c01041000000204810301062035031018420100411a4541c4054030705107c0d502070b405011042703000c100f91900441d801003021416078000c6240409010511814401c0f800001c2003600054804800e01160b60f0008000a1082e800c40b510980406d603019a60310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 117248830 1250 117247580 117247601
    0x905010e0a030213090809120303090d051e030c0d090b0a0f02030105060a0e060f03010f06080612100b04060302030111071403030f0103060c090306090f15020f07140c06041403010609 80
    0x21388144c0386041e070700a81d0000c0c601c0390140d04014102440c0380300140305004010220750040c0c3c004024400e0200c0203218070220f190450a015140480002e40c80803c1d00d4400f003011035041000c000104050402c60803a1800f015504080001c03d0b900c0c80c0003013003404141c0e00e0408040c83c00101912403070040c802c5034144c8a00404030740c00c0000904003183d04140890410390040000d214180301e0f40e1040002d035029180d42411044060300b440350040064030028001440344007200305000c41e004010811032040080070001040c0315200b8400b18000e010554030080d0150318044081800c00f00740b401402100788641c90b01ea0755026585034a641d02c0c04180c03003c003180060000104001419030f4480000c0b406281803145809507039841307000c00c4030715094064441d41c003040f10400400c500aa181035400312034081c21420140c81850307a0b217083c028010000e0040c490b440b41304c0b00c112800c00000c034030454000c3c0007a644a4039162803e16514505003264000d600381000070987c004103005044896 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 117250080 1250 117248830 117248839
    0xd1d01140702131508011a0609010f0f14070c081e060114150403080909060405010f0b03090a05031b0d020102120f0604110d0e0f010b01080115050405040203070905010e0a0302 77
    0x9a0320390200a601641c50024105040da9102140130b612207040164000300104400006e2a81d031781100b50340307041a06402e80e44111402c100c030b20f40d0340c5e801c1030215010440b07514011206009695090700d08685003c3d400043c40000f242000811003041001c1c01919565010b80d0b07083c0c40f68048054080c08400c4039840342c0d03002580103102c41005140505241d50b8002d080031070030442d050310718180c0c0d4041e400a441003a40040d03181c255090a00420384c00041c192010002503151040f0070140c0e82d00380c01f82c091291000004075840d00b00c200061004036070090103032a91010000300510f2403d40c1d904159445015000540001c0c60045c070a40e42c0c40340f00c0001c800d0311036542c80b00380c0400c0140200340d642d202d42c4e5800c0ca03968041003440500700da4141c14000048603160f45030350382e2030150302511701e0301941c3c140021942d4590380f040b0304a04580c81d071980085482902c000136250750007150000c0f90058070200401641d20b90060b40c82d000c48000307803900201c01c10024140a95141d0b54080a900b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 117251330 1250 117250080 117250087
    0x91e060c0406080726060f01080903040603020706020721090801050106020c040e1603050102090a2102061c051e09010c0e010e030a0507031a090303091b01110d1d0114 73
    0x664010036401e981310300e1901d01070441510304030019200c00b41d11003c1100c101c9130035042081e241048160010303d44000d00300201c5034a81800216030720f11850007607504050f004500c64080004c02d03010359401035408031444001404100038110800202c03d8682c000500300440010105418441e40c1c1c142d400381d81c080c0640c40701103024000900b02d2620805482c6c451410201e4500111442c00760245205e0b900259455000404101c3c804a442c2c0180210f060303540c1000784070304a42d00c2022281a819508640c5409020710680e058102810740145900e060100304444c8542d2001071104088400f9003c0c4059100ca45049003200c5c1c4664001d008181d02c8451405150f000c3c07440314090410040807a6510111961151b0900e0455031003101c50660141462082d9800611000c0c0d000100b80c1c011340c254078200e540d0960f160f071200700a00c1c92000320801c0600d80d074420407503200071020307860444941d520710910007401c441c0030f042d806a00b080800d0b500d1000b0340c8170f03012854640b50000e264906 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 117252580 1250 117251330 117251339
    0xb06120a0902060d02180406080d0509100509120c09071e0c02040e1504020418080301030f080405101806110307021509030604030c150902090103060e010e06091e060c04 74
    0x109091941a80e0100c030502403000c01d44c20f1400107092110b005d40d0519000710a0406020035074441d82c011508039006980011241030f80881075922110040322440034030804400261a5440f403400780f103030040d2182c070b14003407401400100c0002003030095981040300ea45103002213032041080c500ca846a885844200701000e03104181903035400d0700040c00050144402000c032031424071000102070200001000b0003003986810b1141c014041540c407070b05008060703941c2e0f800d030262005002c02000a001e2400c0355080c02203035000c4e1000f80101500f00c03441101c0a920240a00c0c846901003510380001200c0414428444c203103213194860364200950410714640e00700f08215035034070303902842400c0501c44001d044d54100b02c414020b600a8481c1d030500f220328200140c4150100070130500d15410082840016101c0442160450350031030000902000040905400350000c40d032084614410312060007100c4038046420780d0540b21a0703000d40c10a440304148280c4505045640b66420340c2c05100410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 117253830 1250 117252580 117252601
    0x3040c0f120b090f010e01062603120c0d02310608180a050a0803010608071d040b031c0302090406050a0515070f08040e180118150b09090d030b0612 65
    0x9800103c0303102602d040d00101000705084400100150005130f464640410003c0004450740c1b0034108065a885078060501200995900c55110204a00c0d14594001038034900640c0503101c0d00070059400755070300c8010117407810525a6145c0c8a000e5121111031030a4081c040e254034a00b110260707120f241059841410b07001e01c030b9014100c4101c03030780250443c20b00003860503c00e001e03189110343c007181d80341d5051002c020315106c0d00410b5071060100700071040c0800c0c4e043d00e0780c00c0400d5004440103e817609611f07000c0303420180c4a4001d0202c3c030310386031064502207030580c014004805050f5020014035640e001000000c1c040c40c45515001120f290044d66404000402015101d014001c450045c20040c0e46111a03503107c0d41c498000034408400303000c052540c1c00002050310000390004d0229942054083e0144100e07642c004200c071a0003060500c0c0c55142c1d4000110f00342c001846240949084100c943d121124100007200107460300c0075102842c9041c80075150306c40d11039512307141c547d0380b40c1e581d90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 117255080 1250 117253830 117253853
    0x6010e1e01030b03070f09050907080613022b02100516020d0602120c07060501060c151a032a0303040303080c030c0f0c0120040510080a06030c080303040c0f12 70
    0x120304250326072140b0420703501d040180310001c2a000030803a1b200c030310b40409281242e002800982007034020202c00c11806c800054082c1d004034031324903040920f904910009046103101d03001081c481446909100c803030304e0a041c0b081ca860b4003c0d11070204507a0000000c540920900d0001440303068220080405810f01e00000b148c490701c150710040c03801d8940d1545034843c020803140400b0744000003c01a041050318005d00780180040d040c5940d2542d2103580e45680e00b441c00c0300484850f5568814508200c2141da0180c0d1032a2001e000c0d07440000c0307800e00c0907400540603030109050a215030b0103140d640c1000401c6604072501945c90820686500045c064990700c003070138580001c1c1044c00004c4602d0f100d41c0007840100302d0880001000d0100f040900c036400482220042c07220420701040142c2d450751255103280300d4407440c101c3d0441d0340d40914035000702001e410140002540660103d041c5800100850040d4024030a0f20311050351001cce48440c00c0100d00409481c83d036070301440000110303000c945c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 117256330 1250 117255080 117255139
    0x100e090714040609020408030324130f060302120d1701060905060d0b090f180105040b070302070f0b01080d1b020f01030b040b040e011a03120415020703080c010b0906010e 75
    0x20490030360304e000c1c10301031b0380054105101e95000007050282d409090010104041d80c880c04502c6840490030004094254070010001001d4a558010079100c00c650310240240d5801030450b1826903d0000d030303039a5688201948804603498103003e03020141c01801080c104d503125640c3d041064100418040160810700800c1162a11540c4005c429950351701c1c001c0c441c61541c0b42c6c0308a54078000010ba20350600307011041035180d1501d0305000200d10300001c541c0e400242400c0242e503400351442e00c1903104400039406481fa0002c0c4002007151140802c0d1005203540310340d1100c000404800e0f021a1105858000a5006010104c100550350190300940709256008000040008040000c00c06070f442e24480c010044e5034034a840e50b0146060108030f141480700344c005107120b00050040390964070880c0a90218071412100003255544200595800703541d108407441c1d20741c480b1482d01406003520044581c4a40f111700d0000300903510616018441000003401c800100910303403624882d00100614 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 117257580 1250 117256330 117256339
    0x40809060c010606020606010e04020307020c0922050c012c0103110f0d060812040608040602031008120705061506180303040b07050c0a05010302070b1b21100e090714 73
    0x5040715440081c81542e000f0603168000d00345915100b00010b0070320040d40002d0348142e1043c01031050303155000542d00c1000f4804d90361903485880c0c4000341042408504841c041814201d100c42041200c049403081c0121002c0c3c0302c500004049104500d2500c4c4074184003a1200c0701040000c02c030358420f400a1045c201070181d8146410340300e884070030b4941c2c40b408005840c140c403a03c040002c10410450804200080d0724460b082c2820008000c1c01c2801c090030142c501c036008404160a896510b41e014020030a8004131a85030084003240c24854100520664450040000042d07004072120011451050010710036403500d2029164081a442c0b03032440075815110030720020a03541491401040e41c4c0303010344000c02070710750a1820001c80c0003031500100d04141c01805440006032812415a40006c10350b0200c010b82c480820320f030000341c040d140200c0c2030f0401c0409030060303400c00107401c64044e82c448076000c000ca075101c40320f000703800e075090b1141c00440d40000010450003a4a1070b070300c140182d0051 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 117258830 1250 117257580 117257587
    0x114090a1e061b02060402010809120711040e010203100905010905132306100918020f0607030c060504060204060806030c011b020303040506460f1b03050913050f04080906 75
    0xa41c001e00c0c120700c3d00000242e40050140300c190b68101d0340c029403000f000d500821083d00d100c00c0c1c402e620301950700000c2003010b07600c41c0c081e0716680b00e03040b0005617524940215100d10380038a80d83ca602540d440740e07841755807500d400454024100d018042c8541418440324072400da084d036807003d51b02d080c4101c1d600e241c02c0c1030440000340341c000c0c40030501880081d0203254503142002401d4045a901030404c4507550524160500107803550104a41000c1d811200661121280e040903a44855049002041d0616220802040013883d45c0a003068909a554049003540c0e8101416515100340e14100d0200f80c6042500490070034200301a1070107480035050324109607075400402ca07160023000c04c4090001c507242030540b40c1e5810040840420032000395401c15080900588039000d10201003101c100034240d02c040304080d0203080d0041080c880351054122082d0a820300030304c6070304042e4449100f1001c140440100310f043e4004c45000d41c0e840e007000c1001e0b032901e681c4c100c1560b20107010250080001d2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 117260080 1250 117258830 117258851
    0x1080a140406020901021005060f06071a01090903120209010801090b0f06070503040602010b0603010b0301300f030810030b0a020d0b090109090b0105010c05031b0f0d020114090a1e06 80
    0x4040da280118424040561200b40841c0064100a03004400b4240030386410100300c8a6540c498149100754402d5403c6942e403155400c203410f01d03260400c80c201507400c14000000e02e0138404c2d80310100243c0641c0e078504100c0c1d04c1082c1e03002644107003c111800a03038441c005012040081d4440f020280d001417407106180c0b40f54000c030b02c10b5001600156455000440d08100d400d80a01502a2441e42110802e1656041584a00c058041130042802d40300440c4074588248101c4500c54800c3c0700c090540302a001001c0c40d041851910b0b020044002071880b40c00701e0903400c20001c01c4030660fa03000c0c1c200c800940e251880f030030094101404004c02d107a02c6241c940a16250301810320f0180084240104020601d030501c0300c038860040e0f0005c0c0c100402190b40c80d000c904048203803466150308140e004072568814902c2c1c2d02d046000041020340303020301400d80e414035030150b2145071842001c0760209441e5450341611511000c041c072014205a10340c605210900105452044030513214040001c0d0f24800d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 117261330 1250 117260080 117260111
    0xc030b040606180e040210032f0304050c0103020a0c030e0a0f080f19080a0c0203070b030702150a0207080406200d09050102150420030a17041e08030901080a 69
    0x10ba206601003026103048a00140c400c103190380140600b100d001984c2d05050b40420f000d0400511010101070b07440c04003000c2c00c481e1498036040851384602055071001a04488481641b044c0c8088a191140032142d0740e1a50281c0203550901e001500c402080908944007512008010002168880c29048021030910040c000850251802d88014032940c940041c40300d00c0c082c8205600c104840001c20460001072140b0100c50b0704210904d4203903021060303480400c0c50240250810309024201104000032a0390018210f00078080307200e00030700640c44645005040744074401016142001c100f0040c81440d0240012900110398a0554038025056011860810122204807400580708850400103036a040007004426803213090030702c00c1800c02c2e54507107500846c1c0c602c0307140e0a21008011140d465406000c0709e12240c2e04004801003c074156900420a60700c58041c41480003058440885142850042501a2880980114505410b8034010744410100030880f032100c0751201d00e22800740302d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 117262580 1250 117261330 117261341
    0x3180902120703060f0515070b041115040506070803100b0a050d0b1228050a0605090f0d020304050d0c1203090504050a1e09050f07030515010f050906040c030b04 71
    0x140480040c0c03241c41c00c0e0600c40011001a08040415061404c1030054040342c091a0b4105d40040f2516101c115800c100c58000d8055100c010f002c40c2e0301d107010001849041c6661031944241160840c040100b081c0d1651198000c2e0300805811090030b004181c00184160020340c0c008501e50038840741965101d1160340c440e488a00c84c00b00007400407550a440f10301d54041c0c080c0f92201100ea14084e0641c0300d0f40d0f10b645149929550401d844504680f000c41c88111a022070388a402c041514064100340c202100600405d9a41da201803080298024409101098807141e482559000c0d40c686454882000b203c0a1400b4042d6100410340d400081c80e4501b0f82c40303d2402ca8801d48075640f09528100c01c000c200c42d4001c144444003400d0050340b00c407a08403103941903280302c469940000c0007040f5090182c58011300d00412009882481c5020092000c00181076500c04da0851030b80d41181c0e00c81d90003003a501407510540350044000d002044562919400011281201d40790000c0e0001811000405944 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 117263830 1250 117262580 117262589
    0x806040602180a03030c060f1104030c05180c03280c0e040c020102180d08070f08070611070c06050304060e030313031d01020d0c0503070c0b09011701030b070c0318 72
    0x2a80000d080103100b05001c2c0112000e9011111a00000d20b50344002d00101c0100a00401d026036900b401d220800d2141e00813400c0380480c031005515aa224640341c0309000c03560107241e00c18010f4a0103081c522801198980c81010b00808407415511384c2c14816100740d666003841d09a4440404030700340ea1084a01ca01c0c0d0300207200355070310000729a000c000e11007100e054030580030071640100012f800300a214400003e9000b020344a042044a240c10035904c40e0180d02c4008050f41400300b064004d000e210406020924050282042881c0c801440203e8501c03d02000401e240590b1004200040c020001345501134040c82d8081025142c0d20302c22400c44e801181d1043e1810fa060540d0001d2650191a00c41501e10060fa640312681c1d43c44000307551034200510007810084206862002c1000a006544120f940041c000e082940c80310004006d9800140d401c0380091404d6944001200310802c0150482c1d4201c0b0303407244280c0340c00d081218801d0842c2400e40c203000c082c0c03070203c61400302c039044c2d02c0060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 117265080 1250 117263830 117263843
    0x100b0f090d0b01031a070906050c12120709091b0c14010615020c040905061506070501060602030301030b13030f050310030c030803060a0b0f031f031208061009060c06090309080604 79
    0x10f60544c644102902c100400001c0003078000e000704520300c2d40081c0303c20141e424500308140c4036002495105e01d0a14000d414041036407011801c094620344101940e0f010725501e460b110300ca140c440c4000b1084078045024060015a44554070050381d000e62000740c0d00b20300444000c0b4175054400019800c0d201e85501c03802240264a251240795036060150070700c4410101d506024008030b58481503031310000940940066509240c4c5981c103555604111000c03a0350040080c0680755079150f02a46070b40092005540c9030a9801c0007a03200540c0606184915074162a004103c6103007140c1242c07250402010880c281d0581e50300030000c87c10311009071008501c100c400668a02d4860184044042c059000d112410000e1042c07104540c04407054a5100e1030114120589441d0640030500c2860607500c041c0c140c21003030401d002c03503651000001c2c2c4919015510f19000c5400c650741180d01c0203140c81800700003556042c01d2400504250405020b140c040c1c5000300400783c4803100302e400c010045e0b4003210360 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 117266187 1107 117265080 117265103
    0x50403021302030f1605030411010909020c0309100203090d0305070c09050703020c0c0f0a030807051e0d030b0420030403120f0b01080c03100b0f090d 66
    0x45030020555428800100c054070001c0d070003a10312031011011840000e500b414940d808403a03848403a0b81e0140785a80ba5126150070440c5071030542d0410a03040d17000900b480c12800034100543c9000003944da039900903c204550751940c60300762030a42d003091002001682c3c46251403007240d40c02d400c0099480302d5074a0000d0264030f9542054400301d01c0c0c4001d00000d1940340d400703080c000c03100e03408903810060102c08110500d09400c1d00c156000c1e0740440d0910002e03072014040d00e0780c6481038003294281030010b02c3d20000e00542c541d0841072680544840040603902d8014100034060546d0204010480607030142c0468a92481d900041c40000010904151161210581c0c205a0030f6040203a220050b50183c0501080d110050000d1010808900301c0c00e41d0300201c078042c0c40c0301a5907042c9a86010402000c541011440540c290740c2440701408540352400d921030146d01c5003100500 = true := by decide +kernel

theorem cover : BRFrame.Cov 117086330 117266187 := by
  have h0 := BRFrame.cov_init 117086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 117086330 ≤ n) (h2 : n < 117266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
