-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4386
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:27:12.370166+00:00
-- url     : https://prove2.me/submissions/646e23bf-4f02-4032-9a91-8340b67840ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 788669064 ≤ n < 788848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 788670314 1250 788669064 788669099
    0x307090812040b13030615051c110f01050c0d020601060f050f160303060503070905100b040509010b0306012a03020f0c0a0612090b1e0c1204060507180f 67
    0x195004006001d0000c401401181c080d10b80c407503030180d1507000020603014560030907040140118908030b107203460250108143c0003103c1085402c042501c004610221240e40e0340a0010030301d400a00e200140341c80c09219100403040107240c0f05003050b0032000c406140c054ad2403540c01c0942c01c07010041c00002c2c2e008041d81c40c134102070b007400e1380341c103103076010441480c420000c90008610010328a041010f00c071f0703000341d0010000101100c070700340d440d180030900401059079031860154334000d000614109810944085903030040c00c21038035a18044806090b540300400d0b1504124240b84211507419426401c808918204000c2100e034a545140c041d103070001010f6000400e41c0308030b1243d4110303981e6400c0301003680c8552500e00442900c0b084954003802103c40c006003c0c03d0343d41b04000c54810207081042006200840210440e255840c85c4540c5102d040d441840e207084a00005020480380d8000c1038022040780f0309000e450a480102010303403c19604448100c140700007040202c542201001c015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 788671564 1250 788670314 788670329
    0x14042c0c060a0e0d0c0e0117060919030507030c081201030312151503091a070210020c06070305130506040803070e0f18090316030906030501091a091009020f030709 72
    0x1414011000c05843c030440b528801d44a0380380380024008101081e24448020101c6140c08003941d40c40790034801c481d100c0d401ea0310800d4407d83e0b0024150306800540407002c0b45015000f11001c04103502d04494551000c0c6040d42030145500c4080000380380306004003110351802e4661440d55055103001815a110492514042c5043c01d0b001c0280c8888650180c00715007019180d45040301d03896100380e014000282c0d000d4a0030004101070010030509241507882034005074242c40440c150008280100e0140810862882c0e1101c0c00150103903020f9441950006901c01821144c00800c1e40c84a1400340c00300c4d01141d407148040305104007607400894001c5041e030120341a07008011010701060141c1c1c800d000c1b003c1444d018801141150310306008489100002c0c82d03003025015520705001d070408034203108641c0007915003000051054200e22958604041600c00720110b0316810040182c0c0030030103029003014409510340007030f484140b4802050f040128551a988030318011202500d540c0866004a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 788672814 1250 788671564 788671567
    0x5060105030609180f0a0605011a040b04050d08070b16030513200103021b070e0109051302040b3105010504050c030708151c0606060f020714042c0c06 66
    0x10095444002d0958004d1000c003100b0b5072005288146480c200003220b20089900683c0016010f000503500518103031480b100a03854081006070129130b05118601c02c40000c10f0052006101d10b10345190003207001c0703020b08806030038126552a844110b01e415200003140311050b40d004030100350140038141e44040a000c15004200194551011412405000c55900001c945030121075a00907816140c2c0040c0d604e8804050040b400300c0c0d40d50303400c4c032401201d181041d58000021140300e0790250a00c160080b1400c0c111200d0940c1c01c0c0406092505041ea40c01032540c5001e07002036004242544150b01482e4104050032450406176040b2035040e00003d0046051404224601c0010001c41e904050346140507c056924044819500c17003550030050340c0148920001c00100b0141142c500005000d90310800c0f280e59a06000c1d00c10100c0881170601603005030307a082014501ca4820700074000000fa00220b20b84000751007440962803074081941d07081502100256003c1400c000c07030380c282c510658409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 788674064 1250 788672814 788672821
    0x4020a090303050d020d0c08010617040309140a03080c01020706060e0f040f080d1e0f0c0206010b0703020106120503120a0b010804150e0607031a01090f0605031f03030f030506010503 80
    0x40c903a010324000a0240000000c800708421026412181d0034080b10a0801c0f41c400300d240002c040d02428860140003952164135000140003903401107024680c1a00c81055103443c0c81d01100d510228070748465444a030fa0500000460100401000540c3d1010001070341c4090a1900740101c0c0c123981c120340f0a07140000c003000841e60442d00c0c0c564005030455840326600402d4500350940d0b1040c1c010348818a8200560010000c540504601d8602581b4030180204070000701c2c2c80c022203130100a68030051341308500400182071030031700418401c0e000c0d20012980d10303283c22070300c0e4076a101000100c88907400052480e410901d030075942d503002003403000c007417041c552080002055014003410240003242e0520451141001603800740300350f030a60070290340f031038075001202800401c03d001009012545400001d04203610981240095401520091441901b000c40445540c0c100400b01c0a820b6002029041d01c94a59040d00004500c00c0d42e402c59000c6500303900800395440179100f9410701c2014030a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 788675314 1250 788674064 788674067
    0x15050708090d02060c03040906030c05030105070c06021c1a04060e0f0c0a05071e051908180a180507020c370909060e120c070e100e2404020a 62
    0xc84807a01c0c0100c5240c0da40e4180707400010b6462044c502c01480c3d80c440010005000034458105c6002c490107041031090701c0c0d60f10b006160a84008a0342a0b0000b00700649800010300d041d0701800d100009100550f0340b0f40411906041180e441c4c6c1c04c12101c000d07081840c0b18443c0b910b03000b0309010304180c0200c94841e050000c0c040c2150100a091303090403400c003040d52400d05d0310a00c10781c0d030402e8202c03940c0c0341411042d1800c500503441800007510140112441418011240c00d0303c050380981c0f00300280c1c6014041c260511001007400052680f1900c4400002001c0c0c841250030f1400e90840d80340080d06003402003029140c0083c0d412110700131640040c4109031401e00c0f8080c580c000b400910800e0181a0582c1c070f289803078140d9086645038a18010400d018065642c2c0201107107884241140c0d40040e000180007168010280c0c1e0f1501584981c0702030001400700114580c100401030081c0500d01e842c0d00c1d242d2500c10048686040c440307200c500508030115040040303d02c903c000d0b03800310315001d140d290 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 788676564 1250 788675314 788675317
    0x109030201020d2706180902031605071a010e07110105070507120306090203012702072402160308040b0f0408040620030c010e1506030d080a1e050115050708 69
    0x340014400c80300d072504100c4085801e064142500600e2000313042c0d460b0701c1e0240c40d210070310b0f50044000712810800700c0e0550f2a071003180e01072021a00f0109244003001700464070343d4801403044440c620603400365086802c8c881ca01c0c502801030711480b200ca901d41000000c001d00e280800400403681000c040c410a207400108813682c09421804039461074820110540142500e03902c9206014400400098500c102d0300c039610900c40340c561220700340311100082e4002c1c1e0155000252508585c40488140c440f00040741811040e2070100160602e42445003411602d5501107040e00841c5c4400100020464000051a4015425880701d06c4a0400ea01c400c0c1141c0101c0c081c0100303100042c40000203642541c2051031041405204036642c48200c02e5045000c0c0480d0343c03e009540c8550400c03008214982d410003071003090050000c1c0388179070414034100c3d40c0b100007030312070704019503581d8a002c107080802220580015024001140551502d1051150101503200e44420018248070000020b404c810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 788677814 1250 788676564 788676583
    0x1e031806071a0414070b120c13120b100909030215060f27101208030a060b0d0c020715020304052103030a0f0c03230c0903011404020f010903020102 65
    0x100d405890316050b2401c1004031001e01030903840a000d00040104001c40003007841051003984003078542c0e49640704108415806182c2c548404240800c00186600207140081c180003d00300c602050000e5540c1e90245a500d0410301c00d403014481a400c0069203145100c25100138608103808100c108d40648000f512821121070245d80c0410301d501182ca19a80c0320078902500e01d0003401310117500da106464102d40410005aa0004010600010600c0001c01032500032900e0413010850301c548560b9420101e070340018203540c08a070341e400000c520680c0d818090b00046802c0440043c404c02c00c0100a40341c1003196020102c89075040c944642c046501100741c070700301c1c0c40a50b50310310000200c0da1450140ba40032205c1e02d844c0c0c07001008200140c880c41c2c2000000ca444140c0802c41e102001c1d10032020b03141d203991541c04400c0040103803003403501e50391803859028620600c01400c0a410b00b002900b5107241907017952102c40954140410b520f026603400348a00800d003024580c0c0e92035540040c1d20b0745200c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 788679064 1250 788677814 788677819
    0xf0503070e0c0a0e1f0e10031103010b0307181d0c03070909020927010e090604020a0312020a020307060f0207050405161b080a0c0b09010917090a050a0303021e0318 72
    0x101211341d0309803503103502c0c8030700c618074a4903e00c0403103050b810007072aa006410304244560300b00280302030b80360702038032811120710000031280b842c5070b0a00148a03419400604464100041c0c0210196040f240c800c544000d445582813424001107130491101c006174014046a5a0000400a1140d10b50b040303401c600481e0300803072003d61180c1c0e0100002d0001e83d0b40748561501000c40740321300e07042d580c2d000b1780c401d059030b00c01583c440c11901c48a80c450b90710182142c000350002c01019050001c1802c4054200d00081c40e8811a5055030007540405c0c1803009139800030021558105602c0c144980600980300504429142002249011084040210108191a010f002102c200ea885440920f4801d501040d0010086070342d590540200508002c842401034900a10040c0801c0c48040306000300110503400210252282c80e150403600f24942c0b1980c00154002c4c00c40e100090b064480c050641c0042d40603030040c0030740400400d2442c9860301c10b60300500c01c0341c0003040f13625424405140d0a1099417400d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 788680314 1250 788679064 788679077
    0xa0c11031905040816080d030b0319210f020f0a120e0109091a040506030105190c0504030b01090e0105130506010303080a06050612220519020d0c0f0503070e0c0a 71
    0x4481d801e85103480796070440310013406802645011030042c214034004941413901107604108001104800b1521221281075141c0c2000b1088803412584802c00d003030301d902490002441215150810f030903c017074040780d1000b0a07020720a00800359010b01550182502c0390b00500b030a65407030394408000d000340c01d041e04140011a0210381507a44161008009000c1d01e100812000301d00891900e44801c003250703803038461b034102000117038682010300a50703000d107070000244030810403011170382070140003401050000c0041c00d01000000c50915032141d0f000389000c0b10005001c03480051240e094901c0100324001e0b0146100040c40064000950241140c0c1c040c5000c1c42551a2002c140c40546002c4c1d004651103000490381c4410070721402e900780d009000e001e03440812800c1c0c000d48641d0f00800860050102e4201e0659540907102c201812101c0601c010030900010301c65540b00c8800020781c0d040300c80c07858007003001403040e401c0c00c00206029002d202c00002c0680b91403580c0d0304c000d2246e46601c0c0c0c20403c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 788681564 1250 788680314 788680357
    0x405181510050a03050109050105060a140d11210601050a030b0a0209040f0603050c0901060311070809030c030a0f1704030c090b120601060201020a1205040308070507051c080a0c1103 80
    0x110201d80c4020300001000807082590740c2c00e04901070401400d00f80c0c0c01d0752030038011880f585443c41ba100c045888071211704500354004002c01031041031112081d1180459800750540996805007105045c101030a1005100e9014038a003a10b0040160403c1d40030301c0c507400c41880407441070550a40c0c00031342e10380c000d40ea03440c03540c021038041c018075887c1d801020308105c0c01004010010030324030607140301640c000302c943e07984045c04c034162403c5034000b0040f01400c1002c40003007112013000744490302c00a4111240c0307807074240c0401c1ca001100c440075122080046600710030002844c5844903150089007105050a0542d251014110720610500c80403175a50729050b80e880d210000795146103921581a900650707074807130029001c0c0d40950450340024001804580803020a4812070780200e4055817044120794500000355410350010805460320311071356005504030031048004580340410b03135440500390f04004080c40705480c40070542800b403200c07a0a814a20200c00002d42c4c0c262001700b01003a9030400c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 788682814 1250 788681564 788681581
    0xd051806062106040f050d0824010201060b041d07020a0201090e1815070210150311010504080303011517131104020d02043003050306040209210a0204051815 69
    0x1c1641e01c080b507036005000411090207860802105480d00031010f0764042006503c0172030b48602c1c1100c5000d5804046819580f60700c080380c1c43c411140b1018000020b0a60710b0307080c0712030190419400241040d144540284d0903080394894250030069500041c410407071107a0010302248000e00460f14900c28030300000711501504500d0b01000c00541c401e071814019168000030582d00f045031940b0152043c5010030f103000340c0a1061110301e1007100140100f443c216514082c00d00090f51445040000a00c800b00b520748040c00150300801c3c01550240081030280c0c000f6000d1000c82180e40d0903280c1c03000c100090100541442039102d60b0214040c0509558080040c00a01580000d080c0080c0f01150108130007180e07003050413171402080781d410b6603c42041700700310644400c041d00030006241400801c0e6181410f402801c0c821000404c10014820f900300008222001c0420000f07140d8000c1c640c280a40c2014482d068104900c90704900546000307190300d941d42e05d46014000741d00d445200026040c035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 788684064 1250 788682814 788682859
    0x3270604031d15160b090a0c0e060a030813080c060f09120f030c060912040612050a060335030105030c011b060c05040f06180303030e0a060f020d05180606 68
    0x40300403120680c0c41c1c400c03846800d406008035000c205c03943c69203040820052040050350340d000c29440041c14181904024490303200e075030302510154214506001c04400a203100c0d014115001400003000c440c145841d012034900380d110740b62113000d0700d000c001007480701130400c1c00c542c2d50307200c26650510752444c000e01e0940741006a101c3c80382d0a000104000c21510404940c05024a2400c0d0484418100507030075185584154032070030700444d103140d046a80015958000750b0740554800300c001615075498581e40e4603400c0200505503c0e88111484140214030219031921000000324154290f40c14480426603c007100c0705a181400318405440800c1004160502d00a80c1d00030001c3c840c66840c24400f900c540c010740520010310380301c000f0208800348182d0030055032904160031014940e00e0350318140c00500031064061b207903001d2150f4400101d807041c05030720b0070161a4580140e5455110829a0403104041d0890600c0710302400052403100c0c0010304070b600302104690040007080308c00140b0980 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 788685314 1250 788684064 788684089
    0xc040c0e0f01020723130212010e0705040509010311120a020102060a111312051c09060e0112060f140415050402030c070b010305010f0f09020a030311070b03270604031d 74
    0x200f0a6105c09a100c404082c01d51150041040e104e4810061908030600107034042c84610700703040394500004002440c48109040e40103051030034001c2c549900e8001181c043d80f003d0b00161086002400c05403218103202e0011182950101c006c1c120741207540d40000c0d10348074050104210507896840c00d100c02c40141d4202c0700409514182c44102c51b0b52010b8071627428034070311002e0310540100384d081c081031840d80e50025840100342c1d0721a60500d080c400700381c800408040342d0b641000301400132000114424130400b03001c0d02c0262441c84141b0700d402c46208800d0301318050180070b1420404610302009940b80c01c041a54421a4096100d9898441c40d803500c0c010703524090310034040b541c00041400419070201c980031103d40020b00c8860b1340b0003841c50955070348600c001e40016013040c1c10408a40b0641c0d001600c010301f842540c400940c0d450760010307107410030f4a450102180304041aa20620501103a0f04900d4006000d460035103000d44010b4a80131410380300c0c0d50805240b146030401e560f200d031055401c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 788686564 1250 788685314 788685329
    0x120a1506080f07050301060e0f060904110402070303150603060807300b01030b010509090307030c030e0d21021204060c031206060305040c080705100302090f061b0c040c0e0f010207 79
    0x50b9142d8904219074070640c1d48282402540380210100b22007400c08600340c440d08881c00f401d002501c1d07003400e0140306c0380c0050054541c1d40e5440c10040c103607610b90009007081406030398045207203803c8101180f01922123a10081c1814a04981001000d03c00f040100480c1c81459400b9039a008812060140e00c20010b035040c05d1000c0040d0341804c0200000e006c0d07050704d000f201c08104a030b0f20f68060040c0c10005075120300c4503034410320101700080d204000f0381d64814400d107408412508174101080611080f003808507584c074440d95114400d10090111024014030510042100e0030759907200c17011601c070351f00072903040001c081c8c040028103000704c40008100e51407403010071041780d90b00d00042c0100070689041350010a40000040c250f8000039110040c0d400040c2a00a29410103c043d030095101110315504030802e805040b02e1070355160090200400c450b80201c5618480300c05042c14810451446441945800003519a29900c94184400d801d01034404044465403a0010b0307140180c07640c002803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 788687814 1250 788686564 788686573
    0x2070e04051023010609061409130608010b03060903180d03050705030a0c1a040209060d05120301030809011106133f090603020708090d0f140a0b06120a150608 70
    0x884040b1450341c01079911948075103c0070590b220b000071160002c091040c1800151586000120824050010042424018500055048180c2009003501e44035404400e07540d5403903900088605081c0106580004080050340c5410b1500b40800380c013240c030b040300c0d03030007003080e1040d0400b0103010754110769100340c00000303da4641c6180400101840742d0070034112011400c01b1941c103080416080001d01865009000c20041e5035580d0502c00ea00007903002c281e90620400d00b806004540c1c002c02140618000c2200541e600902c0d1b001402259007100c4140350756001108115100306801c4040c1c03485644426108141701d44440b41e1902c0d441d10600700a20070140907131035600ca004031500302d9545040742d1a80d11440d0380c5c808040c0d04a000c2c0c1c034005000700d4403c1103072042d585409042d6400d03162203258101c10f0110a5180c801841045096180090b801103000c0d4052044000f20075034040000c880c04c1025043c0e505900c0c1c1ca8990f041801407130010304888110912000350000b10143c4085e40448 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 788689064 1250 788687814 788687831
    0xf0e072604020a091e0e0307020619090b04030c050d23070611190f081201090203010812070510051815040b0105010206011a09030a08070b0406060b030702070e040510 73
    0x5000384038041d038040744911401d46002400380050300030344401250304e42080c2d000c40090b0b5506001b9142e4000b034211103000c10004600107a40722405000c5c881c40e02c404000d401020300c1ca014000101c55044603001c80014001040082d44047c5503005480041d564030110030018513190000d07110b085400103610b00e01c0510307450125800141e28040350074a544240c400d07198800031a441e841d14000e81c0f140d040600b0400000301305903101103509544a10340482c0f80052810440041c000c007a042550095000001002854000c0010a0300c40e189820f80d585000c505595072a600e00c101d48102d410716881d00001b40300302c016040031094032103101081e030310610005440d1503082007049900b10758140307800d000443c165100251150507541d80e178403003502e04101513441c001d040d04901d548070741c58450314048100042c040005045694800c428000039403c2c213140c08011789006801c1113908800c140304012400382d0004000040f1078041000c5000c50304e42e801c00303a00b4a031a20000c001c4045c20702d680c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 788690314 1250 788689064 788689127
    0x10b0a05120705071101110a031107090c050a022103010519080303190501080c03030f1e0d090302061f1202010504051f0f05130608060609040f0203160503010f0e07 72
    0x2400030318828404001080c5415005598407d40f0160040e80f0750300c0002820700182c080c1d04144040048003084410440ea548065000c0c4c82c7c9044108000800104402c54542d030108420341c22030750010050708000c2403503988042a804144242c6207c0c6852111025806156004403409844041d0640e03980345060341400e072400071903030b11080c2d059117424000100c14101244035514200010080d51a2188030007580340c4907000100c42512107a060781802d00d03c982d450b40202540c3c0904040803400c14401d0501030f081c42001011a120710440040f1010100c442240050603030703007108940e01c0402c00500040781c907400750f504900d03009000544054015110003003800e541e01465600d07440b07001d0b02c001044905003d07070329400d01844215501840901c1c001c00380fa0f58441400fa0216080c0f0b4903210014040c2d170049056908010350000c2441541d1605184c3c0c1c4d4041e8020b41400361440d490007482581c8241d05108200f140760420340810261407169420010412040d48000c10b080d12f02c924 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 788691564 1250 788690314 788690317
    0xc030b13020c03040911210a14100521070e0604110c060c030402180406153003051608030a14070c0219050a0b03010e01050a030b010b0a05120705 64
    0x24028403821000c58000c082141030300880d100142c80300c000d1030404c3d162850700c4003e080d2001030441c040d03c09114054204000c40304458440000e4068100a030402985140846003024110001c009803482000300350440800c1b88030032940182c5000d000418041d10087ca403d9400311550340324050001c000a541121001c03060140400b150100502d8104c0000e0030020b00c540c03104007001e500604000f8030b41d00d54103400703554040d001801000c5e002d40c0e000c06406d01e480c81150200d400c1035980501154020344041e403400a0410403a504a80c44000300c0044481c0c405419502c07445a40344480c202010711031400d503100142003203095146480545001c0c55640c00403610f203900b8a241c13001501c220140d080d66103028840540712009200f40c9a000d20204c0348400300c01040c8203c0b130080011305a00d5400c20580240030740b0070701c4c2d40c0380e504010500c040c440301070f40944d20440c0220760910110704d941101e5411180c21951152b0341c0c01c52203000340c400b40104d00800300c1c1000390b5000c21050a401030b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 788692814 1250 788691564 788691581
    0x1706330a020c0f031c0e03100609050a0e06060a051e030a0c0602010f02070c170c030607020a0203060906070f08150a09090b0703060e01151202040303020c120111090f0f03010c03 78
    0x84003201c540f5030100905a50701030301326a65541c00c0078855540c03001030040d0002404600701800b656800c211100110017500c04aa00107101c05680d4001c0000c812030324031a22080c00642c4000d042241800d10004840407450302a0f540314810620074108071200076040d003100440080d003a034454070307890304241c491120584219000342d420310300401c2d0349a40c2442200d0500c1e0b4494642d9002900380040101020722080d00000315211710660f081943d42c0c2000b085104681c00d60083c908151144141424004090700700c800a070303c41c109007e2141e8020040b580c0d900700d00e01c3e002d01c0c161350fa04841c1c80c402c2d01024a40317400c01280840498094400c3d00b00c0d4880c0c502917035620706240c582d001c048048514511446120a0550707005111304958071012050a040a2800c400107012915112040340d0081e803044000d60b000c040500d0144c10925080e1032100202002008202e0307075120700f50110f104101d00303244100102d14202c00c130303691000c0201816a1000d4000c000380450000050010070111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 788694064 1250 788692814 788692819
    0x140108090102090108240910080106050108160305071b06061706040c1404020d0213030209010b0c030a0e0d050604050c0301060515160c180902011706330a020c 70
    0x20800640c019205008444241c241a503490006585030b01d004400544105a05003801e00841c4004c03d07150755240701c180c0156210040750041914111946e4215074442c0d00a605001c0e5120400c40418001080e1b0384004407141404140343d13035001001c8511548045c850b00204504050142c10302c11309034000c10540c0d00074802c2c420100140542150340c1c0e00c04880042c148004d544052040280038810300c2c4142c00041c00140c20210b4110314a8141e030040404540064003a120400039440e00c0101c0a0060019116585c0b030b20560b030303e1480e101e00c6444007250610040c21012001512180c2c5040d5019410400307503421070805190142d12014a2405513101e076003003001c007041c2440c103c0f05100d07814080301ca5407842c110601304c00407400c807001c40c401ea5030040e50fa00b001511103200c3c204500c01254002001640341090f03c005002d5411212a5001d00d0792601c04105194440050015081020041860083d6001e4056210003409880c12031609500410703c90b484079000100e04070051001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 788695314 1250 788694064 788694077
    0x105040b010f03080306041505060d1a0418060e100c0503060406060801060225090908130911040e13080d0b011412240604030309170111030718030c1401 67
    0x3a1450800c18003403d00021308011800c0005c9582c034a4140e00511210b00d84400900c0401d0b0b80f5000a40c4030f401a80b800d620080c1c0711103103031100c1000b0014900c40003030110740400c520820700c1e6540300b0b5001c40610080c256681d44184005001040103940f040848106080c0605001a003005009810176260180074900b003000c08110a40940a1030341a9003240d030040040e00e420b13001120300d400007000078042082500c03001180c08440b5002e0515201d00a020080d92501e64000b40c0400411a503c0604054907103454602c590301c0340c0c42200c003150344129400c21552112007003a02c00070705402c80140442c00c002030725400031b4000c0e00301c0a0354010988039006c50031503d0541d19880d12480005076121624440005c0001d41d00200d100031f121188035103520800b0440307001c81c2e060f600c81d03001600403d42d202010000004800c1604c000050004002d220344603c05100c18514040a0848030a11041150000d01c0d01d00c4014060003c50300b00013141c80f9035550b0700f000e00040d070032280c1c2980007038031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 788696564 1250 788695314 788695319
    0x1204031101030635030a0203120708130305030415150609050f0f01030504051c030614041404082d0304020301051f05011b060e060a0f0b0109090b18090105040b01 71
    0x41d120f08801c449a01540d003c0030b0307120313100d402001c40404c0142d0070013500b0810300d0140000e0400151001c45a240c00859441708200080700184030000e000e601080b07146010000022030313a5110500540c0c0c18200981c8a4036540b810800c0140d01f40000d0300c4891402c6070b084070804c10056904110780b11512034802080e22001400400c6100c01c2d00660040600184c100d6607500c640d101d070f640540510151588071a41400c8100c2d2040300001407c0000e0710b5050600041207911980b51941c90104d404200d070b01044a0303000c41111005001802140340841e5020b41440c25120500e8640c05544501d500811003030302000301030f041500c0aa0296207840b00240c80d001c6103405c1509a240740b62202e40a443c507000045910904214002c440551202550070010344103000700d00c52085020302400e401c1ca8840040c0044901c000310041900d4249001010940d8010210340240c1d80707082030104403c68180042102c116124100401c45240001040859041940014051361040300c078514145d9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 788697814 1250 788696564 788696567
    0x50105090d02090403140c010b040c0e03060403110f010e060a06050a1d072604030221040b0702030111031614120c03041b080c150a020a031407051204031101 69
    0x240819a540002580c007072440035103008075545500611929040801400300d20400f5800d403c16a4603015aa440c0c4903002d02030314150051196148092811320590f0454000295881002400c0078003030100d0350402c45085041804031080d031100e40c0c3d000b80282e01007120700541c0c40c40b04a035031f1200745140032004181c918190500d00121ba030600c1c9003450441700c035901c801c48680054040c8050000303e068100480c20315a01c0341c840c5802280d1460312601d46400c010b810501100d40541501002203001a001c3ca01301040d541501d014a142a4803012148007103401071000c00d1802803050340101c1004207155a2039404184000750303603603201420000c202503403e240612804030f60012100c200146040410101071a4081e0040c80c035a2103400848500308109401500410301c81e411250b0201e22904003054004144002d4040d814505002c003c0e0083d203d0100034ac000b0100091402803c12070344175402078803404c0b600030040d81e40e04c4090800c10700c46544288012500003911003062101507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 788699064 1250 788697814 788697817
    0x1b0f12050d060f301a0603060a05070f0309150e0c0307150e100519021c050301030c030b1305070e040303060902071a0c070b0112020406051207060c060f1a0901050105 73
    0x4640b52640307140e1213200c120a810300849480b1200410180d00c0980002244e4901c160354064030400c0300306030180c10f02e00181810722100038800300c0310740d0034101805051940200307400c0786103656103070000304880a80f0342220011580b640c004a040e0900c890340030000d07000700b0440e4400104030200c1d12403980d2030100400450081040001103818a0410309250500e003003070780780d0180c02d0b24181e403030b00d040007000d50004600b880b10000103a008550980031134112111741c80e80800340d420103038199850b507540e8a01d0240d40c1d000040ca6010a2804030f1142d291016400c540030380d00c9025140d01c29191301100d850004200c506030f0029040c000300103021801413017140c05182e0420000d02c0b450b0790030885c000401901030140701e10640204071504c0462403110485029210503016851410081c0c0100300a445e02500040c6c4100e040500c16400004000381d000101c41403400c000303085c860a41000002059444203120251b800c114408591a04c10742d1842e0740c403803088a04922690725900110f800d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 788700314 1250 788699064 788699069
    0xe0406061715070503190f0504030e2b230606031e0d0c0203030c01020a0201060302040b03030f07060b01020a020a080a0201080a020a0504140607051219020c011b0f12050d060f 77
    0x401c540c000c0480c40f0b00b8450001036a0007021082200098501a440442241c1581d404020116a00c406120401d41d002c14604014441100d400b18403040c407802c840400400f403002c0e4003010030404074450411600c2c10646001c0032140704032074481c41403c00306030703112101114598880d00540203494103005505a104282e02d070400024580c14074800340c165030550b414102030381e140c84140718074000d500c4240010700c004803031a40007052061451050005584513503d809109030400d1107080c10020b90310043da1001c2e500701070046280f584c403000603800d182008074085d4112002d0b034004034901000251040b0050310030b03030740c280301607441032612012030191884803000100100f00402ca01d1618088070b0f544404010f14180c41c0110702c0ea2030074a8811801d94402d51000d000c0f0f21003642c10001000d0300800d440500207420401000300000344040100e010940c0c4060808040000380034041c40101070b403551101d60400003003180503000d8410342107040075554441c207056011070210083c0041604 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 788701564 1250 788700314 788700343
    0x606150806041517031b0a051c030b2d0307140105070311010204080a031b020a0504050c0702090a0b120109020901030b0403170112030305010816090e01060e04060617 73
    0x8035500d524040202074503941c010b0010f030b030942c44800710308050000008208a00030000450380c0c0d8103034041d801003014560900e0403060300321505200200f68045076080015654410b0540310303030304048055005082c00010030341c00140480c00000c000c00100c00204450260440d03600548404030b0400d581c2d0403c1e80581070301c1010780a481d44195014070b019002c107520078100120745d40082640282203820560100003d03600110210043c1034114034180700f0720500d252100040b040d1600450903a401611032140503a54400c00100000358000644500350f41c01010f02c0003d04011344224080c1c8a00d45d4058480c103503181c2d00b00d60010f41440794042c0568003030400e649580c6182c55081490070010019070034085841c0841a01401802c15640649000f1000b611164050708009041790016000052036078850a55030a40c2c3c1c0c44a03014108850000f50701040a9502a00c91070140959902142d0a405503109201c200315039a042441a6041c4880c04401c001c100421240d85514503100d842 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 788702814 1250 788701564 788701577
    0x31103040f03050313210e030a050c06090d050a030e0f0a0e04021903120c12050a020316020a0f18050f060108070c1e0f1505070905061e040e0103060615 67
    0x500283c015006144c1c818103c88101d22103070815107421413080b85050400d8a90b15080e4144040d003034010442200d424001c0d0028102000c017031b80e41070764a400080b162440f88101040714421551544540b050f1541c0c44020360780c0d00c010900d0083e124001c84098541300d807504071400003540c14880f5885040340d207000b0341c4216a4a40e5001d00c2030402045070310444000c6280c0000c808503124001c210051800781c4c1e120508000d41d410001a641581c1c8018000c02c4000c11031a6803099002003a00d11200034a10080141085480003c068148540c0300201000482c4800a89444c4003907485030b00aa5000040c8100d568002100c803a1440440d00140846d840c030010580041c800d07400025614401c2900b07100036181883e2418100800500403580c829441d0042c604000c4100da41060080303402805100b20704111601500b810080d004650003440e01080b50a400e00d01500c041010301d40001d0030395039498940781a91480c0d002400f0a8030344a0130604001401c406640c00e0920303200a80c0d447d03070f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 788704064 1250 788702814 788702843
    0x20a08060301200d060e0403120e06070e10020f011806110f3f0402041a0f0d050309040906060608011203051c020715020c0706050301081203091011040603110304 71
    0x94a5420008444c40035681c1c810b4040b4420741103444840c0500c0c002d888102100109410350030664407410001130701d0360840030500030203d42005024000c0042280e200c0254810604102c0ca000a00702c0705401960802a003c140b510310030040244443c0591028801e000c100c0100325014420400443c11181c4100801c11030001e00d0071824001e007803442e120901c40c3d401000720246100d4203103001915440b00308103001c11440e091084c041c1c240640104124620821000664904d249645050280002d641020f0030800c00740103c0c1d0815400400800c540740d542c0c00c280d001883c00c3d000301804199101c0002c80c1c107030001112034291760b84c1130752079038900b80e0703611800c8001006481500300c1c503603000d00c039000c0018011544400b440c030300c40c4001030b1510500c0c480c984c541941a8000c0b020f1080c10401800700f8440800c0440400c41e404a19136030300d840340c0100510300103401a03901005071038981e0504064000c5001081100da00359404d0100300d540e010180d0b418030042c2d40045c000c10000914 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 788705314 1250 788704064 788704121
    0x10204030803130317010b0d14060f0108070e030f030405011403090d0302090402073c0803040f050a0203061003111c060507021f0609060819031b0204020409020a08060301 75
    0x143c0c18a51003858448480b80d804000c2d015130344000c5c0c0000300c03400030114034000039241c10700c181c16800c08202c41001c03450030010040780d050304042c2d00d96810003005c84005100d0900520b4022100b11001d0211031090750070307100c0507460782c0080c09220300081502c405008044080c0041d00c4c010f4801c8009001a0111014150300039400075044c55089902404540d0100e206038140b00300b914040c1c2010000b42400381031400c003440440303c21040308800c00200c9000324a01c401170729845517101040c503819048608200d85481501c00b1300940c14450300c010401d000100340c1d19481141e00c182080700c00d65603540c007040304070045401440121184185c103080441c5850700480c0d044045030054509201020440f0001045480f100e50145511440108500c180c3e600c51040240035880151140c2e00d41184640c0e40b01c010240d014040146124009880c90460105952502d6008004554031552007100b00d01a4000e25480004180204005881c0b4101809284d0320071542c0101c6015240070004c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 788706564 1250 788705314 788705341
    0x181a0901060e01120c090f02220602150402030a0f1202060106020705060f1308010c1d0f0a030813150e0301050f071e05071b0806011205030a0c14011d0708010204030803 74
    0x101645d0740d1803d4940002d615030644145a15103202400159070b0b903581c58007441845070151103040e043d2248541c10410320f5404901055000b034101c0c00c00106071500c4c00003a15041101d41d02401d000d80ca188464200481419000c4500119400313603445a070340c825003640c0b20103c80c401d9a0300610200410404924003d0050002031540e03550001c500d43c40b504501c2c01c55580401a0780400da0044503003c0504101e4480d0f01c1c80e070001c64990071a000610040f4101c22818800280580c2c40410307580c0141e6250005c1401410401c2d00400080da0a40300040841c042082014025403078000440c00c205041c8503003c2c86004943c59210840c20414000480d26101182d00020018240104000154424030108040d0748030410b000c041410040003504014043c1e010b0714940540708805c100182010086d01e40000d50350a00024aa6160030130007405d01e030403000d981042d441c084e0080312900405d030411111035041000c880b1000e0f11891564200e1007540006000a0750a20010303e980d040b044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 788707814 1250 788706564 788706599
    0x70f0e040b07051c0e07091a03030a110f03160b090303040203150702011416020f0601080a032f0708010c170a1d0a03020303011802090d0f0303181a0901060e01 70
    0x1c00c4004000b511a40040780c203850344503651760700304a804205101c00c9004038214003862005280e005170208000940d82e00c519007443d41030101c49030303500d0842c1e1810f010302924040a0b900382c0c1e582e034100d2528072440704401d00301246c41184030b4021400d91180007050302d104d03a83c060300800d40d140300c0240002592038000c0600d01190740351f11005200e0320007103003100d0282e2048400c01000d0414040040e090101002a1a807103900c6503004000c194000181d60841940604040d101c2d00c4251410203001d002146c0700c442d01c3c544a00c425101440002040000c603110500200f00003010201e00703c5131000e800d071a501603e00c010002c02d640003400c0d800740e464148210030120030280c07213134083c6081039550342041d40940c1000c0b004214142c1c071110540e01d00c02840604500d00040da20020b81c140424010280c00e0921174609201094000d5014000001a0070440401d030340c0240f030500f5250100030003010320305e422900800c1642005014210680c0c1e1906018120f50703003441415244a88402c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 788709064 1250 788707814 788707837
    0x14030f10200f070327031a070309170d1d0309010233090a0209070c061a0108390901030b04050103081b1c03060e06010f050d0905100c02070f0e040b0705 67
    0xa006050041c24407178600002584900b044020341d0712034110150103072000070f2804003498140844000043d010010b8044c0c40803911180c03607110246541104000e00c001101c803804030840d081030290800c2c0006c050000c0c0c9000740e00310762502c03150703629007685071000c6629104030f0f4072107001040103c100c1e04040e0b68041030314000ca4000c60303040c0c1c0000740052801d961070b0000c42c500050300402d10545000b80c011001d81c000d6030103003000c0d005000130007002008001801c0d0320314901540c1440c000140e5403910841c82d4010200307000512035000710a03544201300250102313151140081c00c40c145802118102d0b40c00542e600c0c141070320b00a4265070700548581d851040e0043e00c090b401200150548496040380c40e40d4005006403c00ea01140d00c4a03000d020a030500000c52000360310b079a03003d000c0380c80c00e040700c4001140d40307085894024600306801c00c1c002200c1e400c1050000e010f0b42e00052040c00c55010300641b03900e1681d10359001604902c281c030060800c1035210700049000780075000501300078451 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 788710314 1250 788709064 788709107
    0xa0e0d090501050c100f0207020909030c0a080c0c09090303180a0f081c060b030f09030c0706031107050102040305010c0816050405090c09090a05090c041514030f10200f0703 76
    0x20005e50034110760b12107514180c110b50104100b015801d044104a5000703d82e031000354980b0001c01c50f042e80d900b0000e54010a210400204d040c141d0034107001d5606103150144c00445141841d20010741c80e0f81044413020f400e40390240740e02c0010300000a0101000f60000b048668510460311030b250300c2d80c880c2c502ca5840584c42c0200a101042d280304490090114040d80f545a0a11003d0b04d401030502421254003070740184905000e229020458400321407090078009082c0e00e41e800514110700503000013800c0c5500c0030500005114040d0031500d4114031030b656510b07c0d03540b07812a07010003040d00e115000000300d09002c1070102e410010545138105041e98209801e010402c00014000c0c682103d100000503202d13000d11003480303020860260b0a142c1241c0a1149000d0000b003030b1407c41d4144600044c680760310301d07a008030380c400340500381c01150400c055a1010b900090301e04007510ac981c2e419200381c1d80e42840541d030314658000f55007240d0b2115400601c0c00e841e03030f00c040300c903031040d001e111070903030324 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 788711564 1250 788710314 788710333
    0x90506060121051b07151a0f100e030a0609051501060c060507051b1f0513060f1113060f030207030f080403020708011a040b06030f040b0415060303080a0e0d090501050c 74
    0x71401c05402c1c17651003000e12140714800c01000b102030f500c0020042c0307441d1190750ba03404425500c0c2c40d02e41001e98000d98007003800284d0450308480c0400d82444603905030040da4040e40910621386c01c0541c2c261b00401c01c482c1c207005114030f240d441780001d21450000801403c0c0c000c00103941034002ca90010f1040c580035003070130400c5c02c202d840d041e0501d180c101c01d40d0000c0c506208a00300000b102038003902000c0200002e141104502440f9000c10070010043c5650762070b0303100c040c0c1c501e0340110004d500d60300540d034403180c000240c0103840903503002c0c00c1d0104005004840041d48240211040f0341d0707050b07980036100e42e200c16041d1810030000e0021815401600c07070102e000c24003403040072442503000c0d241300110030940007880116940b51240c0341c0508010002c00800c4284c050000341c01c158010354540f2142e84078100f1a0004140e81c140302038050408034000203050b480a42e580c083c000440c4200202c241c40e05800741d491005902200120759060303800c00803036000c3c401504661070008182d0fa0642c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 788712814 1250 788711564 788711611
    0x7080a0b130e010f0522031715120109080403230a05061501050708091908010204081e0d0806010e04150f031b060c020f0406051309050606012105 64
    0x4901d03408003000c80da45400041e420380c03090140307003183c5600180c1000a41016266840000350316200c0a084e503102d5881d83c803c1601c2000f1001c1c440101201074089424130f500580007011103540c9940c45441d0401943c9007194040c4142c0700050392210a0903d00303403a582d02d1405054496108200c1e090f0018980c0b051031005200c1c0582d42c603c03403000b4000d1450000758607022000c042e000b42e41004418400800000d10500840e0840c0204a0303120002b41c880044500521307140da04001c0f034a50012500095103440033841094002c0102c02500b1400c81542803190781d0404500c031000044c2c80c00001c0341d4294014940400f41307400c041d001180d455622010b81c054110076611040c01c280c24101c0030030a12460f81050580b501c0c45842c0d2201031403402000401403c40c0303840c081d01c9410311048444d400d9440342e02c544010030b0040c045040d49110f100d9110011b003000c55007510710340a0007000880781c0d0321540040e2042d840c081d00d01f41b194042d004000c4000c0c01c005004400252424000c0308031003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 788714064 1250 788712814 788712829
    0x2150103061d1006050301060b04062c0a0303050c0d0503040b04020d020f030f0f0d020a030906050906070204050f060406090b13020c100504142a0d1109100e010506030c0307080a0b 79
    0x14140ea5011038500d107007170241030846d138982c0d00c085841b0750240014400f295000d000910002c4600d05110b09032042005d50f444410310406545908c00c0c0781310000010150030902500ca10b940c2c107402d13a0100c410441c415205403004840080c040c44040d000200180303800308244180c1400941800c3c04441042e0201e80303001c071100c0042c030740f0754098490394203810310070040e01c0b0320030003035101411110b84141c0e000342c81000a8040c540a01c10081502e07a0291188030a8948040d001801841141000d80291082d0807050f00e8080c062414003401080900e45801050300001e07000d0b21000c0e118402d800075000a401c2404d482185000c1d850300f1038102c003681d000b41da001c2d500544400003000d5140810742c3c5040b60000700b43c4689080184071003191380401c03a03480f8100d8025503410700d81c0c0c0c800b0320f442c0002043d02b01405034800c15090901000d000c04a00390401c0e0703100d14115000f00e98aa6042110a000231a608400302e6820030005803468411104250421884c040c0801c594540c40300241c8003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 788715314 1250 788714064 788714083
    0x14070302010f1e110f0304030f020a02030616030b0102070f1203030e030c07060f0906080c030c1b060105010e0312070f0f0609030e0a170d0f1205040c0f0602150103061d 74
    0x107814600403021001e0300610984d0200b02d03d00324458030b0f164407080714031420701004001031700384100c0100c0780305014000c0c0a407402d050303402010b842c9607244c00c20b6041c2c070459800c6840340c00280703081c001c940d0700d50002a4000965807943c0c034400741e152804c01102411803081e04200d00b0503898680a115904003000030341801c5407028050424107080c900010b14011300501c1e074100f080100402044a41c0c0c21154142e00304204035085035803070780d413501d00000900c55501110329140c90070841ca50300e844003140c01410380b0340903079607050f080950030205981c4020103071598024070402c00182d0002185c0070b0004603910310414810ba100c00301902c0b0041191303c0184d00b6804a0710010800c01980ba02c508200c0c068401c2c8a01c0e200354214258100382c1e200c0484e945c4030180101154240b401c140502c000300340410030024144103518042c940b1301c60b800b1482c03242040d61030503078402103600d900204900710f1030700710314498107075981ca551519030143c50190201d504056404100540d41c1e038052003482e40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 788716564 1250 788715314 788715341
    0x70c030606031208151021060e0109021e130b0d0212010504140615090a06051c06080616090e011403060c04050f041d06101406030714070302010f 64
    0x3500703440c5080a0b0f2007200c4030480c0004000d4084d04100f0302c0c1c40b071440d184109460030340f4003840d0380d42005000c0e40e514100d0902e8140f6149440090300c8a0406a000181605c801c525014260b0740e90706140007c4e400b45048031001074041c614540ba051815502600c0d602220355600444180d80b503407036103c9075005440c081c0791242c0005050f400c245580d58402d004100546c0d040080100c000203201c411540a000244103001400c5412030f501d413070300140e400040340188031640c0555101c6018020b40c2c01000b210704068405001c82d00c1c031f100d19124110440d421031021700f07201e0713a5041c980051a0040b058080520440140124480301c44a170190302804400315180500741a00042600d0314200420301011b0b2041040240540c2d2100141c155008900380c1d0042000c4421480b00c882d82d0518034142c1d0124491002004240c0303c04c0d4801800b11000c800d003690703d070f0110384240150f5100499000021404050300d610b45082e4000003400c0a0b4024400010031a00d200348580039500564844039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 788717814 1250 788716564 788716571
    0x32301150206070c02010e060901031e0606031112060d060e07090902240a030b060409090f02120111031819080c0d0203070b0109153506040b040b0903070c0306 70
    0x8112078040094a401010f141801c03a5030070040d600085c2001c107418a414050f080200740c1c003800764002e4101a400103c0a2604400c0311203042450000308110f2080c80d0000f800e10003510a074021034801c8440003107034100f043c1016584c82c0d0a000d01d0710b948120440e4a03581e074007001c4800d48001e000c404090655010301003490384840c0100310900820a41d1380b0740d0358014400c2ca085101c030210450b807869500e070802090007803521000610f00c3c061030380425986814801040b041041000c90504114800c88103054003450740140142280e04500c0e8100c5440000c00100700030140e40312000852400500461380c0e0040e9540001018000c5650121550640407803e614540740503c415500781840e84019801c00300a61a800e03000072041c800d400710309035a4540300d061242c0302c1244602a1030740d1a082186240000740501d00381e48250403209500486500c84041400c002c510389006e0380c0c00506c426056100c68a59200145019200f04403520080101d40001507a00364180001d501509000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 788719064 1250 788717814 788717849
    0x12061507050a020f060a09090c031d0a061104080304060c020406121a010b0c0703060903030912050c0c06040e070e01110a060f060803030405030d0905032106130507090303032301 78
    0x1061074042419031900c5280c2c24400c1b2442c1c6030344480440c08540e4140d42c0480c42408122058000309903205040403031407c2c0240030002c0e04000107460348243c1c854182080645580d400c450454000c030700074880c151f082000300700004c0344103000c3d01110500013000000c149070b58252038180c0700681501101d100f03507681c000c0e1441080d02030820340103101d4010007914207440682610f45500840c00300510307076940e8018410916100f03921032818658400c00c48074603d85188006002c070b8011219214076845002c04294a50410905480c202d608a9001d1112030b1604034051382c401142c98802d074100070500051003140c1c00204100c12240e4061368000855416500130102902c1150304500301c8c5e5031040050200061000080364003000d003e81000542e5202840d02c1411445641c0c001154003542c0007031103078071700742d0800c009008100860302003614038540c100c0201500ca041350b1001c0801c00b003507000c00200b8001d80100c01d9030a2040e00d8406060400c820820034041e003a0810384050703031041d104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 788720314 1250 788719064 788719069
    0x5060c031c060f060e030609010b2b06020301080304090b0f090604020d0b060a050a200d2a140c041e0209041803113018180a14060612061507050a02 65
    0x8550f02301200800a21410105102160a1130715030395000140c0c2d0b1072000384004001c4514074841c415648138005655a580d1140001d55a8005c1d001c0e00c1c6029183c0700d000072aa00e08000300d00c8405001502c640b059070394902c204402034020b0440030722125203619880000380c3e07601e03005250f5100c103902c0301d6844114045000380120a0302c80041003100005013586480c0500044600c403043d40c91900d140c408c191140b0410400c020785c1d021140e03038001003104e60100b26141140c0e102c00364000080b11111503401d01000251202104135100130030540c0017a2149414540040980441c0640003003003022501d40c010340c0c68400c02c0300075400129201c480340c07503c26043c40291a40700080000000140c21951618410385440010000f000800140c504940d81c0c410a00c414002c0001d201084140e40c114a22025000c1201c01407021441c2c02c10700100c0710000d0b0b48060144070041c1c020350600d90060a2841802c00142016901462017564010070300081ca0060484601c654098085810349206 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 788721564 1250 788720314 788720323
    0x4020d171e0403020a09020708040801090503030103021f080a0c1812050606150f0306010309120914030f0a020d080412082a150613090c0e0105060c031c060f060e03 72
    0x200094082003040100f0150361240d503140d081c2c80107020016074880e45450300410070b10440d40040790950800c0cc045081c0030001c0003450403a80241c03800142041d620380541c158101c021001c4000ca40c441c000710b00154815030050000082504243c00d00314104181c0713a060401aa11440700c900d00104180c04102c410703c803030342e04a001074901e00c501c04c0c030712035140e2614007070211401c5080402000240f0907a201c0e40103d580c8a41000b0303d01801c901075100200351a81900401c40e040300070119004960400080c146503001c90800508404140ca50800003450101d94080c1c40e901c03014440419100610034070089124451072816940da846001e206000c0603a81e440e0082c0300911405203405540c000c103954a520040d121a203a15035151000a0b000e0f000c440b83c00b0348028a0300d0441c01c10000c0c4820b4800645861f800c42040c42e81c1e80e0010815240b1078005000e0050b001401441405806d00d81c1080070740d40c01c40740214500e07854101c1c02045a55640c450800038203a032804001c182018070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 788722814 1250 788721564 788721607
    0xb13080c0a050303030403030e01110313020f090105060f0d0204240306080601180c0c050111090315060a0e0907090c0c1b0b0f0705011e09150207050c0904020d17 71
    0xa6541c40c60307510b0080007a0304e80c0402000038082c50b031941005460000c7c2940901a5001c44030303041d0361281000b0b9450f10344100c4061b4101d00500910108080c1c0746000c00d40c41c0e04031000141083d2904115140f190803d0f08080c040100b100d07000e00000c101940071086500400c0100100c8203000940f03040c008007900c03183e92012616800490040c070400c09050040e14403100c40354000b0030b0240c2004006c41b0720f0084504050410b51030030050303540c10081d250061210090837012214003682c021600e078030207482a0f0b040381d4040c1d20f80c1401c1104a0080c0c00880c0c2c010810b4040d0740040d540d074000e140540d600840c1c8000040d8402e403084080002e48200d20110444c569800035005041200c0c042c128825104020021003005c10b001d020403109420400b55a082003500051440d11404104082d1541c050300700e4480070f50000e0700403107450034400c0d5508190040002c2c030001c0c1e0f128013031040004024005a80091922031480e0102da040a21400310074410200c0e2035549807889010565680d054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 788724064 1250 788722814 788722819
    0xa111201062f0615130c030608070501090b0304020108071107030609120302030624160515070c0b0115120504120306050a0605180f0d03020106050f062506060b13080c 73
    0x3150786411102d8002510307580081007007409042d052080000658620b0b000e850304000741c1c20000301c1c02940d9130603080882102c5119040752049501d5900550380c40c180380c0240c5244450600c00503001d58822407005411800d2400e2800078001d4070100c060078020542c0003030f29899212140d000410203d140c007070340c0e1340b4003906d000c50550138160000b1b0002400590024103840c2c1c040032544160046100315402d6003020440351200d1a61850b04944030050a1280116040340d500010111802038144018060380b01100f6207050b801c00c4040c00c514158920850704010007601d10010a840130b210310742c02103000c5c62032120340c410501402001d46180f81c011901844101c4020003500c0d8102e8113131380c20b0728608040180210503075804540e444502a0000758480701020701d0605054044d40180c0c15100c0c2600c000b00c0c5d410014003400071038804c2d505189088020058001c00380750011340a0440c00d07100d540082800c40ea40c100d0078100d600180301d0585001d1500b071007007040b04410040c60f80340f44c02c01e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 788725314 1250 788724064 788724137
    0xa0311010e040b1c140118050c01020601050105070b04080f0c0a1b080a0b060303090d080c1005010f0611010b06180111211803070609170f060a11120106 67
    0xf000007042c4a152018860850f454040601504101420f00c401003511500d00080000b1005402c0b4000e903100900400c0e15103000304520001103500c0480d41ca81a510180c407094548480c6d80c1c0c419682070b800030000c1d074000e6024401c005a02c8460001800759070300020041c445c901c464140480700c0c001440750708004410b0901c0402c070100d40441c9010400da00251a820a41c2c1d900010074258881c0740d4003160301c170541d12180410400110060001284000c04032881c400744a404001114001c1c001d8054260040c0b04c104507940c415040c0b441c0c09010359002065004c00e00c40850039641024510303015064442103145015640620f6800c5c5000d50340004107c03051054030803035118a1101c14039000da2400198440807840e00d290104000303500079049910b40c40c0d51314402094800c1e64001c8090b0050a0244070401c503130000b658110038511440600070548440700100000e2102d1040348401a800703110100c280d20020b02103d00030300c8640c54292401980100701c4003c07424200d00c02019146 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 788726564 1250 788725314 788725331
    0x2070b09010e06010608060607060908070c081005060d29010b03150916111606080f06062b0f020316080601260a020d0e010b120d14090f0a0311010e04 66
    0xd200e0246030b0800da00b6941c5589e0f0303020508004d0b000d0082c0d000050301c41140064241c2c1080f201c00710000458121400350780e10000c0003d480e2007503440a440c1140e01c8080b0010100201d2000030000c01c90000403504030901c14203149210f5814042640041020500401000b04001e0766205070343c1090803c45107200103141007410310509041da48940b008019000c05c00e05046101041000f4000690002503040d8582d2094000d004c1d04003203860420707080749030700420407500744102a035481c6600f20078805510b901803401e50741145201c1d4003c01c3c40e00c1e164951440075103075606c011070090403200d24000040d07080c41d07009080d40e800601018100452a162040020000c94861684920b81c60f136001d004d44805400c0006400790000c003403090352a08030359800c0c0750300540c0704c402548030a4a0035070503412000803590720b50b0410142500403512580483c100c030844180200207051000b084098042403072408141b440e12103400c2143e02141c02d44041d1030b41e60f0006800001518100d0341442800c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 788727814 1250 788726564 788726567
    0x10603120f0504121e150606110307060527010e0d0809060c07021f081608090c090a0f0203161e050901110703140a170c070b130902070b09010e060106 66
    0x4034504c500024920040420f10802c00000c1c01d4a0062502c030301100c0030a0201c4c10219039040d00058811780440c508080003407810301a1074109042803040c0080c2d4100580e6413191b0b0050000204140d08025403040040d140180c1c00710000e0705900c41d20000190042c551514603e40701400304400107110640040085410b000100740b070303000c0101400c40e61903c2d440c0c8049040313008e124100d41c0c0351501d804840d0411940c4000c22511800903101090342c02c10722106c099800c01c0c030a4602c7c0d542e6801c0a982c000503410954411500712541000008241c0e25003058441260000d940004c02150400c58a403140b5500030001144260782200f0700216035080030002c0c0952003003010b00c41c14405070180c40d070240c00d0140190b030011030300100422200504021441c0d10b460f10300100b220110b1002c001d040050803100c068600a0302034400801c0d00c103080610034034058014841c2c908240a030b01c1000f0070950094005055240c0c854402e01c400360404141040c00c2d2a0301d1519202950300001c010000035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 788729064 1250 788727814 788727817
    0x1a090a09051608010218030c1f05070f121b0503160804030204051807080f0a02010c02010314040503190c020d0209090a0510020a03061202130209060403061e060503120a080705090909010603120f05 86
    0x272a4003108442c5034400d026094130315000b401c002400e0004010603103014484103a45245c420003059489444208200e41140b48013011440080c2c075650083c0400022840d60302d449118007030290751401c2c00d1640d0303a8009803d40b4003c456494010b400301d001218503840400c8900041c05108020348004580108215a1410300c8030010341046100410311081d0b900035480000c0004071252001d00d1850541055656076207c40e480f1140f0035540c0541740d2015101c0c8183d40e0980b90b0040039032441541c95020000880e42c0a400541180546210800002c0d020041e84542c80b0310954050380f10343c01c070b91015040751000d80c000c3c00104c08004503500181c0d0717080c503984000c00403400300580301d41c2ca10300450850f000d9500002c080e1441c21a03a01e10040390211448118544c00605120264642c0c09158940702d1111030b03003424500034401301001c1401000c80300d40c002d40d0707498201e0810200c400041e0103080152551405655120410f20600c10140d01d00e030204081410421141102d11600411342e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 788730314 1250 788729064 788729089
    0x30a1e030905010212061c050312041b06081b120703090305091201020d0b030c03120d1407080f0702071206151a0d1a090a09051608010218030c 63
    0x1581554a40442900a40c00100000d0300000210340380d11800000c4010048160380b1207114a1802000c0110745124500250717209a00001444c01c100580703904e807460010190040391101062151503c5500244050700e0040040c0c0e0b4450641d0b040c08061200e07000317041c0c0d120400039001005001d031291103002005401c00401c0c0780024000d01c0c1814e041b00c803401600c1c0d006a01415030307d10000c007500150080d101e030b0583d80c201000b0080004007015900e190324100c541d05500692342d0385211079800310140100141030100030540c5501c152a5101c49a000c0707030b0400203d240c84080c85061100100c296600c21b40c50300040c2429420004407840081d0300b680c0050246803525515109951021290380c01400e61802f20b50b54000564649040c0307070401c13809804018504071404030b4504050b04a03041001c4003602d01074032500c500400340050620048141c6484c03044400b1192812441c00034132008080d00800180ca810300303406c412050400c400c400c00d10991081200e2141540c41030b110212 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 788731564 1250 788730314 788730347
    0x20609150c0a140a120e0f030609150a020a0801030321020403060606020633060d050a09050f120a03020c0c030d02160609031e231005011508272508030a 67
    0x3e1070f0000100090035500c7c050600c43d098081c94041c403280714000101090490056030201840da07547c0090f25040b40103185801000500c0b0a00400c04240680910b01c040401810b1103401c041d440300003141030368003541c802c5802d00c0e40e80e41704020f226414040143c02640c01c8107040d03505144032940d118940100c100d40d25002800d40c101e070796a551044100e42040034200e0061010b80f402c51303001001003403041400d840381d001380a00d5401409011a4a911600c2c20881280c201840d10750110025001700e004041e0f103228515104a0701c0d90b0800803000a914654003c2c94440180c0c1c10124130200e0303d40c400f4003409218201400003880f0554080264001c4e5910001e1000b07050034205d60840340019102016000094421074403800807814040c0228048000d20441c0d07038860501c0d14100e00e00004134002070701100410402010300d6441c84001030f21204210080c01c010100c58145180d4066504450841f604004256000b20350340c034005203800d80245040c44c00c0090054440391500c4c0030882c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 788732814 1250 788731564 788731577
    0xf13050114130501031109040906060f06050c030a0e0d1e150903020c060c011401060801030605240d0606090c0c05010605010c05060a0507020a0b01030302030a08010b0f07020609150c0a140a12 84
    0xb1040d6106c4140d4200c0a0300500902c03040c6040c2c11f0502c014200c501411010301903000001c14024094400c5440e440c82c0c00c0000e51600d00711071130450742940804419a070200000362100c021480c11035038140034201044116003050f8091404c1c10311458503101c41c2c00028101040240865000b0071075a13920031003680c00d00d9544803130021107401495000d0800070b5402208002080c4154440c40c4036050701c0c4181e001f0400ca880b6060002c1420012882442e0200600d490701b9072076040903d040192240b060501080075500d400c68541030301c51180d05540080d036207103808014032809024280003441c1c00e08000a168585441d02a11002d004210303000240d158004145914404c01403981c40d44e07084038108440c0c0d42c503440e000b0740300c0d03000c80c109100240180c1c001040c03485020040340e090034410520145818260303820b03c92140c0252001950200c1940318000c0c07419003940060189074881ca0250a2510300c510300714002c035030328800940880d4080852040000c80c034071121141c0350041d04040c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 788734064 1250 788732814 788732831
    0x80703180f0f02060f0d0b0315040809122505101403100806041202150105030d14040f090902010807051305120a02040c050d0e06040206031503030f1305011413050103 73
    0x9410042c20761400a4110100158500404080d04082e20101d0b206403004e00c856505d0504250b81c1e291070120403c51008a400480d0000b00418001c14070300d03401410340041d80201031505401c21510022070600e2141040c01d0180e000c290000c2c0d080540720450f41c00c1400141c8840080c035281c51208160403004d80080890010119403132490000c2002d00200c0d45c00346003900d484202403aa000d040d002600c500425058090250707c1c01c40e050720f030060014240d080380444221090881900c3c002801101000041740703030f04000381004050310310b01c50081904005440014041c401c000c00c514104201441100c0c4801d039910b41c1c41d81221002c80700b0071240d1060cc0074103400d190166500135813051030041ca50000c0f90f0003602a051204161008100a201088159480d0303441181c0080d4000b83c01c00000304a612641c4c40b0050228000d401c90f401c10b0039000915040d607100000401945a14201c200442d6902040d030a07842d003003c240190a040181e44001c1c0d000515002c0c1e41d05041d15003000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 788735314 1250 788734064 788734073
    0xd090804030503041d0603060906070f0c02030616110303071b060626060a181b0f060518040b0d0b0405120f030a0605011701120309090906020307080703180f 69
    0x50324040c60b004002e0380d5035103540e0013441d00c0102d05c9000d48001002e9101c006980d6150101d111482024140e000d030071255070b074075022542e115500c1001002d010040d00801d001d40c4080010f01d101d06040c189000801c201403502030204d201180c140e200d154410002c01c40d4280e40001210b1110214502032100c0d0900c03480c007603000d4519074204402c03001285034001003041d54590144184449481520a42e44488020313504ad15108400e9030070524510540000080d0403280c140710005d003030b004d40040a0b0315030340304400884090380300307130300213a008240d0010098901000c1da818000850b42041031f24460400301e2190088800301901d0a0000c00008040c08010b105003200c1040540501d56941c04003511000290001d48240080070326192020442c0d500440c06001c0e00c000d0211501010703884c00200d40c91400d02c3c10012402c00440c81d00010368007145000e032055007482045c001d62a46401c0f00000c00c0d0041c01042c40701011300702035844070710120800c4d0301e050071500315041810485141c00c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 788736564 1250 788735314 788735317
    0xf0604030914040f02030903091207050a050d0c0308030103050307140105010f03060510051002010903020609150c0a0e150408011b140a020115030507081b100302090f0d0b01080c060f0d0908 83
    0x2842013043d00010800c4841c51004c0000c3c003214008541148890214a603020341d5042c83d4010190400e10740d4000340006d2802c0605902000c2c8034ee804400c58070344076510800e50790420b03401105d4591000c2843d80812400c4001c04183c404a00d001300920f61602c2c480342c4050549200103056540c0d0380d001b007104c590203114814003510300507008036102c52565500034001c01d4a04029030043c02043c02054404001003010304842c1c25040442500351a0165122800d501003c84d090501034000040f150076214108281601130703403c030445484920341107005003500c1c540000100c6102c21865070703030442c40e000407880c5000d0008511044e00d901081901b44d00518602890301e004003c0344a0003c00c201d400a042410394440c2805c2d2040c0941c1010412070041d1440b0469511030030100c007100f5018801e901601005000410b8003015040d00b801261115500d4031040c2d4071280400f00600c1455000c001400c05098203588003890490b0301c07101040d0700e01030700175081c03441c03034848410340c080c081440c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 788737814 1250 788736564 788736581
    0x4090b040213140a08012a0c0b07170106030b090a0c030e0a0c06091208090402030403120513140a02090a050606090a080c100507030807030f020c01110c0f060403091404 74
    0x3004055641d468803006010f142241e00ea140c03103005001c44c0800c90000c1800783d44050f500082810504240e0b804a2404442100c9000410015087c0300b090218000d1541c850007a0305a46424810411000710035510040c160460020304d41042505000d40d180c04440d141d100385c281c40f000545820104d0110040c0804000d100c0192084070590024003c8416900d02120f015447d24403a41c4d42d07850301c007070001900010152a94800b03002c0c59007541855001154042c1c82854205c0060610390848011990141c600c080d00e0380800303003402c003000481a65141700a050790b00a10301c040b0141c0c0080c40c1600c000700004510317501c0e100814000d8a0301d00c2134401c0400001c288411203515401e0555441c1c0c101559244205441208100703124000e1044409942d091340d52001c55551302501a0301400542e0b103d40e444550030000414403d20030b215004a41d2280c140069450903400010752620f01d00e0301a049840d0050004d0000080e08003c48400300d40310490340e49034011401001500501e00701 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 788739064 1250 788737814 788737837
    0x311090402060c0709050604060e160c1707060e0c0901180e07150c03031823100e010209090105040204080c090711062805040305030106140c07081f0504020604090b0402 74
    0xb0f0384c0130800807050b4008511601068030f00b0080240c0da0400741c2c41e829001e0341c00154105001c496403950b1485407003c84281ca019119011200026020300c40e44c0b58030280043d00e0880d41c8520741c0108050074400b50921081c111042c40155040c03080960140d0103203c004030b00c0300c0ea00e40c150b543c072110031b001c10002072035541881c200314408040090218400c4030003c400092409000c1c8190905241c0c040041d075070424001c0c218407013500181c040a01044d4000300c143d1040c2c00c4e4030062142d8900a194083e031a010002d62244902d000740320080b071040e000103204600501060104410000702141d90030030845848003240c46100040d40d0380c203024000e4180c035000d00010044032101025180448541d0f664401c00c0c0c0c00da00302d8841045440546e00280001e00030401040520f21842d00b000764540940300003464890b60b0302078103151120f10b034030903c83c54010085400c218070b265641c0c50b200807180c0c0b00500c00313032600c1c1d80020843c1c46140103a01e02d4a07940c03d0070f413800e601c881e810b47e51349a200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 788740314 1250 788739064 788739073
    0x501022d1905070b1c05071709010606122906040918110108070c0b071106040c080105070519120e010c0c02120c030705120f1509010c090311090402060c 67
    0x54020300201502a44042d107592040060000b80c442006044404410317554040c01715400e10700040001802c8054110810411070f800107100031880554501d020b6490307003000007542c078542100984110f04c80154112468a031040303140079050140701407004140344000041f00404480c0c00150203000d2a000b03451061b1402d044402c800034410140c84103c0c3c0184009041c245c4000011684260100c4000c000101035005110000d92080d0040d03400c40c0c400d0404030350290003500c2c42d6141c41012076058900a02c2c81e0001c1113090400c0c4980c680041e40d0703242c11440c00400c100c1c6a200310f000400d000042081e030881c200090303d1140c0c0709500079447c010080c0b00070101513000038a441c00c0781070706074450950341c491400701c40c800003200018036a020740030b400c005e0b00d000c040241020441d02a00703081d00644a00d519041e400b80000c10b1009140185070009081c088459421034501c24009018482d21410604c08039081c40c1d05468104000c13284c0c102a5941c40c804204540100c041d090058031a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 788741564 1250 788740314 788740333
    0x7030f1b0308130b03130b06010210090b0619050603010b0315040c0c02360c0c03072004052e09050915091506010c05030c06190c08010501022d 63
    0x40342e00915107101e00588401403140c40740510005840b06403549400c445000c203600b00021800c1141990000050050380d0a245a4282d400103880c5070007801c6403240c0320701041202500d8803180300c00d500b00c2400404240a0b0030b20010440d148818054107411240110010340c20132110490309410740d00c044c0082c40701014501d40600700d00e020b008102c0c4605451100c0038101c10900c20420001c100701c00302100c071031010102d900c540a001400c1124031840030411544030080400c000d0a44600c5000c1110901c40b42d8401aa291145480f03c2841503003090240300e074882c162060902d0540c0b0441c65221808600e40140c01b80f0700150b40100354050400c000c01c841c0700e401007480031000075030300d00140f819500e500486486020038208102604010f0001c00c0195100308018880b40d482041184c0c94414188012172030400103e80c80713802c404414034080402c0100b401501246026803c03e28955410400082d48a5025000c4101d002e0400110064400d4011001d60032480800e0b00b614843c20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 788742814 1250 788741564 788741573
    0x7051507030e1002071514040305060906010e07120507020c0d030201020d060501030e0616050706110415050304030818030d05090109140f0606041d010c0e010813020307030f1b03 78
    0x820650381540403500411100a2509144150f80e45240e0542c0c090400d2a0912402c3c45214180b125150100300000035a1403042ca01400240701560003807000f00507900e880c2000a25100050f080606910302d0541449602e40c0c0041103020251405180403c0c5556012400c0303190101140703400e90701c141031000150600d0340640c010500462002d409002403031b06c507001501940c05219100c10030f94080c0002a05c050f0540348440345c0f0542d545402850700344d00c1d032034007416110308183c4591003800024003000141d641280c0303160080d40c0c50038000c0c250700d05620301030951341004003141e01e102407070041d42000070b03824030880c0c0c1009081442084a42000c0711100d00801c901003080f83e08120162000c5650200050080302e0b1024a000412159840400380009000040740c01d0f01502c020002c800d00914080c020f50300d03084100d640d00f442c00d0030100300050a50304e0180064200100318003c107409070320003241043c1039030340088407201250018036200c01a250030038041030750003020342c80c08030810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 788744064 1250 788742814 788742817
    0x82109090403140d05041e0b151909150906031a0903091008060907030203090706110c131e06050a0b03060a031e030809031603030f111c06150f05030405070515 70
    0x6c034006c00c542803041032070740003c0d41000c002e01c1000d0841c501d02000200012800000c4400743c0d8000f078070440403119a01c240210000c0e060700000100d64503813005a4004140744015030041040345002c1c0b00c00c600c0c5840350140c0110203030729010610441000154140c0041040389d0440e180540811102130f803502004184020503100d40d0b101d41094000709084c51700c24001d50f4007072524100030300701107440e001c0c003503031168903401c1c0840c2c3c103000d40c004400301e55560122104814440000109141e0441c0045040c03814980c903002c039825240103801d000d240c45000d8500280c880700340500d50349481e0b95002482261407640300910003020132314025400c41078210309103034851094842e800180c494548258aa0040d191404072481e0142000d50120744241c10107401101c014000084280348201b0403603940d4440360388081c0440d081100c1440d100d81c42c0c80389200501e01070590032022545894001e050072209040081040400300120f402d128080c000d00c4014200108040b040b0b4405c1d040b0042e06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 788745314 1250 788744064 788744071
    0xe010b0c0609010e03031303020f0a08190f0e0402130305010509070608070314060108040615170714060706110d020304110111010b0f0909070506030c04082109090403140d05 76
    0x89004003004030b8040101400b038600b0b0a8030003009103003036582e00280e16101c00c00c0d420b0150114030504044000300802841050300440c0221541a51034002d1415580c03900710003a10001041109006000d00f1584621102000e420032280944e40300b000c00032403245143c4503040a885546031005004514500058580c11118261503c1c81035565401c800e401301c503169400d805007504401d0008150358421241d1a03440b034130443d80010168a0760b035440b0003844050b00100c5403c1c0042c202400b55420810a25000308002e0b48500c0168403845d0216001e40503103c0000c05d5a919507060741860f079081d0080d60441c2c1c0d5003034411505c920f13040c109549100a82000c581c00300f64a802e01101d00007041c00707103035828a40504110700382c00c1c01d0810700008c3c0c2c40c01051070080b4012840c010a040e030307600c40158002c0b02c014407031540701c90428281904085511005492509007001c00f0b40d605044481648d07290b000468106078246d0301c80c2002d94103540b912032400b1010400043c6480e0721241e5a114501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 788746564 1250 788745314 788745337
    0x1b040e0703060f03150b01031d0d020609160b07050a08030a0614102705041401082e0c05040905040b09010f020c03071b1203080f070306230a0e010b 65
    0x40560342c0b1840f8a100d050741c0806009114000b40c0e8408141180e088481c43c00380c18500050030301c4410b942a01481100071700701e003003900121400030b64141c1c1000507907045000c0380050880078060a03130019140d0b02e144600e071105800032406509004041c4005400650008000303580c0c1d1620141c0e0328010302540c00741c2d4020743d91581012a55007800401ea64001860f030710b03102c41d0340c0d070880d450a00307420080301c4000005503c044040340c2611180034a1400001c42e000c40d00d29541000f41042c201801c5034150468104811941081e03546134198018201104207400504041d2080342210540b10701c4c1c10011900e0308040900c01003021042086201c6c042150007080842d01403041d60b4281d10558604146507803040c00040c0100704082400c80031180780c01002031555a0741e041c1515010340725035096001c24240401c2003403442d100500703541d0084461600b005440d081c00908102d500d00b5a10a400841c550360001a203a20b40c10841c0c005401c8030400c42120b0340c4d56071030a141ca90f001501006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 788747814 1250 788746564 788746571
    0x5090c0d062c0402040b0a0b070611132c070f0f0801030206040603110912030703020d080405070902030a140435180102070e0f0103020a060e0d0b1b040e0703 69
    0x90100c2e9207003071200309404581d581c022400b092450b0b48006420280c4180d03400b5544a000240c10f51703070100326400070000454850b0b10ba0321642885003c44450400032884080d00704002031050070507500c4c0b01c00b40c8010103000c0205195480d41c90410321061403020242070b100a080c403001c0da400018841e80e90030940c2c0c480b004180c030360030211510030081c8002034003c18140028041d02e4040c1e0414100c08001800e81360810442e140000c0032840100c4050186420000f4040c0c14142d05019240c540da40500740310b4802e05140d6285955840e0b2403060600c101d501102141d04124141c215001c166000b0304a40480d04080c1405100c4510279018501e0040c00c100c1c0d81602e940240c1c10340300e4020324903007440c0e041c030030005586041c024401c804281103010300c2801140f003d403518019401000f01da54440302039130552050040c40c500682003030303080c0201c0d290200019500c040452804961000c003c0c0c0c42a01c4044991982c96802c61031500c081901140104045002d0b4407014031403110307030343d051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 788749064 1250 788747814 788747819
    0x270b06015705150606130522020706050403180303020604020910271b08130615060504180207080703121506030f11040f0b0306060909090f010605120d03110405090c0d06 74
    0x3c00181304142c80200740b000d004401f00b0403883c0c410000507180a07411301e462020700e650121041283d01011040312815554410721051561024080d21901d4079028640c1c2c0b40b50440d20003070341d103107030003000248980380800c00544410803a02d040e4000301031001012403141590290072103540c89225107022820700e41001c40c44204112402020045419140c0700425100c1900599081070070107016208503803100d2515540d484030070714000c020091907031210345581c14640d00104d01081100841800d038018040346011410241c01c4451456150906618501385207031b0407030140803140d41d51f500c028103c03c000a10340350150480c180c0390421010803c07151440601d404124042c038021200060307541c01051001c00b0390707407004680242e402400d00b42000709400004040034030444141500d600002e401803034082e824092840604004c640b8030803411a85c0d11083d07516000e0640c0c2004058841c41b01810340c025031402ca40c050040a000e40c1000e103401d6a40c40410340c000428444060b1420000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 788750314 1250 788749064 788749069
    0x6041d060a050f130f0212120403120201092003070b0d0e0705100e06070627020108060301051510031d01050615040b0706270b060157051506 62
    0x7110304c2040d030600c20968143c010344450b00000f00181040760060510b5203601c900200c1088040402050710440303035035031802d52900305050300c070508131031040d6030401d94900002224034002080354000b00e202e00d000c0c50000400649000003a9001ca0040103000440400100c400c0e0417481c0840c01d00e6086400980e42c071820701a9003c944180c480005100c000c00070754138a8124002c01c3c80c18021400480c020001040c00c403107003220712900c55650030221106004650b04400f900d42e00050460003041946030000600d51903503801e00d22a031040d208135207441c0c1c806d8000e9120949040e6100da20f0010b030342c85001e50074001c0c60140c4583e44100f541116019003a0509021202900c0c0d040900c181007a02c565101d101804055001a4402281d84400d581c440c40c4030f070151549a006100c20ba5007810003100150040c2031800ca0395010f10410403000810710201e48884d8010611840d081c1c4aa1a50314040c07080c11003104c001403950160200102d040c4000000d00310302000c4c4809001005440300b204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 788751564 1250 788750314 788750341
    0x1918030e120c0f0108070203041e05040c020d080412180f0e010e04110402070f080c0d0e15270607050a0b0604020304110103110c0304080312060102010c02060a0506041d060a05 77
    0xa0039507001c0e24482103d45907500ca04101d9420420b030303004907070509403581611003a40010120712500140646820491490b090040d00c0382080316002400510841c800f0007085094002c1020b00301000307900030105540e11031249083c403041e400849a811a450b0310072141c040d0a148a00c0d0315042c0014004203110340020700442c01103600c4166550001c03075400501c4040e410481040c0c0c0c400000c0700441000c208070b40020061050300c00080c0800c140700810252205011164003030007040d2840100342c290301c2e040104c902410502003140082c54407580ca0a0070500c0d2240c000e80c120030f0100e090020031500140b1031262500c00d0041c0180c079910a002d00080b40021100038040d00100e02484015500991101d400c600580e100e140c0303440400c0e041d0603c0c1d82e0207940010155030002072000041d510350fa80d1241c0211003417000b48428001c110f802982c803100030f844403800e03513a1900030039815540d44e0b000b42c00104108140340012200c0c40030583d2107210440b4609455800d103800984080d00507407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 788752814 1250 788751564 788751583
    0x30115111009060605040e0a210203040306200f270a050907030b1c020a12051e0307051e010c0c0b0c22080d0f090803031918030e12 58
    0x40c02440030841409804000c0d000380785042c0c0d569030350f030480170550340c03918068101d001d92094000c1c003d10010380f410000070b0180a00c0200b040e0040d1031091042c507400b208480c101da41000002c140c044801d1203000c04070641440806a60100292946a01001c0000740403030600d20b0319004807911030b076001e22500c011965030352580040c10b1013040c0560714050030315a800992500e80081c0110000012034001c105100030740c500c860080102004500e00714000d04080c0405081c40340b079140303107580c03043e6a030701000c0d461009003030310341035910f01540c420010744a030b95400508403010f403001c0c449604d845000229950401d5402c10002001d002c2c0648181200158040c0301300c07400b1384d50078080c5003444e00540c1005299100051140d80d9417144820300c18054040f610207044194031002014229019800a6800f03010344c00e001008034000210a030384c2c0c45070345200e040740d8100300038900600802c0100180840d0300d0200309100c00f41940280000e41c1c1500642d00512040342e400e44d002d50300c07032510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 788754064 1250 788752814 788752847
    0x5100201020a080a02160f06060503010609091232070c080f0d030b01180305030406032307030507140c0c040e07051e01050702100201140a02070f0b10150203030115 72
    0x14404120b01c404c8907402004031058800706404941c92994451280652091080d1140303511158288428075003842800018003040301d0030480030046642c0c0f040c803105c0b0b040d140d00034020f400304000064091400300444d040c0e1601580d00311a48500b400f081c0e9604950b03805c3c1c4004c4506c0b400030076030030b07400560000360b209524000c28452203905022405482d074040d280c0c2c100011901c00d0505400c4092000000c2c40c4200c2c003542d269400c2080040c00c0b0349211101d50030001540d08868111545080c00e143c01c4180792401282e280e8490300c00340d0b03141c00c90801180c51114000380300401e251000c580220004070881d0240000524a201a03540700814003441d036115080d50280d00030303205140c01903440024103040103030400031103800140310000c00084c440050b0b5110b4083c48042c2200c2e946560b40480d00400460614186407106008045213850080141c244000460015030a29899100800a2070f9200e01c01c0d100303a00700291250820320480504c108105011040c09014404000002d2201e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 788755314 1250 788754064 788754077
    0x3070e070f0c03021f1e0e0115030b011217070503030405070608011a090a0812030403091a0409020a0c0b130b060406061e0e060a0815040905120d141005100201020a 72
    0x41041e41e890462015501c02e10342d50312140d0403580c6c00c08045155030070055140c005403880e20841c240d03003526207050300c3d989081c1d0a10814070000e003141680f9410341e8020700858410b050300380342c24124803020315010501d0040c08103000c5c0400c4000070055100c0d038410410b0f92a92a506c880603a15160280202061144c28500000100c0802c602408a02e040249054507143da40d1940c10304207812a8030301004040d00108110900d90400601001480e41000c1c2d00000e0307010b0b03410f400c56400342e0702880b25040e0b000654074911501c102180540c1c2a0084d26059090406500c520351688070600c040fa8a20002000502c107071625200b5542250440e456103000c8018202d159404038280402c000e06011143c5484011a1901c00240c81c0c030b1252611600b00300c1c2410003108001501030080d061140c1c0c00c02c8046400520045950115180301200994031105801d0810b13002d0a4444a046820b0000320304010800316098014030881d901603c04546422241c24200d090340305030509040803412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 788756564 1250 788755314 788755333
    0x26010c080a09051c23040b0703030203090102090a0f3002010f0207090c0306050906030f0a0213020906030a140606160b0720070f09201803070e070f0c0302 68
    0x4440d005000103c3c030034070503501c429244284200343c107140d141c4d0000008040c10503c030300d11a00c0c48440c203041c4524500540c1402e280904014082c821541c00400b0181c0100c007040605009405032000008028100000e15031680da516407026454401c0c0380c400358102c09000a84080c989200e401c1c806810140c81a0b004290015212056070544003400c51180500002e0380c00c03024402c1e4804964560f90200d50180fa103403c20260400c05428030b44a50462a0842c480c8900080d083e94565410703902d11000f0000512030000a01031800113a8100000004001840119922a80e882454032201c8101c0382c58404c10b10150f4021070f510703140b680710451601400718a21a898583c003241e2458914141c0c82130000340b20f60942e0281c0c000310b0b9648001030038440581d42812410150048480030002160040c2659003541e140407840300700e900c4001902881c030405480c00110b00403000e022a010700f0b98a810b800e540c2e840842d42c1d900010140648a002280301c0d40c1e51401441d055401030070704c0b00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 788757814 1250 788756564 788756581
    0x3080a050c0607020c0907050306011e0905031e01060e13030305090a020a030b04030f1e030207060e070305031201050f09010504020d140c0c06090115121b26010c08 72
    0x50028005505200381400341e03103200c03082000710398454881c95019000a94688050008000d0050507007024401e0500402c0510399022420035080d40c241551300d00c500b400b510094806050030b410041e058060742e49043c49095441038150b4403044900c00030051a95500d94001134440c0079560388201c0e854100314600864465040590400400400e50f54106d480750700040d100c8107a6442143c2800408081101380341e00800c0707040c0a50a641000846030010031030703c440040000205400345039001c0303111014060198886407500c1081000c8601007900ea04046980350817032072405801c9801c200001c0b900d41020303041100c01c00005840000b450f402c0104020180d00b01d20700100b10580d0300c1ca007600c60000d80f90802d900820100c1d074110f5a03205400380c0300d42008c10061141c1c42d56811300e403090702c001c0c8500b8910300c11519500e40d40048104e9902d8801034410840d0020301e0324a5040341c022541d00707888940d00c02c651032a10255222401c005182030b007a00d059290020100c1d440000040c0b081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 788759064 1250 788757814 788757817
    0x3010609150210021209010c030e0304230603090c031603080d02030406020d09080a1b0b040b270c0a0e15010e0609060409020a080f091c0912060f2003010308 69
    0x3086103005aa50311103e0304041c1c0200e8101c0c024222418444074184042440c0a00c241200b2046502c0d06001400c0c801c105190740b885648150b180c054a484440d50351049011081b050182d8020016542da05054040d5580c03001322086040c0b1a000d00480f40c100803007100b00303440441e544110454180346040040c00003c1d000140240c480315000c009001030b252840c030414941502c80d000540d00d985040000919100c0c0300750780d0900c1c404a41c402100441c2d00c0341d4240354081c0e4845c001c01415074070b20103441000960300b480426a0010400905180708000c1001040c0040c16160708a40c196a03e50f000c1c4010010340316400c0ca081b08880c206000d500c075003144041d11202420719032501000b6404590310364065480b001203940d01240140000e5403002c04036801090b650704007030b81410100040c0380c45a10881c810940d40c0451418400c2d00c81c00703030180c4001442c0d0342c0b121821242090400304060f2082d19550b08110740341500c60700b0340340741d02d800903000c0040e102e0740a41182e0940e502e59910703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 788760314 1250 788759064 788759099
    0x601030b01091d0a0f0b0106090f05100c0b0709061205070e040b0609060d09140708070e130606060215010905090a021504090203071d010504060e0409030c021f0207080303010609 78
    0x410f410078240120b070300820031200d101244078400d1000840304604000c121040b06803c51020030103988001c002c41850100c148003a194120340140c07070040001d20941701030100400041c486941e070420004010340152803241120ba41d600c4100221050f005040100d410403200745c40130900300030b100c400d1801e040d03100d0103856901030082c9290640b02000609a5000b204a22078665100d41e034040820290400d200e940d010903c00410115040200003a10b8009601a411204800b10001408610610107110846400ca44c0410445172a0b40d0000e40b24528046421742000c2010b000040d02c40e0785120b1a407081e04050080d10746903505608001d103c4c800460819650300307041c0408600500640b0045d40240e6080e140d28101c4a03400842c00318088020040381c2c1403160601c800c001258000c013540c00c1d0302c6002c40300001c01d0651031406071440d021001c4065040404081e0402c201d041d0f00002058044407502140d01280d941e0350712540d43d200c24050000098450103080000c0301720314002400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 788761564 1250 788760314 788760341
    0x1b10030b01210c021006030c050d111c020306090c100c020d051b010f0807090e0a0e06011418060a03080304150c0216080d0816020a05010e01060905090601030b0109 72
    0x20b000003407a180950203084101c15106035695415801d90310fa03010000e002200301007540a21031680b86883d4042e0825251150b0b5015400400d0582c0422080c0401d401c400c4400030038101c1901041c07000b962000300061800c0f40a40700343c1d40814403400340001e00311442c0740010031104681100010880f1074095850089070032507512304040c000600184240014504201c0e20008141402000100101005030300401070010700400c1c005a40c3d40f19480d44259000158941074075210481c0c0c041c000d101038080501c983c05504004220040300b21003030201d641080b0313155041150041030904c14610706844413940a040c582d000c200043d100c1014681c0305000700d015820b49010100102c040d1400890413000681140381c003070044142c056464030141c44403000600c0100e40b003c130302606d50180600400e20381c103164001c1502c060310070090440c65960040080c401e00782101c41c40b50103003070b0380d0007060211410440000c20390400007803450304890300611141626480c1024083c000c01441c8903005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 788762814 1250 788761564 788761577
    0x6030a150b180601170103050601061803200a0b040503030313030e1504150305010e060103240b040905090105041203020309071d0403120e100b0604170601081b10030b01 74
    0x8066a4981d00c0556940411000b9034030603250100005008000003080940080903050062000c14000500103042d90054204030080d45161480c0c0c0640030f1140d0310040000d00c2d181c010403030304107011043e0899008180c50302c5a8568580700701180c01c3c0114010560590b000b84000b680c02e40a09403086001030190410311420b18410010890b00d00da20000480c140800241c1003104401202d00600c90210a240c2080107504140284001f41c40c040d180b10704041c0caa020313080d0101450401d851070a400c4c2400401042c4d616540c984c8150003900c0740c0440c10740390400088008030103004941c816507000c1107070528400e0080056009400240260560303101e100d03804030700a16003544405103880b2802100c0c07014907292074010442011005034800290400107540d00d28180003a896901502024020170b070341c240a0b010560600840d44200d45030028241094550000032481906070b50400301a80e020216104482103144825441c0c40c0d000b14985d500e5041845c426401000617040c14540030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 788764064 1250 788762814 788762831
    0x1918020f0f0c1f1406090a060b0a03200a0c021c050a0b0a15050a0501121119140715020c030d090c0f050f031b010c060204062606030a15 60
    0x104040d000100400c80320b6005190f034104002800c0242e11030240c0141003400894002c8a01c000c01c0c1d84041c02440c05140800c000c07601e51365182c0c211201501180e40500c0c1c46800005000f00504406620720781410255400b10035140400412104100c401c0e0300c5800310101181e0902c6210781103000c1c1c0c10a61605044500001801400381e40c07500350151410503103a040590000f0708880c200e0100b40e4231a1041b900c00c212540350307045440c0865000342400c0484690210500c00138213a128200c10485c0000540164048082c10b03460440407003a43d1005174030070403001d030b14285105d00c202c086d0000c540c7c0035404078150201e4000304044550349042d03c1c100a958060042a1011500d04071000166050b0078803076040030350405d0b801000102c4001c50103003d40e50119441300103120350601035540500749901c5503401b8080c0a903660340e11541c110364480c3e440800800740d055017110042803a84e111214551000c070801d4003401404000c000d00b10800b0590f603411800d44c0d062541c03090464842242 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 788765314 1250 788764064 788764087
    0x7080c0d170c010507090909030806120c09131b2106090602030a06051504060503181501060c030f0c02030c04240b18090405030a0309030912060b1918020f 68
    0x140000e00074101c0042494100407002a00c0e040607500208112454190800e009c244d125134540d41045094900c00381c0042c0c90a030044c00e0104450869801412107010b200310158402800d502c40d600135201c024101d84620038407000032501c1cac810703030f0f410054140c886d9240080c0000a407011911030351000903000510f9440c1c000307a81044490038861a6540410006810300c5880c601c5a010f410b4441840c00d424030f00041e0040c0401360402403180c0071f0316450348005108008840070042103022245540d80e559100401e600301c4140110009242e500d040624079015540380441c0582c010003410302540c0420601000b0000030300e041d000420010060400031505040550203072441100d059982c2c2d100840f10140348203110010ba004080c83c01c200004241d0110513120b403030781103140100b0390046900381110030084030b4001d0040c4070441c040010403c08198404c0c40704040c180d0304818101000340e840b4840384607620440502c2d0424402078001c190641e802406641015154103017402c00c025203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 788766564 1250 788765314 788765317
    0x612080c010f0c11100c02120304020d02120d02010c03180b0a061802071703010e0408030709090c03020c1b0102060115090b070503032403030a0c06140a06051207080c0d17 75
    0x181480410303440c035136034184000244108034107004400707000d100042d504e00e002569024407100c070110409001c0049411550352900d42c1e000184c0040c0380c4103885044102d2a0344a654400500c000756181c5650b5542e03207800b034060750031070b2007800d103617220500380d0342c0c84005081c140200341104242e0b86140110380505111703a030a4171103c0980e801030b220001c80ca003020b030690010245203c1c41400f03100410165420b07142c2c4a900c1684070100c1c503101d8451a80a8442c0c10842d00a501814101001e000c00d15505902a08014000e0700c2203c4e90100c020080c040f401d44c1600701540141c00c010014486644140e040b80750300c248a10b0002c2a03580da4a1217010b146c1c006000490b81a080041440400d400607000380c0c01d030071601c40441c0782400030710000a07503030300c40d0600d44030074071504208a10a10031070394043e000d10300d80000549601d0be410151600204250b0107102c0c0310b8000c070f0111401c8510001035a400340c2e98060001c207080c0302c0c0e850401c642d5824441049440420070384018081091020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 788767814 1250 788766564 788766581
    0x51005060f09041115120412050705010f02090922030315080307060515030303010f2114100c0f02031b0c0d050c10050a0507031808010c02060103020907030612080c010f 74
    0x10030202d2880b03503c01c2003000300d044520070040310030780030300280140c00c031b41c5400190804d40c804504650316013010800d8540d4020000003400035445c0040c03807a1042c501d90000c104428085800b95099a1501840301a12050101d50482884e1401180c1c0000c0e00980c4030101e002100a694045a0703a03400d0421b155520021040761040c0d102c10500040c101d00c2c103021121010101d000e03609560405450202c40410381c803644241c4400000701850780c6a010303070b4007407400e03400c400c4506029802c1e1210b1039886803a0880e821141c3d01d48034003614400d105c0c0510318807141c1d46501440c0b5203002c890700e00d4450180c44d07130f644200d4003896840d200c1554a00d000364100900c610054000242580204280c1c140038800080c00c0c8801040325074803040e0300c04102c40340c02e50305040a40543d40c05111151403114550001c1180c3c0d8a0a40c480251076000a60075040320320848001ca40f030b076102e14007102600e20f40d01c07800840000780f0070304000142c2c4c01d10107400740400c0c44000140310391a007680c00003a0744024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 788769064 1250 788767814 788767823
    0x62110050d081b06060105031603021b012a1d03120a0903061116060507030e0706120609020c030a05211003111806010309030201021905121003051005060f0904 70
    0x3d070100716440140c600c0514100e00c0b00280c42d09160150002c1c0c45480010904031240b10b0250101041c3c50003030f41a903419118045900c4c821821041c90103000344100c90303680c4030320080c8622a109581076244100031612031075640200c5407900e1500141030180500d6440c0e41030042c1d040081d1182c000d000500318100b0580e613442c2003036141d030802204440030040340918692041155416052410804000c0103a10200008991b42c030394034120024402d20fa61504c05001e00b0708001001c41e0f001c054101c02c00700b10041040740d40c1c0d03243c002e08120701c07a25000c40d4607a0418443c51501a01420281c80ca50300044440c0c43c0350150102d074401129011556410303502c0640380140180100821404e6246a0a8940c81105140268018181d120040403281090b4595240f002094401c2d010784401540c2c0c94100d00f452202201e01a0298101c0d00c502d00040e24050b00160710220b8004c8100c0403241c0003400f600034002c0088100d405440010705036034010030060034110039a16400000e9120b176014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 788770314 1250 788769064 788769067
    0x3060c17150a052b21020d0c2306100f0506030613110f07050105010e0c03070c1407050d080a0e0114180d050a060b040c050408060609091e030315062110050d08 70
    0xb2401c22841780c5458583d0504640c0b00c51401c00b016a0050110044107410026800708050f09240c02207841002181d413400c0b50141005009072015121404415521890020072980703458109001c6c260000300c444651001030111108110502d80e808000d0940c000100c4525005445502c501e040c1e010745812605a95548010041d2242810f03030309803c40c2e4030003545484d40c00c004074020b03d840110100035000550603000d22501d8141080010300070580582050700c46070650a241c407841e080303c1003880204200005040d80756108141e40b2401018a604650500c041d480c0c82454804442c0ea03690340150700000b10710f0203c0c100700040740e80944251008600440380c40c0620090703070001e001c0d40381445010702c414020b1560204001c0d40c045c20640d142442e60361655803551400c040840d032130644206d2280380760101440800294072400c99007036680300165041c0b090200c98410000c5c0c0c80e0b51846204041b544215040300b5240e0402000c25040d40296103401c0003a000e00c01810040301d08180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 788771564 1250 788770314 788770343
    0x120f06270c2a0732041e0b0f030c0a0e06010e0a09020703030b1c0609080d1d0706020303071205060111061915030807030507080403060c17150a052b 65
    0x2400c00c8000c02030401c0c840d20300205030304d62040e403904032005281c1c3c20344d801d80d00304243c03469216603108107940c5080c1605542c2e640d84004114008241e0301400741e0150b4040b0501403024280010190f0030404080d00007190300e858050b82d85e4240c44040c205a04008074510712000541d81c0d881c0c010040d0195110050382c4d0b81d45131801408a84240310810300500782d10443d640c2060b1400070901c5541d0b001400401d1084030f902e80b010350351180e210350740025450712040100c20465020000c00f07602da00c0007142c421523203400701a03135a401b0407501c1e0300008074201102070441855800080e0800c1060502900942400d4030890500b641180c503c00246054518083c44c04043c1c01001070b4800c03110850405d05080d07444460381407180b40b1015080c0035002510303401f08401c040458008641000d01009890341e6201d00515880c07404482c0d19440c401c0340082000320700280c1c10540b41ea01e004024182051401062140602000c41e48101c0110404c4207140a01c5102296114082c80381e680c4001d01034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 788772814 1250 788771564 788771647
    0x3150a060914040e030901110a06020d0c09140607120e3102120703230c04030201030b03010b0307060e04060b0d06030302070e070804030806060906120f06270c 70
    0xa80c42c2c400c4603c260304000d5030104980c0d010085900d07440e8207181c000c00050340c40d2403951600300b80c01c42c02080c0501c0010000d4820903e540b0841d40c81015a6900c0c0840380e4408004100241d000c015590140040020000042c44d220400000284a007007400807180c0c0280020300d1106055000b00050314290500c01000e401185d0b10f800b00c1a81080440c02c148038003101a03c60079006020000f4517503940064036000c130442c0280501210481c2172120380e468050b0703c20a10f90040e1004a000c2400e060804440d807406000c0c00c68800009001000090300c1d150017120340718000310101c1d03040307582c9030004501c215040d4000c10442031a1003002c0785180c590300e4000c0c0b0f0458030354428602d2012103001d1044143e03100c000c1540042e0140b40282942d1940e1000600511031442e40301c1d841407000400d00c1c114507001d915a4400c14102580310944c1e50f40c032007441001000403001c100c000b00c4c0911010107254a08942d16004a190807085081880c5040300c1c403580040d0003100c04200d11b50000403130303142 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 788774064 1250 788772814 788772839
    0x33507120b030708060a0e031306030c0e0a051c08091c021003020c0304090c0e0901060215090111120411180901060f060516060b0a1e0e010b030c03150a0609 69
    0x5407400c0d030061801a00d0414103644548000c3c4c18003200c00c1d101c072181801d002040007520303101c060f5400d078611820f0361020003400030500d181c038503804075a1300403181c49a4580004224110781c000740c5065038110b40ca05807518902c50424085030350490510080751640c5510300e0380807049080c418460a5a10382c0c1c01000040c0308100d22190030035004000c002e402800c0407082d5030491b1a48400411800e10821054540031152003009030001001030002406036030000b10b044216050342c4c3c18941d5615100c1c00242a03c200341244400418100304101034241a0b03a400d0ba0703c58086c91950b042d41d949400052240c1c0071182d04040101820380a21010320030a200301030060007a40356044050b4a0500058140d0203140c1c1c0c2e00707400101e91106d8800788052600312042c8032000800c079462442c1c41710302490000c0c000302c002201d851f07070a0750f0100311301e800c0002c014140c411604103e03003035964038151035800b40d100070601e4074400c80150703100c0c4281d1155030f10710703001c0e258a440f62541300d400c1040c015000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 788775314 1250 788774064 788774081
    0x3050603060606040e090c030d1d010f0f050d02040e010f1a04060906050912010510181401050d211e170406051008070315051303350712 60
    0x81e412150501006a54140441e001c50780201001c141030b6a500d140b035070500342c5d400c030310075094059541c00300c009952001c070b0410300c005061000d50044100030011101c0f454419043d001086240743c8500c0d403140a000904141141e041000d485c103a110340042048031000ea224459881a142c0c00780300305580909404040380ba1b0b01a420b0030503107040c000402c0c4080c1842064180b180015140c007850701c41810280701581d01c10b009000b1402d240c980c1d220b00c6c1203076114a6000e940074400d021001120f902031004c2400c100c035131001e8030b0303402c00c07040155088001c44119040c015084030b43e0101d18250844000042141d210122041c000c1c605008440b41c001301c0f600100025500c58138010402009459009608a2000611035540b0010401c081d02e983e084440b0030300c90108000100100580c0d0000c0c0c0003001d100134081c6460307030343c0300c425000e140c0742005000c11a030340744200c80044044202d0213500c2c52080c601c0b0011040360b0142407290015161440010103407441186c000000d802080790 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 788776564 1250 788775314 788775319
    0x10e010b040b19091e050f0612030703021507030905070803120606091e010201060801060f080f01050903160302030f070b2a07020d020a15050d050f1b0c12160201030506 74
    0x903c0c0b801c1015201001003603001c1d136540c00d0740c0ca040000c01404030905058545500c0c9200300014141250185050541203403098030070240098030039188140032050729580c590640041125201008003c0c0c01400010120400c0603039600f828404503c00f0441800203248038005565251684079442030315200c0144414041d08040185282c6034407485070311040c0c1c41c101c0b294900f1045000c1c0040b4090110307640106815803c01902044010400c0d01503800c0791303541411202d2010782c110009003a03070300031149000c4580003808401d0484207040b84250076a4424810349203000701e600070480715504505801c1d81c140b00e00c201002400784808400b40304001030107083c0c07140c010441d0410a40c3e4484c0300ea000340241c0e002e171084011500d881c102c090290400039800d554064009000501c3e9401100000343c0d101d0410021031b81403001080380d94010740c03660380b181082030402950b1701540c0d480400d00c24211b1081481c102031902d8290040c205001c220703214a015280c06000040940313201a004a2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 788777814 1250 788776564 788776579
    0x80408071a07120b0105090409061119020f0c010f080c07080301092309060c070204060b0403080c0610030203330903090a0e060d0b090f0102030c030709080a0f0602090d05010e010b040b 81
    0x41c641c1e07007020694640100c208c2d8041100d05051800e500609a0041101000350380892018003004003419003001c07481045c0c0c01c1342e524a04e050790040d03a41c1000344043c8d0116210901c107200e05031092400a0340030001c00001407603d62990345000716a803091380b11858143c1e89030310398202c202c9802c05007240d011205414804074106030b056640c40c1c640180402c5910f000c006582d9003151241d800610003041c02d4000240c480c0e90302c1c10034443c4c2e0350110103030f14242c0c06080000361500c0103d51080c41170326005402803408005900406500c0f2000c80b080c0b8502403180030304d0001c89804020083c0c4500a181e014584402c0b002c0248103c400141c0c01c049089000b0004010b4142c0710011101c4c55590800c100130382030340395100070030304040c00c00b60710452a500010401a002418030000d41c090765650ba121800c0c6c83d9142c1000e622103032880001000c0d10b89845044011404d00d0300904a4008010401c030290102c0b5a0b17044c0c01c641444018032000e9440c0c003204d2949181c94401d03125404800d55a20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 788779064 1250 788777814 788777831
    0x60406060e0f09070e0a060b03010906170607171003061b120204051f051e04030209010b0307021f0e0a03030f18031202030a090c03080c0105180a03080408071a0712 72
    0x140c80c4c0495000307880890141500080407041e07240c01020040c01c514100d180c1e256110340440001c2c00040c0245c007a1100c1c2400140000040051214401e0306141d80e40b10340d5003502a114008400301400c01c4901850150010000c03400724420550304400006c280100c2c0352621501420759107448041401191050004005640340c0010807200301e40c00c003030016541080c030402a15107010b00780a02e054032004070304a9240c00380c0807005100740c9008030340f840000da030b031400b01100c58802164403e005812070b05200750301c20828284600c014580c1c0130082480e0300c58011280c86d101b000c100075000643c40303030070f121140b07280c82c0700c2c0c4155035400f401341c50700410103920080c00681c9800c120b0700d90b00d0760010008184450030750103140000e52004403040040e80e6800d20517050f400500301c5528079464540864100e03841c0c03c03080001407001c1006006801c89940f0161403d0f24018030665021004100c20b40000d10381c004d000303908031f5840109203503d0820000081503c05000844c040b11441d15028 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 788780314 1250 788779064 788779081
    0x14070206150406050d021c0c0b030403020f01020301030812040c0e070e19030b0402091b0d060e16080112020301060e0c1e0708070b06060c15060f01080f01060e12060406060e0f 77
    0x500100d8042d00e0171681503044681c545041c4c8030107e005015140601d5000c0307214071400380298011400f9500b120b4a118014108a00701e03c0281300082c50711004000d621451901c0c0c800b45c40e8440e00441d160700c1c00a5890340920003d0400b1078001c000500328a48403210741c0342ca0142046001c1b4120048546642160b84900301c00c40c01800c060b104504480001c0c401b05038910488541ca90360301c0c8117644580103180d504d0054441d90107005480e100c03040001d0340355403041c3c4003811044099910407109903e0800c105c2e810108800c2c060341c165407203c0000c50f05000400da098041e514580720103540c1d1200b56074030001039442041101c3c1c121810000c2c0c0f400b0600850a65160680045d40180907460b000001241d40c03268245c807000d140201c4020b4070080707050710700d054030448080d1211340f02c4087c4600111144c1c041240c1003c1c4881110006011080c07042c440319400382c4010303241642e0a841224490f1400c5400c581c11105681c9441003400740d02d9040b0101b07904001204040030700c500b0130001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 788781564 1250 788780314 788780329
    0x131e09051509040c0f060e090702030c07141512040b090a171b0604061d0a2402040506030408090f09040b04020d05191406160c03121407020615040605 66
    0x92842800d07800049010b1201901c80e050041a0705802c5e00c1109644000103801d03181c14000b494400d5862900040460f030021007220b881c0081e0310054001241040702c466000300e01040b00c90381211740d00341d45d03201605071240180951200207502544034601407070401036095008040d400c0a41003114940b00141e211440b405040b5242040c65481d003840041c2d444010307102c2d058142d0340e48103410a21081c8003003588125008440f000200952041d170f40459a5142a040030082001d429519210b0395030001d100d0200d0303d80c848a0001d85440c0c2c0d01c00010f040c54105950a41e480c0b00c00060f007200178071702428180c460107000d031506c120500c0d0940307401c000c0e40c00040000c0d00542003001414100070052201c08800c111103265610408901e042001c20b10f40c40c030081f81d195100c0e80020810649400c51610b1203109240d0310550070001d01d0b5022100031103c680c2c50209252280f03281c01c0c0070500c0540d0310b445054103600404640c80e01c808114138007440c0701c0351030303000d285895410f10054840c40c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 788782814 1250 788781564 788781601
    0x191202011514032b120e0717030c1f0b030109080403150609110c01050c162409061406010903052a21071d01120503131e0905 55
    0x5003032a99100302400860b0415440b206034800c20759060b048013041c042d4020505070b00841e00e550380d0300101d260721648011503901c0c848142555100c6502000b40800d01c04600108083c1b8405413401c001e58811500d1408004031800d140852901e40201ca003481c0754400c90788844000c4009002c01e40303254076400c609116078040641411701c04014441c50071480e410010040240320401c1061400031a00d512407501303d04204e551550a11b804174060a808806442848d40c41020b0418810484c0e51110080c07403405d03803643c2c80c081030711030f10304401d402d00e02c40c100481e0301a400103c0c0183c45218101d807411401010241808141d101c2403000c1940051703052004008800c45800604c900500d90b001c000234482038030340c010030740034414200050030f03a0740707070206a01c01044648032500c440c07140841e42c10380a0144048003011004000d000c860035407001c0018016401c1c0d81c58802d108000c0460102c05802100c00034076809841e040000b200c0010750024091b0503000c001c5820030b4010502c80c0c2c2d0058 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 788784064 1250 788782814 788782829
    0x3060f100b0904090c0905160918090309030b0903042103091a04030209040c0f120807110105070f240207020f061b070920070b190204081912020115 65
    0x11904020b9521039a2102e40315a0304112003000140c2c4c5c841901010b080210340c000208511010740d0501c01e4010500302c4152031004804070705c00e040317070b070308084c02004104426003c0018640700000401da503900780074081c0a000000e90b940340d0a2a83c1413500318408040200410007171b5220130301280d80080b1900a42e41c018680d515201007041a01c101405540c0000e940300c2a01424400ac00140300240300448160b080610700c11070b59200420f0284130084409013540c8410810315000480d00307070014030350034814144941041c0075034a13082e045980c0007004444d0110007d070100ca4010b0956181d07000300080b1441540341440b00c1c0e004c600340d2030b21000050701644000c106507042d1400450041c540144650498041720b943d040d40da0090700710219464448042c50140b00702c000308120403901070035046001c03001c03c6e8640301e074640009101d0100461301550f082c00081044841403100c00402154a0014400c010050600c51242c05a2414030402d5a02d0980000c801808401d000012103015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 788785314 1250 788784064 788784067
    0xc07021201150f0306380d0b0a020903011b120b03010204051009030c0b1305012001150305070e04120f030209030a03030203040b100803090d060e06040c0503060f100b 73
    0x100440140504a080014416020b980001103101c149055100c0c00701c901a00d8207102980b5800341c120b0302050401d40c00d4101b04201d41c6c1d01e00c0b0b00460030102c035986e207001030001080d5200b01c0c5c40e6800034003010f5451820440c1c00148200c0349103002d00480d111625800550261008180006802c4042c034850542e8029100c52000c0416507003981602c000f032002500c40070030703801d00038001400011640800c40f5883d6407508046040004203040e564195501620076500c5800c0c50010340e134071000700b44494031a8400100221001d03500b07000394002c07000c1084d50740700170030b05514216081c07500c60382100e4514a100810440031031002100c07442041030724100013502d020380c100d0443c06440748820582c0c144c8200300d00d08041550583c01944501d015660580031600d0b0741c0802c00d203c40003441510038681c800c1c40490301c94500a13070351684040c447d030300c0050b80201c4280142c3c18814125401d031040c8542c2c02c0c04000b2824113128140e802480ea000725030680c0303061889003407440968001c13030340078880 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 788786564 1250 788785314 788785339
    0x7090320010230071412091311090a0801230609010e09030f070c150e0112021309050a06031b120f03051c200a08040b130c03060e060f0c0702 62
    0x4604031250344801001d03643d940d407400d80f0f0429640c1e40714890311170481c0340304601d2107140010700e000c25a080c801d8000c202000308030302803140d400a030840108455051008000e41c40e02680c0d9500001c000b4003c100000c1464104c00403c1c130f000000205014141d1100c100c20807030190344a07241141035980c1c0c0e040d0710440d920b0ba0340413240313075000d28981c0c5030b0700307580010307400c1d040c0500d114000e0f0848d441078840d5980b002c1030080c01c45070801100b04850100750792811b000400700700c40e00548410061185014a40c0d0358958440d400c0c0c0d6800d40e255000c181d0340b0b031000e1050022601d2a00007040d2404120044240b42051a282401110002810742004225680c040520584c1200c0490310410140700e5503581901207180181200c5142410744685030a46207031481501c1d090340c00402007500c0340c455030ba42c3d9864000c2c142c1002800b0381c01d17124480d41c0c90800204030001100142d4051480010301c44100c800e61484d00c00040e10109040d83c5c2081008a09021801150020f56054891056102 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 788787814 1250 788786564 788786623
    0x90e0915101208211005190b18040b06161502070512160204050a1d0d0203040b0d06030507060210062301030e1516170105010206161106070903200102 66
    0x3071380410400103502810051000400300c9a000c2819142c049400c20750484440310103291030401c500c0f801a0080c010700942801250b440c00619100304090b102190050825000450785d51201c1d83c06407612001907100c509202000c481800706e520000720841c80c114035520348030782d075100980401e02e00c408002084a840840c009089014a81c050400d01080c20414000300181c0003035015090000b811066101c080580000c02174a0079500c1d40185d4902824104591104d0b4860043c0380041c0341c4800700000043c03402c01000300203010070740c090071041c41c15181c4007040d6007103a0300401c1d58900d10b9200408405050306142200c00003402d001603804111040a0f0038064541e480b03040fa8004001000307900100441c0b0109224050307680da10040c20800b00d012048031081c011640143d00c82000031304905582c15030001805682d08098096103100d1047da45080c20851b403810000308040410410030054a017403004d103c100c03200c0807c54400400c0000d54a0440303107458500d03150984100c4010300c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 788789064 1250 788787814 788787847
    0xa0c15020325030201050a090804090b060c0f0d02100c020613150603060e10021602091e010807090605010302161b2301020f160510090e0915101208 65
    0xc2c54001c4018405152001e032403010103645000d8003d5401d1100040d0ba0950a104c2e09006c1680f00046a0a0908150305140241a0488281c0e08400b08001e0030740090030030800d858061480c0c2c0000c3c04228404040203003844000781240364030504200c01d004c42c40d60081480c81d03200c1c50100600500b89024140301c84a0414000d40079001c52030800701200b07100d400e400030758021240301d0850301014000c4804a0481c4141c0c204c03a2014400403000100500d40f4001d82074000b00301c600010806440d48000509018080c2c3c8010441e50111504201803481d030f001e5803000340b100342003c6013400d10b04540016068aa1340e0001c016100d0b101404c0da048a800768100b0240c01ca0b41d943d04c851100c1d1078540c00303d003881c0340080e9016100c1c2d40080d550080e800281003402d400e03000c2000e41860300d05418800304003002c0e20300d10180700c85010041001032078001d4440c4115074107001410040c00f68002c17070b281d814000d07080840b0002d1541c0c1c00e001110414160390041540a40040d075241d00829054400c1d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 788790314 1250 788789064 788789077
    0xa060501090e2a1b070f0503061504020906030f07090603020f120402130222050307062c0d05100f0c0507080d0609090b01080d1b020d050705060301080307140a0c150203 74
    0x241c042104004010310340c168003698804d420480380e28540b00c410900510180344241356042c1d2200c0b00080204c4081d9981503124071002e880903040c800010005086900120780300802c10b0501d0081048259125102134004c2c00c1e5814118601040600b050344580708051003605c40040080120382191104191b030740c4000e2a2800854884003a1004800d982d82014882da080d0284110041504e25020070003004940031502c41801d071011006481c03084a00101c426400003000c41e81041d043d07251260404201841100504072468625008408030b80c0700c040f082c00ba0300e26100400c8030305074010f01102c0b20700da00090420b48601000c10355902403d41600704040c0c503410034180e5403c005494613098166242401a21340702d1402c00c504440c4140401d540041408800c101c0001504100f00405440390040c4240c82e446502c41001ca01107034003e078000b0300507500024100702403101110240003003d044002600380b9450360f40301c005448881d40540400c3e000707482484034042d030007002110030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 788791564 1250 788790314 788790391
    0x3030f2007090b19030b070e04050406050703050906010e062103040605031b0f12040609050708100b0118060503090f010e1506090609040b07091703030a060501090e 72
    0x290000e88419098036481640b0640003400c0c10000300014a241822440e050240e07141c1c181c91840c3c1c07542c0c4a150051402900d07660500121030460301864940d8014503110314001c6001144500341100d0040440d83d004044866a4001c0401440f040c8003001c0c1584d00102d0840c4c264040740c1d280080210b6002d040007801d40320384400100018060b0304500554480c15089051a50810341082c000401d4851281a14000035042250740859110000c90030342103801340000086090259440b249410340640102c80381e948899030000f203043d16800b50003406403003840c1008014045820500d81c0d84901e0040c081400804070006040380d00030481c41c0c0b1707a0a1002c0c000d0101054a600d040d49800303428002000403030741800000d04e2804c1c00010070b4011500540140c0407540e0310340307079808900c00103003149080080c04000041c40c2003100140c030381c51040c400091a40c078103190b140f8008541195005c103042c00101c030420030580717601144030b682c4014003c0c1048400c20f80640305021445c02c2401c0c0c0340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 788792814 1250 788791564 788791607
    0xa0b0f0f1204030813030e1c080d06050a0f0302010e0d02030a0512090a0e07022505131a04052419170f010e1f1515080a09080403030f 59
    0x4038141d8036440d41030045000307884000312929603290070700d691041c3c0c1070003902240d40c000b181c4202c1d09040d041c0b141090204501170249642c1681d80c00c0c00d1780d0104940c8009103031544420310240c0380901001d0010000c0f0492000c60520f103600281400030000720862003045e100064400703544040c090000c0071988001034400b46c1074040340046480d0070505000d0f004d04021040401e00c40c5440d11030b039002e0007094004160034a4143c0ea107d50140450b0303403291a155020900141a894620800180c401b00200104480d0310f00204220740100cbd00040500c00c9040c181440803040108101c020b00f2040e40c0c900702c0c28070104e034001c950f01d0b000203003242c5c2c1c44400c040000295000700301004105901ea0f041980e10401d0100c10b010f090381d030070003415400c41e002100c00200e21250b00f0b80406100b05108008600901412000d082d50341440d8443c04014180804c1c00d91801e510410456202200400401403040c0d19100d03c000c0340141d00008060140301c0c2c01a91071140910b1040d41390008044100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 788794064 1250 788792814 788792827
    0x1002030414060c030a0c0804020a0b090a03080a050d0b09010501051c021c0203060103050a090203100207030e030607031407170a090f020310060609060c12030b060706141b07020a0b0f0f 81
    0xc2800d50003105c1c0984483d1a1011070340b46c4610034003006015980003400091824203054041400d03034400000e00740d101814641c00400540c40102800101c8450345a4580303580b07035000b5090941e21000c442d580728464810062225030781110a0f18060400d401c20708025803498100301009204996440c000703c002c00120000c010f00540055214071070a036802d000c15112024114151100e005009500d03420548007000b0281080e40509005402440c000801184110209040500c1914ac00c1c00080c3c035900c81068640504000301d400038043e26000070116000101c0060111001e080d2000250b00c0b584c0450500c1000390350b122040b41c00030180c901c64103100c246c110051041d84100c8000c203203000000a00d081c019281c404800e500003440aa0040ca102c1049009011074004181d019806002140c0440c42c7c52040b4080307101003040b40c184606191000c070740100c2c40d800050912100400c00c0340c0041e01c40c0440c0c10708030340740c0391070290311100440ca04c1652400707881003950382e4040100c0c69 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 788795314 1250 788794064 788794081
    0x70c050727050402030a0b0c0d0608160f0b0a050708070206030a0608390307210606051c06091e051b010e1f091a03070f0201020903100203041406 64
    0x941c0e01c044035054800030403481e010190301078401c12500650700d900511121808a801d81c411941e20840c031500784da18094400741c4050458545030400c0c90b19510031007074448511008000140030f003050040c044241460300404c050f0a1048500340020441d002c10178000708050007003a1000d0642c000c0c00e054032403420040c0403004100781e11810700c003131054400382500054114a22141c1c1c091240c48400100c40001400ba02420007040003a0588506040043c091011030320b070204242130100000c1c1c01c0c1e88070341001ca00b500c503140c100c80d200307161110002c020b00c1c413025000c41010b6400540403c620880382007069480e100d8110a04482e84d07140c104e08100640442c1461040c0401d82d20300e002111890011030b408020100950340104805d12203031802d5045090860623060a0f00d000c1c8c211584982c60100451031b0b102240914490100501040c5600061181d4401c1010b1008500f000681d0340080c0c0d8030350724900050302055001000c2018008401540990f0029050032a0340c0303410302051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 788796564 1250 788795314 788795339
    0x150c120c0602360108090a02041e02040806040b01050906010c060509010b060429090a0e1503120a0f080f150f04090506041707050604111f02010506030d0203041805070c0507 76
    0x81c0b83e9402001450111a150f0150010b0350040444100a2040c0001d503401d1100400c1c04100e003030500c1c40400340f409101070b20703400104054400710300500400d00785032810054864040c0c01203072007a40d9060401034681d03803081071400e0305034011001080c00d480c5c011b901e50040c0081d944894101e20005004544048041e4040b6420040b92140d60b5200070b4804403003901d0f0050305180c0754040c4a1040800c0500061115103410901c510700d030302d2a0248441c0007d01d400c0c0c091100a2540101046d403103c0560000719035140f80390070341071180e686d10308800440c40b80320f0b00401c111210781e0041c6040c2d851b07440701ea0b0f0005100201078420460080b00d0306010340c0c0d680048800310b03022503028a0708007510302c40809540a055006004103107644490313a8540742201d84110103500200c80d00140003451480424076a88041d881d00000f035141040c00506042c1745d40c0c1c1100c142903510402003080f0050181855140d0302c5c10326040012a40c5810004452111242a0240061041c1800450701c407400d80c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 788797814 1250 788796564 788796637
    0x3c1b090d0c2903040f29010e010b07050a021e060301080106091b05450901050102011514210102090901050103060b0d0507110a0507150c120c0602 64
    0x3000115181c0c0b001e00035158900c5030540d10702c640d01e02440030030000b500100000155500c500e15040710000c440205500000203d00b0b02c5203640b1241300104030441c1040155405807070b040c201030385030031390b02e840d010b943c0d842030b45000340583c1b00140c9110000300c492078000e2800e8002403c207036a80d40d4034003010f40070f881140030b800710543c03a000a41d0460500c08205904062464869500700650b504002d414005100281520221740f00007980141151060110303002c4600510b032002c00c10f146080c003111b120144c1166055a00d00003807840c001800715640411241c204005001c2051504085129610aa18000b50201c0d508440c03048511064000d0090f500c03080d110000a03a81c1d560044040d40c0f002c1c450a003075a9005c00081c40100386031b800c160303444078240c10102d0003403c400d440c103881d100f6440b10580b696008000240106d40502c191241c4c15492860142c1c4503c25544a04290f011a268054188103c0300c0c0b008040082c181c055464048184900e01c03507280e8070390b8aa9001d214001c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 788799064 1250 788797814 788797829
    0x1a100c02010c17280e01020d0f020709020a26060f0402032203260118020d24081e03040e07020f0319020c18150114033c1b090d0c 57
    0x1480807a51a4802e055034410700c41705170300402d01003910030307803c0d81d2400b00844d4440841c020040701042140060000f042c8810441d48da82d054120024504003a051220902d60311010350002400001c1d500c036000c110150008407801a6241c031450001c04002a081d20180400d8080c132044000f85504150201441c41405504096420314814002443e5200f401668070b5030884512401e400b941903409420f409015010005519807201e80c2040464404080ca0500600d02841030001c102d0034410109540c6001444141429a11007000d0b00c0e0b00a0b4087c21110b50305110014001038420028035200a8044043da5561040388201d01c014148481c0744c0000f6115a404080007401e1103d0710707a501d003201036a94882a196102e10000d140302c148013060402001d00001005200c411008500968002c036407011180081d1203c807581070710b51403041c080d88035201030b0500c14001581d034403540300c10004508241468600180350140c010483e40c51f403c1900e5203014000c004841482c44141d5020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 788800314 1250 788799064 788799127
    0x50d030603020907020c01120914070f1d100b0918010e04122f03090402040b0301080105132001030e0d0201051801150b0c1f1a100c02010c17 62
    0x107a11003a85d03241010041e807130001d03072511482007123200e07558060f0443c0e134440c104840b03025941c50f40b60351501815800600e84054031101c01c0240b02e02c5102c54882c90f140802100300c6a203801c1400d8468440c2c50301c510460001c00140d0380c1812340d540505059110b49050700442107503143c4241c2892403104480c21035200c1003603019046880e0003a001641800001c1c0c3c18000007200f54614000c02e584c40d040c44120710311040c0042510b640d1980007800203002921203071070700c80d85040c10807402d46038083c2401180384080c1303070071a000c80d0b40c1200d0407202d0840100118081d040210048006010300005021240074070100f02110741d43c190001800390184604051026103c6034480b0301700e03683e160324086000a004402c2101c04c2e403000141106000c0f03c8280c2d5510702e01c020540400510f040f500d000c04550340ca02142c29102403980c81c86400d141500c010602110818000d40400f061030406814441d08005040401a480c0c00c01001c081020b100d26441d500e00707040c0d0322400094183c101446404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 788801564 1250 788800314 788800321
    0x40c09060501360b0c03030603070605030705030417040b0f07060c0509100e03010b030d0c030909060f05040504150f0b0108092103180a080a121119020307050d0306030209 75
    0x414141d601d144914100000d0000c4043c0d2800341450441c61003c407881c0f0030400001580c0d049080c06444080d5420b0051030f42d0340790400425050410360b82168050150910900049603400002d481d4007643c45849059000200e0300201418020f5900c06000503c0008000c21401894070251080e24800c0313009000e500c80075541661180240460260465511410292107504c0395050464081c005800000d0003861070340424100403210142d580461140b017524000c05510102080c000c00501d401001030905200031010300907128030890341300d070f80c4540108017030010b085c80100c3c0b0006000c1041150580840000c0c020f4040c000c592408a11860700050b88040046042440c1c05841e0350055680c820041d1220140d0b00098141d4030391000d1408404601202080f01d031524501659485484001c10400148114520801030f080503080c005c030710300707091013000c141c5000440034000b4801c88504114224958040c02e1400380a070320408884090441c0c141d44400f0990303000f503800220599 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 788802814 1250 788801564 788801567
    0xa080c091e0c07061a011b0f0b10030506010b0c0703170c070314100b09010e0c04170105060f060a0f0809240106090807062a050114190608060412031103040c09060501 73
    0x120550351781303010031210318138544280d0000007903880311441041500105c030200e0f1103014189504441c03040340001100010310a2150030451780740100b8200b03d6079880c0080f04208aa04e03084584001456884036202c0c680350280c42c07100350340c810078444044802e445c0c1c0c0c0b400c010104208001c8400020b0103403402c0b00420785014080c642401401901101959213000405881c01c10003c02800c0071020034000071502612070356204105810b100e0010641d420300d0f0040003440b9503813510b4644252410040343ca0004e4101411821807a01400d03d03075160380e42d412550b418480ca202c0d002d0000d0f080364000050528800440310b041c1c940356608c2c020744039261241a540d5014900400f004a445040306200c104120001031000100c00040e01c0c5042090382e03202820f41c0c011140d800c86485140342004554504030780c0551035144445d1003403128518118840d07450f690068409450b043c989104441d105002e600581122642007809c0c541d00e14080c10302804a445501403200c09170b0500c400040e256 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 788804064 1250 788802814 788802851
    0x16051504050a18020903070e07031a0f010e01140a1d0607170901030b060a0206060f030303011d1f0609090f02030c03130303150f030507050a080c091e0c0706 69
    0x20752001d072242101500b0000340c2007205501650b400708098080240c0c99080d01d0911080004102c00c040ca01c00034141240b0180070f46482586041c2d00740d010010401141c0d50f50ba040b074011980a00385602c801c006040100c2d0104010f0741081500c1d1000596018415031020b01810242420607241340340c01441070402c1514820010042c010607805c000b0b80407200b40070401891084414100000c00c4101140410400c2d0403601c001d0380540c020b003041040d507041c0246c1c4209542003c030085e501c0c543c1485d0041d844a68510101200340300c2400000b60711001085240300c040f1241600c01c1541691094028070301e10f52070060341d0019041c1791a1001c2001c442c02520b00031000101c406046507216016030703c0c219010041541015141e02181030369015000002e405820094413400446055085c054501155684024001c0c02c800c0c1e42041515800310741040701352000c4030b41d803566488004407002c01d95040102d05115510310400c1c80840c3c0110001010a544a0601400141038280c59810403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 788805314 1250 788804064 788804069
    0x1030603060e0c0a08030903071e1a030718031509061508061f1d09100608061515070f0507211e0210030c11010911150403080f0f0c16051504 62
    0x950b200807801e000465051502040004202041d102c00f40d07502c42f080074090041c1b50800101440000501412903488010b500041050a003a1401507240d65190039460540003e4050070590380c1000404104158024192440900b0307802000662504003e035268041a01c402031300c1410040204d8407942000e50010850344801700c0311490025032901c0101108005140300302c240030b01515400070b003419110781405002a41d00a00091510243e01c0000180028050707200302507144100103070100400c00c4500d12603203d400309503100c91034500b1518041454000040300c01d9207040c0604040c030308030110324902d0b000d0174881f003021644807509803130403248d554080d400a10070403401c85624007942041d01c28100b46e280281c07145452030011821150000001c81d584402d0204250042c035150310034a20306480006031a01e01490344c1e6420070304c3d11414510004610740403408481d21020350040d58000c100c50010f480c1d4111111807103e241203582d01480c0e200b0500c200381040307240124001d480c01e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 788806564 1250 788805314 788805319
    0xb0d06111801110a020405070c0b04050c010e0102210702030703020a091e090b0a052a0417010b012a0c0306021c1a06130b0f0a030c0302250201030603060e0c0a080309 73
    0x402c4e0180d07809100181000810034414091140040740000c2e4900446e035220340d000e2400307049101c400c02e0005040c501e020454904540c0015405d8010083c4800343d0291003074140f0003141d8840c12803011905045c041d0380040d5004502c11000940390f030b4150000c1d01c41d540703a0f000e4042d900c1080852203044503125000036068860003000505141d0290303000c2a000401d007a40784034a9031014401654100d02c07811070303020f20301010504200070308581d40c8507070012554034000d0000c0961800000c140005c085110599a24080d010101c016035007506e2031007180c1c03c222400d005030345a0070028040d500c250500c103490622002031901e038030071030b103e4000060442c108900104000340104001d94000c07651799113144405090000d40b01d405038008021800794400b50301d0700d034072a090001d001c60344141904824107004000c003040000380c009030b04444641c0910403548030556400124002d201d00e8000910603880d01d141440103040009000100100455407048990388490105840b4083c0c06421f54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 788807814 1250 788806564 788806573
    0x1b010b0312070206090a0b0301090b090c12070804080f12010302030c0102011a01030e163002060a03110903010c120b0f0901090504140d050a031b0801090b0d0611180111 74
    0x2801490502c00801707541d0030040c0407a010701c0d101c40d0340300d400b6030007070340840400f81e61400000700034104081c0382680722030300034111400c1000c034181e074000c0c0e020010205420071040f080054204940d00094801c02c0c1102041507032103404594104c466040f013800b041c2d20a201700345001d040c2d9131050280d03011140b0348840c801c0107086418015000350100100d0300c0200c0c003d18080010310f030801d9001030020442c2500c0151544040440e034030350900420940d2554046182d090b002513207c07401118441f0a841c500010503500300b04c0c2e1071105014601559505500b00801c000d01b0503031006014110040085003006040140001c0050180f00d80b61300b690000074dc90010404142582d0006070b106004011440495440003009428100c00842800206070003045034602c0540c1881410200400d800010402024000015049200c144100b001039600c0d0111b05245468800644021560020052101510308841080180c100300039040e4441341441740024250710501420082114440150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 788809064 1250 788807814 788807827
    0x121f150e012001090501021e0a05030402060304030c060c020a0c06090f05060d141018060602030316021e1c030b0d14031216020705030f030406231b010b0312 69
    0x19122100c180742584041c46900400c02c995540c20b00130030f000d0a1103000010307a00e2400070b6106030318203030446403403000d00c8040c0001b502c256000421281c220350101c4c1d12075241d0396946400c0b00d180e0a00d01c8010b14040c108000480407a8001581803010742c03040c0580b080541e11107004403203030051072159603c0781194040810640c20004001c1004014107100403c0040400d014070710344c0d01c0143d420301c8201001c40c40070803e8103145082c00c420711040782c100340085407400900968070300000e410888610400c802c0b02a94600030000186800c86104200d00c98850441c640b6481e0584440c40042400c002c8910707c880360311078800c0c554083d10041601d0405416034644544100768100c040380303507100c01c000000f007000c25010010320603160031340f8810581014060003030030803c459100c030f4081da02400124006200100c10f80d82078405510742610002d070266184024141054a0b44500da40c000551002c00900c40954006061913031001340691220b1380c00341a5200c010014011401005200c030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 788810314 1250 788809064 788809067
    0x90921160804170d08240f030715030509070506070b19090609140106030b01090b1305040b0708090f07030303050c1b030319110d020906121f150e01 65
    0x1401032000408501002684180d451044540c02074200381c5111101c1900405043ca0030420b1401066081c500041e082c18103404a051125550100d100803009200c817902541d10f0301c0e00381100b6042d004007205e000641d50350b20104040031441d40103000904100c00100140400907214080320000b0b0007051031310900f40c17079080c40b001d0b02401d0242d442c08898000c141c544803038000c400c3c1d524090480080c42184601d4182c2c0002c80410300d20b242c036411310f07500708041400d40b110581152800389020030070306100300024109800307118007030585511707000c18403040c0485000c0709441a501c5481c3c201c0151942928955252445400390025500c074403001d0001a1107504100c0d0000341e00300b03944d0302f0549041c0c1ca614810364030968102c2c15a0010007004240c0042840200d07544c82d4015003001850f481c10302010b45032060944100345140c00044a071081d4172100300300c0d41c0d0b07000344030114803041c10002e040042c00e03c9002030740c0c007600480d502c012895400310160201030210644a417415541010700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 788811564 1250 788810314 788810317
    0x609050303070b01270c021606030b030c04020a1215030b0606160609060605121c050705070905072d030b10020a0308060f13020d060b070b072318090921 67
    0x24005e900f440c0440405000c85003400341d541c0c80ca13910b40142c400f100c0c90700e2144241d00000c0e8820390030541003480c0c60010340c0b40440c0c10341040300c01303482c00760f40d6a1030030b034007a5031901030707480503102180c60120700305d003803510b1800040b06880c402c0d1704455003900c4410405c003950086000c9032007003425840507803000910f1640614032044c4100030100d42030756070748001610210030001992258128082c10601000040800e10b080300d0a814031504204040e02d82c240e070b400690043e01405650b03600415200f03030086a0003030b0000000000e0440c4106424414400d5880d03040c00c050102c3d040409000705481c007040d0807104042c441e4010521700e0740729101100d40c00da0240940d03810000c0c900c50080a40c903030100b5040c20b4800504056a030300510308845080341c000e6805120610400d1086500148251840b1504034140d403500c1e443c14051208013016100356800000c0b440040050010b4103500200b00d20341c04080201d07405425035480ba04455210215016003004c0514869502044240700a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 788812814 1250 788811564 788811599
    0x71203200106090e0c030607092d05090103120807080606190e03100c0e09061f0207122d080d0e0a0203070e0609161202280503010609050303070b01 65
    0x6001180c49691107040c0d07001c413004002d0780240f68024514504540c2001c00070769412580c3c514020490703d00c0d200c818803a0f909013aa448201064000c480c1d6004020121824040c0c8801000d104495075240341540201c2c0d40f5002100224400400040c0214000d00c42e00b0310844004e00f0302c518221a51300048003040780d200840c0c0c11f0102205901c1c070603440800c09950040c1d9075580018940d905d00c1400b600c820065824a480f40e8401c400b0043d07291600c121000e558858003900c0695840d10b542d0a03810400e280e08460b615059281c40e0000748100b9080105100c0764045e035070700224007000f8031542c0700064180040c03e901010895040e0980c01a4401c807450000070050700d4440c80d290340020b0420401394411130f001000c0344188001031800c107502a8021850004100e0700f8445800058800000400c00d0300580785d011034102c0200710144240d00d8200a0a11400c46045030240080c005400a018000000340100008107560030008105c61005400a0841c841a0701e0034100b03265155a04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 788814064 1250 788812814 788812877
    0x60a0905010e01091b082410120506070305090a170c15130b180a03080c0d020d15060e030309091f150e01090608072d050c071203 57
    0x2c1184051298003032050a000d2071213074202c1c12241103d000407210a20090704841c950b41c0040d00e2003c91081c04100c1070001e10482043c001040c0c0e01c19881c2803000030194001c03841541c042460b1420082c0c0814881c0c0700d42c45548003000b8079100d9a035000d0343c0d81702e0950001c0c01e5581446104001207840c00c080d10f0410405021103001c4600202e408004d2602030f00c16a2481c0c90003213818003000028030f0080e40c4640d0300030511201700d64105181d56103280d07860003d1300703000107036020510804a441c11580d180300ca52900313540c1c1c0d0300000c0d841c200419691210500018040c1c0d00400d203188240640c1070742c40b400a005600302800501044803080d0003a00e16025004410394054642c00c815507064000c015101159191200c50701024104c05030b000201410010600750510000380c0140042e600300009145c401c03200f80c208007500390281540038807501c80b14400d0354041c6425904c88001c145195020050b50091940c0d042c0700c840720410140c0050114417020346481341d80801e03440002400707041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 788815314 1250 788814064 788814071
    0xf151a121006260102070b130204020f0c1b090606460e0603060a06031a060c0c0102070e0405031615050411040515130e0106080f0c010f11060a090501 66
    0x319400761040354001ea01c110000e10005200301c0a110940c900800c0c10034502c8001e501d0101e00e5034030302d40345110052040702e1036a0400c2040066445a50503211440c80821240c0e641e11446810113a5410114040020860120040741c4607800c0000d5040d0041c0c80c058000c50400100c528141c10318010200852403584210221000003c40985400d5200513064160300001003c40c00082c0104c000c2c600a50040c402001441021303250000c500088528610380007032840710092400c03c1c040b20300640554017680118010881040104100c5102e00f400d800311100640d40f11104000041c04442c080d01e2030300148000c150364844a10918841441000784030913504018190104030340040d2802c0d01c00d25009801222035080034030400350004464070b0001310780d4140500250480320401c0d492003d85842b40c42424400c0025049103000e041c00c18240c8000c60702240005940c1c0b0a800d520074001110741e82c00c6181342c0c0c000e0342d1890701458903101034420360351595a408080c10a159003203e4640d80c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 788816564 1250 788815314 788815333
    0x1506010e0409051e0d0309020d030809100f0516020c0303040e1b030108060a06050303090d12050912060a0c09082e0c080403141206090604020c030301030f151a12 71
    0x18880c00d021424044d6980003c1e041d1030200b02c1c81c0549400c0b042040c9841c3c0b1400c040036a913980d03a00402c0b240e0610b4040ca860384e41d012180d05096180a03070f000d840b4104000024140300903049103100d1010f8090007005005007043c05c80e52020400045601a041004113019642981d130b1995880221944a500e40000c8541ca401459009074041c0005030401010b1101c251801d0040c00d0040c43d00314001c50078100c290000071070100003100018458090040f100400a006d001501c03500c0c40003c20400b00c3c903040c4072134203889a50403945a00080e1030008142640fa00844a10060b600608010304503200701003540404c0c29640041400619600742c050120150280280000c05649a031218402e043c2442c001d402c0c1261074850050310720b0144145140c8946806203a544590111707400862601c903440070400910a8020b80c41d205d0000000120922500c0400c00d1801ca10442840c000c852041440c8000c540c859080050f030000e01981400b01c1e0314185c80e8102409400b142a1152602d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 788817814 1250 788816564 788816573
    0x27090d1b0203120d0c091203081501020c0d03020307020f04050f0109050a0f020a0f090b0315010c0c05091006260c030603011b0f031b050307140d0c110f1506010e0409 73
    0x70410a0013020140d1114144041030f940003201d80000c05000c80114488511aa030242c11460010018201c4103500018000c041c4c2c820802c1c036072082c1001d003032500403e215050094503a1301041081e8040c045011a10950f402d191180c0c0b413061130210311260070703030b42000c83d080c000d0403016010480e05521000b45040018003440203101420194072425100e0b0311000c0b015002c05102d82c09940c1c004000d00c104440e0840c4a040c8800040d024a09103c0c0200c0c03e01d03020450b101c0742d4003c5a0484c89200421a114039411703240401c0e10070544032540001040c18400d82c107180101d1914641c9450f01000c6004500440c000c1d6410400040010600750b060b40700480007001103521500026912011208901c1d405218016404100300940a107051243c00c0190103848094242800c00108900d0914038036503481c1a0307003000540100a021207859020020031405031042d04a900e4008c1d5000c0a800c04c0c0c0c0010515000100038810384016a2000015030742350191050036a0000c2d06c4142400014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 788819064 1250 788817814 788817817
    0x24060f0201050c0c0d0f0e090a050103120c0803011202030703080a0207061d0634060204090b0d050a030c020a0b0324040e07030b1305101a030d090506071127090d1b020312 75
    0x1c049c8100000358945c03541c107020342084074101041051210a181d0400441d070301c00b04580c103503281c902d654040e14000d131020030310b08441070b0b0003d05030443c0881d00c00c80195011601800320781082c0d82d4206218000144000344120340c455840e0302c240104110710080d44520f000c0c0c0180d03160018180c50410761400e40012050740900215030603540010103000240e41481001d060341010f443d108070a440680d101c2d5559901040080d00f4480d411000600b1035032201c05040140038496095034803801c04203501d2001c002400d107068a44010005281d5031810248680144041120010f004ea14a103480c0c4050f400005082c103c44c41c0c034020320100100e042009802200f00241c500014860466a4182000c0031f10884083c440c0d00000410742c5002e51050100055940c222055980e4041d180f40ca01c0e0001c184070290b9401421180c000310035141254800c1d01c0440160410b08110740d07a0304c100d581c070b600ea240d0741e0801240751451010304016281d840300001d984003408a0380312001003100c00205 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 788820314 1250 788819064 788819071
    0xc041d0c16060507260c0d0b030307060509070e0c030f040302070b0a0504091d0d0f030b0d05150106080705160c21060b04020a0e010324060f0201050c0c0d0f0e09 71
    0x1c40e80f26002d00a485a00c000c210b10174103a1806038901c150341034400b21041d5200545154603800d4081081000b8142c564043e45800c000201102da8803031061401901514040f076440200e8015120700040725105135511910908442035150b283d030b40c94084864090320058400e500314401c0d0301d4041404030a0300700900c84031405440d0503032034a10b07290014041c0c8100c1e080c2c1402001c1c5005099600304400180181589a2400c2c04a02c181070b01c1801c030010034201c1c2a181e4400e48680b010800d100010514800440c4c0203040c03022280e0725010b040d03406a4054410100151082009270740f4010003e2016080f80d100707841e00c0700d03043d40e03c6541c011b02d1850010199100d030342c40c640d10400c10600380300d44070002000780c1d0198201510000e024141c0d0400c00030380da0501d511207103024036224111100300222220b0722038a4030345036110240100000810b1885c0000766281c08049114504203006840500e066403004144403001e1010440c2d20701052021001130102d02074000800d42e841d404010710 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 788821564 1250 788820314 788820323
    0x30f200d090f1217340605070e0a2c090f160605030604020f07020d08030601020f070b07030302070c080a08091c2013050405010c03050c041d0c16 64
    0x745038103061128418680c01d6021191001200ca40c07140014044441407920000105410340c48105030100c48400390220100303140094800c2c2049010001901c6400c0d04040c02610700b08096510b454080d141001c4104e0080e500105041041050710058a1100b24241e90308070a0804407003007150800110780b06980f0001e90f90091801003240d200200031241c110301040e030616076581e00d084000f500034400984407038065034001801107640d01c104c1003243c0c005640648040300207031240c285407509400c203442190043c0145443e8000c01c01e40018582c0641c0c4171a60705c01c2c54407005540560007980b001604540c1c10040f4080060b041d64248481c4008901459001d90f9403102401000884c10003658542c1e03e1500b95003021000c00d02e80c000d0700c4414210316080681c4020001c0008040350b09013240100c01508101c200070030068190400901326415032420700003138a4020301d14510713011340d0046550400d020440241c080d810040c40f6504121003c03621464004084d02d00f04090000302800d58 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 788822814 1250 788821564 788821577
    0x11090702011512050c03030418050a06080f060f01050a0e01150201090c0b07051e031e0d0c110c0f1e0a05100c050f010b030723060304050604030912030f200d 69
    0x42c004240409018404211b000e589040e0074181202c041d0070714400c00720422581e42000034181d24107a40400e010300b50312012030307102090084504e56202000c445264100c28420000119400c10445446c10b480f0100c1242c240381e82424400c01d0b010501039407a404640d260181940030500d412400c80281c0741047c0d40680e90b10250034041c0c0303443c0303600c1d08090090740e03d489141a148004025206800f000384a00c1d1050500b80407041c1283c01440030080360a444c0c07111842509410546804190402100752040a82c45204208150400184164020686030204000040d95844c50050490000c1c0000003003621180070840700c066844040005c5400701e07071050300b403003010401c41c003042240800901110032550003094480c4c246d40315542c20b4200f218008281d0030f030100785c2c00082440180401d40c803450541000c03950303106d0a0728141d01186071082c2c007150010400410b90212034141d00c03000030b03010ba103600c11641d464400c0007a02c0504c0c0b130440050840f420620044001c10825501c0d80d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 788824064 1250 788822814 788822849
    0x307050307030e160e0703060f0906080705090c072a060c0b0f04050d0c1103010c05091005040609050f0103090506070228020904081b070e040c05010c110907020115 72
    0x207000c8071410030f03241c0940d510220340340000d8204185800c043ea10070103d040040d841d0098250081c1c10207030442a2445031030600452240c0c090360101003100c4d115002c40380da02d907440f824040721110035100320190034000c20814010408080f40d00580084030101c2080d8500006040c51203880d960f00288002060180c0d100240262002c038940c000c540c0807900c400504065480c980e071141c02103c2e030000d0090484a010a00125400c03218500801500a02c0281c465800c010155408403a402e40700b40200c020406c00288140d080d00c09660191703c0d50301c211402d100401c02d0000340501614100340d1687c0c50000000c1c014003810340551074640007005008007138031121803da02258855a0551540b002c0000560381e0080c040e40c1043d04180070342d940f11150740c0c0c0885c00c030241c40c807101d82512420500081121a01c044144103a000d80401781d06035440d8801100c000c444000080c10068941103580c03c1c51603d03000140e0860001d000000e64502d00c248107800d00e03515688a0700380b00c900314124 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 788825314 1250 788824064 788824067
    0x112a030406020c130b011d030a17030610051c0914100902040509150f09010902090709080c2715040f0e06010501030c050d050402220506150903071a040b0307050307 72
    0x160555244c129606028510181c0002040350551520958180c58600d20742005a1414008855426045039601440f498440c0038070007070303030701c10354049020b08002044680040c0c8500e05130ac003032003214201011071040040444014003511841503407030b17800d03082150500c00d00402020502440d42040850411182c1c010403048900c024415a079a8200d00c100306240e90040030081d62121904e1182d00458a45400247c0100300400c0b000350003810803c1401003003a00308040004885800b02240e0094101c0000d00c882c100740e0b844214091071109498481c240591001c0b42da11007029003170186482c0c0c00b60005000d82e194010111030080d594039080a07050000e01c0501c4c0549000c0c201480968130502c4024414460201c0d40e1141582e00c001050031582d42c65034946105c040d00b44602e00c03000c064a00a001410305540c50b61050105520700c88804040d40e0076500000801405080303020b10303114804160411038000210303111410040440d01004036000b42d40100034035690580c80789001d400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 788826564 1250 788825314 788825329
    0x8370f0c050c12030a020c19050c150d090516090c1206050a050d330e060108030301060f0507051005010501021608030a050711030106061d04112a030406020c 69
    0x80110030414100140691054001110000080c0305400d40c3d90307a40c2c0700d25460009001e85c7d1200c03101d5006010803580303405511112400f0007401841992409078100d420442c001800c078404031141d580510600c101d0180f02c1c0c2c8030461580c090320640d044412000314a2100340147d8024803116981c404580a10300e40c8010101e50010b500c10003080800c0c02c01c03000440c001018410030703215a031140300c1c160402c1041ca14060011210602e8507080a0403445031010200085d10b4a120007864015000001e1500054840c12541d181c4082c42c41c513424000119514040c0311064000e03c0810000c4000048042004030020b0a0840c40003600c0d50422000a080c40d002e290804000c1504100c01e000c06034004c01152643c0d800c9003400c0780e561040307140c202800c3c0b9a804041e5811b510300303900010680d401030b1407016019420380c1603010000500041204a4122000c40c2242d00710078485840d40c2d12440c0680f010500880c405c03641140f000c0c8425518650050b00301d080144c1100100c10400e090000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 788827814 1250 788826564 788826581
    0x40e0103020d110a0b0408161404020903120a0509040e0a1211010905060a020c0708120f0313081308100c090302040c020f0f010c03110a0e10120908090f040b0108370f 73
    0x20468860359127011401030761100e400c00352a00c0340f036001403c4109903400b0410124010521a012901c88400b8480078086e508002d03e903d000e6401d00d98070b14100400850006022540441d642d948900810740032140c0e445001522011907596440c0c80010410400c04c5c00c0c402c09400d030001da50f038940d0610f62803c2c0899035011a40c250f0048000401c41d1345400251500c3c44336401c0910b880f030342c441c0c007500f84030908002c02500f02c16002844c9030b2030780840c103100c80980720035504440341d61000103403040071518030483e140000b6680c0311080c001454183c0103641410403030310480c0c1c1c040740111b1b0300300d0400c01c0b524490881a91b4803818004400e4040c0140d0108d032056244032810106400e60140c020150002018401c1a14551415216004614102c40c014400710100003101d15481e0800c0c0c0d96003c1c0c082d01f84a0454005840300f10311700750060701c082c0e92042c0c4d24060282c50340c080a6400880010001d0651683d00303620f140100f04c00502c02c3c011040d40180417501403103a1203044100d5030040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 788829064 1250 788827814 788827843
    0x6040204080f030c210a0f030209090a09030f0516020d06020f030c031503030f0403140718060905130c12030e030105040c05190608060111030408030c01090309080102040e0103020d110a0b0408 84
    0x1403240e800440801780541e40d1410090900104029900c64120004c0c400c4540150b403004039282404000d074038591044040034400e4403160809071000c9425101d500440c0c49030766800c01c0d003072030407401424515200c1503c00c6c031499015061102d050800481c98108070381a0100304000f00400c0a4114940117005409205801541c60035048445540251045020250003500901100910801d0070070003807000309000c102c8918a030818890102c090034440c421403550303d0910001c02d521141c208103040399184e20007400c41c8a03510b4010a041c40101995040e41400705400c0d9500854800707006442c8a00e12614440542d1820001080342c01c004004001514008041c001d0200c03640281030345822140900f030140283c139106001c0c502e1481990004603181c0404150041c1e6458150040c02002d4800c1c0c0380e03c16040c0c0c681d00824200d000b240b1034140c08160410040000d0308080f0348021415008000c411102080c60010072100d404e16070002c4840a40042d0400c4000d81c00c0c4045c40040c00507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 788830314 1250 788829064 788829103
    0x1021c05031b030c0909180a05070602010c090f1703120408041802030f1506070c0902040608090a050607030c05040803031305011b09030b0c0c060c071a16030506040204080f030c 78
    0x10f6201ca0440c2d00449005c00c1c0107150b1030b004241c1c004030b44803c80b0542030500e0212a05032445107800764841340a407089002660a000140c454140a2041002600c24107521020014034000c2c0b41c01c500079000e2091101c9010810508251181451035544520700a1035103641e168980f80b0030100d4801d0180301403030003a10510900284c0c0e1105024240c00c0003900182c3c0a010302d1200000e440c41c40366520042020a00e1180000c1883c00c3c0e401a2084508980f20800155507101c1e0f40c5445111001d4000e25179045a000101d85034003aa03c00d0483c0700c03080c0f5101e410213454417031292455105541240d201d45500101804010b0240580fa03070012291030f044083e060b0010001c2e00062540c04003c1c214040c09000410121454050320000c1808104880c403074140a894010320780e1002d541a00c2c0440f8200307405002410200d80329001d003200c6000152072252000080b40200009000e081e441502004001111681000007804442c034480155555407040e09001d450041d0504000445000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 788831564 1250 788830314 788830321
    0xb030709060308070b0711100e1219050c0304150e040b06041802031b04060f0e01091a0a0201060503010c09051e0102071214010c0e091b041401021c05031b03 69
    0x340502a01d00d01070380005170107483c2d242e21009607406042d203a0014064170400c9403200b941c01e043c0e08a1103101c02ca0300c055525220103100f0b2403178030344a02048200340b501d000c05a1503001c0d124500500d01250090f05980c10036403181e040b10072084014002e60000ba060410400c15840c1c18801c100005800b100c5940c43c181c5058441c80750074404910302d41c1d001e03501100041001c158400b0380a444298601242d9841d612000007a088242e02d000300c8000941000e607099555010b42813400544161a051403941c48119640d0508c6500c442c4001e011035407070b031a0014968400340201110031801e92a4100c0c0c0908202c05c1c004148103090aa4101e00b207103202c0200d5598011400710b003600c80e00c100100000340c80d4180841d25081d107070001000c66103490400c01482d0350285800100260844496245890790005001e00c1c1d00a09641c0080c0d80301000100402601400b14426441040c0152840d03021a44d11010001c2c40d400134800203d0303000010401c403004040d00c0b03e008a281c41004504508 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 788832814 1250 788831564 788831573
    0x5031c020610150e010207050d0606170c0a2114101113030b040f0c0603060303080610140c01110c0607020d08010f050d0f05010c020d02071a0304080307051603030b0307090603 77
    0x3c5205181d07051194282d80504143d02c2030007040e010f000041c0045540481604e480f0008202510030100c0d4948444100c1100000c0420010140d2100900b003c4005080a442e0090310302094005c00070326000c0418040001c0008a80c0111030030400c000d4400c00788140c0d50403003aa000c0d1a0804100c54040141007010030480011070152504801d10701d1159480d03203030000342005014009804481c0702d42c0d001132003603416086942540e120740c0c0d40a8040d110780c3d0a020510400ca0056000706c0c00c0c154003a160f071150f031006041210220701c004030b00c85200b90112041544000340c0343c201c1e600f000c01040041501000350701d903d84079501d0025115031400c00b0541c400740050041134416a208842c00d400c1c0031030201030f84d030786940001c02009101c038200c038007968032041c3c5c1c8482c0015001d40c41c000100600d5003440115442070181710146165070340d541c5c141d0185e000030000818000c0a1090f0101c05000e030b104046098441d0b18001144404241050b290403002c2c0d0003090401d003070040610015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 788834064 1250 788832814 788832839
    0xf030702031e070503070e060a0b040b031501180906141909020a0e06040b070606080c01020d030908070c080a063909320402210a0605031c020610 64
    0x8522240a200001c116849810141c8a5110543c140b1560001203907503511000004d016150440da280c3d0500c1d0785258041a501a90cc50720205600a2000030700407140301e10080c4121005150942a04603111580c4807821050f0304501c001c00c0e542c2409000001404104040c0c022044485030403001200c6850b421048050040000c6140c0208880c000c19001c2d040144a040005048640b26520340106940680045e8401c0d520a402e06100003441640030071101c00940c0b040c1e0203000d02c0e0340410000d40142c0b040510840b4079040410210010031101c00482024061007005400d810040b42890800c2c1c030040030302c1e04d6158118000c10507030111045258014445001d0a2884403025035409030707138400e16544108039200c0306400002c45148045c050b4181c0803001045820000307405414002280111a503240424804c0c4003c1d001c050402a40380358001e2040321b01041017512035000c642040f02841d810080f41d2100c401010040b03405100d43c95102d4129a0380384d0780305140c000d00100c5d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 788835314 1250 788834064 788834083
    0x7141309062123100516140a1b06050a0603050f06101710050903041e0b03180708010912080109150501050f130b0405150406050403120507120e01020f03070203 70
    0x142801a501d4452800307260110b006a42000425500000c0084194030098541107070080c00d11012010186d076058058030155000c0d204c80d000042c1003030480d010954005090021482000d076819140400040150181902c134600c6224045243e07841c40c03038842c1c07800341d01100c0b007010fa030001020045294803002ca08801c5813401841c03035800c032502407851410507448425007208541050100820004004001c008071101d6244c8086240038102c92a24104840c2c0a00003026404001068400a0030200903595042502c140d81d84155208461800c445c5084000caa800d2820500441c0d1503400002242c0189280941448442100b03212040089124000c02e814400003080701c00300c8501903810389840d955503040259419468090203403043e002445224403810b031010aa841250040050301d080b1000d41d152641014215981c400c0342c01c4640350540c0c01c0101c20f228440c0450f6500c52080741d08034064884460319060003000900f0310304000080307c030f107270b00c10002c140c01620005510801d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 788836564 1250 788835314 788835323
    0x80f06180a0b1803210601020f031602040b0d150605120613030302090d0506010305010c0e031b0415090207060f0c020c090a18050d0806010c030c0b071413090621 71
    0xb0a65a80c14040b40c50301d4602e800302d0502c0c4804a903070604060110500c0421089401c1102000d46e1620012a50b4618000e20320b52150028050390152401ca41c8140715124070080010890004c0200452240d1900c0c1c1c60076204508001c1500d8480c0b4400d03ca1b41001c0c0400343c0700034406d200c000100310b59036000906500400c03032a55100d1010f05209905132407000c40c004085801f000307140d0500e40d660328802e01094030036520304200d03011140d0141c465090048070142c060142c10075542c0b6091b16254000c1c00701278000340c403100d480d0000500300c20100701078404c03a107005031a00d00a051036011a404c80e1009c0c03007164a002500030481d5000941c48050784c80131900404103540b08810040074180469404041b6a01410040208003000c2805000a00700b507480003402d517122001154440065070004d0b002c242d0b044200300200700c1504515500c9041c6041450820490300580c0945a200201462862103043c0b0f00340700400340783c000c140040021071081d04001c0040d91003a034591a08000081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 788837814 1250 788836564 788836583
    0x509060a0c0c05040614040e030c12130b2709040507270603030302071203060f1a160507060320031810141605030403090605180307080f06180a 63
    0x60802200c040b010303000c0c0c0000342043c4505035036000070040407070642400621a43c1041c1c581c08010200000b41c44040c0d42600c0204845403614518a000340e0152032104c05a143c84940400c0e408610300c002d090003883e10385600400d10300c0703c0c2c4030300201d8070780d0700f4407407092010302c1c103001c0132078000114401130344c80040c008104d060030b41800c14860b11084007a904c100f800c020340001810340590240100c0d5008049040002c0ca0382c040c1107003250441d024101101e0380c128014007040b550507090107405e05210040c2850f054111101030322600f141071045407154043c100c1441001d07494003c2c0c1042c08102141c0c18a109004d010858050000400003144d105c03854000f0b151340c800030040311104070100d000c100000d04032440300c0b00301103508507290720951101c011400946403103442120700c2035030141e944482190604c039040390346a1110303402d00d030001100e0040842c15075003448080000c184d030700028450003d51310152410640c000702840e44a005030b20219180b020082102d004040c0e2000104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 788839064 1250 788837814 788837837
    0x5120105040518060f0f01081c0503070905040e1c02010204080a080c0a02221b05070201030509070f260c010207030809010c14010507110622050307060c050d0c0509060a 74
    0x81040f00d00c0504541c409104001c280201031380085e4440e8010301082d030f0210882e030b80715000c15a0710055143c103880d0480420143c08003841c0b143c4040c41e0050200d151200140340e90b0340004040d10036140c001d0b030454005100d0b00c0d102a502140324800c1002d2400294103061910085036214200e004001d8200080040e00310242d0f0014071201090980c002d0424141d00d240801c1094480c1c210110103165a1804038400e01070341043c080445c00c1d41d0307203035501840c019450340110087c1038040c205141a1064003004640180c003048070a010341120310007046200b00900c60086882417801e481c0c081038020190300c01d45641d0214104055030340002503140d17034a45d04001220098401d0f503020349598502e03c4800c0c0420010b410103070050300702d5981c00f042010721001090310b80da4143c80c0c5203080d60f42c2a00f4056104400914130307000c5402002601e0828104d516070a040e05e40707451807080000d00c0050f1069060407603100c0c07004101038510b011030800e00d00340301050043c82804807a1050111070f4504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 788840314 1250 788839064 788839081
    0x10810060c35040329010501031808190e0a0b0a14091e030c0102062211060a17091908030a0209030a03180b031302150c06160f051201050405 62
    0x10708584810b0942c07945081c06100c900e60046030010300003110b000e640120301d4021444000c5074402001c04a625200d1542d00e40700041d00100b14007485100e0071030200e6001c001050703114014020003030400581011680c81c10b4401416150071100c120f10800c10b4100030b01640b203080d000e0703505013100e44c00c1c81200180e5140c1c550841c0e0240d1750100f644042031088008009200c058441c02201080d0201d0394840c483c00010fa80360ba504640d100741e61400e0241c40b1018240c42403105914074000d5000e449402102c0c004903190b603005c40340e0f242c0440c413211425407403040b11030318281d0f000c40d400300900503240710343d011a0045001900701505010020011680000c650350450f032019000400300c0710061014034016150180d1004001254042c0e884000b800030314500c2140c0c400c1c00c2126280c194180c450b07080103018030301d0804126019400740312000001d98100200c2d401203080b001070f8404a1100c0c04001e15804400c51044200702c4103118802002c22541d40c014159001101c001c10103550b41443c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 788841564 1250 788840314 788840363
    0x6010e0a03080901051b010e150a020a020a060218040213240203030f041e050a0b0c0703210603021c051002121b160c050307060f05030c070629010810060c 68
    0x80d6800e20307510f04003075020007200c0003954256503980c0450500d510f5550b8400d80ac202d005030070000c0c02503044104200000341941c0d00411144405c2e002041000303c00b0008941240c00c4440c3c90503e041e002d08040c02041c1d4240c11881602000420403106c1c03a02e2040d00031f44030f00018100105444c1440040ba04002c00440d0742036070715000e1011185103010a043c15a40c4000c41c00301070719945215004a8002a45903003100c1505406455040f50b880034642c40702440d03248802100c5c1c03801da840d140400140d55540307020440302104011060a01c0302030600c582095107904600106902c1001040319049805404990003805010305013189090b182d20142c0c10f20030307908030840b00e20030301601d24200302c1c0406c3c40c141941c3c81a81124000d0351a000155a4003090750052000718006100084102001400034040d603482958046400a68201c2410305003d8030720745a9901c12100c1c10325955560b102d8055a8004107481e40e144030503280280140002c8100301015081151000d0380811610141e00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 788842814 1250 788841564 788841607
    0xa0f050c060304030507060c110a0b04051507090f1215090c031b030b06030303071e26090c0f0901060c0503130306150909120503090a0f0b06010e0a0308090105 70
    0x24840ca42da0b1400780b50007170050740089400c60303e0a10304a17816051520070385c840e40c41c0301510340091826038095202c0c1c0d8085000207108031000d20400c07100688100e100014540610b0702616500c4016041c200d500e1804c402c03e070008084400f080c103c0501150703240240c4030381011602d01c005114521170409080c0702d401c40d0405130640e041010007103500180b01800310107ca0203007142c0191a11460b08142e241d20003a5148800501d502e2441c1d010b055600c84084030103a9a41402c2d03a81c2d00c10100032000500728610b226208060240400850b0390003407003103040b4408100c0344291000d11800001e402d41006024020400c2000500002040307010403c5038441e010f9120140b10076a580d01e0604060013a400c070588085003920800030700000c5078041d200c010ba6200c00c0c0300d003818007100c104659035040107044ac50244214030b00c0d000401d0079590403084c1503000e41085a018600000090400341001c00154091040c4810400104081600b0b944580c14246031169907892200652a040044039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 788844064 1250 788842814 788842819
    0x2090f0114090d200406080307060c18080d090501210c020106170606030f0604120807090b0d0b030c12030d020d02040305060711010c0305150d03111002030a0b120a0f050c 75
    0x6180f204284018103001080180713485160f40071030744291041c001039622921800c50254014000400016110b402c40030786840207182c8250410824001c40c1c108222070340c420901d03a003003803c0d44040c1552000c03605c00a00001e0030900c1e0001420300315001901d2100090a103215550045c50200714400e403c0302009240e0200e060413100707800c191503901c9002c1a40c80c0c601c68800c026136000700e0307600031075068800c83c2c000c03510384580a140201507500b01c0c4002e01030b50401c07105920204031042c610300a04000c6002072400030f0101410310925203094080e00c3c40c4c40c81800c0494818019007000400c035500441200342c0540c441d0080da00d000d0203030169400060040c0170f444104011036074010080418904101b00034402c1c0c0716600401d5041f544c4c10760b0754019450f104414051241441071250030f00174460303d0203040c3c00b1040b001c04c504044248034038104050b00002844016022400381d145060f00456005031480c0c500f0905a650780c50100000b08110001c2e0020300600005009004007880301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 788845314 1250 788844064 788844079
    0x50c0714090108150c030601051204140615130b06040306060303080f011d060d050a08160c0b03090c090a06050603040f060f051017031303030503041502090f011409 72
    0x2900c140c8680816201000c0340100781080001410010010b1180034120303a401310b0310226250514441550b502c0182610305000701080f007400101d903881c02107441180507612064107818038040d00303420094080c00c422a03400c1c1810702020785c1c0d41d82503c0115074804201000820b2440031020030010b004942c005010301c5c6c54940300009041d0046000c0e0b00c07441440a40c54800c0e03032a03e03403003540e881c0c201c1060302050000c1000180542420010801c0580c0034104071220101c440c2c3c4c541000f6403041e081003107900b40f40c100a400700044010220040e0000c83d19090440c5404154195154294241c2602c1100381001254940d015907000b000940385c00382540343c7c2e0b0301d0103084c400001e54070507000b00c0d03d503450110002d20440440c420b00d40209a1440c460140c0703454000ca5481e0f185c1e02d03041411a5000400083d446103042009d80030041d8400e0300d555469142c0303030420103264015040d00e0174840d401000606420303070b00c202d0060f01011003400c0c400f100440304001800c0a00480034515040b860 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 788846564 1250 788845314 788845319
    0xe0d080c10020403030c060e1e1b0102031206040b0d050106030c0f052d04020903070e0609070504060207151713060e07060509062d0c0706141207050c07 67
    0x400002000d506451008a40c00030350aa201001244654407000e80003a4161000340000307522508000311070084d0404440104665864050101d072014440b00c003e9442101e40c60002c90340c8940300b505030f003400d002541c1051b070031900701e03d55058010003c13842603590b044400c0140c0da80b20981004260400d00801515480e45000b5580d84c41034061207000341c1c0d51030b10004d100d2424000810101d810031802a203214048500e070013085010958681d030007a000d002e0f510b11610100904d100401d00214a02c0441c280f10040c020303204400780410040000410041c000143c00207a2442103070b042020704d840c1e109580e181101d031030072810104075480040d40144440f040000701d500001030301030034041144a081d400001e9580302140706244c04940c1c14403070940c2c0c624091001d00041c81e910450036464039040c1c001e0071305407214040c1c40d041d641c00100b03001c660902e0801800010300f280303003402d10310041e501e121013009000d00c1801e4007104208000190940d8801c030203403208581607070100d034a640e8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 788847814 1250 788846564 788846573
    0x1e05070c1208040201090e0601051801140c0a1e210c120201050f0f091b03030904091a0c040509130302010626060c040f0612020405031605040c0228030e0d 68
    0xb000350340982c0007921600c404034403083c03090203103030048038140c44040ca86928605c003500641402c2c000903060007040340c90282c2e10030101008012020303815007c0d00310750400d8038119524200d0399001061500610b2007100018000c2d504d400d0822858034040c00c12101034120131100e02c80c0c0c154004040a69807055007205540540005000c2e007150f02001d542c650316145030910038103080b5180003280d400509c03404503c42194038500141c90020b019a450043c1180200f0203607000d05c402110400b03c1441c0b8501d20104d180c003017642040d00700741c1c00340c0f403e4500000a601050040c10b50720b42130b184840ca02d030405000758000c3e0000c1107054080c4108818211190b03080c218500e030010018051000040c00018105003160240d03451400544000d0b81041008c5802040d038015070030029a08007c01708030b6a41c01c0001c0c010746000020101540e42c2800d0a000c03d40344c40c0c440e6503065500510780c3e006d106003200d56280c01c030b00ba0041c07007443c1c8050506045034456980d40040b500244074030005820700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 788848920 1106 788847814 788847827
    0x301050a090302100e0a0512120106020a030e0f01030b090103210302130e061206251d010e0d0b040f020406080a050a060c030b03060a0c0908011e05070c12 68
    0x90443d0390f5031f1480e1408600d01c1c80f002c000080b40340341d080022507025034090100f40c0b01810250b050703543c010304003504116005e446284445400150760348250720085100e03100421210340c65940c0e0030b010680c9211a50b41e0244912403914a1054501170b000300d41c846000c202c80b842c07105141800c0c1101d5060040d00c2d507a840312001401c4d02d5200001c014440c01380302c0800401c1c0100221135000001c03030024510381020703c4200a203c168891140030850a0f0910070308101c0e202a4007207000680321a00007800500c1030f0702800071301083c04104020403511510a032810445151100001d540c0e80700c0e005002419544104004e90001e80e054200d440420b071070303007400b04620b440c80340003c0c10503100b145e00c041d0603035a5070200600183d010010300b00078481030000b040860400b080c000003840100e0100d4001503154004036008a1003198116445500035001c031000720304519008150 = true := by decide +kernel

theorem cover : BRFrame.Cov 788669064 788848920 := by
  have h0 := BRFrame.cov_init 788669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 788669064 ≤ n) (h2 : n < 788848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
