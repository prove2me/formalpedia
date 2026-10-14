-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1904
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:06:08.336557+00:00
-- url     : https://prove2.me/submissions/cc7a4fab-6321-404c-9194-0cd5f6a39e2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 342266187 ≤ n < 342446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 342267437 1250 342266187 342266201
    0x3020901080d05030406050c040312020105060102061e0406110f040e07120c0e010f0302130f050f0d0c1e03140f0d080105030a0605090c0406060906030e060c120702010905060a020d 79
    0x48542c02c140510400c2079401003c0300d8205402c035202050f1922081060102489039520003400a0b014000d160308090b0103400c031030700c140d4098090310311654030080008000400d8500391400421000c0005001030050f90000c920943c140303034900d040621800e2098910381c825007011850514510801407159403140e000100c450034141c0c14040843d1400001d0580e1000d49580d074180030360300c0b102030002d9200340d05543c0d0080c0402e001130017007580c4041070301c206004c901801d406134444045001c1039007410034128a541da80440e03603442440ca880043d001c95420a8000310302c07100c8401c0000301180c1d00440000b132410b2184c01814241c030b01290100d103480040c074041c60034484d8840c01001566404503090940e250000400700f1680d40e081d0002e4185940140d031107900c1817410401244142e4012020070540d11141c404010110600c0340040d900d0303000300d4003e008a10f01700b0400295542940b00b41d900301195000105042d2101d0751b440741010002c44084039041d0740401c201c071503a1440d01400c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 342268687 1250 342267437 342267449
    0x103050111090a0501030209040e1c02060a0e07120f080403120305090115050f01020a020306070e0108010905061f020309040f0e0d09030203060c0306120609101b230f04080703020901 80
    0x28a07128498010810b90301240c07144c1c5041c10380c0461000802d803a1604810901078150003a50850401c0b07e400100d51034410740581c0061250300002a0303143c98502c80e00b00c10194000c010042c072494808410710340c0c0302803001143c822080c00c41030300000756240081c0025610500e40c016800d800b80d100141118030040c104081a8144100c2d2a0020040f900d0003064070b600741e484404d0080c1c0030700142d2030400400c50094047c494041004056030303100030300c41d040b15400d0f40c030500c89980ea4040c0000350380080d00e90650180c2e840c090f1f00c49484c071061001035001e6280c0107680c141100e210015080359075001d0700c40d60450700e5003c8099012408d221085101c002c9003040c0b4065800c40c2c010030399501340106040500303040040403544940e0b030220303800c41c03400c0103800700c40d01481c100603d9504c42d0f040c801e8450135903003408509884081207002e51781c2c81400d5582c4504184179146803052002840c18100143e4880c100a000da40039171b10002070010b4000301000f880114594410700c0070640c0705902c15 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 342269937 1250 342268687 342268721
    0x105090619210c2703031b0503031e0f1b130801020c060907080f060f42010c0f0204050c0f0f12070305040c12020303091003050a05100501210209031501030501 70
    0x40c204104c5810580543c4e8041ca080441401d4111050b45110074498020b4000d20011080041134100d001031404150362a0701c0100c0c0d191a142c2c5202032803882503c0d01d0a010030014041c0e010829014050408004082d10300c81556030f80d4440b85003241c1c00b0340d00c455255000101042003045040101e04000e00340840145001d10718402581c4e2a0103001e00488101003000c8045086002c02d078150940a00990b541504411307a80c090884881003100080a17104010310686030566000c1e186180807142c01482c0300b01032516645c20403005000081c2004698a42884100740c4044e014002c2c215401c1c900007070b00d5944a08112106605c40300170a10410941407100f00800551808042c4d4100c1780f04000c480511602440041d0540c0601024a038200d8001c001110050758960406805000502410400d139100c800800411000602800c0d01242500201e030b1100f0881001041e048040010018107000072440068100008480d0100081d0b21070401030007032080a2040d070000032409158 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 342271187 1250 342269937 342269987
    0x90c0a0b0405040b0619050703090e0112030f1e090e1f12060209060706061e0b0a120e0a030c0308101202061818090106050105090619210c 61
    0x649242440340303019642c060f5448201d402a65155001610481d000c0f40c5120139a42c44994001071558000382010f070001070b460b02e000110800712501150680f80c00110080d5030f0041a2010340340390104045540c02c12a100c07242c0c03c0d825003030000d28294003406540e41d001c241d1824440c1e984200d006000440704a41003000d01110f4000d052403041114541005010500b9a506001000780521314203213070441c50010b201000c006255002c08140d4000343e64051441454071500c000000090248c803c02c00d20800208412a01401e240000c0740c4c02d1050110355616905502410010f40d40c004030080785d0f10001c8170b03080640056500c1d50286000b0507441440d40352000d6080c0c4504400d0002e402004002405668407040c4a5040d4001c1c8024000c0741080707031540241000c2190441d4084c9240d4603011020130190711a00c103c48443c007006010724144600c00501c00036010f60120400c0610000040203840584030001c1103080d506080c10000d4080c0303003e2405401c1414209a07100130b29002c0c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 342272437 1250 342271187 342271199
    0x180709320714030f04140f06100906080f0d050904020c07090903030e160e04030e2706010e01170c0403051c1d01020a1211030d06050a0b04050a03031b0b0103030206090c0a 75
    0x5a443e170243d0848034100300405030034085404c0000c0404a00d041d8011041084031075041d1003080d00032108590740400417117654120030f58581802c040e10032629001400300d065201c0c440c1000d00303581000248014903103501842403e00d06031142d40103001c016124212901410780600c900f23200007030494017401c42c2120400200305051094000d020075100c1142c00b06082c14400c080b0490540c1010b02644030341440c5421000d401c00b40700030100740080007030000400d80c0d44078505e00101000b06031034407211090089208800c4200050030110740c800e00f0b00002010a004215800790b0310320451a000a030080384000070003081d1a0410401d03e40445145101c059900107802000c15030415902802c00ca000c4004503000d5101c81c0c1d100c0240c0c40049810351107100710380d000c0812505c00300c0349000020390700c0c11402420f01036031107203503031110020504101107070140303426032504603c0c041c0e40c20302c4a0456681c800c01840a81081d001a4407200c200102d0303140411600c890824104d44244816140035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 342273687 1250 342272437 342272461
    0xc19181b0c06020d050f060306240d11030d0512010f03031209020a0305060c0a030e07030203031e090409080703081302030606040c1808010b0918070932071403 70
    0x280100c0030844000620001e001c02c030750541e1000540c898040c806403c0c02000031100320300594815100740108004070300d2082907501048503400c111198050b94a04083c100440d00b100d201094600c2e4406624421095130144580308401340242c40b10307511203000501140c02031030141c000d006074403950001440440c0c0c000024040b0b025540c4000700b40400c291003c02c41c01c00460b03000174854402e103024050001d00503809050f002c0f1a541d001c100b98620b010a0969440b21480003a425070401c00030000311903810241001c800342c404c0407e524114a5030042400c4420340300c015910003001203040d50415a10070001900540d0f81c500c8201c448080c2d0300000e864000240045104c2ca95440c0321001c068000c44414101c40201d07030a220920b580d500c40740b80a0305114080c47d2040c005980002c100c01c0d45147c0203c00a24414014030806040c200000300a00d1010310803051502800c202c9840010801d41d65210f040d842d0700718071218146808090450b07440c1c004040c907206010300810140c20048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 342274937 1250 342273687 342273731
    0x190206090a0b1e0a020a030b03010908040b0a020f03040603090b0a020a12021614060403080903070c1e09020a090608281d07122306070f020c1918 64
    0x2c240c40c401d464589004140485841c0100c03008590340c5401004040d0000da400790104c42101e450900140d0f008030201030898082c450000d0252809100c140150101d80c4054030054025004070f42441000e040c1c2107180d50440d900c00800683c4502d040c0c02000801c4190a0b04010700341c2c001d5040800902d000b07010050806500820a80d000c6030440700c410110f604045010740041c4072601b84e002c0c0408280d00c2c0c1000702d400b034002c90030550100d00160400012a001d15810650b0818200e042204c140600e03019080303810941c41e003504c004100d9001d01d1008061240b500c1d01c0c5c00004a10704200942007034401844601e08408070120310160010b4510030a10f081e508920010702a107003001116480d02e18000b9400300e6105102d00800c0c1113140c0e01c003807160fa6000d400a00032107440360f50301150503000c510041d04280c0008021541c914001d0f0031900790304844d40140c071528130790b0310302150170503024000c40c00b1b811007d0082004511042c0000541e502d00102c002e00000b001608070152001d10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 342276187 1250 342274937 342274943
    0x2b030c050306040c020c1507050105010608012301140d1a01020c030c13020409050103050703060e0c18130b070306091802030a08160b040606060201140610121506020102190206090a 79
    0x111401c1d03080e954403d008584041000500800f547c03001886003410680000b00300315941d61030540040b80d040d000c0c009141c102ca42034855410301174404000d02d4180704081030064140481d000035854409100c0000e02080c01d66030b940040c2c88912640d40140c601c0200c00b00c3c2c0c1c150341060b00003028544006c43c00701400c440a03641d5044140aaa0740c0c24000e11469122803c1507241034000300070400003040c01411240661418005942d10113000d03a100e0740a501011784c4845140b1030010104e0218411540c050100b0100c2d002c0205540c4440c00600030403540000000d03506c2400744001c42c1c10740700301c4541e0f283c0341c0c44d0484440c1c80c0c0d41c040380e9180c0c10003801800d07250010a4140303440030b400c04101d100503801100031000d401d0900c0d00b10007408450107410055400d2103104100b40040c940002e2003200024021103d041003201c007910b4105222000c0b0204586421700003404404844200f0002c0800d03600040e43d402261800c500c1d2000c0002c107807011508003400744080c490000440000c0c03150 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 342277437 1250 342276187 342276191
    0x150a06050412050f030403060e1b01080a1e0f02030105120307020a0324090f1e05060c0d02090613030215070b22020d120809030702090c030703020c2b030c05030604 72
    0x101c6418038a28003d041d808103d031313512000602004200483d0081070b44600520111003c400c82200800c6e00780481c0385840f800100c00f0000540f547d0626003006251800c0840e54072400c46013914520155007002c8d032004511600000100180d00b013041140340d080f84004080d40c1459480c0c0d00051002402c0d00c009081001003110000ba00000708829890455180d0b80400c03508440d4980966659240d883c191003010140c142440d0010440741c2d541503465004002c0c06c0596626005140550481407420315038a50a10801080780c446c24024540d0180d03610034554484e1071072041108010501c00070650340241423010f000018005145507402c84141c402c106c3c0462032075201c1d6580b00d1505080030394410116504074083c4041912442c3d4051066640c03844907070755801e800c41d503038440e1400003500245040300040300010000c003c1c58020b030051a0152038080c40c416407605d0400c059107103500121101080d01100b100300c0e49100c00e41c078000d090521540100510203002070000a2105000d55 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 342278687 1250 342277437 342277469
    0x301020f070809010e03060702100b0604180519020403050606031c050406080603120a03150609060203090d230331060c0f1403040801060f0b04031707080304030503150a060504 77
    0xe80581721407000c05038060110b89191030040d4009594039143c841c090102440e0007040519420210122001d5580e1443c0040c0060414100c50b002803e0003801c00f140c1094026803040100114001440110b0244c0010030715401c2410030542442050200c0c0d00042400340b0844201c02d401400b079500701c0741d003820203000350356600b80400d0800003241c00360010404005502c0050507016400075500d03c0c020209014050340f1400240d451030a1409200007590060010141910307002003000407a501c46c59044171400d00c28448403505040c071107051840da40010840f19034140c808550240202e002c1c064141c0c4100c00100e211f0340c0364055001da98100490100120140a40d004030f603c10301780c1c441c00200300542581034031741d00c03a0458024008994203060001800840c210702000588111301c2c1e0b207074a85803031a0380d0982c01000c0e0310201040044280a42d1740440d8545015501c11402525180e030340f07142a00b01401c40f00410a0300b6840b47d4041d030070512500c1d40c40b002391020740b290000c0c500151 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 342279937 1250 342278687 342278689
    0x1802090c040503060c0a0e090702060a020c0109060204080307051027052407090b04030b13030219050d201203060102161203260403050f0d0c0801140301020f070809 72
    0x2921840d0090b0350503210318428010340b959000d000b081681440c1d90750f0303450381c064842002038211058800600581c0154082400029150300409401d941000002a05c074000d40d10403059030803650119050350400301f210340034008d0604c002d50907489900c80c1040301160300c100e0302c180110311070041614007e41c0b541c0001001810010800b086018070a88060241d0071814000c00740070454007000001c1c2c80000c0040d0740c501c940151001c4d20341c0507a020110713569603106881c0c1002da503901601184030720111481c2032040a407043d0700090107507000d48002080c4030800740050b04001030480c020074140c1c11140d184100491880c01c05100b4048003a80c035140c800040345003150306134400300c5000036000001022449406e451414a05c291502506003004080501024882d00c07982c070400f442c0c0e100010000f130702c540b00414820004112150038866401c00e010100c90f0002044004101d2400041c815143d6803800c034030000c0000c42c02549003c2005044a00500030040010f1242d10086080740c4a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 342281187 1250 342279937 342279961
    0x305060109061d0604181505030a020603011703040f0810051305061303050912031e25061104080307020312030712090f02092809031b060e06070c0312180209 69
    0x905083e8406c1480c5500c218a280081c880c024441080710038403940080d141c00c0c0400c1e00d10000d9001000141941e04e00803040400e0302c2e001008046d640010000400c1e00000d0409410141c01703400028030410012098a60440c3d1001c1c0511a400509043d1040040c40024205d58011307004140700b0000b800f1860199013038003d1041c82c0340d002282000703202c211080080506a0000740505800f040400100c0c9903d4922a1f030000005019290301400500c06c0a0040301c51b0143c07184c0c50014859084800300d0805402640140816803c0000c440c02945020041f0f1425004040c01d880d103107041c4210080c1100030386000741112641c8556140303040c410302405c031420883e0090083ca4452401c403500220100c1c1001c0403810248807803d000c23884e400c0394414806240ea243e1034410300c15001c000c140010a40394101112400c2d15803402e0341d40e003030007030001324013821044c1c40b000c102e500d6529000d8040308100c01000812860440c0d416114080c9110807240203405441d100303080d41b03c010070700351 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 342282437 1250 342281187 342281189
    0x108210c011e0b0301150f0b03070e030a1208280902010507020d03050403170313110d140309010f1b0201031104030f0f060507050a0c06020d06050a08010203070305060109061d0604 79
    0x200445040354042c0e401d5509400c024000202140200b000d00401411a10f0080007405103850301c840608060002e2a070450040d41c10080c5810280c114588990010340b6007000404201d45151034000c0341c40c2d2040d08450b000d0b81002400440c2c204000603002c100804001e500032805541c0e4a5603445815a40114100c2e2800d46d0080c104000f507145508001e09140c0c800d11080322700102c094128181c5000d03001c07e40b03010b00155104074a9402c0e0f503842d9501868000c0020b6640031070380300001d02c0080e46090300424202041c10142d505e0f00403910024280a8100d0300100c00e2240461014125800c014030030301c2d00541c2402d0004001b41030200c509001e02850700002c01e081c1d08403020009000000307102400c3e8038440c41083c4020354403050300321400d002d1016801c0115581c0030180000130115000380000c2e0025150015809a5400016000507419488400ca42e5070002c10303c5000da90601401d540480c0c01c4c00d00080c0381d46040e00c000c1140c0102c401035020201c4441d0100c00d5603955070100e0b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 342283687 1250 342282437 342282461
    0x90e010f060e1e190e04110a0b0a02100b1c1511070f020d06020715020c1009081c020910030509010e0609210f0d02090301060501081e09031b0f060108210c01 69
    0x5e90f451809180000c20342c5007c1802c6440754100d881d000808910403404c841580105e80e01402080c091a800d0f200902010f90004d0f0740305c0b840c68060a007948008000c0d10045c0d0150440808080454040030100c8060301d0041c4031283c010850a0041003030503d0791944a5030542c0e50317048101042c10311000034003600c00014520000c4640180d889111900a040b840303032004183d50811b031702143c0900807107419520040031040c0520903040c10000826a01c500e828070410b0143c42c0c10300d5040050304d03074058036120a010a5079081442500300007407203010300f0828200020100c2c1d0509070750703a60365006018030100e001440c5034500d10030356071080169680c0058091490740c81d0070405420f00d0107508582d003098040c0d8640f082c001250762080d1002c9018401024803910fa107013044c525080d54240041c09034025100821402c08805940031000e03d42c8442840901600407142083c141000c0c1c0617408001e046d4072182c103032040c40d100c04500c02c0403259030000080e03484c8400703400240503006a440d44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 342284937 1250 342283687 342283709
    0x6050a0b09130e07030302061f06120f0501060201061d060306060607060905010914061b0405010f1809020c07090605031221010303110c03070b070210090e010f060e1e19 74
    0x1c210f110000107401042e24820b40980d001907030307101d80559280c091254070924106407035100300001c3c3c0c0949045400d0f50800720000c1100070000c9918000d48200f0303031105005039900c82c030401180101c2110030f07000c00c40b0001c01c648181806400299148406803e80d885003500159900c00c01400c6d0303005130211a80300d4001e1104480c9820031200720b40c50ba10020070240150380005071a004040030140d60007428100f8141000d08120044960f841010603200034012401c1540ca120082590001c0048c181c05001594880d18540c00c0d0b400c2204543c09410f100781003040c00e10040d40d01003451104a8000c410702900d80000e810078420b20303003661105844a001000010090542c0143c1c00c0320350425210403a44d6a8200000b8550b4a0400344986c1011600c01e0280d0f40c014600f09110708011649807419030100c513202c1c81450301c0e00314203a010040910346c52000308407050304001190601c040c22182c10800ca40811202d05808004407500b610030a1450f68810340c0e07494a82141d4060100581c034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 342286187 1250 342284937 342284951
    0x20a091503050f0c0313140a0c150e0a0602100203270606030115030f291509010b03070e0415180203090f0601081203070e1503060f0406050a0b0913 65
    0xd0010a0b0599028103110458400120001001c030112406a050002c0c10317803280306251601408200c15140320391081c001c908990340820032507400d107006002407000303a048210008034054021701d202181c076030060440780410400c558021a840c2448444100c0150766a9100422415000c01e09084d401c0943c0d04038203039465034030001076041d04c115415002000740500560048c0c028000300e02c00189815032121440c8000703840104110440c100c1202200c01c101032400342c4d4201711004031907000481d5000c0100c0100d40c90f05086180c0103090082420b40f6605041e0303c01844040d804480d540a0b03078480d00076020000d4480501130003800034000c8802d1003442d24410700701035401510300d00040c1c86050305000d1079010202c1d60710704031090b00d0010044108840842603007500000c0c12101400380850200f00940c40d00001c81401c0c080e09882e0300d80d030380380010803c502d00c141101494011854010288502c0c0c441ca949201622034900c80186c985d000d07440007500c1c0255404003402c40c2414100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 342287437 1250 342286187 342286229
    0x1c14070501091505010b0406050c070e0405030307081e06010507170409020d05011a1606150608071b030207210816170c07090b030309030d020c01030b01030618020a09 73
    0x10003504580e201d500120024480c0c40050f005a400a00450302c243c8000c000421840c1d010f000200503111700241030741d00f00c5030b42d042c5070014040102c4060747c17903400020401c4403480d4050555a07212855120310350b072507001d00d10160b055820051206d41030010001d1408107000102407442d5400d04121421542c036500c51840002a4014115000e105410f05002042c264400020300008400202c06a4148100840295040000c9520a840031070b07440c200d64241c2c504540000c0007070443c0341c5034410b107810000d60062408560355080000040d0416a40c80000e0307000c0740400c11640c8400722400101c2c240001d5074181ca0b0401f030002d29074040091300b052046942070610502030f0140d01c0341000d85000f0b03214019144101c034404109504040e134240414201c951040c5440c501c0039044030f0501171400080703481e14502c0d04a44000d80d100300084c50f110b40c0d050040d00355008003031a0034442e00b441c10760000040c180310350044040b41e4022803240101071064050300c00411004811500c0d0003a211 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 342288687 1250 342287437 342287441
    0x1030f031806020c10030b0603060415090501030305270123120a06050f1909020a1b030c0b070c02061801020f07031101080106030e0c0108060f062b0606021c14070501 73
    0xc4e00501909a9940c0079440c640203200c0c05d4000314010307150034690764910f0100030040c030396071080c0380c581c80380d41e0004950300f0050f1158034061362003501c0d1184d4600c0e4550b504a2a455010f40e00044c1ca64550f602d0005030b41d109646c24002c0321081c4051106900b1543d0380c507070740e01405810040c2c0e00e41c800e01300510507001d0382080d42222030507201080d00602c0b0308140310724004c80c66112002601c092204002e0030341154020000304c0300610b803210310a60b1164240501941d0120243d00140c0354691003010311410812407500b0010038248404200096804581140140d83c0d082a42e400a80f5034004242d00034800070091460941c1a514078584070b02d08048800445801c503030005035001c0000c82c0140c000c0c4142c10304101010000c20014000b2030044500000050056801c0401c510714800c0c551590300242c28003030211551004881c03020034080711f01d400669818010182084030070404a50041103404000281404401c490159a1000da4040e8070800c0d0141c0f01c2800010704100344034041d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 342289937 1250 342288687 342288703
    0x170913090525180c050f072f04110c0d0e030f060106050a08010501050702130903230d1b0e010804210807110c0907182c09070e01030f03180602 63
    0x28480602200c4011010800f184c03031285510380070420400409821106a80c042c100c024450707000f545004000078400724100740f6000f042c0c1203090701c41c07a889099151600400031142e614000700d0342450b11321a0010ba40c1c0380103c884400384180c801c0c461b4019203003409100201078058003181c20550b5502d500901c1c0e40e004c004140000b0300810700110b0030398800da048072603981c0c004010880701040311004900501d082c0f4012000d01080030100b6010380404112600802c3c0c0c40307034400781c50b452040300980c1941c4401085150b000240301e081003c1d00e8004200e50070400082c80d0a0322142e0300c1e442c0c4a601003204006407000001000c006203906a440900c403803150005558400c00313030246c07000682d92000010041e907808200e0600203040c4074420844802812040104100f046655000040c0301c0b4803164141c0d0100c0c2000740e200842505003890294000c00c14100070700d5500e20300601d480320502d040c000141001c600340b07120720a0512034201c05070100c1a03281003d580d40e56031980030750b0350440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 342291187 1250 342289937 342289949
    0x1121b0e030d08040807060c050d06060306080f120d0519090804060e030a050607050901020a08040b0403021c0809061b03030709080f030a09170a1e170913090525 71
    0x1542d10204205446090300600840e801034005040c80010b030740b03a60151807541d44000420406208a1007081c04078018440103007082e490003c0d03800d0501c4825402c0c590070180044041c5e1000d0010440030004200300c810801e034501c1b00040c56202c4460140044030200002219241040220028041c2c400300410803941c160b1265a03440151741c0501d83c0752041d052002d02103030000000559020700520041c4055001441901c5403224075944500301da800c2500101621940820148210300300b40c54108510f06001030f154064120683c0d9041981c802c40e403035075001d4600460784404010012800f41c000c8030714282525240c2c900f205000700940014400c1441c0d1707214010b1000ba0000c1c020003182c2808038980e4030042000d0805401e6a4070700d100e01d6800f0410702c00c2000010203c0d1702e603181100b540384141e500c0c6141c1100c03400c041941d02ea040b03083c51802d2104100c4c6100c6d03070b52200c0d090246141405004184c141c054240541800c140400d4801d000f010102410100702c0658544800d60324 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 342292437 1250 342291187 342291193
    0xf0a03020612011e140d03091707031e0210050d1e020705060115120e03040815010618050a090906110309010b091e04030c0f05070e0a0c0309080901121b0e03 69
    0x1340c54103070b42c41d07081c2e28440c1ca501900307a0707a0028058180790300900604ca0007070506603421565888402444102000d06414a4011010620070006e880f68800714102400c00c108110214507000607038010780ca554200c06201c1c0000f07142000d80803a80040800011140d14905180b0000c201c0e038021f54883d2900b00c50314065800003040c0b8903070183d20000365404c1640d0f030400d51000081030800800c4034840e641e1052206100010324000100400c2c4610783d030010f440035043d4503258000e07101c070740040d41c20044484808002d02190325140640f404590301d01c44042a40d00b80360802d04000c20140b0a8804000800002c001c11090150803615640710140e8962400740d58200741e500600400494044195140e500403401280c1b0605520204a02900d1070301001c0c142e0b0755910340303070180a42c012900180c298003003000b0720300144580b001c1c52403182024850140c6903510140719101c0d04141c103041c407080080e0300d05443c00c00e17882403410314101c2140082c4c840c2c2d2114081c04010764042c08610030300c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 342293687 1250 342292437 342292469
    0x180b03060c04050f090c1603020102040905090d090815360c0f06070506010501230d050105092a13091109040b0d0309090f0b0405130302070902090a03020f0a0302061201 74
    0x7051171001984151403c28125003070641d58401c00000340b00e03410040c2c04642d000d000108d0801081d1049501840c031840007400c60f00720b40d01c4090011507443e40460020340014203204040d4403d151041d520680703005015400010402041d13052200307101c568803001000308500da0303000000043c2286107207011502c10b6408000380e02003080303901c030700b920003070658100800410207540a607508070341c10f154405000401c4110381c000070742c25030010004041d403203841e02c0041080d8101000305c0381d0413812400340034400d0f20301265040385803022070014242a02000800f070400505130202d4a0240410103002c2c0103511011241000035000f113054207100e1482d000c071a0b40140351061103414002d41c50740342e4807181c6146c03418120041650307200300c880003502c8401e80e40d02c66456104e01c80c40392081d4003514501813000c4c00c00910707260321a001404494810410035903140e1b2802004001c603541110050540c0c86450302043d0010b000f6030000390494000b20341096a0840311032440e0507a181007800d00405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 342294937 1250 342293687 342293689
    0x30921110a170304030c080c01050a0f051302190504060303030b040e010603020102100f020f2808090a02060f04030b010f140f150705011b050d0e060f01180b03060c04050f 75
    0x41d90603090000c00740310404616000344071180300510750190007400d150380200e41c15203401d00740783d100c0c0440d00000d96440042041e03003004c40c8210103011204800c00c01141c80c1c805103130640b8009002e4013074807500750005034808070001d4814000140001400501500399a450040c0c0030308000c401541c0300d281416841c00c1c003d08144688000c49405074002c011410340c190900700108030006403940d07250b408006052031038500c00000e00a050140f141040030300075924111950041c0c08200c04108a10701e005d0101070040081d02c41c0b400c1d41c048a50b2503032400c0c0c01d03105080c10f2140394001844045040000070f12101100e0b90003040300d0021040e000c50401000400c1510580354405d40d600124019410000c450303900090301665220b0800001c00c1c2c940741512641012600c404180040c000140042044400e80624010700700c10fa4028002400d0004d41e48600c010140102842c14084515031429100203800510400e8006015107400381804800420ba0f54010b01a00c0d000304100c040340646 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 342296187 1250 342294937 342294943
    0x12010e010b010806180f09030c0a0f05010b0d150c180306060303080c031b090303070b0c0d0b1207050f0d4107050103110c150f0105090103050312060103092111 70
    0x520701e1017042865900e010762004101c3d4040c0030440c291205210f409e1a510041082610f0140510404e4145201c10301c2e1290941d00d0381c41c0c1f0140030710803900440002034051981410304005034180400e90140410701103c0341d40c83c4000d00c51225001540000600c180e030790165050364025034500959980f00c6140c90101d02c0151904400000d0401000a0280650028000051004042c2da1401d4525120707050200d82c07c7c0d640701c030301000029103000d4030740c1c00384100c5200040560300f50711020310110003d5110541845518050f0f42c03a00c0c80c103426680c030308110324129503000104002c2062090202d4100510780882050039049508600d03400c0c8800e4450002c00c0d04202d0000d0840604040c01100036150b01d404c1802019414040240c052009001c9941c003a1403d2102c48520b02e048107000705002410392002c3d024039411401400415004412500e1180c83e40340341c2c402d0784c1c5590700128001d01e160340d8050180760b94242964900390900c120200c4c031625581e90712210b50110740b00c46403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 342297437 1250 342296187 342296209
    0xb07080903030f060a050301020a08151210020a090308180118210c0819020a0e1003060218210d080907030605040c0e090d08010e220212010e010b010806 67
    0x110780c01800015000c1d840e090b0b100e50f000c04080d14041200750780d1404203080ea040002c683c0003080143c42000318400c0d810400b1001203000303d8005c40031141046c06551100395682002501c5034001403141e00c0103008000c0c9034002d50340904003981d43c81c90f802110158203800c820b0107000a24032460112401c0c84000c00205071a00c1c1071040d04125803c00352020717506c0f0700e1030341219801d11000000030400e9081c015a5600310004201454082d0a807041000155032500b00c00c000121460074403a008182804d540f099130740c44840103980e1418030384407198481d0004001e0381d0048544c43c4080d8074421490070740000503035a80032240340b110803104c141c1d607902c01100c001490394030142041000c0b034003c0c0c10a5030000d01a45501010503101c3e00c544444950848203140103a1003204c191189590000c0d40c079004005e405800b0760309081c00c042e01c0d0401e10f4140240c188441c0300445442c155030b41c942c044114150540e00800c000024627440c07501070159000c25502140078070300050481e00741502200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 342298687 1250 342297437 342297451
    0x3050d031b0e010e2107170705090a090c0620010c14091306030309060f0206010b03070309051504030908011a030a0204180b0f010f060302070f03030b28030b0708 71
    0x40c0208400440031110b0140c0b8030100c5041100591481020f13480340d9008015a0504c1c001c0c0007124010100c10314030f400140d520003500b0310640d0382c2c002001d007008540d400c01e0301d408076080340c12901c41c03a01c40300240c10400e2000c1c2110701c050000049403500010054691150103200150300c040c0c59140c1422110914005000310b04079102e5000c02032840c000400d46124000c215460ba2040b0490308412070308150800c4003c140c6606c8280540e070b8000d00080001485480208403660502001d0101400302801d21030034161a0072640e030800c90180721640d2110484c803028905031a0030704008100345110321450071294a45000d5100314100c0d92140c6290190140003849605451f600f404001c084900c415002902c1c1440d032030b40000d459004030360103071607951300004055040c82c0105020030410350240007498810440400021100241d05041d190103040000703568030204d0204030030382411300c0d8103112005c0c10110307601e001c8170307420509003501c2c021051040541d44030041540c0b1108207071590 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 342299937 1250 342298687 342298721
    0x3150612041104090c09020306030f03040303090b0904060314010c0908150112080c100506040b090708060409080f0403080409050106051c020d06031208072a06020c03070c060903050d03 81
    0x1401182c2403407034141109030058000500e114480e1a41450b061054101400740340d00081408203900e001c0100f02001032580000d545000c2c0355540190001d442c9110b4100451004101202c241d03580d5400f01c0c00468200512406921400c5442402000440c2810f00030508030f4602007900000040c3e45002080707080c1d000314450742010103c8130042040340085503a48402c11941105c00c005210000a034001241c0108184c1043c40070401951011440c0324080c514000c104881554000301041d040b40d401e82d000030380c503201410f00961074800e8102101850b0000603002041000c01360052080720030300c107020441641c80b282c0807101c0e48030742260842c0344000da041000d04220698020001001480000944d543c1e0b665114000c88090790321130307000304c4c903840c0801064070b800c5400800e2400e11850178800c0c6061810004500c181c125001402c540d50105102a24440c01c008070390400c1d80200d9031416543e80c17504010005110340c08221038034052248100241800b81c0195600418a41c0e03032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 342301187 1250 342299937 342299941
    0x7121815050d0f02040e010f0e040b01090515040c020307060608120a050c070503010515030c040b030d0513051306062a0b04080d09060c0e0102030f0d0518011103150612 74
    0xc03103850b0480880e0890300c40d51459034402c14000391005000411004422900329894000c905468800130740c44a2545000305040100244601400780d041d110b016030005010386a55825218002d07507a040705130003a10344420070040d982c0000141c407125210f0801401619180c40c501900c40d4240f0924055240c41401003d15260155000e0000c000825044850140d0b4507000603094400c16100400400d0111141415a09061110b80801903084c3d80a01888440101181e61b482805905900300300d0007144d0035040384220140c61000703150003820603c5441503025032800a180e9485510007281d051000c140c4d903400c1c4600300710414a104c800100b95261551035000070701c10000c01c110b540070303002c11084000154034402c0c58125070145200003400b4900010240c603008403004039605650080c4901e0303548403110341c00c48000002c1800c0c04206600c6d00d8940d03104050806500750110350809444c03466148001000d54810140071070056155411581804068072a451031100d01e9405200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 342302437 1250 342301187 342301229
    0x6080d0e0a0b090111030307030f0b0607030804080c01020c10020316090b03040305130801090f0501150e0103060c030b030616090f050603070807021905070f3002030a020402071218 79
    0x1c00743c40d0b50481814025020305c5998900d6056070310441e0038102080d0b40300503007105d02040340706500300020305846440ca4507076903450183c01800c004000901c0e4600c0025288100c0c4000c0d015030324958141000c48511103811580d50b0080d4002326480d04c0d000c03400b0080e00407207503c80c2070b80104507a850040245152941e0b02e0881c2c09130300c00c1d240d040300d10020701800036100c0740901c5410035490040705041030760400c40c58203e00751130b0000710984c02c3c600e0ba80b030180040e24484603a54110b0743e000d80b0018542c0c0c0c42480036000b40c40700d4110325034980540c4040140000628444174000b0225945030301d109a01e0f5680d4a480d100c2500400c4e0700300d141480001c544a014806994200d1f1240c0110b072174420340b803102e1000746185580200c0d00c5401c0b4400401c01e026803415008054403002e2442040d030f0064804441c071401000101c0e085410381402c00340b00b91340301880f0038009150060f1096543c0c441ba41040d52034130000500314000a04c0002980c1c60400314041000300b03a45c41a4107450000348024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 342303687 1250 342302437 342302459
    0x61804020a03030c0503091e01020d08071b060e0a0c1d190f0605030d020307060605090103121d130902090f160c020a0902040806010f0603060e0c031f0906080d0e0a 72
    0x811685e500c0700700420140c99850300d07464104001c07508804010301c5c641c1070009091428512180b41031024000501c4401900040708007407003880000092070580107410000013802100080719007601801010304140001c0141800039101040c48200c80348118512014002d141101d8445074420390030000c001140c460f820850b103d4410752808162507840b00e000a0400c00040f810a0240c0d200040e0384041011502070540140030407190300302103600d540c8405251004d000d4040041200c03100c00004507034941c120030b030a1060082c102d42003034800d4085007002006401c000368814520380780082d66130500d4084051040001e003400205180f8405070588400300491422a0b000d80305040200b070062040c409003004288040c001d001b01d52405215400d200f0f0b480d041001050300300507081c400d01d80b107140015006030740309140a50f00d0f0307101e00d40740400d10b4001c540401b01d41ea44010016140505401801c10759003000103440d03220a20020586110040140b00c9801464010302080821649 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 342304937 1250 342303687 342303707
    0xf09060f0804140c12061e060d24050c0a122a050409050a060905100b030f07030609020d09050c01030605031504020102010b12011b1715040b03100203061804020a0303 73
    0x40f011a50340264540c0000c6280d030441101070720f558494802c00c4141003c1414000100e1056040b661160602c0e01c08201280304c0300318064103c600407600c03865001e2181c0b6003840b6407405d18004009908103200000c03210f0b4009580400000c0900c0e01c0e01e00d11200a106007107071202c20124152607040c2100d0544000c41041114400b400400c1c0b01c001904034290043e14402d04c44110000350150900701ca220803034074082c002451845120300140200032585007280d4111b800ea00102d8501e41c1c41c01000c6000d8409500951140d80c00441c01080c415080c3d00000c0c203461280065460a0304454011022070b8058420907030306510a4a142d8003000480030350702d03000340c01031001156128806000c03031500100c050030343c00548e40d200c90f0744c00d101041d0a0004032000941c500341041d144840c1e200000e800c2e0148c000406203240140400c4159210b070b004402120014087c1d641460b180011a00290004c07524107005520603258500100083c20000b84140e44c0100302c5440c075070031520126224048 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 342306187 1250 342304937 342304973
    0x60e04060b040e1608061005030d110a0c060203032e0909050c060304050601092004030b0601020a05060c1b0c06072a091b02010903020d1209080a0f09060f0804 70
    0x503992414284140600802d01c00c0d4401d003413241c10321031078101503a18040b00206404454205050b00340000e0341c001c0b854503000c22152800f0318440d01414070982c244610768400801c140c030304c0507000810035008000b0f188a00054076100654902810858020341e0740300801c4409180311000c01d1010752aa54400111107015400f160100d00500d8045901da9000742c7d0151095840840100300769016800b0b440f1103c207401608e02c4102c0a2004001202d003c2e41c00010b29074640000010442c2e4800c1121000c0c0175045011108035080c0311f00082910390100351792a041500d101e4810403410320009810801840281c18070785020000d4581103404030410307a07142c0c134004141c0054010074000101f00302c05001c0101002400c054584104650340c280c41800800796410000400d0100ba000b0600301502ca9650030141d00860442443d40300030314010500034038500e004211400b0542d0b02003286440e6041e191601d007080d50f102e51040d521003600038031100020359141c00140c0020b0004180303032514a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 342307437 1250 342306187 342306191
    0x90d0f150c080a090303020c01090f0209160507020d051903030b03010c020703121407080c010618051308030603160e07020d05040b09060f043c0503030d0b0303091f020d03060e04060b04 81
    0x30180d50076081d9040c0c00014bc5604e103e00d11500c0c150301e04400c43d41e8214001c61400b00010094000c080e205004211002e441084422070490901109004090342d4001c061040d205200703452801030700400d100c251082c043e41c607041c201948c01d0300001328401500e4000c0780107109500b40000481d8204a0005041c0405070140100c03c000f903141406048403000d14000410440d0408103100b400480241800c02e14a00380810702c500c1012080e1700d2400d0b25003110081e0b0303903036660002080c0790210030781c1c101318000308c8070400007501d078162014680a0125903080d1803c0c0d40704184221045d004030f0003521890903080180200b5441d2150007009460400d901c00c84c00c1c29a0b4100e0101c005441980410741812040713403032000351203a482061505460034600700e1040341400003081d80c03405100350b047c002503592800215181e4040003581c02c0c5c0c10000307100f107603110b11055911003503a18428001c2d0140c07150168000149020b03003d004203a030036408070403c290ba00c0b0f459185c0602011840560826 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 342308687 1250 342307437 342307447
    0x1060b0a021f140c031501031806051f0305070906060e0105030106031e0e030c070602030f09090c1204081b01061a07140106060513090c090e0903090d0f150c080a09030302 75
    0x1c640e809a072440380034041511380e00c91912506c01c40442511810040c105072400d042c4481c144203c0600c0100f103500200001895619401881c050038144c45140140d0142c80d14000204400080c001003514854030050003040d582d28170544100e040e140300746008c00c40500060081d02c0c803a1f40480c00d50601c680c0c0401c00004040f80100481d510244da00025070000030307065202030000c0024400400f05480118034014550180011038084c146040c0d2042101e8408103100ca02900250b4581e2103c1c42c00034281410705282500c10f641c0408101150f0855020507a1a03040043c410b1100b214001c1440d0090444581c5040342c281d40181c0c0708447c0340d00b951802c8000d1070000d10810b0090401902da555541111110800c0d00d2220390340480049811326a01044466205004004076034102803d4884c5031180c1d50007600354041c04182940001080c0c0001d001d102c00d035807407400018060402c145403c1c50b00c1c100b1500391100454104e000c241200c0104442030304079803080781414007a2030018140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 342309937 1250 342308687 342308711
    0xd03080f040c03021306140a0f091d030d05010f060305060f01080c12090606030c0603221e0c05011b020f010f090306091209060801060909020f0403050a0f0501060b0a021f 75
    0x140541050014040e0380d140400c0c03000003000601001e10900c100e5a80b0100c80c580348040c020007542b4020050200e440b000690020385043d050038006c0c420f01020350340c03038164201001c40208024171459260403440200082c0706402841110302511019040d1030502c01088010340301c420001d40301030304041c010846003825040d40c0d041d16010f01c6521002d0905410f054041624100070781c030080d4420b500400500801c600803c658140d0004118020450258142091740c0180b00552401c540940c206454004004031324a00f00283c903401d07200d030441888020a401e0880f05500c00094000701180e04800d829030164425007008003442c9040e40140342c507940c842003950001c86040b99800d1440300310040b0312f82c0007224000505a10715009105614140006006050f81e05c0790004207030380002c52a440c4039440e005c6401840d0000c0480300103152038070300f20602440510064800707501e0454003286040d2071100b1104812480d600804e00004180030390300e00e80d0140303040c40040c180e40f881e00e1100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 342311187 1250 342309937 342309949
    0x3914040b0a14180103050919020409050f03030711010606030603051b13020c030c0c0d17070201141204060b03010b010903170702030106060206150907120203090c0406090207110d03080f040c0302 85
    0x5001c8448a92043e51040c84005070940c2c402038290080750304002e0402050018042080b0082c07601101e022880500b141001c60a202c1c001004000b07600002007000b00c17003904084a1030036404040001c020702071b9152401c6044071464000142241c00407003040d13604409400201079503e83c010b1481e41c0c0520885c88404c100c0e8481100360302c9940000c120700380701881c00c1c0240803031541e06a4444581d50403035516858030860380c010000d144031000c204041564801d44014480811018086545119603000b804011008a40454541d801c00042d4402c5040601500310241c0040e102c001405080da680c10204803404030907141c014405015100159070240140e500030552030700034140da030808446692101c42026021800b5082076400e104107143d001d4400c4041440035500140c60383c03144000c0905110a40400c036500c0390410a0100d480c14180c0d0042c03403114801c200007030140c40706805208950040c49030107000f154100002a100e00e0b050305c1019400380c0310b00001e4030015140e50002e24 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 342312437 1250 342311187 342311197
    0x90c0908010f0b01170606040b0a0210021303140106180207030314010b0a08092802010c0210180801060803040504110c030304080d05010e1501123914040b0a14 70
    0x1155119040b83c0c41d41c1d600140b01c24805800c3c80a0701c030442c64a5008105030781300b01e00c50402045070001d0300e0458135200b448410303601c0a0300340c4150744d20030b840741c0c03ca280100240011303506924160001e2594080520070407044424a440b800100b848141e1004020b4208420980a06441c0e00c0207250310303000810b10314003034501928056201d45065400038a1454014140d0505600180036804803007800c2e61030b140c074400d102c0d800da0a804001d2004070784503010380c94020340250301e0201e074048554000d4241c050760720410480c840c00c1980e80c04628240d0f041d03841000071076041080140078509045d00500ca4481c2c098034540d1a115039081d1440c0b6680c02120142c50005012500440800b603500810f401050007900c0030155082042010722011100e07110740d4113000010150303000071910340d0081c2080f6120340000e00c4e4903407a003100c2c1d680456180380c84548a10540443c005d21207000740030043c5507001c80b0302c050341820304203041c9946980c0000001c1d024084441d0701001c0704542c2100a003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 342313687 1250 342312437 342312461
    0xc0405040b07140f4509090a03170702032a0705010305091e0709090f050717030a031a09010b09030f011a061803011b091e090c090801 59
    0x60202d141aa0000744201c594403203103000c1c82c20400030490618140019108890000354413440c100120b000d2041138242d08207600308408298007076101c1d00340320f10400c529040c0c0094136090a40d9881c4040749885900340100280819040c00c2c00c40303000c1460144190f072100c05801100e181a82203c80518400800b45040042c840f5074151149108420300014008260038281030059003030644100381c03291902051010341c40d0040241c4e21489604000c6100102000c080412441070542040d0280352100e00042d105481000c00014000420b0010080c00003200310245050081c402e800310301400902c11640100405030304070140c185e4480d20028000c18a20401d0355480404200741424000c0c55441d0b03466503450641c48030301c0e00c15501c400ca14241022115244d0f81c1e036920010f040081030074001170350150b2800c001d040286400a039941c220710801d48845c240665242008560320700c4041d075110740c03113050b080c00300000c846682181c0e56214560401e00718141d100c0c81810700710f0345c00500f91 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 342314937 1250 342313687 342313703
    0x60a300512220501020607080a0b01030603120e040e060903121801051503100b06090f062709090604051203220308100e04170a1b060c0e031506120c040504 68
    0x999442d0803211046002030000b800544140d1802650143c071281004141000d038540b03800b842c034100da10036440440915803080c0301d078101c1810480c004042850030548540100c0ca0a981c0041d9000002800c2c1d02c2280e141004500c0c4c034418a409002c00c01c4c002e000044140c0c5a0114201547c2c800c0c012a440785600307031b80c000000020f081c10146040007407503041c2d1000b0f107002d10030001503c0350000c5070200c075810744900b0003000d080c5011031444d00c248459110f50703846440d0500c1d0400302c0700082c002004022500e98100d0744030302003040c1d2501d00544c1e00a0075a80090108001003180501840d4024484420002d030110b010a480c0c040da00c07140c0040300024180003c0007031b0315245241280243c081d510f04480c4500d8650744070410190364200120111001240300c1d01100d22900036038403030382e41a0080900c8c18091703103402000303003074114180e201240c8030485d1080c42d410000b0b0b8075211101040d4002d001c130745800c010b002c58900c03407611050080c0148004101e003511540642d50107139100f2040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 342316187 1250 342314937 342314977
    0x25080615180625111c0203070e0c0d0e030c0759070f031406060309070f030c09050c0f070f0809040c02100501080604020307090f0b0d0506060a300512 66
    0x8224584201c5c07400c24a001c3c07010200d603000342c4c40008041c820764001a0801503240c0303607841c4007102d50150301006418076061a000d400c0201021001d805038800080440e04481d840303101828100c41e80e014480790b92101e148401554214140303202e40034410003038400320340c2610f200a042e02880486800990582000203108080f0380c4010500e0031504103260130401804c1c1d15084049009019100910604000c408030300c08010901140009100c401c1010190b15034038038000c00014454810304030018506400511002403079409c48000c0a0243d40b100e24003d035070b07581d6250444412170103403915003013405203050b9901c4078403e8442d4010070b0f4008211a0000020708426600141c11021007508800f09200c01600e0004402c8291120f500010904001044000000f82040f20420740e0205020145805110000c10824080e61056450140d01910b43d0b4005441403000000c13441a1074141c60040221807101c41c0142d14188580156820484441074410a03500545020503c1201080c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 342317437 1250 342316187 342316189
    0xc131508060a0503010606021902061b0d121b030f06030c0b0405091602121e0a050c1009020303160501020904060b03091908030a052508061518062511 66
    0x1110b600144821002403144d20b0400c0c80080d192075800384540c818117080c50005d8119a00c84069529007105140a41d130380d00c1440e04501da0b00c0042807100f001080b040b606401110105000b200c0d6507180d00c1000c10040c0f0003a090440090400e0040150f6030303541c5d40408000503400d00010300c02411420780d40ca03141c038105420010302c032201420310080f19455984050440c0d8020548001d1034410000e440d40b114180301c04214203081803000000c1003840003810002d116000710291145101800c200d50105d442000170504031359100c2c5002e9070561003484a110307510701403140b408034944038030005400c100e9150301280950307000f41c1016800160220410150003010040c03140d250304030a4040c0a007606584500680d4030010300f40e045000c0e15000025203521803961401507402c0700c105170300c031010002c0500030070300c0d401661142d00c00c100030034103403946010080030386000881c410128801020640100162980039520480f45d644900141072050071825405a03251809100d0305016508410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 342318687 1250 342317437 342317449
    0x3021c03020c161d0c1207170108060613111210030201030b031b0d0201030e03030703050405011104030309170717010b040606170426072a0e0c13150806 67
    0x14410069007840031808103c0d5060145980079161680184080a6100d032001c2c00c5042c4104800321007031200311801d101c0c1132070340100680e10000048d030641000766201d0283d26203442003698469401107500350151070702d005981c00a018050300301901c030300d4510b4001110000000440f090742e010b41e4801410002d5507018003401202c100124082c1151148000040004880c00c800c018041c0b0000c00042045900075440110f450003c181280d490740351002c00280030708801c031f40450741d55013040d05881c101c520350360a60b03064940c99251118000d082c2280e503403082d0300715441008944035104002802c3c0d400d40c003416040001d034200101c0c0c24565202484107440d11580100100401540c1c41c0880380c405442c4590002c0d80401414240b03029000e225400303041c0011007020756080020445d00304044000d00e09008101e0390280407107100c1028008030b00b51640d10a1144d0700c00d1050001e03000c4002d05000b418000342d40440c0389a419120b1200f03600762616220300c040403a40c1003050003031520b404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 342319937 1250 342318687 342318703
    0x302030306040e06011a0c120f090f01090b090622030f06061203050901080403020c061314031506011b15061809080901210536150403021c03020c 64
    0x81c1e006190301d51510300c1ca00061150301da06c00359100b10225100c3c100720800e03c458807103400440310898580008940c48150b65116861a0303100e041c4071b0b100940c0c1135000d03003803440482e8241e204580c00e010020f018410183d01001e02d00f000904603019094030003141c0c5144d8006140101c81000d0a0385c501d28200040700d0302c5401030000d0010b100c080c140041c0c0c2c0401198102042881c00213050f0300c581c54280e00c5c1010194149520140108401200c0d0001c0600c10085403a400980404041c05400307050f110701803800344904660007400020b0340b0b540141300a00b05d042ca150042400f0f009a5140c4081c031030780c0c400c02c40c5001e079200c210800000040540c40408400c503801e04000240c51a40d52648070310440344064140410880f07600c1c00600b802615088401c5810010301461601d0130001088045c020b01c40c111507440c41c03000b4042e60320317841032125444807071100500c0d1004e0a5001500f031000010002c40c2140f2a28407480041c1da06000e4007403001c0c2c0107490168442c41e14800060500c651 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 342321187 1250 342319937 342319961
    0x5130b0409080a17060d1202100c031a01030203010315020f120a02031e07090303030b031002040807060f14040e131a0f2413020405030604110f120d20010603030203030604 75
    0x20005c0c414036a6500218076442e640c44450501c0d015140d181c01d07070805442080030a07850b031a02c0c224800c0682c058100640e04510001e4403504940f42d40019070882c0428040941428074030319003d084003540e07600a010f42c3c55006003090a040401c0104030716084212014802140c0200c24084401c00f01d188000c00c1980744c083e000100c0c984100000c247c0b0625110180030943c90b110300000300d84050100661200d0400d1065503525251030723120399150214802d80700059182000c04695a20850041e401480c00c004183e1410f0f14283c180440d88101030010100c80403a0040c2da800035046402100403240f0600c080b800915110b803c0c038102c2c0d00018081445140e82007580074038419402503803070038003200329941b014820031904048002d0140f50402d54051142c4010312091080300f03404070384a105e0403505d68003660340e00000d00440075440c5c4c009001c5a40903520801c40c0034042e40c8600400c14583ca540102441404103280c2542c036182d1080d000340c0c00000520407a070401d802502c0d06914 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 342322437 1250 342321187 342321227
    0x51c0606120f02130b031e0c0f061905040b04120309152f031b1b1e041e06141f2d0801210c05130b0409080a 48
    0x281c1e1288489002c56940080c401c5003000c85441301132109a020461580d4058121240301a8004c550a818203000b609410304c0d21542424046920b0a240d00c10954403024200034284104491880340c10916461601c041c42400c4c003000c9a40085400034000070700005000c41c0d10261039040c05072440c07000340c03c46e40d080c1c0e0744281002c2629402a1921f130400a00018600003000d06980c1ca00d0110315070781000301c00b8000001c19006004145031880415150003041e0b83c1d0000381c2c0c44481c1e600d0152017041c030744c015080100c0c041c5d80c50340c24074150158000241012406100100810200c40703e040410003003030baa0b813103090040b84c64084c0b01a0408030240c4100c884801e0542c207100b140841e0803c1c95003000032030301c01e0360040e110710740d00f241c125846060148005080f00502030000c035030074000e0000d0b0907860014441c441e01da00300e0003160f1542207141242c0180c181024030440301c034869601d0003020b44034580700f0071607200e501ca50700140c0c0c0107140c50382c0c44a0000100600e10003241c0e0201c54880c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 342323687 1250 342322437 342322469
    0x91e0501140702060d1104060f020328020109060903080a0b0f0604031712010303020a02010e03150601050313050f0606180708061e041803081006080c0f04051c0606 72
    0x207600540a20000342034210510384030000d41c400141940f03e01c20300503118504000081c180316034014041d10603140c89840394000000c20b12000c036a640910405a100f20150201c0c0014140407541b0b0a00c001095200105a400c0b50b61034600545031070740c81c05c0340050214000c020b4180460302c14803580c204200c4440000d40e820000043c0980280e00002d004000303e02d03d0400c0206d80241201c45281103042c03401215a543c0c03c0207500c07100c1402c002d90104422925605007881c01043c644500d80440c1c007021850f485000c01100d0a8000820899aa0103130341440d4011420070894122180582c0c001056586000c0040c003028641c038580e0b043c9400111030511003a00d8020010310707407048080e00c0368591400440d90380c0b034001d201182003136042850302c08012219016844908410303030103522a840366480e039a040520810080c4120400541c00302e021845a80000004012054825a49506194a030400100200c80d00c415081018101c0401401001414010b00009210a2007068440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 342324937 1250 342323687 342323689
    0xb01080a031205060f0a0306050403080f060d030c051906020d0e150a0209010c1a06090c0a14160804080a140718050907030605010603020c07051e06030406060b0a091e05 74
    0x540c902d140c204855190000079106442d00d0f4100144510000c0135400815928200500249400c1e00d00780c00240107480003a032409070741040706029080c0900003001142403910100c840e040c001100b10307098020b61041c04080030440c0c004444440c01440d00582d11209004103004444440700321031003503000205410164040b03003c5480d0301040d030000144e961401100122488000c2e02e10040c00314141d810200b00c120035041506101c0c4a080c2c2d180f440c03a880f0450203448038007601c0c1040e400030342d420385006501c002c400c0242140c440a1a00c03140c0d030310156581c4040541180d00700500d40e9000b0500a81070041100311407042c003007140f000e04002410503e4132845041e00600300d03101d4a8070307003011481c034520800c0007000458110304201300c0307541c54280040196000c00321841c464400c140c0c01042919220b008001e04143c010b8410800910120170707c04c5a4000410a442c0c250303a0b482e0005840c00102c009000019140d41e0b100401800c0c65003011502005008016860781044428062 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 342326187 1250 342324937 342324947
    0xd0c080f010302090c0d020f120708060a21020103021204060912031407031a030a0318050406120b1015020705090a0203091f0e120d06080f0c0d2d0b01080a03 69
    0xc0d0740840c106035120b441c1003c106c00fa204d40a005d00300b00d40e000400802c0700c5806c2202a0082910f0398441626440d50400c00c1034410b41c0380145498651044400002c8103000514450310903c103041c05070405a01e0300780c2d0700c2d5100c021a820744207142c89891303000c101320040c0702045042e611410700b0071409000741c98100f081c06000780b5400526a481034400e00d01c103081c80c40c5008a81d4003c045400074802454010701c10611080909141d8170b14050204013494076015000545100c04c101d0310001125861702858040c0241c1392240c28281018081000c00c144445685020a16001020660301c1c040501c04000070083c40c0c595444e01c184140081c15901280208184200b62020102026001141c2e00240000d0280c440310344100e14185501d4007143c005840c0e034000640f02003051540d9056910748a8007802c8642d5210b8002100014062801e000a054060300a204800c1c0c00311303203401c220b170340c5043e4141b8419028015124400402c101070f501203005d480344001508038481e1300d0303a001e02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 342327437 1250 342326187 342326191
    0x50a080d020703061a0306100e0705040e0c160807030302041d090a0b09011b080a0b0102010b091b0f071103010b0a0b0a050705030c011d06091218010e060d0c080f01030209 75
    0x12109807100790b45c1c11518032503482d807039840c4c0c8002d003030383c090303051280e840c10041016104510040695400041110f1f00413025202102e00c440d6110b40c0943d26010009021340c818025913a03850505400707030340400c60310405018954405c0c6c40060b0345504051183d00d8000520140d21905003044080085803a80410021000f9911006501864840c41c0034039001d0b02c4520343c1040111407181420b03e40c04c0c1e22030902801224226001c0041e10205401203090b104442c0b50b40381c03c445142c001c00e04401c00c282a68402c100450b00481c200458403400340b00980c00407000b40c880410000907040c42e49820710811a40038411603442e09403070f18040c518020fa004124001050203030108010052000500494406034080e030020000d035110001c002c0003440c51007680340b20900c1490002691410001003241c0105014003405092208020f1100211110341c1d80d40c6040055104695480b03440e0b84014000c07a180890300414080c0811000401030b5800031f0550600045220040000d0303107440306c0c0c1d65 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 342328687 1250 342327437 342327443
    0x30f08060913030f022a0f10021f0b1003060905090c3a0f0b0a0606090b070311011d0d03061206150e010b13080102090a090509070f030c050a080d020703 67
    0x1c050b224114001d07406d10340580b401d1840012000d242e10700d91900400080e03810002241c2c1c2000c40003c00c400e0010b4101c107501d41c0409a8000d80344c0404101241c906240c080f801c5a90203e210b140a03004240c0e03003034107160803501080c0c5600c02030182d40032a00900ea0310045480c001c214036002c4800280341c0c0307828034207100061144c40d805d05084a811416200441580c0301c64001c0d2036000740f4100c0c0f00704c500030301c003540c04a4514002c5941c101c4a0b0007a1401c03101c03140e968111036070401e2040300c41c1d54010b100440a00005400440700c02d10203009841c07048440e22140c9044580070300c00b22b0b0400d040d032075003d010545010014801401c2900078154000d03001540000c2c44060224661350513003a40c0c10285488004070000140119000024400340310285e0440350000e40d00c61005d8243d00519107a2544281d038100c05101206050340175070340c0900380c0412145c00c2a510b4203100d03000380b420340054850244d0090140024188040c00e50001c0c0310f0403005100c2c040301c5610003910b0360f545020003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 342329937 1250 342328687 342328697
    0x20603060a1703040317030f15130507020a03120c120506120f0c0102100504021f02030f0c0309040605190b0c1c0c06060b031b090319030f0806091303 66
    0x8241240c4403181c0d04005894a06041180d03128014012541d0b42c00622003220f12041600a07a4020390424054038041e92070041089600d0301c0e070403401480d0b2a1900d42954100501044038000301849025035404ac0100d0340181c80700603c1402c0040503c1842110001c2c580d00700040240b01c1c40e1312070101300210a8248001417561140400150401003540c050f00a51048036080d1240500206681c01d85180036000c07a41e65180341e580910940f013040324040e5009500e04529610102550382c2070300d0f100441e206481c5010b68000d00c1403500c0d002401d0818950f070002c00d030125107091600c00d038409003c2c00c40e0039039050300c1034a01c16201100300d80188540150042050280c20a042207800c194000d40301c8444049901031800a1400d108003005840450405100050000121040742e025030310004101c0d40c2282d480079031095651182c1d19554051003004041c1d180d50616284441102d8440d9a400c0d0502c841108028416007018000e81d100d011a0b07402d00c8210520700da41480303050743c54144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 342331187 1250 342329937 342329941
    0xe0105211003210e0301060b03040602030402010c0203070b040504151a07030e04050a051608240a0f2402010606120b060d0603151422050a1403040906050319020603 72
    0x5150300000072a030004104061607515100b41120349800c1191814055403003450404c0224105401c0e40c0302c600c81c50060403801c02c0030801040d4140c005662160060400a821840c1c90b40420b20300201c41c1d0058403040808a024800d910741030003030821008035070300d1122031107045c500c980121096418016907594000510002050300812640c00c40003401481000503241c4403121002400e0700f210703401cbc42e000f5000606c103074075400350030130358010540d158000d408001c0b40b02110354224101810b45134021401c140c00200c00c0503c464240141070314020680d4201484044260003014880320201907904001c0c0c14484247e005802d030050040b4000702040d0002800e002c00c925100d20841890003508001c03021003408000c401ca40400401c2050400c038621200f04600484d10082d16005000e0081e480040d84244d1040b070b1107004a4001c50a0760b02074440c83e641c42106483c140300b01750068002190030086180c1d00d214010040ca03055010700b000740304040c030100d140564104024854400800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 342332437 1250 342331187 342331201
    0x9010506070f0b0f10090507020a14010e0609030901180e070302030403051209280804051e060d05011409010e0718151d011404180207020a060806010e010521 69
    0x910520458005020990f10300708020450700301d90088680c610f00200c15400082c08891034030a00344600f001340c2c054140d15030385540310038943c0c17a07651201403107640366080c1c0303407c880060017079078024001c2c04001c43c6d4900d00070001402c10011640c5030342c5501f02c50b141c00c10081d0480719409a2103032151800580d290758074a01550f143c0518292040400c0d05002044002040041c0c00ca15480c80c0700c00340e41c0928403a60b2060041d1401201c002c2008005110410113400c005181000380b00031307401d120345a07990ba000410b11603000078804544032a16400100047c06031404104e08541040d11840d50b1507041c0281f40c0c00020006d002041044031401d18081490180d040d440040c6c02c03e03589034a699164003100500744e4050000d4001340406800c41c1c01981d42c05500d0036940f102c8000320217800e05203031003541012940b481404090283c1c00300040e0005a41c3c404a54001d400c40340c0302c2180f6810280d00040660000420050510008002c40c103100c42941c8400801004801c040030301d16a2541 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 342333687 1250 342332437 342332453
    0x6040608101a0a0503131a0f220f0501110310140102030901050313050c06040602150f041a150418030201050703151203140c010605031006061b060213030c0501021504020901050607 79
    0x80070302480700201c111f10384190150480d9000d5030340702e0100810741d100d003050200840c1c440000118000b900721300c098001183c031030040701198012000040c207a4841d4071000416841114015041c0c050260f080c0070f800540603054034004000e01c0114140303290400040d15903c00a015203c500c0c028142103010000100206040700c400502055180d954030a40a5034a03100511012110f0000f000003a0070071902450039840745800001011076031480d5a81741300890300c00343c07020b00c3d80140c1c1b04d10100e080d01c650185070b5918007188201c1d9440030040c140242103c0001d41410101400c02c16803070200000702200c90183c0d000c0c17004021041c0520b00d03080d1000140900b22004450000c070f00a00200302c10b42c460300480300254140c4807400a510b102c142120260b0017a10701050307001908140790030224040c151182d118000050ae403d0308800d4902074040b9540c0101e0b004c00000006100f55641071100c408100e0840d03aa040c3c160906030700250918405011340d6006850110f100001d0081d41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 342334937 1250 342333687 342333721
    0xa020406060f110a050d05031e040c1401170f06120f03070515251209050718090b0411030a0c09090302070b07150902040b06040608101a0a0503 63
    0x1842041040d6480700d01410989001040201081142c44001c00400002c50341c24009680080030785070b941c000f800b0a85003030700044c20b884070704052009080b000f40425500d0350300a0380114450811a07141c504c050006032200881581082001040f03102a4a022442c95412960b484d40800040c0c0d903103c04111004180b000750005886064410b0100750408001031071494040c0381501c0d83d158100980c271200c26826681941400d03c405000d90211015440e040b90210481ca030003000103d643c0002c00a13214502802c1e140c5802c4400300700405004104040707c1814101c00a011080c13980d00d46c451030200c020000792418503005510121a5001d100b45903c0c071b680550840c20310754a620740c9000038082030100320302511400c00302041888030740081e1070095602c4001410704191111022001e088858002ca82158450300d15680903075500d000340020b0106507a416400f8540210021401d08440c2e02c030b8001810310384402d10005070443c04644103000320742020380d525181d20340003050040d20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 342336187 1250 342334937 342334939
    0x18020f07030e06220f08120a030c1701030803070e03010c0912020604050d0b0709050306191a0604140307150503042303040308030a0b01090609120f05063c13050a02 72
    0x188413065031001143c411041c2641c100e4403021120f103484207411652960310006003002d40c2014400c003044644030741c10044a441c040e15000101c02c281240303801c07480e44282c00441d107840b40413040004455001200c494401d0044009002281c2c81c48005400341200e401043c04840169040d0401d540780c110444004140c060300c030054509690030300e0141c1003401d0f00c011001850072100007986180000c4c1c2c06000d01c00c4a28019468040540c00c02d0081203019041c00281008030740105003680d40002410081c5000e5041ca07040615100c00c250800c9020303000748001c581205078405003264044284c90380944d01221316410f4010200c1d05181c1c414800780007400d036100001b004010020550701460241410000a000c002032540042d90102107a000b80d6000820384003040025604075a07190094500442030480d204016840d854140742c0c0c110b403100c904000d608130a80c245481c900010b2101c0d20007202c4040e1541202144041608026040c8441004501075070020300505021044919038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 342337437 1250 342336187 342336217
    0xf012403060f080c011805150a032009030c010903150c18030807020f0d021f05090303030a061e03030e150c0607020109030908150a020d02130f18020f07030e06 70
    0xfa03902c0a2603070794a00d0400e104d0004042c58801070740c00c45120860800c0d00e00040071070401242041d0000d005400299a0744101074072044000c000c0c54048134070100389888205269a20710403042814544100c4d210014100140c00c0b004101050704444401102d4108000c0450090302c0c0c0c8004803080303c00f4051105808113102000800c02c000e02d801444481c2c4280e074000b816400342810003c10800455010350001d00c8000d20800341801c80c00e00301c0a6155609000341031a0040000c0391642e042110020702403607444805000da919441030710440007181010380c562490669070018004169001001e015030b54031161048007102d0300040e203c2c0031a04108403821440c01640081c064003401500f50301040740c1910204011401241c000b800d2001c002c031119454132240c2011000b54808500141c21075401e0007005050b80036610071340c00421120800180107414034400a511046901071031010034810020102e654502500f070303d0341d00303405080121a02d405500811003a1003580510540c0b1301c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 342338687 1250 342337437 342337439
    0x390c021003060305010b0402070807030804020a0b04120b0c0a0914150a080f06040e030f180904031d09040b0403120e06010602010606141813110703030c080f012403060f 74
    0x703625a0042e0116401407000748401407180c41400228401c04c40042c000d020100031640c0401e0207008200d80180c8003030401c8280603940e500340561904980c1141c44000c910812410a219079140d80b20b4018041c03032444ca05d0200b4545028101000c40c0c0b19800c2e041c0520006d60a8565904441200800325414481c0e5600300c1d54100038005141201e01003901c07a0080040b85250a00d4440d040401d440c01005519008280c1541441c5402c0424050829900340007107005a0702c0f003d09140c0501d10a8450030403880407114a5410010420300203401200310604020100d40b40e40041500503415050140f070406c0c0c117140d084040c1864400c0a4464810030000083d44c690540c0200c088603015990900200480c203540c0050340300e20030080305110028480420545408911042d0b0280c6650f000505141c8000030b240c1070390001041500400e681d1440e04400a07042000250b0141003820a0b103e00d40c14081020400c0000c07204699400f84100d1071455050300a03804030007c1c28128450002c85 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 342339937 1250 342338687 342338719
    0xf120106050418060e0606010818070b0403030804050709050903040506074403090c0f010519020c0a080a0510020a030b1908160b03010902072a030204390c02 69
    0xb000c1c0103c400c0341d25500c3d080360344041c110089042401158140d40e54070440d02d0341ba0706102e00d00040280c41d8511f004144001600e0b0106200420040d4480e0325048034614140c14034500700440ca030310040000d418030b010000c100d18080708450541e40101d40300d503100e10050070a00c600d8032440c503400880c4681c0c1d0340706141402205450300d100358030b03810300712880d1018186988001d000544a0020340d600600708580d4919160306c6142a410041c0b600c20b04240003082d9020300127005a0300140503030044000301840c1d00700142c2c0c01e00507181200003030a40880503912990350360b00740d03031004129030f80c040340d01030314148a074120680d1000001e00456030721404101035100820329100e500070512070300468519400c0e0b0141060220360031001c005046a2810b001c800c065488207800f2102c28004103c000c01d48442a42d00001012030802580e155a05600c1404102d031044641c26941d00f00f1545544080031104d0200061b40200301103000101205400c00d0ba505150186c00940c827480c049100c5c100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 342341187 1250 342339937 342339971
    0xe101806091409060a0b011b140a060509014d040b0c010b090103030f0e01030212010902030402120309030304330206042d02100e09090c010206090304050f1201060504 73
    0x140c40843c03d4410faa00c0e11000b000444200a0b28540400d000d00091000c6e0300c07014480301492401010008408100c421102d42010082c410846031641d90300203001025100348100c0c03401e4017000c002c202c2e0101506581c0c11044503924681690640c1103510301240400401c03030156812079000c000c9454544030f003c2c000458210b410306090a40c80c240200c0540c0ca04001e80c0c5049035010b80b01d41041072802d20b401c81d1080d240501031414940c082201440800d14480303114001d000c13040340140c40741064410800c00400b0000c03421900c0c0c1c010701100c00f40340d40200c100c0e0700300c1b2041c2c030b18040034400c41e44202046100d0441c1d52030103000c02d120540300458001c10140e00c200c1c810100311220f000c0312281b100010880c00c104141101d04449080c0060614447d0582c1800e540c0c10410518211000081d200d150215003070984d54004d244e0b844504d50f0108000bc1c0c006c0034600c00b40d81081e041001080301a00007061300e902c01e0004c0d5107802840503007944660060b01025100744000d001075248100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 342342437 1250 342341187 342341191
    0x312020c0411121f03022704142b12110403030906080c04140616050105100f170606060901111501050a060507020108060f010207080f070e010e1018060914 68
    0x900d0100e400d0019a1413a9100420160f0200c00b21100c18900c1c196024401c12010405008010f4003040e091000c100480c030300c02c980700c1c80c41234622036542c0449041c0a1708040c07901d40c10008071105c0226286540c4c5d00c0c1200743c0300c110354a2500c0440841c2143c0003001038424104414241c41c000603000c030070316034402d4000c41581c1940d107a9100d5510346003407910301031240381318840910021140c49580e074032f40300303005200f06840c01c6a008059100c68540d6400c481e13090750f000d00c10b100100d40802801510004000081c41817000500c003070302803a0405501d03082d0080509201e114009220300050380901160b14407100d080013101ca58030a228076141c1050030078000d6a1281b0005800001c400b8815411603444aa043e91850480d407102810310640c000f0150106042d40515040460800700c10800e0407210310040004100b41803408030f001e20300000c180c002e6907000001e9010000c1d0064091019011601490141e04a800c002c50ba274000611154020303825032030404c9081d0b03039200c03100c0c0d10543c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 342343687 1250 342342437 342342457
    0x80f03070f0207030c0504090804031e1202010c080f130c08010b0a05040e21041a071202010b0607080c03040906061106060a050d02151b030c24010312020c0411 70
    0x1c9a0104900b66a0354080f807200428401d070f0142e090040c0e0420303421820a20307101d071203414206920380d0f480811000c0641c4d80c140509003207000c07032400d00c0350200005100d10190300007040742d49030b1102c2c0105800c800802070080d0006080105000300080541050b0f0290840c1035100400d46400301079001c1c0400002c95445100306d110041161325040c4103030840480910024184000d50340e010310011031281c005042e0900c018000056113281041c0b10301d00384c50181c5415651074840d8a45001c0b1502c0d071a0300e200440e0305d8800354600c0e5441d01c80844c0c42d085d42004d116601d60039240d01003032071482240c0044a180d8280f030400a0b656403c5900300b110b01020005442c03103690781c0700500c101c00340325108450f030020300400c50001508102c01c2d00e02a03a500e4900c3c051034071250401da015040e20f140d0f080b035155440010040202c9400788414a000e82c81108800c888220000ca040348000c01800050300c0103915400b440000c50007044049100724019106100c02880511b00340b40d5038010500e44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 342344937 1250 342343687 342343697
    0xa02060a09080601060306060801060f020a0b0705070b0906010e06060f0d0c05030108010e0c01120c050717031e01081f090b09010c1404051e03030d050a150e0f0103120c080f0307 78
    0x810294000d0203802c00342d23206550303a00180d82c40c1c141c0840301c1d26456001103003540075000c040c001180f00303401c01a11030411503ca150f5581120301e08440000001030001c000340e007080340140004c0000901880d049407080340d10703588072082102c15080c14406c90300082d1100d840c11502e05081074000010b9070407101000001c00011101c0c500540c1c942c0c010042d40d90001e680e00b0654502e00c01d440d440200b58190302e00d4000d04080c500d546030320014245202c0b40003103000101c10404401303089140100c0c8a113030740901e04555450120314690703c0461001000000040040505806285621401555800c00c412850324208030026030f009040c0080746000150351405503e140314144012035086800107006140f41e007034103502e48015040c00600c80da5050000700000185412180901d9008409075400041c5030498111113091010741c81d80866003001d441d1003000703c0d03032203041d8202e4112900001c880c4c140001d00001194085100a001411080c01203070b40001e8800104c0503600c1a01030361a8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 342346187 1250 342344937 342344939
    0x30305071107030f1415070f050f16121103030103060902060c0114070f020106080a0f050c060f0901020c1815042004080609161a04030c0e0901060f080703060506030a02060a09080601 80
    0x3400c3c0c1b10985582c406015044070f0b00401c082504c84c01c2514a00281490300c036081c44014039040b2610760085090010410a00140c0d505000c100381445000c1f42c024180b2031107408103048416100d000501c00500103c2d82e48451009540f2450101c506505901008000ca403142c1c210a50701c41e007064034103400040500700324250090052140ba8103942e1510020100c3c03c07001c0c0d403040d00645201e0b030102c0b100d004540300e0881da1f80350310000c1d00088110300c040680300e6000c400020302e003901c0701030300c0381c03040300c181c1c001c0c890b1100c0da40a040e030071000701c8203542c101c0301d0300c034002c035002c2c20107824581200d5100f03800035442d084d6000c0280095a00d40010343e0240c1d110340ca0590303134a2031596445001442c0300b80c000c11141c4003484001002200f030318011414940c2e070303071204540d4400070362005403003201d90004c00c600c02c042031103280042d02081114008031410b00c65001e56030b0041c0e0000030007003940c850118125503404c0205005c059401459682d44100c0050300422550151141c48000c0c410100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 342347437 1250 342346187 342346223
    0xd060e0105032a04150603050c03010b1c0b03061f08010e1c030908040e0f06040c0f0e01020c0409230a03020c0d1112070515070f030305071107030f 65
    0x109412144018010560b240d11150350660903541029120b20070103c1c80d42d02e2015855a01500e080c2084010040a4141c0b03030803005400e58800410340c1c2c0d00303135004000501c8500c80d49015a60804110345402018000c80382c0341100074454a811140e0610031901004520784411103400d00502c100b142003c0b81503622030f03038039007a20b01074140c0d100d258100040d00b511449015003041c070180001c1c44c003c82c20200c142c8401d4915809500300c5011419040d04000200b462499aa0b401080580302048040d240c200d004010201d0b004503001080f80103180340b80c2580c0300300b08845070303118018400c11003480c01c3d140c02e1121843c100129076400081c1c0100c0707009088082050f003038060701500030381010b1811a003044001d20b403000c000c8903c000201c25010254035500080c28003c5205401807080d00d003800208a000da5030020a09131035003082103040d0000d442c9290b00804181c2c507050202c0c160301c8541065840c1ca116042c1030441d84110340740003080c041003c4070070180501407851b00c200080824 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 342348687 1250 342347437 342347459
    0xb0c2d010f020c03160519050102030f161710170307050105010f03110d03090b030a050601030b0a03020a092c0307020a0b1213050309060c06100509090601060309060906050901020d06 80
    0x41c080f003075400501c07143c25420440e4081c035843c9481a810380e608901c081c503c00d0144505250151400ea5010007000b45501241a83d1034021100c0400c44040c8a040c44008240c5481c800c10b001d2041c4da5000403070041c0003d0500b900140400700381e54132080b422824529501e0f0489001603d1039070030400000350204082c51542d00342ea402c4100001d1104646050040c10070589004400308005144001000f031f5904002d517001d5410384074040741c24140a400101039440c245062031080740d42201c1040140c0d00c100c000c100b01ca58144022904000d218104030005104002d220104103e0b5a6208801c0c00040001e086582c400c448102030952240d20812545c0200141603200d201d007540800c0c00e0100c420740c0701a07242c0c0f0900403039113084000c0c008102141c00c1045510450390222007070085558101140b00301400003030781c0b03541c1d2901e880400c01e6540c580610a4006056541c051304040c06000c1e04680b030380d140c10034418030071400c00e040d206000f544031401d91030300c0314942140400c2c0d0b0b000c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 342349937 1250 342348687 342348697
    0x409031206170607260a020705010e06061c05120703050301030501050106030c120b0310110a03051f030b040f020a0e0106020c010903020a05041805100e160f0b0c2d010f02 75
    0x150010002135444d001c055a11400218140300402c08840d103880d00d404240c001c0f1489001000d0000d41c0721116850100c0c2034410030000801582c009004100440d150020140241c80944d41c102c00c1880e1b85003400c60400042039848001020005800414590401e009604892142d0000c00c040c0e03a071071200b03d003182d008030407890004107014000f101448007030708002c001d19001070a90307822900c810320042c1243c1e4070f1030982025445c0860381414003070b018401c40780c1c04240ca000034050316154a182ca29002d81c5800300622284ea034801080900417030055a00d81164050035030528140c49104800c000c140c02d00c60300005201d0401c028901e940b090f0032030740032643d024060b00c481c0340c01c160400020703211007070740030340815100685c1340003040b0108025603e042c86281e002441c2000a1025401c06e500c164140310176105142c410400c3d1126006400203c410700c800b19030300d5008400c2228105000c04051030460310b802200d89030902030180200401c410118000c2141200048007079050b4090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 342351187 1250 342349937 342349979
    0x6121a04050607050c03090a090609060b0301050a05040504050709050f0a0605030a0b0a11130b0705010506150304030804032006060307061103040e061203030a1a0d210e0409031206 79
    0x602c0840e21150181000c0c01d4100e000c1421340341003403448804596061400d50084055075164103003041003034600d205103400b501d800c00d1404e05d10360416011540c2d650443c800c0b94000c1da40d40b0005014080103002c90405000660000c3c4964100f603040307042c80601c1550806143d51500d0b00c0058207150005d1440c07005940180640d180303a8440c0d101400800079000c420b0111001044148a4010400c0c41c21025000c01400b85440310402c5c1456421680003d00d11802500014403803215540c403101a00d6120340d05181180b411707030b12854100c903000710030140c00c0507070f1450109207010b5120101d0580e12030a001c3c0c040301c0c0541d50f680401c450801d04110584079581080005000d41e01c2a01c114650142c4080d00c0703038030500680340116203151320484244042a640c0c100d0406058074800f500500e001040320071280103031080c7c9888207200c11422094a8003141062010544c0d80202c0c00894443c130010010800306880b030502074560340c0c400740c0312160395203044400310349078140300e02c07444078822 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 342352437 1250 342351187 342351193
    0xf18010c02010f270e0108010f0903120906060909050c1203090105040e06030f07063b09060a05030106060c020f030a03020c060d09120903051c050306040b040f06121a0405 75
    0x61105800d40d482d11010009250064107440d4446110240540d000024080803105e1a003540c58401603600b19400503c18022003424070700d074000401e0380707c2c045030003000c28030100045941492411000502d803650100d20414186582081408000710300301810b00400c1c0c070444005001114916201e220b04140540410002c0c4424021200c0001003580e21000c098219190700642c2c0401901d0302c4610380c003900019000412084082801c0d85840f10442d80ca0000010000007000d50038403420300040d04207008003440000075841d0381e01d64841c80d0003400040d008024058407444014034901104505900954800008100c1801d001580e15043c580607070107002c0707200b0070804000d130a80c45864241e6901e81c440754543e0105e1030001040320010780c283c46040c101883c51501500340f0300c4022a104048140e8484881001d401500b20303680194111000101c01e11f145000074018901050001c0b1003a00c0c00f4008144075007400e162259040c010410744904502076810303500b506004880042c042d030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 342353687 1250 342352437 342352457
    0x2120412050708060f100e0402130509031b03030a06050a030b01051002030c0706090e070c03020709020f16060203010303110d0212180904050a0308090309030a12020f030f18010c0201 80
    0x402120114a0031034494402e5407003550f61075030110b14040c0c0984402009007802d009210340b030340c3d1722a5140018400d22010454914194000a000038001004003019540b20f100095402205100711040000722007150b1194130f4450154558130b8104854108280b840c01358003290524000e084c03141241c0d0300c00340c0002503038282420300c80c112000c49085003d500c011b0185c102d01031014400d580c090b05866070b510b0b00040c502080e0650400c1c01030405800c0c06a00c64141c004681d000c0b0b4000166282074002594400c4222800d84080c800c0c0450001c48804205d181e07001c214440e0025030489029554800b5910500b81c030680e140d100041306e07a00913078030011900103090034207000fa110030603901d040c01a080c895840814040300b82107908890707507040704c201c0c4010075400204994100344540011400e1180700400710760703110389015020346403465400151075041d108029001d030300c0b80c0100580fa1158082e64030154a0b030070111803007001d4102c50858201c0e1394454051004a29016540ca00d100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 342354937 1250 342353687 342353699
    0x90506070c0e0630030403080c01020a08010e061f0e06130e0703020406020304060f03020706091a090610050603060604030c12031e0c06050a09081b01052a0d0b0a060507060b01021204 80
    0x1489005201301c12a000510001006c10a401d000d0003c80c101c200025a69a0b0340f00e9004010103416003159450790486018000b4988460419410390f00500d1a01c42d90000741d00320550340e050404610b035034080b81c0002e50030f1000240b0742e00c0e0011a0030894520b41c280d1110360741603099000c1e9024010041c0d0084c4001c1100c580309d9074034598120110308005203840d0b013079164102039825403c420b0701c1c0d54501c4000403002c801c03031405c5250301814410140005040c006d0548980159030b2003104d02c00c010100c0450300958510044500843d072241400e508641c0c0c4800404400d2160030003940807412003000003500b00111000c2000d8090150784040ba49003459580000802014050351103803030380c41d4204400610040c0c002c00c0c00c40091807000904e400240344490035140d009000326818540c9551000c800b42d088103092003c030307041e5041c0c2d603228103e4107002001401c0803200b0a501c400040000103082c0d030080010300d0f0603402044182f101400507030043e40e81d075512422010600304100810001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 342356187 1250 342354937 342355009
    0x3110a050d120f0603060e10060b18040b0904051f0212070c030203070609060b0a170d0c050a05120a0305180a1211060f15030d020606060307090506070c0e06 69
    0x2844480340000655080c0e00240c40204d0700340d50002c0381d040e03070340f01030442c43e200c810048a41a103403810424480903042c500a1403041c062080c0100300045800e107448a640ccd140e4001c003004081c054845042072405080040da1070301c80219100602c0038101001c4240c840d01c4c0200c405104459451010b5a1145078044030481540c54050302140400d00c8241e0004416000f0000e0031401a0301c04980c4100490401c2080700042d40440401c0321340014a03001c4080c0030400c4181019541800360341000c85003000740c02d0007541e140050850203200132410401d10000b0140131003800d540d808005540d140d04c110f03a11007081c0441419158450740e01034002840324681c158001c0e04a152030310200082110700b5280c0380003600e5000901c2084010405080341d41101041c011108a00078444420b8440002e901c1d0600603003100d004003030000004c0d4115001e00b0b2001c0041902030042c3d42d9458460905420180960140820b100988000715000b4645103400490000840e0403907001e1402003d91401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 342357437 1250 342356187 342356207
    0x80313300e06040914060118030312050601050f07060c021207030c020904020111070b0d0b1008130f0f05010504020906041e1d0601030311010b0102160b07060603080307030903110a050d 81
    0x1030b00c114200000301d8480e80b14080c075180068803900015250801c600054000c1070800711002d218040b80d4810008039900600c0350454014082e0006074940703c0200485203882020500803140304001080410098a82d00800f101d1070aa400d440d54420410307407034a130078070680340c01500280c010340b54400580ba011804640040c41410f04c0c1c010740c480e000009081c00d0840c0e0110082c00c0340840c40000303280850044002c1400c088401c40e1445103071800c040c1000308040e080a50103042c0c01c41c60300c01c1250400d111441ca070340004440c0100011454005d019100c1210100d00a404d0a00030442ca03040c1030140d00f031409103030031502d00c0600c04111124000d140155040c1841c844544410005507802e01605021714042d13915016086042540b95003900c26060019046501141d011004120310f80307061416203081c0c10300c0300c0d541e20182c1030403006485190006001c2503400424440c0f6103425500034160725100b602c0d4280c00690519101b51103c00d030200240442d003001007113008083c800c0140031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 342358687 1250 342357437 342357439
    0x30506180702011d07030201020f010c0512180a08071407050f010e061308060708090d1d01050702031219050f0a030207030c081903140618060d080313300e 68
    0xc504e280d0b81040c41d0619189210788480381c014507014025940e042c0405c00b020701707004000340080c0801d948002d1891080401c101c0c00034000c4008a50140030b0721141b040d200c100c403012560b02d2070917401c00c0c050715400307103200700c03032103465800929001500862070390104d48004004a040c2061040152030482d0384021107540700c44100400030803110451741040144c80448018441d0b40f420b280b01500d0510058501d4005030300c03554080e26551f6101c1c40f16005c6210030b85200d54088446d4005a409005914001303506018454000110040036000380c44004840408440b0b801002c10054178103211f01d006020920900300300807040940240c00514096101c3c1c60b01c0d04003104607496207950380d0442590003603885081016800c186605008010503044000422401801c03d0700000c3c03070b401440031619101d80007220010b901c964848021103292900306246a40e42d242841402141e4000000308403016440d10442c00d00c401d0a80090018016070100340042440d40e14a0540341503078800c03112 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 342359937 1250 342358687 342358691
    0x20f21070209090a060b1903080a0306150309050706030c09030f0f05060925061b05030c0106081f0507081f1701050610140706150801020406050408070603050618070201 74
    0xd8801600c920881a01c03400c8403001500340001c0c40e1034400143ca079803180c4c1c2481000e034012440100c4403030040444c05c82e948040c0069a0b258051004e0b00505070f55400034101d6510300d141c070181190143c01881e1100d20860940f000c0d281c644806904580500341580009540c00c4800e20002e03200c4000312440c83d000720004580c20300250744051130154111140c604c540c0050300f0803120fa40d41020142011041d401006401e02c0c10700790001c00103000ca0309030350090401805541c041c0142403080302d41940300306000f48056078682508540d1240704800b194202218020620320515181c03003024001d180550f1602284d466143c2c9403044029086441821514032410004003e4802050340b40400700b000c00116040c0380c10420805e195174280c0c2e40c51705003c00514050801e805038811660855440800011030b219012a65600c0c9a11500070004540c070010703011620315048805401118001405c50780811f850301c0040701078420548260345c06c440c885015190b5181d043e408a5408083c034800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 342361187 1250 342359937 342359947
    0x4080c150f220b04031b051008160c0b0c0702010909020306010c0818060412050606030a120320120f01140607060504020d020a0f0501090e0c03040212030c0a120e01020f21 75
    0x55015194400e1740100d0341600f06028504000c1c00c110703400c1005090865469560b11525603010708900001054588040002d000004400d80508001c0f6801074000c105418285002c1d6102c600e00ea224103802d90114040752030014802c66a8021a8451041070707451708215101e0747c1e60322042d900070405480d03035001c41c04941c1d450754881e08007800c0100368a041c8000a0300711414028103141e4064232050294005034400b4010a50013100e1103c241e40c0c81ca40092881c40701022240c861221905c01c00140e44001154000000094102c07030280390445030700103159a88020660704240d040c1c0d2200e0b04203c2c1441040003207050b903480f541d88240040c040c5540340c5078940c0050138191a9401140003141d603950280001c2d40d000c10400003802d0041c050300314505003200004400d0100410083c85646e035249041c6071440280155001201040201c8002100d18a0440043c190300141c1d940082e0078a95181210340c80002c00703120600760400589084403800140041000a000e40c40b81c040d001001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 342362437 1250 342361187 342361199
    0x3020f011e0203070212030c0c01140d0e0a210206040818060c07031101020a0f060207060e030c0a120504050d03030f1d06060405070302040b0406050705011104080c150f22 75
    0x4034400305000700d58003542d550401c910421211040003540c0300340c96801030164030b8041d800020400b050680c00d003480e4407844031110342120548641400311000c1400c15403811810100003e01002281c0f00720600040c00b881121130030303402e64000d0310400042e480744021130082058200289050f44540c150200c1340140c0d400031407510381c418002e0030300a5201c80c1c0200140b0202a8450540360003d2000c0d101c0381d200e540398158141e011410190565900042034820400198001d004030301e16201035a4660f0001d11074641c68200c410015580c408604640c4440240305000311030503a5002030500508540545040f0018601c9030a031007441e580d00c41c03500790301800380901c081546140f0700090000380750450501043c1c0f60041c1482c03060600511040c0140604441602d05071a049e1828949411003810820b02500f8001c0160750803150005000c20464004038154088900950300d981000c1d501030741c2240300c0c0c0708100c3d4800c404a818030032003420907203100b428185034541d03010f0400c45544400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 342363687 1250 342362437 342362477
    0x10b0f030a0f032609060f070f02030405060903010b0907050c0708030403020907110f03131809080f030405150103060203010503060f040c1e0e0c040503100605030307290901051f080703020f01 84
    0x5500345c0c529501c0326040003000e10101c5003a83d4000381e180380150b244c2c484c4500195490140d40101446942d020440c1c003070030f890940c88401e881000800070802c81c10020700151050380503255140840c06144000300709c0040c004202e0f400c59602410040040e030740c855088611380c241c0d94529255005089810081c1402040070f0540c1511200c410f004442c9007000501d004060440ea6040c954107007803e0101103020f03031702501c41d803244001d000f40e900e40d03480c9880c41c281032902c5003402d01b60303100760004401e0145542c050f5043c0c81054040320701a40750000e100b02e83d501c0c1101e00030610040d100342440704590000c0c08e203400c580c2e103122484c8034031788901c03e0390baa0307440840303034201c0d585000714041149207800c00c000000c07a8003041f401c200309402c280100391644034078400600500c1c18400070b40300000f203031503e08802c1c0381c940c440c0140301d00303200031240d010b05070503540500081410142c003609000d41441450031030300040020120389240d82e003401205120140da25060104501d0a0f00c4240301070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 342364937 1250 342363687 342363691
    0x904030302090a0e09191704030c0527040206130503030d0507020717120318190302011d07090b010e0a0e10120b070309050f010c02010b0f030a0f0326 66
    0x180c0c8000d0b031920410340501c00c0c1c0c0030319913000c03009010400c41800f0001002050506400f43c0b040300078a6695400d04182c45403009810798082d03640350000300001446683c1601109488040b0b400d069000d1030700c5100d02c5914040800c408000c090350300864014504a001460301c081884200b05401da5140c00007070131500160034038009640c0341c1041041444d0705005000c0500211140310040c85e041d040301c20341d600210b196010303401500001040c7d07449002c40340030301c1421210040301c00c181d017100503004c115094248214090341c2401030040400b45102d440d8503816110000415110f4500710112000d07140207100f09040c0459a10343c100151900021800949098207284d422418000000b130700519240e40155041e01000e81c2c0075001031640c04283c2c1d00809540350104541c4480d081c42c600700a01d0b405004c010758a8070782d8101342180c040d00440440da8049820b01c0c40448e0441c1815102d48240c200100010a8204001d0010b07018820000c0d00c060400244c50240320741ca03a91032080501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 342366187 1250 342364937 342364943
    0x5031b2b0b220e030f0d0207020a05060a020a0c050105030705090d110402070f03170712150504020c07140d050c0114130e01180903020c2101021207020d0201050f13060b0904 76
    0x607a90000001d0741c0b0b015000710300032140004c51810180007201c030020300910100c684103680004240c1c0035036880071010300103490024195a640c8001c490040d6a80400c003030203d4290920110005180d070103001503c0c0300354000e454031440c2500c0042000017000041d942140d40304040c005005894603588041d02d035417032081c0c94141481314181006410000b0510641e00030704420b0040003d100c4d0b010741200d0344901c19600c04102c100c1308800038040c0c41d50503040190803d201003403c046140001905070111000c00c5c090b94030045d104414041076141154004d00941e025070103002e50f65100b0881010641101d040050800300c501044041000c500c1d88070240e90340d140e00060102e101400d00b0f214455400d40c408000c070b0341c01580c001e511140384000309032046035144906500702440a55500b80403101030021540c2d8000103e000b07040d49001d4031540014412004110015401446200c0c01861850090078841d0350707605a0040030002d001080fa00d01d5103809030520103841e110b04942c06144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 342367437 1250 342366187 342366229
    0xf0e09011407171b0a03021308100c17070e10121104092717040b0c030301031514040803071701080616020a0519061107060b090a06141215040305031b2b0b 68
    0x101e86cbc0c0b004168109040313500c40400032010900c40900d41000d01400c1c04441902c0340501d1285c1e0250a48909010381481c80705141400d00e05441660908000c206554200c081080504803015800d0441c100c021001c02480d600c00110798045040d8160070319220f148040326a1801d51103c0c4031903000d80000c0e80c82e101c0340e40044018010007400c5003a86881d0803d00e00d08201340e41d07181100c5880c045010384050140600000400c034064030520380d0340000015905444520b503500c881d942d80e104c1c81100c10104114201e9100410b052000c183d1044d102d40180003412410051403100b0341990f10070314101e6687c2d94910840082403402c0003e801d4490007100000b5070030303010800380000300c1030040c04c00c0c500624052040c04060058007a0b05110001139602000c00c50696403d40d14246541518840e61105e80041000b01a803100045214103201c042002d01c01104101e440454000e40340307005500e8141c0319600000c00ea40501141c0341044c8134401040a12240740401d189110854419407802 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 342368687 1250 342367437 342367451
    0x60d020d0302060714030610210e070302040c08060306150604055a0f09010b031b04030c0e09010f0e10150f0e09011407171b0a0302130810 61
    0x2500306110348032601546034411b00c0e52070020009043c10b00500544800d000300c80000000c0803a0708007c00f0144890984200012801c0d240c415580d6401480200c1c07107603041064240000e032288824034040c2c0f001070010007194654607401c04031b1845007002e00c1d410402c01c4c00009401d070788900061038446011744002c4002c584d40c000900d00103425601c110010400c4413180341904000d00c80030a108103003120022200e2200c0400544464120980558001c81120022562514410065005240b440c0c000e10380d014420640c8a05400307184009002201c0140313080001456401d005a4002075840000499440e8400c9440403181200d0f840c20540d4440442014040064801c240000201c8411030400d1403078955200d103801c80e107004044408010741e02050040310309400501e0569104441d0103901d262000c001005402d4000da81d00c415860031011070100710440900940184e0160503043c0b900c4490321040d0043c0d4060b0820840c0c54440e280c0014100d24180100b0f82141c10a11001c0303502 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 342369937 1250 342368687 342368701
    0xe1506120702061503120d0e010c0503090d03051003120c050f0d0e150a0f110601030807030905040c140f21010e090601120609020105070204020a08101715060d020d030206 75
    0x403e90040c40030040100f00b40407100c40c0d07603002960465640805154175610000b84c40e08001809141c29190030940c01c00919030480d58015002c0c40c8580c0140d41111800044040210252082a25501c400021403030051000c10260194002c004003203090400300b80c2002e0b50744a181001c0b501d8004803d4001882030b070344a5501101c4024004030444d80810204042600c01030584200b080030340034003103024020300c07181d40103501d545100044e003000d0b54090340c0d4a0621112a510a0004500041d0003002c045a1407a05118a0040c0070f40d541d1281045507400151950550103401d4182210100f03203c1d030943d46131b49400304030762202040c00c0c4040c203501d001568003040724064010b0209030001001402050b940d4a540345c0d80030b03006980401d500b11903000580d0544114040a908580000f41c03144100760840300142c042c00340002c0317905c10595500d002012246001840c4c00b22a0070080903c4d41c0e0004c03c83c4400d4210b03c008080da000c03003143d44d002a411180c100d50450140c0c0080c0c00300005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 342371187 1250 342369937 342369943
    0xa020912070e0105030312220203030c06010932190608070810181b09020f0c0d02190201180e070809060106080103080f1315020f01050c040509010e1506120702 70
    0x404c401c2d0300650400c0b008221046030490020075800035041d251840540c004180d184005505401030240d9589494805805485074001d01030003112501f000c00c08008a0211901c500040d04007140208510191003011a201d02000d400e400500c030310b49140c408034011a100f1540104061801811038a151403500345c10003482410301d046451518544c0c0c6074424005529405032903000300c0140c1c1340c50f10b081400c11540e40361f4101561032440440c80014540b0a1030050482c0308620080b180d100310464000ca9841421418503512120204800c00055000d01d92002441038046240b00c4d2258544c1ca410107494401c8501000294211050014200b01400054050800303890110070640c150f0700ca00c2420304c202441d40404550000b8041c58591002c180500a0900840701c01c4d510012058029174480301d42d4401c0711035520f000003044840d200c032021542120405095004560303c0d01c058201550320080892510352200d0001445994440340149190054486a000141015030000f8a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 342372437 1250 342371187 342371189
    0x60a0c03080105190e04140105040606061b050c0f0402040b0f1216020706050a050702121e030310090e030c01090818041a040b0a08100204030308060306040f0b0a020912070e01 77
    0x10081c0e80040300b402a507000e410060041d203155401c00e905540380e0340741c140100030007c620f0395015442c0c242030108000300d40d000441210b103140c0d5240c501018900c0b1883c942514484000c2465001c440440b00c40c1c02d0507450f0040d15800284014282580c41ba25003903e40d2051001c94040385000421840f400c00131504c494024450303243d4820501c0440c20701a60791081c0780103440a11402040010229120b041151641d030b83c064900920034110410195581480b0400780f0382107003400700c07000908480003066900c525811944a5100c502d00700a082c0102040d140c0c44402c1e00003080526100c000c00d002d00c041ca0381c4a0400c160303950500c0045c6845c403000311f140241c03040d4244135030f0710141038003d6045803000401f10303800985500007a000468000086d40314003924020b02a81c2140240c1e542e0103001145e0181c2c42e60380311603440c40c0402d0703250f60f006c031030090401803171081001c041500010403c0d405a08500300503d80260503001400e00c4111500c0840d080d88003560034004812200f12941c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 342373687 1250 342372437 342372439
    0x5010e0a15060c0f0f0812010e070c020108060d140601060e03010b0901030b0a0b0604080d110705010f0912080904181a1e0c04120804090509060103020105030c09010e060a0c03080105 80
    0x485030401000809520740248080c01d85801c00c91014240304241d10a000c83d10f501c0103541ea542c507e0b441c2c090341c10082c00d104103509a040003001a602c9801038061039040d0b54145d4a0443c141e545004100701ca80030104190b6011015000c03031032111604105990103412a0740743d00c01503512080405007592405032050f40140c110748010000680d00c41800780d00302c80c040d000441c600042c107001c94142d01413944506614800d603120b016840d5001342c00014004507010584400d0340e110350055401003514205600002c020b03410812101c0300e800b410b4006148145046490074940e80c0003d826621a100c81142440c103c0150204010b52880b10101200c0324950071010340c03615007101c4103006010707603210340411588400a202c00403450122400b41c41c40e0362001c03603802c0c018200350352203810038000c1802c0c02c5e161802040340c0b0f0100096080c1203d43c140d68080c55035844128040d0340780c2108595505100f0310304180e4000d5a07903880074040d4840165246020008941002003030018182e000c0303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 342374937 1250 342373687 342373721
    0x60206011707150c03020a0602031518070503070c061803050903010e0d020318030a050a0f0210031b050c1504050133050103020a020a0b090703030905090708010501081905010e0a 78
    0x40041d28584071000320f501c685400c01039074460b05410203030305001c0c118600030500f40c400010044940c440000303030f0300e00c0360040d14805484940d4210304803c81005031280340c08183c06000154906118140c444d449902c2a0f10105002a1b2942807000500703010304101d011890202d40c41003141002d1103007661051030340e03009001c09001060065280d02ca003c010745401c4040341d040149035142000154020383d4080e0172254085060b0034680320140c3c0241040707114040032032060300114401c1c0a1422440041c0300900c80003041d0b40415640d0b580648928511409644060180c880044a885100358020750020804c50042c074459200c550403003081848140307101940000b80640200c108060310b00070700b00160f54030a00c0c14143d2070800410030050030006000204041f43e00c001c074190301184d100f07444541d10603444108200c108001150040001105100104101d40c4070360b01440d0090103401e040400b08510464000070759009800108d014904d51040c84208206442090310b1015080c9507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 342376187 1250 342374937 342374939
    0x13031a06041a100f0207170d02010b030a0302070e040c05040905010914070b030a0218060a0306050a06142d0c0a050f0303040302030d0f0f14060a05040605102007060206011707 77
    0x2040d40303c034a2455010000c903410320400207802080070300c1c0030f04122940c61a009000e644032030340e5400c55032030200040d420681500801c0c180000c40c80c40c10740c0d1640190a240303041441840303403684020001c2c0c4100d00201000540e03034907544228144a0300600020500ea400e6040401410404090042d02c56010100800c00080820152a0000e980d0311002d030b561209602c0156444c0c0070003041c158441c01c005050046075815511500440d2410b44445221545e81d01040d0f800c0184034182c0b80c1c0d090010000405101415004200f09044901c55511a07002d512041c08060308000611042a4031042007082800001c0103e25007400c0100021407840c44c103542e00a48034091092001021030311034010541404954015007542c421036a03081280206400fa00000500d060740d03114003034250440c0208440c1824021002511400b0304025548840c2140c01c03501601241c03840c3c2d00040d040040e90400607800d06c000d00c010007559000700055414643d00c01c505001c41c81302ca0038140e01c1000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 342377437 1250 342376187 342376189
    0x1050f01020c090c04080105010611010f021e131a091c0f12020a02090c07140d05180612040503090a120c05040c2d02010606020f100213031a06041a 65
    0x90482c1c0076040c1994102e00380d44501c0a050300c0303402544c00c00351455003010008120309034840c03080410b2a0250000b0f00c42d000c403800c2410b01300d00c21024100394207401c01c0340b403c4106c1c014074001c202e9051400c80e908100c1d03680300710010324100e5100c030114003a20002035060f101c0c076000d980080e980890b0f04120101000c55070314010110b80443c00201002c03203442180c0b120a0007800680342e015005005290340b454001002c024541c4071000c12910203c0c00f0210140402c0300140c604001c2105403103442c50640b01e9034070b4002c03c1c8a514484d0340c3c450300404c110b60000404401c101c1c0140d04c02c400442e2a245081c003080303811030302c0307230040e100d0344085c0c0e8010404200c0301b91020040307500540b00040c660313a0b22102110103c3c080c1c0d01001030300d601000c16000310240b030003102070300011540c0200100ca03194101240c0303c000e078080189442e44114101c2d58850344e187d00030148009000da2071a140c41d96942d4042c038107486050310700b0f058203402040004c1414540542042110b540c5241c40e091441d1034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 342378687 1250 342377437 342377443
    0x11220c03141501081018050402040c020d0f08220c0503070503060403090b160203010e070302010e1203040b090105040f0305011b0c020d06050603030d141902040e0a0b01090b0a020d0801050f0102 85
    0x7002e181c10050b800c0d02240503032800b036824030044c02c0030012016101c1030707041c0d040015000548049018900e0003641c4000c507403012508040c040095564215100d500f1001203600500290407a0f04000385200b83d0122480c0d1242c0981c0101d1090000c001190310b001e04042c1424130560215009810150410001a50120050040d40c1180d00c80984034420762220303c0c0304281410009406620b0094500d0800400040100481e4400d9842d10f411649030018400200002c98404a842d4011b11007404a01d101a0140c030707802c0d0040c03400d1401e065555011000c074258960064520340d644913000c407800c4000980d00b04201c0e40608140102041c01d070301150115031a480007400b840d039030340b0120b1902e0350701f8000c40300c0858041106001c404600a513095650f40203070741c81e03c0c80b2514540320061441e0b40b402520112000280c104040e81e8031440903401401030003020504200700014085508400325000d803002c0365451740100f004800e00c10018100340710680159100706800d841d20802680c1c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 342379937 1250 342378687 342378721
    0x2d0105040c1e051c05190b10050a030f0b100903050c0d482c06090702030c0601031110090503070b16050f0a150509070311220c0314 58
    0x2e85481950b8520f071105a601c0302403200846101c0c60705040900401441461603212040d003658810401c02d0108010418030340800ba5514008c12000e01681000e14040d600c015100c0804150129002c00d00500044420721119071050104020310014003c1c010100a0071580c40030030342c0d24108018450b10303a4995072800091700c42114621126030290790403c02c030380011140418030b042c03202c21110a2040d0b910740c041d008000601503820303983d40c079541040b20f0540c55074034441090f0300c407915141c0034031541d080014800300c2544820080180014010007900b4001c50003070341c01c5030b0b07072506141c10001b41d034031030b8190001017002815081c00555404213414044518107440d66a60310301001515407190b039071800c05440c13030042e580500805000411458442c0348240040c82040c0c9005024a046400c266035020039688022402d100103900e001d49002002e00c01044070361140000c1d0003c04101c0c20500340c64907006e407100032905030160140114001003002c01031036485c42c07400c103c0c550050095 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 342381187 1250 342379937 342379997
    0x20a050303010b1b0d0203210f0406020304020d05060705130b0a1713050111031e04110d030e0d05010b011202071a22060603021302030910052d0105040c 67
    0x50100800c04111003200101c0340302c0015941c00c003900c0c05c0041d44070f070403124180c458251140380c030b121500300d0301012034032400402c02074050340d8540e926150025000208200d0300b21281044500105004000b03091188216650340355585103100b8102c0000e004c20780c002428090705201d1415065000003007400700c0c05141c042c00030295030b9500d50441c0c820341904054170329460301a880c3d0b410080300e001944202c90085800781c002500c2030310008000d8044a024009281e6549941660721307000b2000c00c184d074003030310701103049110b0500050b270320304024a41152569902e144980195801104202682c2d15519045081030025203500080030486411041245000c0d000580420320004102a041582a40525414049240000052030b4500080c1d10030b48640c5c01c080460f86850085030700c1011a800070b032210344100c41c5017034045d00000d0100100c4092032456445813201040300e15860f01b4580072403500d075524010501086039043d012a804204c00c1151500c2c60b107492002964280358 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 342382437 1250 342381187 342381209
    0x2090a06050a0314010605010906020a03030c14030f0a0b1909090203030c0d0210050903040f0302010c0201120c0203280806220507030f15050f13090b0f0f07020a05030301 75
    0x5101aa140010300040d00328075409184204007006002161840181440c0c08038002c02100b0340f65401907400541503c42d003030069018080013000a80709401070842c44a01e41003200d2881d0229480301b00c607400c00c1f03891092101880041040f80340d500d00914014910950380244840b400c85c110142e1120540a00104a80c45850680440d101002100c04101d40c0c9006c3d42c545400c10040291100e5201c0750241200b414500820f10142c03021044900f29003500c0c404100882c95170740195441c0c130b85000e00b6418004a128080300742c00d401e000e02215002c0c02d90180d0b030348155600c82c603003072400a04100c840040703d0740c6600c03c81300d80122410b90081d908890012203185401c40c509003402d0800000e0001c1d0b420502400100354050308078001100c2e07001003c0c0040540c80100c5403a442042c441ca80c0c0c418606100d90134035043c045840e842c00e00307108001003418005601c502110003015280046003111300742c20051208107904045420510600c0904a8031407a0389429599003c18010710710200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 342383687 1250 342382437 342382441
    0x62c150705070302090403050a1e0503070e0d051606030617100e100c1e020a03080a0e0322050909120a03050705070b090f010f14040807050727270209 66
    0x21400300012401594010b01d0b2a085d86403d01d0010050742140041402003485c1d8854400703200042d0442c0d015401c955503440303085682d1214219280a1b10403611034100112220180109005112031001c43c60525840750320306161910007812108164006c00c1d4904d520340700c491a181010800c00f180c1102c0ba000481d00c003180c11112800d062848400c4002a450070b03c20002064000401c203000880e0a803080c4814044110266204c0d5000200100000c80c0c03240013440d80e6441e9408024031910907822039040c01003032619070a103202481025945c283c400c03c4204010320300b2081d0a6403200c07048002e0a0203110b00702c030f5131049000700700d54203080c0f540310b03c0000d00041c49081070310b22203034100750660b001d03003000d814850300d81030058036103845942803885204124129000d424244880c59a032011070343e0340c036210481c19400131002115a070080010001e410442a12205000d00c40741c4107980b401c8000303a10704000c80b0011130740800e09000e588246407070652032124048400350140c5007601aa = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 342384937 1250 342383687 342383693
    0x1030c0c06051e01030b09010507030c0f1808030d02130f0509070302091906050715020c0c0d06020c120316020109030923120309030f010905120a0513062c1507 70
    0xd40c00240c0e0503030f0000141d0340000309214811250318000c51084d002002aa22200000c505460001030500c0200700c5100c0c8940800e48031b0b07d2007621401d03c0e820741008058440d0301c0b080c2554440420300544c244c0100b4a2280001c402d11014010901d0207038900c0031a20789404684460001004035080c59801300394041c1d02d40341c101c0c111181c6101d030005010034580f00c1001800d01e40120030280c4211245402203401d41e40d8074803c454680c00c500b0f000300311040c4201c0401c0082d602c103400c211b41b059002c3c0406a10414104114105072581507006038503450f258050689034180316100804680c18000e080d000300c1d411031050420f44803002c0b10040f90b4030b58100440c5061141a05242c2c1080d009100d2003545600800541044230b022419580030f440b1050159090701c42c9620007806036085150390000c40c004510052448089504115060042d002c80111649100b0b5101101082d4400180e031020440246014529215808030942c20108840071440116445102c0d4041d048001a20814 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 342386187 1250 342384937 342384961
    0xc060b1c120908101a0d02060f0d09050a0f0314070c061119030201060618140d140d050405040f140c09030712140f060c070605070903120906020c01030c0c0605 70
    0x262201d20219980410590b038098002e2025100285149000285c1c5803610318000480700790f200d17001000f1504103100720030620b15903805140c4040e92182c1e14001000085c0082c8143c409450103400c1410483e900c604018040c900303e8105481c050104104180000341d0b02c84a07402a0307405490128400b81200c01c4151a0007411082c41c0310424200140c2d0f01010f90541100b4240c030f0155480c160003002009452404503041c9c0a00382100600a200c01c807542400e0b0640e40402c1c0c004c0071109034002c00542c40c1400c000e0501003c10000d074001a0074800740c01d00d8001c800f040d02d1601c9041111880710380c000c4441810250140d8818180021080340c0d07590100a02e00107006015080c1e464901c9511300058100c040802041d000c0c080c0315000c10400c40c02084040c860421050390038a8004103642c0c0700c0060000620300801d1000404000c4081010318120440c00300503620740c80100f074204400030b480c00f6001c1201e10b04040c2007880d03a410700c03a403110740b0400b0346a10141c04034041d00d408c000202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 342387437 1250 342386187 342386189
    0x51815131d0c0409020102070e0a0209100906031d150a1104091b0806030a03052a0d030e190f060621120201090803010308070f02060a0c060b1c1209 65
    0x35a14100412030001802002507218120038840469850a041c2814003050b0341400601a003d600061030410541c56200c0e0202d40c44040620300602d8202c004001030044407941440d400028084101801015014850501c01914903c0401c0066059402442c4d031407180308a00d03c3d01c08440e03004211b90400d0354014000403d41d060800b07440355101c5208000800341d140344030104001400f0b1200c115800f40c443d0a0042e0300160241041603916242614103501c0040100120b90b0342c02c0b44d944601034641540d540a64011002d02081c0b03160800040541d070900b1014082900060401c110300c0e041c003087c6405442d40803110304d0000a86092150045c99664024141c0302203000b100c08a60480c20300740708602e07100c1c50010444840d032030400c03822120040350050102c442040144003042e05130018146180c464801010320040300d41c0403a80300d400464064011a9200c075027a41082840e0141003554030381550350350400c2086d080c210200710310862000d4501e104452035940e00e03d1080903620 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 342388687 1250 342387437 342387469
    0x50c04051311060408030922020d02070605090d121509050c0901180b0405010e0f0d08030a0605060c0606010315031202060f13030c021219050102090a051815 69
    0x220900c1c0c451904407070800040021580d0100c01c40d0300c2141ea141c6030301510144c2d15501c000b1420314040704107111041009a016281c4040000c94500c00c45490b4001819610940c00000d603c4020500d0000c05441d03025103001d45030341181030407503010f5500c620115480d4a4441c0041900c1800c407403101c900014070b0704a22400c0382410100b0066043c048010140c000082c0c0e54090b03a080702d503405413010701c864000c0d410102010041000690310400c41d00c244407800034070403080d02001100050182202e95800c80d0148c0c8044100a11951907104100081c5410307602140b512008001403901c9000c01450030341030654510000d80303080c07240705001380515132240898004920f0600c0180d0745031001c544802148a032100081d000c80c8a03d0343c4048100e52540750401680c42e00c6d42000384131310030500c905100e0302c10300c5c510315605c0381c0a00c0c0d609a90360040000681d504444414065803081e00d070401405450300000c032030701c90740c6814035481d0f100000d0303044000c191300710320b00007141040540e1840d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 342389937 1250 342388687 342388691
    0x70512030a140123010908060c03071707030509010b0102010b0108010302090a0603120e030601060e18070216030f02040e15040609020102030702060a0e090603191401020c012f0421050c04 82
    0x4610b10780e409401c42c26002128407003035880713009000111a0281203000740d9185412880c0444c0701418144055a04038059061040c00c1e0b44048d02032403c680c400f02d940380006a00c94040c048004028460340104110a2009021440e0b8020000c0d05111040c40024000d0811a0003d0600c00076030b440840599031004181c000811951401050544010300d0340d403081c05070384000a4294062030380c00c00740c0070001d0002e28518140c3c080380d0441403c020300701cae029800741d0034886207400091207005000d1841788a0b544650f41d814010b1008071064400860110351242d46280d01c0c1c0303540108100d03805580300e4004101e07811a80300403410b500030707c180290002000b288103026190002c0f003813000e88005031407100b20340e5611020181d5401c4007907190514443e450141102040b030703c101c25051480c6020003d40b40003542e03448c0314216a001c1d451030000842e50140344000800d180d02d6182e60328416400582811300f04039105298800c2c443c1004448005045100100101400b09084849004000b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 342391187 1250 342389937 342389939
    0xc09090507350f1909170a030b09090d0201150503060c0c070305070b030609160e0d1106030f01030c0803040b0405100c06060e090d03020310030318030605150f010203070512030a1401 80
    0x100e9100c006055034002c1040c500100324542111085c8202180702d500304000d06260000003082c044140d1142c3d03850420107480d44042c4d60750342c0758515010300854000c00146480c52003140c009084400ca0800a100c01103003840803c50b2355000261250042800340ea0b4039034170520080c4040c545042c07603000412500603010001807461740180074620480050b100404c15030364854050007402d070340c112010041150704e46c6840080c10102008200c151180b40c0704000d41c600c20000541640089039107031035a03034030140144100415481008002c0880400a500302802c0411540060040b0b00400780214508419056024850b600508070560007040800c011a11f0306034028030702d101124020b409110725160841441d00c241708891140302004186403685040d40d900b15940c0807002d070740310823105510b070000c00800c03958400c0e1400f6001101104c0d44d069215002e0210484030030741c603141550014040080400c02c003081d19140c01e48094a415503a40d00c168021000b803144414821501d403038000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 342392437 1250 342391187 342391201
    0x21002101104050f181b0c0f0a1406040b0a0906140916060f12020d06030b090c010206060d2006040909060605090f01031502031b0a030c0909050735 65
    0x3008205944013900c0051078a50078100703009441218a0103076400444200000e078100d0b4031388070b941e910944180030740c80c42c00313008503000c0d032038a5000e07034804e40c0039041406903e0800c45005224141e540245e00505000d00e0591142d03058200300a040000315610342c2c402030f0030800d09a02c0704204000180f40da0041e4249040038030394850f1420b114441840075000003150071030040900a503a10b0491b941c864603007440700c14080103908501c5c0286d80030350700d13050040000340d00307147d40c2446101160010000d40901100081c40c00c8400380c18140243c16018050003c16860001d041900039005401c5ca9005203c10220380c1070321559000b1000285012900002c100032504140211207003164810420380b901a1520058442880014a0626407602c8100c09000607005036a2101040c0d0105640c0c3c010760700450b1a40d8805841c07400001e55903580280816001007441000d4421000104600c0c07070241c0380a4100c7d07030181c101c41d1040051a805a540814120840b1040410720040182c0b80c18011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 342393687 1250 342392437 342392471
    0x31207020c01020f010e0705040b0f100518010305160804020d0c180605030c0a0e0705040306111b1641122b05070506040308060102010f0b0a0302100210 67
    0x107200a4014020708054100a203014000c18800054074005021100d140c181003100914000d610190010f81d0848004c02c0b55942694030002c44920f500c4940d51410203141a85001c1456001c02d81810701d44014442804175980400c00050100d00b40743c2c4440d104ca00006103d1961417100606020694501103280703c1c0d2000c0e40c90b11400803500c140016501c0304201500e0340b8104110540114042004225445e85124481c1d04284035003840381c0fa00741c60752201c80c00e889204034a60407001001402c0e1209410243c0c00284000302c21028000f203c0781c1112a09948a15100f0ba03558141700f802111000d29a0f1150104030f100880d1035800315520320984060403801c2003442610800d01d400300304282040105001c0514000707000d00c88414880305002901400010000c40304111084c0201000680c08011990107940648c4400d40a407408030002402d44d44a800346180550030302c0b4580c80d140d25018032000075698120b4104425203040303402246072115000c404440107041c4803060019070740d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 342394937 1250 342393687 342393703
    0x60103080c0708010603080910091809030906031e0b28090b010f09271806060b040b0d1d030706061a250c05030304062f03040e070203120702 62
    0x1025141d002d41c1d01c20915080f82c041d0300c40030300034000402c071040491900f15400340c1c0b00003650801e141500c0e16580001148111501d0608185035165141000c1c55009050000100f255103400d00030071031940d00080801c03600c42092409a921050124459070380c064020101074107245a08606410007108484668001d100b0008594901100c004295100e500940b080000035102ca4481528050344101210000d034862030206140c40403a5038000c09a02840c03008089007660f21008801e1070030001c0032030359603512010000700100410410721104c501034403200010740000103099070028003803503240c214560702c0070602c0c040002c25004011050b40118181c445034000b03184500607010500c00e051144d006250008501400ca04000c85c0700560100042e620880070f0304490366507003004c80d00d0b61300f003030f00301c940882d100f100c0c03030041030305c046030b0074420400301241100880b40700072007041d1207129a0183c9900c181c800c42c001020640200308070340013030a8030703100c41c0228540402d0083d00c0d0012 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 342396187 1250 342394937 342394957
    0x902090907050907080601020a08120405010c030c090b0309190b04060b01080f041b0f0f05010e0a05010c02090c2502010f09061d030a060f02030610050301060807080901020c06010308 80
    0xa400114010160000d2028182c61000d032000319203840d0003105031503c3e01c00803c5070b41188101c020a5001400140142c551010424078410840c106440c0c0309083d25850b004bd003080520302900300743c0140d400401304040340e54011540380d80351240400c0f981064455101001205044080b003410006a911450312490168108006628a02d00111040c1c001594480070802d41d1201040c00310f84400403030704000000e032038000c200c0c682e660328462103d40564011403006c481d02703104104035604000544140d80e0100c460100d182d00f0800044d00d0000d030248040d00a61034140001c083c43e00700400c0b244a80d4920b2001c3d580d01000c1d25889450000d256402ca00080004803c1e034949401020100700380c4502da160465210300b0040c0c50240c040d0721a8419605101b96170040b008500f0034455480c4118203110007595070b18040c0180035002460741c0a0200704a010801080071a83c0031401540010b03031841e243d00b0544682000d01d0180c01031050042c01402401c000008011100f002002a803031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 342397437 1250 342396187 342396199
    0x10090e101505041d070c06091103010b010c0c14030a050f0304060e090609010603050912030a0c080c0c060c07110310090b130c1205010608060705070317071e12020a030902 75
    0x701d0410100c1d524000d52084140e18001000c03403001184101c00c0c1d10f94420450710b488080c2e071981c0d8460030103807007940c907054540908080720340c070703803402c0038010031085000c2030801c0b40300260701d690f4500d0051142c5c4110490013107190310301501640c05014000020741c03c0011900380d40c4000c020750b03440740c8c400d104410200306402c03006650307400e2640003548607d8006100c020941c0c44c1a8041d005058014824416400b0b1076510031820740085010354002c8600b070100140007440320401070004000a8410b00302c440e410b0124104540c00001d00c503a01140d2400750584a00309881d040183c88803c41029616008141001000c43d000354000914580070780c103506100e031241a10503828180c0f4860180c80032861400500a418400107030044891103200002034079540d40d0502818040c0a0341c11000058000a00c4000d155001200e00824100b50594660a0034400d40241a03000801041c040c0703601d01c1a425048076000d00c9190300c0c0414170b1103041d903450311342c00c50042c014040160224401c41c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 342398687 1250 342397437 342397469
    0x2060406090f0e040317090705060f030604050f042a0b0a0810050f030a08030c07080703110111040f0509130b011502120301060507020d08071e021311040510090e10 72
    0x100300c1c2421180902e4260b201c05201c400c4481000d0f85921004107110380920231403000103807640300c500080c034502c40480c0d5000c1d12420441c0421098503000740485269040140074000800c0200a1492541c0711000404000d45007004d407003052265030b54040b0701c8000004c40c070580815080011248605040c1c0100081c1a44036010401c0a80490031382503010380c010350301e030340000d0401700046400007492241141044965964038246510441003140084d19401e10242042000d008111003d00048601400c1c9400d0062000010a01d48281c912942c0804042102650300108405003140c020f040c05010b5038640328648900c0b68070705c0c800c80c018812450782c40c0c0380ca03032420180d90607102079690349844c10b41b66030208403112038002e00c1074038054020400000002c030b49600e080395021840824105001e0b1500400c89011004d034040e500703950401c420300d12908140c030b08440580340211246807031883d00c0e460458500b2616040780381340c05010000e1019104204111108451003124421214 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 342399937 1250 342398687 342398699
    0x1603091e080d0c15020d0e0a08071509020d0605072f0c040911040209120708070303110102070209180a0c03050309040e03130303031d030706090203071205250302060406090f 76
    0x5101001d006000c1406038440000101c1042d0002c00c2c10300c41920700800c0c80d0820301f00707031400c24585010490742603000090600800c860491081450000c101c02000411443d801141c45941c140c41c1c02440f16544200040145020b4000c0c0581802410840d44003804c0c41107040460b070f01c0165101c08a48140c4540800b80d01c0e19020700801d8643c040d440d8030701100c980c410700002c0d41108981c99408102c02c00e885d0f900400801101c8000c240d0304006044c50380c5541000b0308021400d012410340b69004101348805603c90002041d0000482c1c1c840100040216242707600701080c1d90002800b07413500036030000c00e00800201501104504403401c028416140740115546d10a111807d10300c1000c010041001c24002e5000d0991340c1503039030381c07840d2a12818038414116404608220380b40d543d2183c07000700b94101080f048015105c2c13100d0026069489440f00396880d0201c01036041d00c1030007407039540c5004100c8012030b00119401381c01c4649494440c00c001d800312000d40600e40360041440d00000d05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 342401187 1250 342399937 342399947
    0x5070f061103161202091318080d060608160e0d020103110703030b190e01060c0201021006060f02070503030301060516050f07030311010b0d0c030b070e06030c0904060801111603091e080d 82
    0x19141d07004100c3c0c100441100d00e9000601024048c403212903145056040c0411328a034010710410111140005540381800ca020700100b001904005005984005043d006034200000c45d0400c582140e02619980103480120013400d242403024030812000310b001c204058158014400c088030460f40c1d1000b240d4000755603008a64180301d09011115040d0042040d14000c000c030041e094010b1041c0d8818681c0030041c0001c0c0c5441c2e50003800007442214142442960501c0001d02500c4228099441c551520000030141d0090540941504030003404002c1003040401036407004282950994510564a0a01401803c9020444419035003401c7e94003a503450001c603525107030395204007440e00080c1180c40302c4008400041c01c10007840001140c210036660b40c03d014500c03d400301192660b89969000511040c0c807191f03401070030141c1c10003a8811000422100b0b80c2d140c0c1081c2043d815102080d03040444102040350300c0340c10303032103800c80445100300303810714801050380d50030f07000c9030564143d444085030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 342402437 1250 342401187 342401197
    0x80a0b01050d080703050c01020d1404020f040917090f0d1a0f0c0f0c0c04051f0602060c031501091503050105040b030c01020606011803051204030506010b0a05070f061103161202 78
    0x48070000401600b130003e8080c0014210a490301c50005041c850104124000c13280000c610441c8900700504110451800c02d54440101d1801d40d0140710909c586c0e551070f600b81c2c44116030143c0400340880c100c0c0301e0f0b80343c50030402603c85000700a941040c10a040007200c030703983d41c0d091346802d030042000a9455250b40320344602400344469450703d400d80342c1448180c03030b402c154001c008074064404103c100341c0d924012140283c0004043c0d00c900d200c038001040d01051558044015034000800300f1801040394401d4a5109050440701d0b00c0e00c001900048402c032500d03401200f0659440142d600b5242ea00d13900060581e1401c2c0e508200c045007400070543d5031010107142c180184d2005c030000e562548165400d600300120609100c0020b44c403591194281122210884008103000c5400c10a1040c200505801001080340302480c2105034080101a48a0101c018003c008441074510400c08968084110030401100781612030401000c0c4051550080a5100016440e0680300c0300150252007110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 342403687 1250 342402437 342402443
    0xc070305040b1e030a0506030d0f080f0a021e0a0216031101110115030609110907021507170115030c0302040f12020301020d050c0309070609030201050f03060406030c080a0b01050d 79
    0x250400b40b402d01d2101e800e0b0302000c50752410061680759510586002405940a160780c1c01001c28903161007410f151401050715895020007940001c00f2035031682042256410610260040c045541c50454000c06841410200044a040e0660540c6000d01f0b010240c10308481e55030a80b1f01d07040a0f83c85e03500342c9110a0201502c0b1041c41089651950b01419001c0002e040304c0d000030030b1211000901d0320210140c0d07481526815110002c4504009240c6803615000c04200c442402c1030a103860b0080d5208c80c2c40d8100642c0c8048103022502c240d0280741020815244034200710709941e11a0851f6507010031003040000400c1c04c14040060541c0280203440079100c10000f01e542d60341c5403140705402450024400d0360955400c0007410494480c90152502c503044404072981d680c281100e52914040b510741c0240c1c20401001740c2032005030790101c00c4411907503001302c0483d2a62103070800203006144541c402018560794032000503000101190501300c0d9030142121607200d81c3d80d40180301032030b000c80d0f03001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 342404937 1250 342403687 342403697
    0x12081608011404090f020a15031803050a05161707060e0111090420030403230304020907050304060e0703060c1107080304060f050f0d090b1e0f1810140c0703 69
    0x186810342840d40c08a40c4590140d00c2462100405d41c01040c2d0980168120310f512888628900641c0c030340601078a141140300ca814200e40650503100208130b4000c10400c01e0401c10b0003e40400c0c00f036858014014500d41050454861513003031070481c9055400a00211045030501030186055074062103101142061104040c0c07400c410311040200828074400b40f11480c9000084455081d07045101452245200f600c80a0f101c2451010062211814490948008008104110042c0c40310076509411940c0703400c3c050703200c0d12503290507809442c030444140c50314881d03030900200340303c0d1a402c442055800b45e19031360f20481c480302030303140c54540c4c5005580720b0341e104100030000c883c800d105000001000746070480c104141c45d41d860b8003951100744081d221544910035681031151856002d0340150764100c0b01c00181140400304d42d11200020500090603c10200286405a1018091040b12a5002919a00c2c3c50a5900000604c10381940204078288980021400300e2040120707412150145c0340c0e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 342406187 1250 342404937 342404969
    0x170a11010807020102070506010e0103050c1012050a020c01092a0501080103020d14060903092b0f060f020a110705060a090b0f041205060a11040b04211208160801 71
    0x1552103070400707426141159402c200c2800462800d1041c50f01174030519012207010351560412500e402079505100c2e00c5000e4903100450520741080c0200403d14100c0e0010625035640303285017000380108a81078086500f405440d01c1000101c141d01441c1d940302030b0702d6555842c00d5503000c0200040781e004880c04507110300010b00140c900500d400940c40c0c410045040c3e5070009590084c100340d401e03a0029543e50020550300021301d050840458001d40c20303401010409080114240224001400644080d059609400600c0303101d410030710f400c809002d0207540e01d20852000500070402080141d4490054030300104861400b9422584680d2095403500040c0b81842907042040e4000c40003210004403c020005401051910442145000348054201d5181c40c52100081c1ca082a0003510320000070041803103c941340805640c10390b288480303030804014055220800301c00c05100040e00f0300c2c040b07020f401038199000727014a11132905850700c07102c8c0447d101c0c003c1c0e418403c00e0080e4032240c2c910f0301d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 342407437 1250 342406187 342406189
    0x20906040618030f0f0b0a2901020115180501292d0c2527060803040501091a0a0c03120911030c151e0d060609170a11 52
    0xb820380c41007400c08000c030744029500d90300c1c1c3e0902c8005080c03c03504601003400c044e0600404403403090b0702211000c1c0c2030140009403901d18941195a8181c101207440301584c40003140d10075400450b01300c42c4128031100045d15a5901120f090001e9202d078149820130f000400c03c00020008201c2140312a601601450b003405210300d8550884201c030b0210484222a04028401c0f00c042030399120582010300707075071f4000c03003d40500f000e481c9072000c610801c800860780194000c101a610444400c07030b20898003031178a18212150a05204404541d150030400c010900020100051080f10402d032150840e482d0b440b030002e140380600121040c80a601400b13500003050269441d00303580c500c01c5c6085040220603200b0311044408030700f0142e41b04043ea10b0411003900701007140c0c0e0a0100e00300d9403802c0c43e02102d506070159100340c18410029000071541050340788114003c0d580e0140c1040010f00c0519140c0400070455031851140d58000660304d030f0403000703000001c80e9900e503a40d041600800c4a482d040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 342408687 1250 342407437 342407447
    0x406050313051c03050a0b030c01050f1605010c031b0c080702040207050d110105070504080703060b01020703080d0212010b07050c040c051603350a0902010903150b130209060406 78
    0x4010411015094507107070001941804404000e0203200d0300031940c0c43c01c8aa000b000c4880041c80030340f4070341c548450002156000184602e1280c4246000c51b540c01441714410801d00511400e056900c15043c080c2c000c000040d00131134000585542d04219030795030708018403400d80d40c110304040454103a42420010a00a200a06000d4005400585480f50360783c0d400b4605581481c4240001c1c1d10b955120758403403020300550790403821a00c0e1050030710742004940c54454025100050100d03558000c04c04040e4000e00c402e100071500708091a07281c03080d0300d404802039400750b50f0040c3e454809100209000d42a00309940419030044000c3c40c105010b00309010040c0440003480050000a0140c0f08029980b00700c090903492090380d034450761030310340b0812004009aa55480c4142e09d001c8005280144400025541c480d034805000b01c2c01280e58001a00c00c1910f60300054840d41c3c0d032441805500c12150401160600141c8400c510101c854011000303e019990300f0740da00c030904000030444c5500c54 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 342409937 1250 342408687 342408691
    0x30307050d0b0a050d08070501060803041a250c03050c0108010b0703030c030f0509010f050f070c02011809020a080601120b032505060c010506011103030402030a17070611030a0b0402070804060503 86
    0x43c1c000e02d4010780300c100040000710130841c1200c0315400000c04004200e02802013100070050a0300460a00c0d041c82c0b00b401c00d584802c0f602403102040803600003035030850b503160024004444807001d102e210700ba0500c082c40400502017540c40e0f10402c0030b44007065108444050407140c207401428204003640d46c0450141418041c01400c0540b6035400d12606480c0d403103101d000e07035040c2000081c403803900100a404c1c0c88005010303a8612a00004001203140c0101c886180301354240707040c280d4040f0404c035041c0d40700d503039400a040c1c41d4804205800c865410800d4903004a0007600c0b42c0803110f24008000064490080000390550880c498a034010f5086441e014800c0104045c00700e281a11103004c43c0454020103841a42c907916101403040702e50300011900f6414a528001d58514a4641c021a68588130743c9401040d5855141c8000c00c650350181c1900e211580c040000d0003e61b104000909040c0c00603194001301c0d900d000140c85080c80d1500c210750345c0c0c030f5001000038100f5180c182c0c01d40e15030b080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 342411187 1250 342409937 342409939
    0x9060203030432100b0d0b0f04050a08030a050a0506030a05070b18041401090c1b080703270f0b04060e060703050f0703022b0c021905040e060103050f030307050d0b 72
    0xd200043c24101a80d80f01c1e02220314248010100b48180301454001d6450107012140908502d80d50203010420514032150300c0401c540f200d009580325072400300e05e0f00018540203440c0354008004d001841116410413030040c6000041401030f034445604160301c8807055800144250f0103128100b10b001144006082040d8103d4420250700510801040503609061811266010380b1001400050203521486900c0801d9250541002190314080f080c9038240c900041c0c800c4101103507400c10103109072001c60700da0000c6101d641a030f00c40411010951a0b05024843c41080c6610b00400d2010485098404843d6290395510801440200f4442550701440090b41042410003c3c2410408468001d0003014460342c002d150b000100c12001c1850908116580b51258806000400c1150f1110020023040c0c0c04850310094251030b1280d103144c2c65610341c0304507005424040c441c50803440100324141200d00a0040c5d45800c2107480c880394691100326a09001705900f44564130184c0955070003207039082c1d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 342412437 1250 342411187 342411233
    0x30a15080307150e03040308030108070801022b020d180215030606090f060f040815060d1101120e010e0a05010509010605090f070c0b362812030b030607090602030304 73
    0x264101c5517825944607030400d848818000004111960081100800030301380d48008609043c14500110704a2000422001c1d0030b140e01285290082d06030341c1250321300840d141013040440d0ac40c3c00c03079014101c032000081c0d2107020b520765018840500c180807280700d02c000070301c9140345c01440010003601c000e0304140c0c81d4015109200003002c0714524001840900415801400c00c050324440c031001100d4020320f00c0380103002c400890f8000070118541c0410102090078592a0b00345982d4a013001890381c0d0880301459824554100c445000c046841c18215014030300901c210b585000c1000c1c242d810740d114550b08100d02c0c6000800c8643e6140450b600010035240412041c011038955402191056410302060721400745480465100e14121480c103824203a5408000016000c02517220700744d076440845a58041ca8000d0841000813230303544e904a070b0140298860420259008004003c0c520a00c0d020b840f5800200750594020098081150041d07401507185503600e030b9603040c2c9180d401d0a5028024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 342413687 1250 342412437 342412451
    0xd0905030405030a03080414030406023706020307120b0a050906011209051e0a11040c02100207050106090605090405061b0d09030e01020709020901051605071208030a1508030715 78
    0x650f050100c0048240240e0303130b13103003030b0305043c03c00d8903d013403001c03403200b080e03a100304030420840707401007101e84603400d81c00070b10058005241c400007003210b5020083c940c240f000340988000c02085038081c5000e023000c1d80e1201825210454910304035884400390a41c410f07403001e0100060b02c1c1c00345915521600c107141056049050b00c43c0c000030f56a045408850303e4204e281079004244c65500340344031901418004102c03c42860701c1e1203c8007400d8806050285407903900070628a8000c12000c641c086102d1800c40da00c800e2810300a00a005034020340004900308500000d4901c0d1102c880c902598104016011546a0f80b182040000c0b90345000c00c0d1082c8203003c0c020194040307200740e100050203a00d40303003180e09145c4002810400640c014084d141c1c0305100321132690740d201c01036400210a08407080d0348d0a07101d08280c0e1810344540d102c548204003800d489001c00046101850142001034001d0200c8521482d282c00840520b0142c41504d41c402e11111001c60b283e0f81010303240d4007600030009480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 342414937 1250 342413687 342413689
    0x8100b0702091e011203020c041407030e1218091506030a0207030314070c1103011503020f061b0304080d09050112051302030304260106050a261006080607090b0d0905030405 76
    0x28181c02da10481c03005518109045c1415014401504241400c50317040100c60340700b81d5449407080010b40301c0c0c0100341d940c1602907840c2d1010440d0084200400703443c1d0707403a0098030310a10700c460070242031316019040c0c220104881001100c0c034121107080c000c148508560314002d508009400140d0103900b050b44032184442d410ba002c54909005445540d6118442829401c0a0800004082c007040c0241c1c50a03c00c051034449499000d800c1d2030781181d106002c050300d100011840d0096000a500f920040c101413424664000018403c940d4840283c1c7c0200c2080401645c0030744071480f03050301160000d220a11180d00690240b503200c0c9404007a01031016868007c03d1450700550810103510050f402c2e010040c0c40c42908014000f0b0010780203105e040d0404021620b641411300c140b004107207041c079584244160703421740c034241d82d49000f044810300c92103504640090704880c412814203000fa40046103040b40700b4040c400540d10440005454841041140070003044240010b030740314001800b02080da = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 342416187 1250 342414937 342414991
    0x3070b160327021e060306061b100b1512180109060c1805030102030112030806010c0501140403110f1e07030204060b130f060c020906120307030206010608100b070209 73
    0x160b000c0b0241c20391030801a1050104681d003450013102c0300105240155440d40d950b4080300e030302c002c3c1030b034419885c2c0103c400c03151400b41021404c0c02e802c0c0039000c0b1002203150180d1103660410401c45030144202e82408070300080e8415041160381c0c0c0304840d0f0003d0540c04c401d9440b4401440c620380000b072400d5180e2984800c84049141003c0040d150038004e40001640e814014003a0000b10021840d55140c05640c0310704003c0c2040083c28010a07400280c0706a000302c80442c0070f12b41007402441030b4128100410782e03400d02140d00b10302141040c18025074003c03000bd04461101180d4008104611380740480492080c0c1c010aa10303442d2251a1001c0010b03203d07402040c1c01400844140d41c1c40301000240d0001c080e03001e8100e02d09841414908016050b03101001d01481e940564026820381c031403501055502d43e109080800600c0000b69140c00c140d400501e130341c121260780e980c045882d00d40300044103a20700340d80320b501c0a200c0244484009460407502054014a5901010040e41e800180d100030b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 342417437 1250 342416187 342416231
    0x301150903080a0e01080c040b030a1814060108010f06030b060904050111041710020c06041403040b03151e13050907050406030c0f0b040e01150908060901020d0e03070b1603 76
    0x180c4d194603000005d50b00310316240c1c1c00500d5000400c0c200390811002d17102c5400010040543d00c1d444110800b00c08d50203600c07d4018940000c1d407013a4002843c0c150903501d01007842088000d43c40c090100203840e060340b00342002e4980c42082e1a019031565010400202c1000e00140c83e2035680c0e409032062201054010320013001c000300720043c0080c01001850419601039014003134680100041e80110002244681c0d0003940301c1204042000c90050603071850203503130411006807500000303212175400c51814504011b80229401c4908500900b500d002c46071744d020b540c1d50812201441050100c3d2250800c5600142240c21254500e07035400006050f5030240e4420344200e407640c102841300c1c500841200c1e01034820b520800c1c0c649483c00ba42080c0c0480144920250500c429040344c1445100340c00b40c0b801031030b0b4041140c2090901d1402503000398132002001c01c142e480c3c0902c0c01154040482541d40391500040d1650b40ca80c3c07400d881c14074003071081007418200b640e11601e106500701480e200740 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 342418687 1250 342417437 342417457
    0x105070f0206010e0c090922030e1201150b0a052106150f0409020a0512101d0c1801110f07090e03190e01050d090605060f090c030115090308 62
    0x2803520300040c042d04111043c1c00c24070f80d8282c0c020030003600014a034119040c00d00144c5083c4099601d60100c0d60b0360b80300d0b82d24803c482d9902d400b801800c3c5036201e019288050b804442018080000007010b600705ca9503040d40801000981908110f10a40c4001500703034029142010b0385064041c110421040ca80740d444925031403c000e0920070f4030304004103810000220196107170300d8207041c01d035003d503603019510540040640029400100500c10410303522114a01001d0f42c0ea03c0c10b050340514424911801200f204e40a101004148600500b015901480803145035514000c0d0382000d400a60a154000a052020708004040b0006041108101415802000c1e250060401404000792002d403903071403400d94018080a055005c110394803a20241107424035442c0c0d41101c10050303407039005010b6003000300c620702102c84080c0801d98108038403464040345e000001700030680402c010300c0d105a5500c03a07070990600050240d408038018681115146080c601012583c03a5038900035544001010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 342419937 1250 342418687 342418697
    0x4020417060c120609180607020d030e0102160221030703020c03070e07051b010b030a1a0903030f041101021002070809040b010f020d12021b07181802040914010507 72
    0x100140d0340a010140c1c201c1d4070000c1c02e91604424400d02e805240d0050400c0d4424030700140401c10910402c0101c1d0710310020181964185c4ca0b01c0c4401039120800e50000c040070034185200d2103000e003410710803102c1c80c5c04680030002c0c0c0c1c9811502406200442c0032050300c40c90301c055141a85030202000a0000d441c480d900502c00288260241030400c80345501405443d14000c0a1124068000064030202c1c00380b05400512000d203091954091b024004129406016801003a01407100d08031102c0380c506002c03800300e06203840385a0516641d1000b103800c0c150b5802d0010102e00001c0d01d03030703528543c4058148125120100f00a5142040f6030202000301c0e2000800a4060b8013810700b40903a0024001c24203100c04000300101d006903c5101d50038030342c02004103060503007803000241e606440110311066a8030031503203014400a039036554a402684503e564010500524031881e014085025401162140c4621080d60134403000d072a1070b983c00c8501400c95070a402030b441c002d200e03591140006907a0303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 342421187 1250 342419937 342419969
    0x70204180503071104020a0518192c070f0f05070b0c0304290c090a1502010207051605010c032a29060307030308060a0902040303031b0507030909020315040204 70
    0x3001000c003541c04a06800b40c0d005215145807c0c0c0c211058464801c50854204480b03032840001a030750f034a81c180c0b8001980c0000f040400da0511380e120381c42c036011640c800d0950610070600c0b0461003d0086403401d002449140141e16003511501195503a04090b0801c2400c0800d240c1c0c5408541c0300855040111000100400007030082c522032907507403008454000c01d0164174481c40c444440303000030b00c0b41000d8100050000c20948418011000419030141c0b801e04004400400038080d500070001502c0c54890341c5000e02900702d0b0a40810f0851301c0507140c4203210007c5035815640100d14202c0242c0040d00300d621000140e014400c10080c003441192602400d04203228201014104c4010090f500700da00420008581c07000907401c800d4a8160500d2080ba98691001400c606220381241034054004174000080681681104400860310122100c644500800484080c00313604405000075a44903c1084925410750013580c1180f000390802c500007a80c00041070690380940e00041004000e03a803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 342422437 1250 342421187 342421193
    0xd0c02010213060315260109110f03071203030507140a11060a0b06120c04031b080105011a0720100908010b041b080a141f171207020418050307 63
    0x5220070281c81076040805c0001c3e10600c4411880d03400703005081090782c00880d040050420070040b205907600f250f00034404154140352124015050040351030059003113090210320f514000ca81b400c00c0e07407400440c03c3c0e442c59042d2001c41c054400075003c00e091010019032400503d007054020103a41d2070380d480350000a0311581c401e42ca0424001c054610305840c0c22010b0709540e441008444a450041d96400c040e500c036400c0384a0103100c2d41c1d1000341407143c1065124502090b44407050120780e6240d008100320fa84e1400300c2ca0404960303081070f00201e0001c019800005841501d00002145c00081003440b00300324401040805001c0a01c03c4040340040c1350030080004240070b80301440000369018004410f6502481030610300910750344007404025800a8503040c401d5000340d5442d10760340300d0401e40781802111494501580b114002885400640101d0700c00725542121030b060825000600c034086107201e0080b40d40c1c10200003241d010391201015401d041d401008030313045500503009103a55004500e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 342423687 1250 342422437 342422467
    0x10020a030b1e0315010f090209120d0816030203010311120708030d09051006061e03150312110d0504300803070f0309082703060c0405041a10050f0d0c020102 69
    0x105101c92413031030300f074010b110f14605002607604480001c00d025031680f61000010b400c20072980070f00c00c1c242c800ca0024030304959208110500801c0a106410300d40b200c041011002e03407209020103400d100e44110400b85030305240040100d903031034060035542c1c195160343c00345055a02c00102c0d031000c10b844000c254180321040c4030a9200076100002089650324001d4041c0c0080041c5481103800b00d420504450141c1c0240c00c81d124400c1490407048010361a4541071004201c03003018000099400d00c41e152450030300141201d0600d07100d898241c1020329280e100f21ba6a008601c0210140090342c801040381d526904a06950510070b8068030b40300d10700782c1030042c40c1c807010310314000c10103052103c800c010a1200085039084600d500060009034041d007540c6281c0441141920342501c101d0041000c2401c0b010003030700546501301e034240200751a1303600000e250041080c7e21a880100300284102041c02940101172004124405500b0114600d0321401142c0e1817481060160b5000564280804501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 342424937 1250 342423687 342423703
    0x3051902120a1415100510020f0703080a11150f0712090804090b0d080703030b06090316030b060612060409060902060721030e06060f03160305011401050307060210020a030b1e03 78
    0x180724946601e1508041c2e564041c0d546211b00c43c0984081d00f55421641c3c802e1205503160300301c0750111380e543c1d6684e10300310703a1075440600b0100c0001c4050f00350f5000304c800401c011048511004006a00781c854070a410110500a0030b62000d005018207010078441c0c03580205440e40d80194003991f1980d24001c00b0105903854504080e10900c0b40300342c0503000626220603291060740520740040c45c80d00c0b91020860030b2180303594040e03151080ca50b0355007400799183e02d001c1c01c4d28030940b1100401c1d00c505050064a0044004074012401c02c03000043c51828142d10510740140501c80204030000c1c940c0204085900014055075410b000d05403a00207138411070000d00d051102c80c68108845404110055220035026000d14820f020008554100d075504103c0c650020880e021450045076407072400500920390402d03403c484100c072a000082624001c180b100c01c07200260042c05500306030281c80c0c002540f0071041c0324285a617074100328601d0f4481804081800107900301d2500138003841000c1610340860 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 342426187 1250 342424937 342424963
    0x203100e01050114090102011e1d0102090609010c17030c04080d020a0209060d02031c0e03100605010807050703090b03161205040c050d1401020a0c1b03051902120a14 73
    0xc60041100380d0f448990101440d4501c03d01c540c40b80b110300c004078007400310b600740c180e00c80c0b040d1140c9001c207000a40c01f444002d108000394203030b10f80c04c20b0b0701c0500343e00490035119804001440108080e50188a0b4200250700c29002c4115044201c15821f096410941d901140c1000104050042c000c0c10040c41c040d000207400209030071209540042c13110a4002c10b0b0310300070071307500046100710340381005a0402440c404504a0aa01b040c110040144103800300d050310034400c80c40101d0a44405110300d106644060b550300c0c0d426035407044152116402a00214200008080b00151122003540514020020240071000494090380020808080c0301c50034602e00d4a003405000009540c0d2074031300c00b00d82083e00d142030446034034140040c2e00040c2084044955000144030004998025198002c45105240c04a00034900c0c230503038000b045040c00010a184d1003020382c804d400c402c68580340107940c0b000b0034000c841c0c1809881740d4181465980112400700e0180c00e1b003c00d255042c0024214900307 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 342427437 1250 342426187 342426209
    0x10c17010b040b090f10030b10262a1e1201180b06070f021014090f0406081605011b110405090a170a0801090e1c0201021c020310 57
    0x1061250141d070610461240b514400000500800310ba26402d5100c140e07510020300c240300d810310001000e4051f10800c0a42841540544c04284056006010b0888559584044040395a010304005c0003000000b43c18078000280c0c1008a0300c415030800142503c0c460504549078540300c5003121a82007080c50741480c0b40740762003846100c0c1c480d07041904181c116221428555401d203c0d8140c00c0b4024110703040150740003d0005a48801d201640e02481000d42c800e5400c02e01c0d40d20000e20031103040c0070090420310442c0c810001403000d49088081407100c00001040000c031150344007002880c00121650301503460740c022604101640e0032804c031031010344003a40341003c1141c0580e16169840c00000405105550381c0c0007181c0f5802e07080110940300c99200c044440106a100d403201459046103250200181c4d441e0000308800c42c00d07008031500d02e081c40005288c99106400034141d00300d15840b001003190350a110440e02c10141c403002d192607c00d00500181c1c1c03414240510040d180c025089440e400c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 342428687 1250 342427437 342427439
    0xe030d020d0b0411070f031202040b0322030c170d050411040501090c0e010513050402040e0a0c0c0c03140a0b130302011a0616050106030c1403011514042c010c1701 72
    0x404c450302100c80e041e50101c1500c2040146142c252020902ca122080940d480400e0104940311810300a5000c5d1684ea200c8007c61301d0240c6864000407107191000300020364031501040001c0001ca094190742c0b0200c000241429503802416045a6040740c060710424201c46400a0504140c03241e5800b50401c80305c28009c01000e948040c1ca2a146042c91034100321001034107403802c0741d0081034600a4407006006550740c0f9980e28081048084c26600c10710307828a0b009030000740c1e03401142d40c02c01043e07004640b00708107442e40d10b074501d900c100d03070074184040e0086c03c000100203940c07091141c0c843d8031005c02040030b103034141c03c2c0282110044204040080381c00200d5a613141c0c0c0e60010b80d801040300a41440160040d440c00a0140629034001451074035465030101d850b0b20b4008040c00c80d083c0a400030405180700304100c0980e80355610640240c0c80117000741c1803450402780c1083d4841800e043c80500404015004508000441c2840c641030303954900c2c031313001e4482e801010400b001d10201d43c25074180d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 342429937 1250 342428687 342428711
    0x6011704050d050f09040609140c070209150d02090a05011401020f03120402010c0503030c03010317030412031104030516080d05040819020109031a220b06060d0e030d020d0b04 77
    0x20b140c481c1010380a001000c03901c1009545418211400c406000c0d0040c40129903400c500005003103039501c06070b0300c0080c4d580041c403011581019078003070f190010b00c0344099032107642c2d081c01208284010590014480d100c80340150703e03100111030251010f9000040e45616080f200040001c082d10841d04641042e07015100044001058030802e0360b0140000b06281c84510060f20f1800c0a008020a940008000c0007070011520010303504803806140f90391041e40c80e00050031550f10044034006d08208d506170020850700c0c440d520900d40003a400012510381070326078403410f00c1c16414561070846070b241034005200101042c0101d2a40c0780d1982005810103040000c01c03a00e0307411703c29000f100f18000b01c511406580c41100703550002c607044058446a0750207824502c1103031404a4400c9180344080c14400001e405d8030b0302850103560440b80c0e460140d10344008010b541d0f0b010140c1c0c1000e03070740c0f2202c625030140001c0c0700404015460440040e0b49445000c01e140a0324004007815100d1031910750000e941c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 342431187 1250 342429937 342429943
    0x52710031707030e4c210903030621050d051204080a022a120d0c08090d0c080607090608010e01030f031709010b040e06010303051b010e150601170405 66
    0x21120110b0751006400216030030b025140240d48180004940c0d4440c1700f50754444c44840302c0f40c000f0050481c044c60300e84101e100b6034030b80d600c0090a41400c100300b0065942240c240c1e200346a92446483c1c04503c4a41c1e544030600c3c0c502117020500c00703408180d0414400c101c401c02c5214401c0680b41080f07800d002a80e0100c482c0e10f4401030028001c0c00e4000b601e03551640c801d003c000c1281d0032140c0b080784401440c004a280c90135582d0941030003101103400e540510310001400390101c0d334082d6500712017415165100050b80c1c120051158003c40984032800001c2c4080b00e400d805480100010101ca1070050f00043c02c0034815070005007071200100043c441c442c0b15241060550360070403c2541c0034032a500d4221000c110070810140c11981940c10301c5020f1106410054011400b03d40074440d58000c60040c80c2c68000a02c0010003145040120100003039250240b810b0b0000704400024901003419080c500380503055050528601c0e25204001f210741e001303003070b0703000c007100c500130381e11280c909170303480c196 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 342432437 1250 342431187 342431207
    0x403031103090619020c04330801020a180f030f081c0504081b161505040305071d0702061302040e2803020607020a05030405271003170703 61
    0x108000c00550340c0c0c00119810411070b02c1c601c001804140e50781c1c0200e000a0b1040900f048542c00601403504540401d280c28040d001c01c01c803040d02c0d0204200342c0b802903030080c0380004c100118560301107080012490000e2010704528103460b1541c85c0c10074159800c2d0720b0003c0060b00021001420080d040c000720341030000001c292036202c414155035400d2035202c40305520702d16005020070380c1403008000030008000c0c0903090b504500e00c030205041c16403076101501c41103651207940143c40079200401240e14440e1070303000d94052504003146440d4490b203825041c8685c0750405900070500003c00c69110141c20703512a40658648040e004504000580d030b40310898442010b445192243d12030030030210180100401d10b204040c010701d4140106021840781700c1100c0080d40903000d0b100010301642d00204400703007402e034004040c40c9000d003410100038000124070000d00c14410003501c2200c003040c0b0300d8044c5000d084803140d45460140f4510300030b07061035010201405004400d0007204002900480511 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 342433687 1250 342432437 342432443
    0xc0f3c031609090c030f12200c0f010c150902010f03020a05070f05030f1b010f05040510090809040f020d050703182009101403060601080a0e070b0414010e040509030403 74
    0x4651050f160404072a8070143d60005444012010031032000c2084103102c80032000e10386e4031044180102c1c071150a1039107000350744e5400c8603005540d108c1e4031440d08120104003010141025400303580302d43c072004c40c5456045144803a569403408007009640c1c1117018078540c1c000c0c41c5004c1d4900340c0130700320090a030700134040001d0020329a0303108001005028003e4500d1000918070040d200ea4109007240c0c400c40e04502c00c50390551802c04114a10041d03030252074403c5030404000d0038045803020122000b01000031081d114000c0900031260956610b0051140001c0d0041700983c480340607031070500880700040d0030b950034985440103c0545543c15240c04803d903400450b600000454a801d000030050180341d5039500c0224001084800c42d80004c040c800e40f2501c1031030b20b02003103001e401e25603904415500c1034089180c3e800054280c6403d80c2044000300e0380300c03007992903881d40c0d620665029040360b0400100707030001c0c80f00f00c001c5507032016040c01c285c0c104443c00d000fa070514001481e22031280b40009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 342434937 1250 342433687 342433691
    0xf16030527030405010305090a020a03080c0304090c080708150f100203070204020a0302040f09061a03060d0b070302211003080901020a1e060b040b01020c0f3c031609 73
    0x95640005528540104100103a64002510340d104216440f54440e00034036001c01c1c40c1201040c0340035400281c2d80e014943c05006d40703117128216240c411054100c40c1c0c42031350f188401c01000c9a080d0490043d410190540d4440008500308550044c0100400902c100001e18442c042d5958aa445401c5000c90b590152032f0102c0154401004034110f100340721001e5042400041c07030340305542c0c0c5036009004036244441d1b840101c0c1c0d1103044050940e440340c030584d981114000307800200341c44060700071904103d005210303060140d10366407801004102110b080c4080b07580880c0340d00003240c502440c025500b0700709042010714a04280d080407003011500001d000f103517020903c1007680c0d000b00060034a19401038204181c3d4441c50180e20580109108c1c100d500c43d08041050700790f410980076603c110b400c1600508041d4009000348058104240d84269001c041c0d410441801040c41e00d85d000c46c180c40e0307034580844840107903019003a1450303d002c07507000b9444888440140c1019450030700507280c00f4240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 342436187 1250 342434937 342434941
    0x40603050c0a080c0a030e150103140a0c05190509133302031513020931050c0d090c0807050f090103060228021506040e190f0c15080f160305 62
    0x411802030100c0c41f02001144111b4490000b48d000d456070343d034100c900c5507a401502d50985201a501ea4900210003804e040e02031400340701510b45000c040009101c424403034000c2c0c070340d5040020fa01e05003d50b0031021140345103040e2010300c404e06034a00760700c07030032403030000f0300d86640791740641d040e481c058009503680d540070010038a12983c03000d0b4465040c0300145452405000d602142c0020f50291001d06d00c6054841c03c075501c42078200c1312100c8c4074a810714442c0300021075943c580001d004001c20200201c02c0410180481900d5441641c1c4d10703a02940c0c8614009081080043c0340c48050381105108403444680040941d0745c00b07205505596002c0c00158660004010040c242040441d10988094080100401c0325900150841d00c1804221041400e40c40b20402e0108982e10801200c0c0a174200820000d62503150280e510086031040d5615086c0a01c1c03500c0744600d403000c42c1c100030440400030b0907000303d191780f28081640240020202d1701e001e003051003c540825901548200a042d11180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 342437437 1250 342436187 342436207
    0x1060602100218032b030b0907030906060308161106042106060f0312030b0a03110103021804020f13060201020c0604060c0c02030d0e030f0a050706030914070803040603050c0a080c 79
    0xc00b140f07014101030111404441200c40c0e000c050000210204c08062000c401c043c000e134800d004141032204042d081b5601912808411005003461070170940300540c070781d8400400146401c00512003003101400fa42d540c40424078000c400c2d00f1043c010184102c605100038480580d9135802c458110702503d00b80d280201c014603001c0040c000340c1c2c1c810000c0500c2213000106008240500c00b0b03120000d55001c01c241c201c803e08101c030982c000d0001a2501c8000d5106081d103501950080803046001c40110b0362070426400004d0590384060ba41c90408100401c0c50325004201d916007201030070940c002503040044a042266032100002c1000e0120b940ba02c00e440f40382ca01070040340885640203401d49440d004005005040340040c2554640244105603001d8001000030440300307030322544070000e0106185031400c124040d10705410301342c03021254440c0c00b03001c0001c204465001014500003850300d50745440000b0741210301c024101c0000480810802001c00d0f84201111f51103040410103d0300c0e51820b80c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 342438687 1250 342437437 342437467
    0xc090815061207060c020418050c010302130b0f1308070e1504090b0406051609260313090509010b0916032c1e070b160201020a062408010606021002 65
    0x240c07000083c1c0141680402d00e20340c0b100c0c030481d009000383c80600610b1101101000d56090320f0501501c0c60b041043c81090343d6100e60014502101007c60950700c907a103418251460f5407086084ca010590001607440e0105000702003040280700580c090801107290040c00c01540c84018100182e50348003c6940425070f03190380c4642d10560700200c443d00140790914040d00144400e41300c850308000c2843c1920030b5103214210780b81c20303140040c041f0320741d40300c008400d86039410708040c69966600050241440c841c40a107e940b005040342100411507060441c142406c4603414800203006a921308200440d46507011140d44400e9043c0c40c000884190080c00441190034482c1500100e04141610709811500051114010b01c41070072111050403200e840343c0e564100a100b10351100105101101d000045c40c04802c8583d401801a01c04c503511070791700d040403170746208a0072240640d00c0e050425040041028007014180c20002001144c0c10458042c0d902c10080205442c117640001d48060200148 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 342439937 1250 342438687 342438709
    0x3020901030f020f07140c150c0f0a0f0605010515041e23010e09070c02010c050f030f0c0606030a0b01140d060501090c1407030c08070303021b0c040c09081506 70
    0x1400300b1521446030110618259222200a55801c0c0031500300d031ba401040400c00b01e400850050190004d40a0846c1003d840d4000c0c8041d80324500414034080c42c141d01c280300903661a07210b070701c8118959103240307001d208580b0180c101034041d0300c00b0341c0c2400300c40e20482d0440b0103544240c030350707a4400c584018201c007410041e80c0084114a039400c0b00080c0b1075100c82400541c0d0710702625440343d126185400d22a4410003200d284e00000c111540c60310141d4040c030412401140143c00382c0701c2074119484270a00d5640121012100580f00180c5015400428011150002c108401070500348240d919000307040038044c0600308550b060700c5034580a6075036100340c1004081c0d0100c2c06001c5036a58500320307002003505500400201d08410251402d00c1c80c100122035030079070f0540b10340000d480c050703c405200d82c00c4038a08500f031603403c1002002282c0c42e000030482890980004007401c034607032400e00003615a480c030355800307100310604144007508000c90365212031021030080340003030f940b280001803d032500c4c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 342441187 1250 342439937 342439961
    0x50108041e050309040f110415090812030a060b09010807050f0c0106030f020307240e0d051c091e090b240406081302010206040f21081b1201060302090103 68
    0xc000100002c001c808000b030450b410085404002040d182074000d015250034800608558038108424440036095003041c9508000c585410500f45440e001003602d03114000101c0000c284d004020050b001616015003000307400c5010b0b1a82c10300981500190491801a000c1c1d4103204000c41d04402c112040f0007580c4041784408000d008295482c24005504118694164002c0c0a001808207245510100301c444d1394445800141c0704403e10001100d842070034000b00740e03001425030402804540b04000c10380040c0400084083c04c0d0303490f080050200394603a030183d02150103a07660040c18140031a00302e011151060000b080208003c00025003800507403019841c805990365080c400240d00b03c001e041901d0158840c4031054441c1c98484120750003c420080c0181d211100180015400ea2000c2108608c24a10800140300034810342441894410200000900d5101001008460508000d41b104100f540c0710307107018034a80c00240006814007480c001d140e00026002140e074802ea014000e500d80e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 342442437 1250 342441187 342441233
    0x507020a0f030b06120c0d211112070203030d050a05090d0e060405010e1816030b0316062006090d02150403080f1b030a0515042702030703080304030305071d01080105010804 76
    0x3547d460040c02080380032650303035546000074040106180c040e00350411261241c20050000040205501d246548039a500320b8060009000c950684441070084070300465042e4808112440c20344901440c105410001d1002c0200440901c010340d1145070407101554400e181120180000502003280c440403620440c8407000f140c0c0411202e501d4a240094032243c00703940612a03200c0c1d900400d940c41c10b0105100d03071741d00111801001b400b80940c5409060744004051080c0d13a00c43ca1400e1401c0c580e0490340042c9076040440c0c5032101c1a41804490481d410386010030100d170402c0d46004164960003020160b03915149030105000d000903a00883c01c0c00c2c1c0c054140780d501e14100500c40040c000c00e842822640c02803019408032841c0602a0080ca0041d1b140c4900b60800c483c00000c1d68a050380b20b0503a01401107a10200101d46450001c40c4528007946021802d403c0400000304218842110460400b078800c0194886070f0f80310f4117481c11a10b09190459041d100c500706418185038a0008041d0300c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 342443687 1250 342442437 342442459
    0x91a0310051605090915011806031b031104090e030f0d0c080601030203240d02090406020a1b0c060c140d08161106011203031103070507020a0f030b06120c 68
    0x855650402846a460b00245201c0703400e544a09a402d401030800b5a54400080c10026044d514004034600003000140342092071100c1100703411100c0c1c62107401c02d100103501e95601d03501c0412814420703103031401e03149400c00085001110001140c01640500c412481c0c503860700b415002c0d42042590802441d40501a95030035072240b01c8030041c90015111030104001c1c100241030b947c001e10a076882203c2d40d04112211244012080000341554440a90b009900d9800b240242c0c0f22042407500c140e02c14040180e44200d40200a400300060b840704040321301921a01200040d61061030500b00c50441c18032564032021450306021030b160f01101850144036044906424a902c44001341c0a801d48140034900240085000c0364800c00110350700c80310342c0c043c00040000d0402400d80c8800707a0b029140010b2540d018095202003944141d0740d140020354049101e40551070541c1d0b009000380740c0d080c144d10301940380d6035806c00070701c2004103514030415000c104e04000c00800c2c403030307104e214200030a10301c802 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 342444937 1250 342443687 342443713
    0x12090b0c03090102060703020304020906010f090b0f0c01050a09021c0807081611040219110708030a09080106080a0201081314071e0e01030305070f0303020c060a1407030b0604091a03 80
    0xd8002d00c0c0c110740103100704d4011850300c0d4028401c50b0b0040d034015202404580e0703000015540c4808510310682000300301140058075101581c017801c0010202d8138000d03551907044100d2400d517440074000c0350b002850040500d0050360743d01c0c003014814100107031850f0500e0442c181445039005d001d0020381107840000310004180c100c00324500e500c51040c0341d94540c4505440a21049001c5c9000c410018046102d0991800380949181c140000a41044030103aa49501109040d900064040004200440400d12000000703004580180001344001c1c031000c0d03540e4000130101000648030090070031007100e9241c241f224a05074901c000c50f0360412a07000c0b81ea5042540d05036005107080b4094141c21400c082551170350206d40a0480e034041d9111400e042440d104c000100244020450a0503404c1003030f1520200e007030001d54412803400e50002001c2c01c9452054504817401800002094030300f45410503e681e074041030300c054407184a0000703500b000c0c01d280a00005801502c680d407601c5036a04074118 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 342446043 1106 342444937 342444943
    0x110a030e030702040207030905090a150b0306030a021009090b030a020d111801060e010f02160303110f010f0e070e1e071e020a0501060501050901050712090b0c 70
    0x140c10b9903540000c00300d03402108202c01188845800304041c2c509607400301e501000762807080c4602e4500f92080c010001c024000c0440000021012030641d071810020101601e50140450880c1342e5001c41c0605002041c0c4100d4900703c0c00e0602ca106181004034101d5a0b055000d003819024200640d54040d03000210350003507030070207540345101e41007a080c1c5490500810302ea0f01c072642d8925007180018410981070071108250352001c0050b00e400325171904904200e81c0c05181a03902d010100d0081400c1c40c08000341c440866003410200609004903034003055003007500c10308072000f4981d03a41000c2c40460302181c5068541c030309481048003140c00c00d204c16a000c1d909240c54900a4102040080c2038128101c0c86030061340300107807280812409200e5100500f00900300203085c622031a000030241d124800000300b0b000031380021682c0440c044c0c0c03c00809001141500c5460b083c00c2c20125079 = true := by decide +kernel

theorem cover : BRFrame.Cov 342266187 342446043 := by
  have h0 := BRFrame.cov_init 342266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 342266187 ≤ n) (h2 : n < 342446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
