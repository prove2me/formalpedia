-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4969
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:19:09.793985+00:00
-- url     : https://prove2.me/submissions/c659af57-e7b5-4427-8af3-3a14073b57e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 893525179 ≤ n < 893705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 893526429 1250 893525179 893525189
    0x10b1017010f0b1905120403020c1302070503160819091703090321090307032d0f0b13050a03020f0f1911010203070c14010f030e0a120e040c0201020d0c09 68
    0x204100c0c01c1c00b403082601e034180112109141041c00c0a02503008040540e1b0151130a0340103034000d0011040c28a41519860641d00d43e02c0400c40c81c1c070382e59940d101d40700d0260705c0000450b10070a2441100703001c00c40341122480000e900561049404040d0003911103405e41c00ba0002c1c0140712056080c11100000460308403140c010020b20b00c048400100e41000c3c01034075141030b0704213424000d904203501d0400c1200081c1d4403c1d54418844900c05507940301003c0c090341c07080c92420714a8100404945203494201025801c60400d54050b62f500084100391072050310014502e20a03000408241039010982c07010445c0344c642644d804400ea80000340d5520151072141c15281d408002d0b0301d0004002c1e07285000c00030380c1030058034217100e01a2110300d5034406660000d003140518421082e26036038885204448426641005c010544000c00702603070700d8070320600c01411040500c100036480d034003448155400320307801403003403007080348541c0028082e4122441c98801103090409401459003e00303030b00400d5403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 893527679 1250 893526429 893526449
    0x3070c0804080f010f02090913061e0204150e1018170309041a2d12070e0c0a0e040c03110c0708011401081c05070203010f140714030606070302010b1017010f 69
    0x27844230f5982c0b903c400c29120044038090340e1020f1201000300e404070010100c5090f000010307200c1345000c0c088000c02c902540c40f1020081c1d115818036403582e54003000296a02c0520b040c5451041b50482c181d03401c01e1581002c028001d041c445400c0c403500000080c242d0b040240c4007400f03c2041606034086c02040c01c9043c2c0c2d40300c03076000103820400c12600d5403204007603100c010a00481e0f60140c0441e441c0b001165245006400c41241032120129403107403181c020f011001030500e440320b200320040074160301c1c00000e84921b403200c4804103850300c250050003003840752800c4c0300d90300d04110951580d2002c1c588031b50b10107542403044a90449003210700c1e0310704880b0004081e01006294024690300142203844040500000740401c00c091f031001d200c0c0b0084042c52000010fa03401440d00d0440840c3c02c020016000c20a1030300c16615440c00b4102541d0300803005a504540300ea1079850168094001c507040c841d003208034400090485944070501d00c84035090f001081d581640c0b00d41a046107003600f4020000c1d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 893528929 1250 893527679 893527681
    0xf06091b03053711090c0c100209061e030a0b010c05030d020a0c080d360809010c02040f02040e06150412031403070806030706020a0c0b03070c0804080f010f020909 72
    0x100714030005410148a40703024030280341250000d4915225141001303881103104400e01001d107041c08076007035070004806107480d0f05240d450042c559541480d40d0981210a402046084a1340c486400395a0304803007842c100344141d42142c030ba2003d035810807211922003d0a210a90a040d400f4003580821150840f000c2c52600c25420b4100300030350b1224038140d041180380a80b81c0c022940200191482d02100100861001e140d007901001c41c50100498003840c40034000c40762058070050058459882c0c2c80341ca0540c0791200900180d401612002019400509144e000902e000c035580c000c200351445442d4401c4903480b2182402440802000c0880c2401c0040205021040340c1150030103105201e0f242c4001d116203910704e4062030343c205407022404908681c00f84219442c09100d0a03021f0000c2d071008201d607041640700c1d000804120b00c00c2c4018043d000001c01d8695204100c014a515004824959102da68a0500f80d072000010b400d0060703540380811240c200089070080344d0396840b00401d08405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 893530179 1250 893528929 893528953
    0x723090a03061d030304050f01051b0d200406020106030c090504020108040f05010207120507060506010e03070e06041506080907050a14092e0608010b03072003070f06091b0305 77
    0xb803c000d06024605040c0000c00310243c0002c10055100d1841030004d0700d4006a1b109149080d94006820740c0c4041031910306e00c4000b00d00500c181e0760080c181d81404203200c0e5410306002400e480041c04103070304a0700041d000c200316405400c01d8044903c40c1099000f010b5885050b10304540040e50001d0000e03140c0d20108001c00c0d004401d2042c180e00a00005180659a03034508910551718207110002c100b021030800280101440791303550140302801e289030416100d40c0066150103007402a496041c58207008515103031140e5104010391006040c030415984e40790320020b810150110b07119881ca02c5840702c04107160400c42d103510f04692121101071400c8841c03d00b04214410003d10032040300520301c4500c00d100010441c51840000c0d01008900c5041c00c10500a22070181608030000000c01081400141a8013035001c543c03841c0c520742c40748070350900d40c51002d00b9449091809801e00615031032400030f200c00c903030000100038845c50440001411080c0c409550250fa4400500650001c0918220f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 893531429 1250 893530179 893530181
    0x11e08010b1c031427040902090604020d060e0a0219021f020d0b090f0a1a0907080903040b030f0a18030909180507090903020111161b0e0723090a0306 66
    0x1034850f02c2800e1910101d800c1006954098100e105038540c40141e541c07803110802100c07a41444100000d481c280608002134000c80c08845020708003e01543d400608000765041d50751260b000f0b010403000306c44641c14040d18440103034104072521201100038031014500380b4000100810503c078000c03450840c452081d041c400084d04080fa8900c0780d5920303013108080d1940c80082c042d100c0d0030146210310417410001d600340704944081a00051014441d111007c140d80d811204681c00701042ca07200500c0d0f92022541400d40c091075003d500060f0010081c03002007031900086503c1510007040800048048104450f280582c0c08005408202c41074014031150419420829240000e40d00d9000301074400d03950740f0714045480c1d0080300700c175540703410741410140e080c010000443d07200d810f850304101d98a480d040003c008040000c1c42034081c41c00050100d141021030400925000882d03000c20300d441c1c3d00107002d0300001d403500e0b50355420069a021440c1450b000362000310001074421440b0700c2c02d6070f41d244 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 893532679 1250 893531429 893531479
    0x18090f0a0c050d2d050f0307081905070b0a020a1d06122e030501060f030503030f1308040e090706080c0d0f0b030109030203130510080c1c05011e08010b 67
    0x10300c00c000e80398036142003000e050900140c00d01c040249804c0c04441402c0c002e0901c418018a4041d07a0010089031001c52900b2080e180c071211303614515030b5461b03079170b01e815540d51040c40c1c03009140790183d408000c0084010380c050203603403d01e80c03120700ca4000f031040c1058000181544066101d4024407000b02c1520303820b461180d01402580c10001003441c8043c80c040c0061643c062641250300c03510341030080080a0040400a000d0100c08102c0e80b42076640d101e8a03404000c0c2544403c001ca200022182a00541034403880c94100064035600c98072104d0740c02003000e0484001c107951064040000700e152080151070b00c1071030104116820702010400314405401511288022142c444030340a045541c00c5c03087da482c9503c02d4009580d18581e024104400d045180e000a00c03035601010794403c0c00f50440d040382c1d80300d0070010001e6540d804034070075242500d24008206200614000001c1202c01c13064210f50854403401c110782031507668403c4a1800e9409445c0300d030703401000d943c051007820306281442c9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 893533929 1250 893532679 893532683
    0x9030d0923092a030c040314030c0307020603090c1507050d020c10110c1807020f010b030c01080a140123120d0c020a18050411100e06030604020918090f0a0c050d 71
    0x650f00341c09004110321002d070010b891420311520002810810400c180242c00c40084801e03001d5410044212181c40e240d00078004007030300503140000000d410580500100200310030090038291000110214850183c015000449040c412800c02101590000a022090000040600c040400500011155200c203a8000760b0684202101402c1d203a807030254a010001402e0703000d01140c90041c100a182042d44d2a0200041e450400140800c4d240440d800d04010020f00f0003080c55114082110b00404500300410024070f2890008207600100c6200620240305802e000124a0500410400c2d10115000c03110074a034010314030000d510b07019180310803800d400101036010450703582c80c040c02459204040070110a55400c1000208401c8818420400c0f100355008444103117540005002d2041d168282c52081002000003681c955407901250014031014000e1511540d0200d04143c40c0f42040e44d501c00d0318021112192603034500050000032032031f040360f00700c01030a1612090084100b4040c0c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 893535179 1250 893533929 893533981
    0x9050f04080f040b07080307081f030816020d030e150906090409320d03020406082e03110a0509060108040b070201060504060305030a1101020c100e010209030d092309 73
    0x400900d55565130701402c052805072003140c0d520300d45102c3c000d004080081c00805111107080880b0719002c03094811400b500d0f4000901c1c0d0b95102d010403201c45842074914004d502403c540000700400d81d000050f6a0090403d44900d0000613800315090218042c17101c3d51038000320148440e459919203034200041c0b903401020300303100d1240007404ca144401c5250f221410b0320780e03400c040c00441d1581045510240710207071404505050901c40024603051025010b480000b910101041ca15035072180c0300c48100381601d4280c080c03603039203280c44501e2101c0001070500c20241104c0003d5141480301e1214440c2c1816541e5281540d40c69a0308115080c01078011000c5643c1c0382408542a1124851040a10b000e80b0040d038803428400401041000180e20440031a40140000c07084107a001800e400070303484152001c41c8100c5000d07425402030059080803541031240d121002c0c0c4440d0400c2100050314104440c0c0380c04600155880c0240e0000c21400302e0304042408006441c403c0c0380b00d11f44040c41e0541071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 893536429 1250 893535179 893535187
    0x30c092a0a02280605190f1e020a0207031209030f0f020907030c08130501151e140f010509031606080712050105031c050f0301120c09050f04080f 64
    0x311080344031121100303280c00c8000044801d05281c04002666020002c0c0c0700089842c0d11080c070600701c4840b042c8000f0101601e40010901407411000c07202c5403040c0c00f41003048807101d1401c0c600081c046244030310307242d030700404500040d41d80c007030084460340c81c01c1360010555030f403950f615000500c495200100c10044804000310000c1c1c99070201c9170305540158100301d0100c6842c010845000d601a1500e1f09051505001204903908064403a50285204101382c032030f84040c0c1005c6015042da500c041412807691240800c986801a28540749941c0d55034242c0b110326152103185009002c52030441e640403269a130f079001c2d15840344009250300d0202406854190801125110b4000d4980c0c000c0004264180d08104030168482801010101c900409112079458400030a465041510703840000c980188a1210010b0007642140c120028282c0d10641e41e40c0d65015568a14041c1340084600e2040d0a000040c0e08a29006071400b40300050014411600e03140d441d0031060707001d49140f2111100c280 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 893537679 1250 893536429 893536471
    0x30405300d12060603050f0411060d1b0807141603120c090302010806040c090e0c13060c050624010f02010f0f0e010f0504150e1203160206090c030c09 66
    0x44010303050030110780c64400301c11410b1054041922110780028041615202c204030303c1841c43c0101d5034200307811004103420f048000003c6402d912400030b601c81040d092012a40c00c0c071041d4042d5019800903540c5100c02a20b03040ca040b60300b41044014410303043c00034000069101c502c24030700382c0c0d010301c24103220388140403200c20301e0245c8568115580229200d14810030540d41c01c45684d60f03200c10100c90070001540200c03000340800607140106110340c202c800000703e00c045104100c65660890804003500310781c0d914401806030132401d500f1034590243c0710202d032203032459051480045141042c0c83c00c0141c041c00044a010b0500c01746a0119074035412440c1c00f0550501c81d6510042c7c03000300c0030500c0454541d0140c2075a00c40b00c3e02e4510980b0b810104004075003032140c18020301618440c04291708c4805000c0c2c600e02130000c4004070511000209211f002d0140e801303078101201068013601c110381da42e41245a02d916001101e540c140d08030962803007483c6014140c690f072010a40c0000400c002600c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 893538929 1250 893537679 893537683
    0x6090703122c100e01091418010f09181a0402011e0309050705030d050313060f020d0b0f030105010806010605130f290306010e090703182303040530 65
    0x41d070181526070b00880203040150408403100500d1031021304040445002d404e00003024205a80310f421000c400301c0307541070601d6a401b0312000100d1b0120195070040d584403000d00d01d4081161147c440124904030030210111207480440c5c1006402441c00580d44007010800c0503407440080c81241004101881c404102490f1724181694500559000542d480e6034078001e8500300d0540c11003480380c0d0001c600308103034540c0072017100e034007458030031030308c6060f0440d4900440945510450080b4450011031480143c7d21541d100750407114084640498040142040c942291028003030700c9090b80064005004443c020300c0142080c20f42480d0003001566201c0c1c4500d602c0c901c0340c201c4c11402c9054076218640c0d2001030101c2c0400c05400340a5031841c14500b0000c1e202000300380e1058050006000000c1d0b44074025404240404206c2078000059045440c1c1840a6080800c10911840030080f00c607a08003000000c1c3c17801d48401406000c0351444600741090303008c0b0900c1145001c11403a5001001d01402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 893540179 1250 893538929 893538977
    0xc11030d020d021218040b0111060934030b060a05040615020607020313051903050d0e041506020a06150312050711060f09192111030609070312 63
    0x40d56001c0e0001110a240080c10004611842c21150b101845080c8007501e022854050b55407003120000388001a520040c0d40c50003840c0c0d0010200d001308000c000100f100410002c20000102d1403005055010340740ba072015018642411100d0380b0003c00500014903080502030301b006c0004c00c0303255041d546100144c26035186401c43c000e074098503040c4483d5031342c04001954200b08503001560a2101c0d41e5116800205188a035034400d00d442c3c040d0740c483d901c2000c0040d01958000c4241c42c0ba0002c0c0010141c441c0c01003002e030fa4000c0e132414040782d103103180040101060351401ea01510005020f42c450300041d00c080c40344020b54421200001000075070303400c001806240c0c1901d819480310410f007000485960308001c0700d4041c080400010b801250014122404210f0444801d2000016514441b12010780340e0070071000c01040c40d000e4210b001c04032010116040c4070340354980394600380c1c030b050586410b0305441524060384030300340c24000180c2560800ca24041140f818905810744080c0c00654806 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 893541429 1250 893540179 893540203
    0xc040b12100b1804120c0305190f0216060207050f0f06031807120c0e09151810140103080a0224010305010e0f1e0a0602070c081b030304060c1103 64
    0x561804405060f0400b210281c0a2411500805909282a45440f11380058012080c010000c080182c041018000c03c19244001201c203050100a41c000c41c0140c5113869991009016100350040c81402004111280d400d450481d4080c01c422071801050000c1c1131642001e069015070a11000205a05c803000518829040d03501c0032242942d900240900300513480c0c120828800c102481c0f1000f2546081801c1708943c0d0907005400c2a9580c2c0a905003030811a10285c05104407403804d0100e00c01402c03001280c0b4404a81c1170764854424000c0e410101c46420322080500c01452004002068018000c3e00e140d0055005681c01310024142940000782400600301130448014018000d0000901c80c03000300f501250f0007070400c0c4510220741d80d6075014003000012040c4103808100340c80340b024030400003020741c04102503454203058a46641e04c0a00b40c040e880b114420306446a10b00341c2c10200d9202c0c907030000b80c0034501d001c2c01c0c60b00031228408001015940802c407403100800a885c00c000c2044940 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 893542679 1250 893541429 893541431
    0x15030610082d12040f17060c0918010b03100b0909040f0201050d020d1416020a110f090408070302010c0c0c090b060f0309010504021c0812091e03030601030b0a080c040b1210 76
    0x903080c20301d01041d03c105034100990a14201b416080c0702030b00083c03065040502c80d0240da84901d80c0d00002500c4801c40302c02c844a20451000005001d9101e802a6010386c10300c5146071a00c503101e2918074040e01410b82c800b5070040c0104089000705803801650316099006140039480c0180d0054060b00fa81c2c001c4d40c003400d0580d9a8a01010140f013031b444460b802c8404c2c80e5405020300b151280c001d544020803d80a0004968180c240916560345104034500f80405000c401c0700d881c0c203040c0f60519800c0480140c000d5424400b03152410380c4500d007a12092503003c0a0b6101041c1400501401400600c0c4c1694108204100c84191a2866000780d07100e4021034001103820b16043c410b000c0b41c80d00c0b24041c0300d20040540e41000000381e0030029a4406100200002540e54503a103001d490940d2002004400650160800304074840200055101d150213882c01e210002c1e2807802d04c02c84482d03034032032a40740c0d40008841132013900c0c10303400c00001103000a12020300030441d111042d0509250541403032180b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 893543929 1250 893542679 893542687
    0x1a070b0f0717071d06131e0524030405031303060902040b0a1d040c050607080a0206010e0c0417070512010e060c09152115030610082d12 60
    0x1c81d61041d010700760000c0411401c00b0505002d90040c14007040c030b0700800541114041c00d441c0e10f0f00c03884140d4005a02801303542c10071581d500c49090001c130310220709007410340c1c6141c0702046600300607a90090040c440b205482c1e02040581c42600c058101810484160200304807000c0e28040040b201c00155002e15400143c5140b0f920404c01182c1c0d0f00118903024844040c410026140154081110b607019000341044035a01c80c6080b098100b8150486ca0344008041951002c0c005a00b0140015008a408685903640c0300e1000b090036032030403107002c03c1d5039908100a00507840b2801c08038403000c0001c002c5800042c0c42d100080c4010360300301000540c0743e5550000040c52001044110f0f003201000c800c603441e020000700498607010542000c40d8401c3e40009403040c0110f241c0180e194020341400d4441580d04000107039480390f581080340640300b44100c1000c81d130381007008945402142c4a47c2c0040c8070040c50041154034003040d0b0740c4204500c502c0c04071b00c081e90610502004100f10500d01202da51 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 893545179 1250 893543929 893543941
    0x9050405070908060a1b0509040e030d02040512010207050c01031d0d031b0908280f05060f0f090c042007080405270406050a0b0d0b07020c0409020a1a070b0f 69
    0x240c030b040102407041403130501d907006c8800c81c03081841269804181c0f50080d0749200400104001d003550740340e40601484000781c51840801c60b86e01a0055500031075480040e41c0d00003039402e09030702070410003400c0c81d00002c1c64074104c1d41c00380c0e104280294200c03401070943e00c0320b08242ca0070040110400c0c00442c1c2c403600d0182d4034840c4410314001518039418141000707030401e0b1003240c1e500c503205041c25440200020008040074110030340c4190561080794803401c02c0c007500d4a40e44610007a60071604182101c00070503100b8403c00e50051140c14000000d001501b0241d08100c0039000041911103011412a203074200034543c4001007500f5030144080b207a40d907103403009001111114900303000404c54902d0b64205100908822641c1190300100c021400c1d841c5d040c900c200902140002d1540b0410030b80c013800070000e007811160312a442a80a0311216010701003070005807000180001e5100601d000180078001c41d2401203a944101000f886040030903613903454500000035144150030b0040c0c2c2c820041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 893546429 1250 893545179 893545183
    0x100807030b0d15150b0406030e0615130b040b030f03090a170304090f110a0f08071b232407031415010e09010609030311060402061909050405070908 65
    0x1d8495410745280c61800381035212040c070042c0c2c002001c050340b80c48410303075111050b6000207a0041c1890b13004031991145d4510000d401081c06d01002d0183c0d014000000d0003c11011581001c200300207400061075644036004800144071405020354081d659425007203940c1c504001d0340b00b40185950045955400b18030410a0240c03c0d90700841440c00e001c0e039064924180801964100c8030f0128012403868206510740c805021002078619402e180880d112100c154040140d518250303031a10340110586a107c81100c000d0000818002c0000c01d04c00d6040020b888102010306102c06034051605078003400720160305101000c41001c150721000291080c05502a43d152600950f06007001c014400e4084088180711200030070403200e40c2c129070301070845a4003e5100e2100e00c00000c021481c0c0f580c440ca4050507040181c0030a500188150080311a460800202940110380003002c0905181c0c4d440400b003010070701d0b21f0901e41005045a00010940c07682d0080d640118640e440701d030310890812310224 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 893547679 1250 893546429 893546441
    0x60706150b2703010e15090c0d0309090c140a0c03050409060b03040201091205060103060902031c082409040828020a03141e1303050615030c03070b030609060406030210080703 77
    0x1e03c01d07494409034001d405c00000f4141e0800900143d81001d55440d00030990400b441c0500141d00101000e000d0001c056100340d8260545805000401078581d031004100d42d00b42d0b280e9445284408100704049001e405012003074030103442442c126180917142d00d204c0c07061b0780640c1d2140c410003002000340804c543e000700ca0803002c1c3c40403080f5044840b2603502d58075600e080601c0040c002c0c1d82d41d044400c1c295201403040c0040d0075150f409900c1042500d010040074450b04540400384030442c007032882d030782581600c00e1021a4400030407840c0c20b03031180d850301c0030154480c0030004414008640444008200e224007400006555000307003012081d40d00780075098211511544d200b00d02c0030022507c2100c07400c5521000403c24208058450055a0f80a52941c003160000f60080c826203081100c1d01100d4010210000d106400307840c100e1a4513014075660b000039010302440c1290a0000038050304080b154240c1c0001c00600c04188955642c0100d01c401044280000018030018104030b01160180114 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 893548929 1250 893547679 893547757
    0x141002010c2f01021b0d080c09090c0c030a0c030807230a050705070b0706060b0f180415090914030c1c03060902160c0e0112080706060e1006080a0209060706150b 71
    0x100d58189804088c2625a11600d41111b1044042c1404910703060380c0031042d10700f842017520031207a07101c03c1c088002e001c814100700102d00040001000483c3c0b10f200b410f01034401c002c4813032000000502c0001c40074481d008400c2180c06c12a081c40030001007402008030500600f40c486c441c0c3d07a12040360414009030340d242e80180240203420031108002413000000c0b644803041e4036900a0360749200000080c0502200d03a004d650209030b10750049002496603120310b1f0b06610a4115414122244016039102d0280d00422503450708079820a151400442d005555035441d180b800162407501d401d0448100d810041da16080031040c18924002c024511003030601604486001103850342c586488914054a0b03150018001c0101085420400109400c00f40151103034011801e028078082060f1100f42c80c203032107007400182c104800326404e01c0d180d208448010314081c04d000e00e410031a40301c0304080c00300c00d2421107036654480000500491088050504a020550000e000030094440d90399006104411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 893550179 1250 893548929 893548937
    0xc25080c0a060e0d0204060b0309101d0d0807020312070e0108061206160306051201091203020304110105030c131509061403150d080301141002010c2f01021b0d 70
    0x20500c03003160001070036032083d603044a0395002c41c8000e10105014141c00d5018903103441c0040207220b0001c0010500c0204850400c100b00700322103c44040e020452140d010000042e005000740160441c85034612030303032004060044074901b0f003d800c035130703c51050100c540300d00091705101e15481640c2c1c0b07d0304103900710354100e5207007080e00d49007061241c41d500041c0c44520b40020052501100c18065040034005020040100d0340a4100c41d46003400b900d8107070030840d00d41c07d52829140d1100d000f8400e4070300468200350280360803022100107403903d0b8005041d40d4042c181c00e01074804171300642c001241c0a490008031124003411260009440c241c255001841031141030900c039840030f080d04007540c0c1d2002c0d41e071000d51400ca02c03010101c0c902c10388070b00001d0714464001001080d40045600070741c080902c00d9851355032004144030204d088070784040414000900000c0d4050109800d40342e032211511592480b007514151815aa42c04c982c0140945544882c0b21041e02010040901c5103481094140c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 893551429 1250 893550179 893550199
    0x70e0c090a080d0210021305180603010b06030f01090209040b131508011a09040305090d080a09140919150311030f0705090c0706230a0605031903050c25080c 69
    0x78020b5207540e8084171403002d203640400c111079a440d442400e44002c0a0103015880109201509622881c404550300d40c042e600f010090707c05230900d20212882020b100d0201855030f400c14081c1c8000c3e5110b821446e502640f01c0032401c0310b550300c0f0300c0844c0e0b0301d07036078013000041c00910644031000082465011400c5645003e0300c005183c40703501c116902c442011030f101521955140b03000c2d591402030040854004140080c04001c114003000109100b01d42625010304c1295900041032440c00883d4500f074124a140703001c21a05020802c844080710602c000120301c0140e00c030003004010006d9401a40d45840b09001ca4a00b4107061060404010640d009491030a060101184803040023403c4812088400204a81441015800a00040c0b140c0450100c8101403550181c03000c502624010440da1a15900003620304c1d002a85095154400184440705078850703e066031150020b80a1490600414203a41c09a502d284529030305c441041c00c41c2c444403400d1000041c503084085403680e004070810380b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 893552679 1250 893551429 893551453
    0x18060b100e09060d140601090b030d0f0c0f02030111070314040e060d03030f02030c071505040209010b0c1e15010609050901090c020c030d0f02010c0912060b03070e0c090a08 76
    0x901c450303814080c262410b00c2103031250404a842e030032040e6406080001c101e2000c501c000e8001c07684078100c0d58811130600407807601004140e1204e01c7c2e110780c00e000c1a20140d805681d14098145001a070303000e501c41100401040c0c001c64250780104010003a071410008181e07007003503003026804800240030101903080a040c480c820b01e41c2c40010307041a00c02c509000d020010113110f40c000720b034503090b10107095480b424195854480340e00055400c880183c2381c0161410442210b00c42e00c1d20644d00248100d1090340380c0003070540321368451604120365005001c000c404500303440e664904601c00f840000d01020345a464030b0185400e060b08604c0030484070140c204419510b0303000e1203064070610038000a881158142c282d10f08080d105010f83c25014a20302000e242e60001c1c1014000f0030702e0740013400203c243d82411645d43d4014016011500c108542e0705001c100c11760300640c0076035000740484540a803114600d1000050403260401d07a0200080d4688040c1403401058000780811801031840010207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 893553929 1250 893552679 893552687
    0x160603270b1810140c070c09050c0f040e010e010b071101050f0705010e06041b27060b070b01051c1a07020c06040914010609050a0312090918060b10 65
    0x3804014084620300804141011040c482401e91080060b0441d92404a07000c0504050001c010a10700359150400004031036102540031500c14070380c82100481103d00701610100103000144c91440e4150301800381c2858100c0c014001e001134500c42840b80c04135171425840e9511440140c01c1991400c8082c00302a0008145180b2901c50507401d0070300c0c0f6101e80d403108804585000f1090054050b60070010035030b01c4039030081210340c000c070b001d181070418664130b01450f1165400036104c0d80c50101c03443c82078614500041120010800c480e03400108010b0f40e41c681d8010290094041503030b219850900400132840c1240e140030000143c1c00b01000d0540440e201d5041c0381c1c560001e0307108452444000119000d01c03c2c0545200054018807041d2100d881f00ca806004282e04c0040e10303070881d10383d40003040705406124280c0c12030784002d10806115095507075408030348214890440900107a404013140f810080c3c040c29210502a2282c4140341019090100c15510030140aa009020741c1c242002c8003548 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 893555179 1250 893553929 893554001
    0x3120403050a060902010509091305060601081b090a0b030106120606030b010c06020706111611030f0304150219030c0629060702030a0203030c0703050f0d092105160603 74
    0x82030021388071010340010f8500b4406d10200e5580404c41c201000380c1c05004112514403a0b005100321103280c0d0381c04005640090060340c0e86955038600b0003001c40045e40d440000c081d0110041c2205200300d98136003c907105d540007a0002030100d03a00481c0c4280484640c0308100090002e80740a010250398100085d024603801ca2016021607000030300320040c0856900015040030701d5180960f07035400d8000c000c5541c407a200304100c0d0000da14804404051074001002102d00c4a014095440c1c07603e40f45d07403c4c0b9522450023400d0250300440e9501d81c008a1488517034507a25000e83c94925802c1c0c002c0c6005001c90301c03402c01940c844410751948810f110000200c8000c0c40d031085e40c40c290344c0e000e5030001030f24158412100a615100010303260000380408141e56007124402c500f250758242504c038420780c03101d550801b100001410082c0c10402889003940c0300c198901d00058084080005840c0d40d1300700300091040d998804110300c810040384d50b0511036012162040b0303810406a4039450b10140c04560 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 893556429 1250 893555179 893555183
    0x103080301121e03030f0605030705131e0c050a0f05031006030e010222031703010e130606120b100501030e0a0f320c0108040b1605040b071103120403050a 68
    0x151000c0c10500f003000c0f00f0000a140c0250003034490f0204000c0c41c0c0103029040044071550b440707080480010303560400145600a82d50010103020340039440c40c04c8000103000340c1d12140e003510b040d6031a0003840c240c0b034440c8000da04001d81d07801d07076074085101025020540c0203011500300f110030010402030300402c1c14240161105458040345c0000d901e203041c1d02a01031a00755110b03502065800b64100203500d50f8240803203102d0300c110303821101d0b8400c80c0e1400b404240700e140101c0141500103400c810f8a640d502c1e105511a4000041d00c43c1c6800e503000342c98440110456480c00100c050007030042d00c07144104000e04003441c0612122074154101a201c4800f01c0c8000d0103004400480d03401c000f5054a11941c4562040810000346d00e205000e80006844000e1302800e8000d00400d840075500ca126640d03c19038010034100c805488000072000d030501d0740f0000404100040c07001246401d01400240440c40c05004d01070101280307142010b04120038464070080000003040f0810000d0004603a07410340c95 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 893557679 1250 893556429 893556449
    0x1e06080601120e0d09080c030f10020309030d050109142505032a1309200a0c050d020304030506150a030803150301060608041a090c0f1306030311150103080301 70
    0x7422040c00201500028800300b5650250000310804e40b0b0f4400041412111040204c980c01c9800c8001d15480b4183c604004100e908507442c0010192042d030000d43c2c00c1815070b01240e15201040001d4001c941003130700b0801c9002e4032800015004c03d002d251494100701e5508203c180780b04c102244480104040395084184403021000584030902c09000100309091640d0301089425100c1c401c813919400010000040c4242070408038800c0501d1044018201885041018480810441e8500303904028602c030100812890458001030301400210710084035500115200e41c114a019803e191006217003c48a8507841d034158680d680c0d040f480822682c11208541e40c80e101d03005400c440f43c981d82980b84d003560816500094055200c84140c3c4500c0c0610682da005549940c0d41200c3c44005403210130880d40001c070241c01e9481c004465804400000b003d0414802c0305144e00d0081d501a5441500401e003511500c0c2e400030030034002c000c2100494400040c0540c1195103c07c043c3c0818002c009980b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 893558929 1250 893557679 893557697
    0x26030d0f0b0301050403081f0803070f020301200405030706020c060a081f120b060603160e03030d11030402011106070507030e060d0518011a0d02040b010e06070303061e06080601 78
    0x400e500754088040110064000e00c0b8501e42410701402070b00050310446207207d2106809034680440c4104002900c207503801440c0f0784442a12481701c04043d40030705aa05568407823003030000b40d40d4111185c12028140e20540e895038580400c050a100c1c090303003c40c0554218007084d5902c2e40d5144216040361146040c00e0302c2d5900d071342e42d480d14803540c4071410b44031080c800c500101e4400b032a50041c82810b813048113103800940c1e0f120b00f4808076010503201d801d480c0074958143c00480740520a6101c09601c060b0449007444405a60001640c1003000d5145c041c44001040c441035583c04150b00c0296020603004007007601780300400030200d10510001404010f2510b01111003540c400d01150101c90002a0a100780e04041d01c106418085101602c500ba42c80c00c454215101e0520165202e0010000d10451032105a0340034040a001c08014284c10849020b181115580d25100078018050195030006401070074404401082c0d090780d40c41800a0141c0c103400c200c20b903400804c1a611040a182180311 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 893560179 1250 893558929 893558951
    0x20c040509010b09071821030804140a081206030a0b0c070320030a023f0c010c08040b13021e36010b130b0c0f0d05030126030d 56
    0x18800b000d40f095000540c0800d001c0c900b503102c840104451103130352080c54550346e10404d01d00c0f02000e00d0b007141010310024a1100210b4040e0601550046c05244e44200c1186041c00841c00c1002152040345c0404000c100c0e1100c540e0804180c6a000380c1c19001030251000d980c40b8151511001812815a5180081c070380382014410100e00c07481d45039098542c00700c286a98185034480c1c21941441c1c0040c0705c0c118030442c420380c003600b09000d101500700504032048000c04072040030031107150005d00300b507034100300c10644448244215103105106071f03a40f01d03d03030400e80b4044100b030384040c000701c103002c6c2c070020002d02690b04e210f00010720510606070040c1043c004004074048652128850494a52108181e12144014040400c03803d030544076018050380c07520340802c090b00074005810455a6840414864240d90400500321840e41e034045800c040b80c0002440e01c0c1c02e1680b980341000a20200041090029140d01c070f01c170a00b00c444404503c0195001402d47d0f80c080d01c599400d1458940c0e080080c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 893561429 1250 893560179 893560181
    0x1a1b0a030905032a0c0105180103090f0602040608012309091f0614010305270a060906060509060f090c0a0c0506010306020a0813110d0c0902031f060906020c04050901 73
    0x103101c1e40e01030150b0752201da020580c410310f5100402620100000b010140c401e8880c0420b051015081c161205801d10302480007940e192103072403070100d040c156942403100100350341c19000c940061240304050b175290f0818500411600781a80040c0b54201c603195421011205031070142c125007810b0303459081c43d9a48400b050b10300b6140c41420607208102d500c41c100a4280342e0042c03015141910405c00f1040b10180044040f44c02c1120340140700c0314801c0f5540040c0f24880c2d45401c0c6c0900c248200c4031044071988035442200d9850388111801c48e44c1c4d2904004508040380c3c07155000400300c6030740540c003080c032011400000000348a070705880c0c00016085102401200241704071a0803c1c00c031071556071a450100020350140c00e22002080070080040d01410b002000942e265030f0145800000f40c0c1c0d40e00a01007141e16103c0d04a0b0315590407030000c113503e4140d10281d44120240c01507010001205034045040100340e411100030401092400c0c0410313038000a005079041c90682c0d00017882c1d980c10b40214 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 893562679 1250 893561429 893561441
    0x9030519111306030c15050316110d02010203070e010c0b15010203041505041d160c02150c0c0108090303151201110f1c0516030c03271a1b0a03 63
    0x740d10600e42c040c0e542d4000629444501580c0c0302e04800700b080398035400390741240d00e0b55941c00c0c80055070070000942c0c20790340002d0f1524005003070700f81200d4050188180c41d083c159111901c0f40180c1d4044204101e030365000c3c104503640002820124bc0c1800c8175183d003032a24000a000000b01c0100040c1054564402c02c00c0b200103140d41c00c6144440101100028203c0c0e0251040f040510406401f00c8102c04500c4109402075140b2407045602c00c480705402d50b0a00390416040e641b00c1c07551000d901d90f036480d0364004c0c40c0d021004030180010034403000024000ca100a482036002e07900600800c48501d55103c20460306140449104401c650b100c41c803540074201000010000c0c01000c2181d20b80c10401fa00035001c111030030910306080c0d46c3c4000780030007203410403260745011440301842c80c01501e00039401541c41c4202441d002c035007110307010140a078402c1c5059040c141d0021f4240400305001c5204500f20703d0140c40d10074207249082841441d03040c02c0f4a818403101c0000006255441c2038020384c400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 893563929 1250 893562679 893562713
    0x1239090c1e270f01020a02090403020109170301050102060717011e0506070813060c031b140105090d12150b0c031b03040f17060718030507030b061009030519 69
    0x510382d03458a08902d20303129020600150340000342a1a8000a8600264504403c420690007814031200c980c0801400410240060b01507560700e0320500d0210780b00f00c02480da1072204d01c00045e6294944000240b5000004061004100683c6c03841410314002e040514110340f1400c00c1c03082051904614200c03154551f60266170712020019500041050400140180c126070500c11700400799208010360f48443c00300030040004030350607500f0180f0303580c90303091500081c0504804106000c5903c405804c550b401e03034101400d0340c462840302e04d801da4407642c980e032482510101403000b80c0c1c0c64900451500641c1c0908144a40040f4078032140c2881081520700c003c140d0062003c4101c1c21a14117901e030b078018040e905c5006800d010104000c4520540185100315140007064190b03130700c160444010400c2c0c2c280f4a444540c0c5a0000003241c03041000030040d43c051008211242001810000c500e44044150024081c1100702000840c101113074410011100100860351507919141a0350700021078004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 893565179 1250 893563929 893563987
    0x903030409050a0c0e060a0807050313060e010603020307050a05061801050c03040611100509031e09040f1a0a18021309050c07023102091239090c 64
    0x41112040e155000500b004e043c94407500e00c08443d05043c0015482520b43c81400701e034215002c038494038070980c0110b502c0f40a07815012004140c5580e4841615141040c109540e9100d4805009528091000700300401080360001d99661602001c00c906000d01d000702116242040352120050340210200c41c0903401c0da10650744e556032100b10141ca00220155045000e120f07e02c4c00d039000b00c04501c1a1405401ea803401103045c103d41d40104140b1a0b07a400503100b4440c402d201c0d00e030303040d01c4902500d4100e655490000c10012340000e412802c2e080c0d0403000b94440c180112003045a1076185c0c038844c8003000c014001583e03550254a01c414440d881754001258107141004215881560a021700301c020710032130703241200070001929120700d10768001109240030681d00c01042e1503003e643c02070180301e034050501140a0078403030740b150071700004041c54260141030b59504284014130a038004212841080d40750510200c080205454108c0140045403000f0001111400020f80c3c2000c10809032020709 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 893566429 1250 893565179 893565181
    0x20c03131d070201090b040609030c0804091d070b1611100309050c04140112150203150a0e070503011701181407061106040b180601150909091106090303040905 70
    0x1000e40c4980e8075451849031200c5506000c159094410b0207103078150b0740c2051021040b40c81c0e42e203842c070080155007403c41c07d100c08001074400041900c0017410007040e40d0380d1b002a042803044205003420200a00e08003071908021024820382800006032140e010071045400b001c0b60051402c5008100c49071050f035405000d42209501f0907606400002290b48154181d07801e816000741808180d0b1003400300002c0806c00c41006210800c2e400c44c3c1005024011442c031f101c0d13591906100d0089038000d85030a1f115140304020301c20a820290b030203d0080030000390211091415440007401c0340010300440325401001e03810101080c409411004820010040301d2001003950b1400042c02080c1d0000c61169024125000030b0090203118040307444200c1c85c01504440e500c90791010005600101241400402070b00e43c103624a104115085c06440060546928407144400c0a82810f80796801840124104440f01c400184488016003180e6400c0d0b400c1501e809000c1d000a0950103607400c1080c109143c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 893567679 1250 893566429 893566439
    0x3071b0506060f0108060d02090915041b06170c090109050612071d0102030f09011b0b060a1a19093501051605030a110301180c050901020d03020c0313 66
    0x204805000d44012140403c0d4821104019100c4020440340154001030300c5e4000303405410b00c003088603802280f5200303a80351580134400d15116544142c1c0c1c2a43d480900c101a003660b14240801d4074050f044a01381a00074020316147d1203c0b480b801003400011800c0855000500c0c5d0060300d2580203860b00a05440d280c6824404a1049881c01c03203c00b400035140c000124601c02012560b50310003041079000d14070705600515607141ca41d1003a0740e50f50420104600d40d641007040041840c0000b80724480c1c4e03801c0c5040c00000c124100200380c204198001d20541e0301a491307000301086a5410000c82d122002070020200305451040455110500300c0e022a00004042c001541100c020030030485050500400310602c0342c5c2c225041101c5a409949807012110100e90040000e558422005103000c00d0544000b0903904c5240c03c00e0303000c04a41e04500c0c84400d88005280142840d1034000e10305582041030b0400001d42c1c032210b0104070804c1c141c3c0010840074505003071080303914030908141044003040c0d6a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 893568929 1250 893567679 893567683
    0x503090a1403010605040b0609010e0a09180515160f0c0606060203210601090302010c050307020343060507140a050f0d0302030c120606070b0403050a0f09180203071b05 74
    0xd07500d5602c69460050041000d19091040c1281030301c0140c80b00d8100410140103440f40d00011000c0382d48032810071000619615540140d9001c2080f04810703100d840489c1c40c00518081c01c0c0c1c2c070346801c650388000c100408201d00c0e80124810544030314010041500314a41540d250401810107000e09040150206045400000400012162070701074016585040c0d5a824070003400d85d4080e0000f00540030400266200d031482c104070034050400d40f072612410741d001900d040c031400c010394000c4540003440d928084510141e48000340e41d14400e06182a8003200c17100b511a0180644414040049a440c040c02480e540c8100402c0e88081101e031041c25606016645004824940c40103104000b6046201c0348203000b0f0380d00592214641a0801040c00c044820f07064000345940c2c2c00ca00188600c10110324110119809240a42c6403d0b82c0c880300e403140202480e685d02e0285080c00a902400c1060780c66440d2a00c41084488034016100c0e210071904840680d589415585c500e06e1400503107082c0400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 893570179 1250 893568929 893568959
    0xe0106060e03070501031103070509060d18060506030105040203071512050c040e220f2916031a0d020a0e09010f0f05010503031608090d050703060e060c04030f0503090a 74
    0x4504907002c25136203000440584004040c00e00c00f01101f800841c130101e000d00d01810700303944010085030410000003489401c03a1003250705a150340034800540028030540b44151501310806030000e0003145003a801090303a5150711f10401040349003c5a0500c10b00b849a01030b0242e0714011001800103007464210300300a9046402540b00500010300818000394400d0401040c905120b440343c110b0310260b0700d0b00400e06000b908152080300c5514054001c10300000304880e015101ca0944904c1400e200ca500c02d44012806c41c00703014146000c407188480710543c0130409440100b200d40000c000e44610100e0400c4002e940245140501c000500480b00010340010207400100002048410365000809060f60380c01c1c403403190541c20400061508248a4800d804400e0042e045989441888004164810044901681e480e0446901802003107082e00031001030743c540c03038014812400e010140310840d11542c88020038400e203422100c0108841403040d140c640c40000c046906c066559188440b510728 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 893571429 1250 893570179 893570207
    0x2091e0405070903210c150c1d030a14010e060708190c080708040309050a060e01080c092b0609080c0c030724210e12030402061c0e010606 61
    0x424a80082d0700c103440b07040c114084079000466491402c0c500600310340220044841e0b0002c01251120600104201c00284110f0560a1100040b0241042001003682e030300e0448041c5288078400700043c0300e6900140349854603801c2121107503103c040d86600303401480c1101c40c282040c0120300c03c204004d9003022140e4440c40c90302403040f401070103000c804011104040300440104241202140b840345c400d5100e40c0e801403090800411b800c7d00ca0000401d2802c681e8410000940362104000c080e50b4054502900b02d09138a00c0e03a0b050a40342e00004554240303e00843c5161442030f402e0340c40010803110030030302582c4c00c40020420001c0c0c60404126503404040c01126034440e4030032081c014180003c04208584151b05402d8900c2c800e450355038081400e40440300c04101c3e0b40945c85401001c070058180400e6401e00000400c48610300c0034906280c60f824070120b015200740100405610340108a640038221341c501070382d0003154805541d00030072100300141e203a903280c084040341098002d03042400901e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 893572679 1250 893571429 893571431
    0xa0504031103090a1503020c0105012c090c0402090a1d041103060f07110f061305010b190501030504150e060919200303300711190602091e04 62
    0x14500c280c000703599100d106425900301c0b0b400c038401c2150303000005c200303501c000d02850054604035014036a1421b613902030b040396902656007103104541c443d01d85080180c0300106143c0000600e0600302c079580319520082180c3c02a40c00280440c0640d81780c001710806400642104040c102c1c20f00d0800298000031181166504440044241185000078006d445540d501d41004000d40d12490111011100480020b0280c41118541e030381c41d4506200481c031540c41d6503461100201242003403800d444c07003a1450383c0143c0c0418201c041003107000703c0841c20341d01e007801d006c03c1a446038a081d075651091b007946a20b0031443c1106c5111003030760120700580a0754001e0200c60712520b40c031030359500c5140302c0e0000410080030325540345001008882c079400c0380d801c01002c0c0c1e410016507100c011005a400e14554545a40644510103a1181030002e25000081ca10703109034800b24520425950703426401955a00c2c0b620020500b0800a0341e8045031100600079284100f211900008070710101060801d443c461 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 893573929 1250 893572679 893572697
    0x70503010b090105091305011503030804020414010b0a05130e01090b0405010f1223190317010e0f09071e03030905040e0a0b0403180f03260f0a050705060a050403 71
    0x15240c840b40c201c2c1a184d000b400d40115840d61000d228052000c0d1001b181e1654882d0403054400c2d4000034550021400307074843c12101d1500348104011924142140045101d8881c01804082082c10130f80d00180b4840c1001a660007001e581d00300c13030100036800041d100b1541000411400e01e607400c583c0280340e06844c20701660b41c0b03948203003ea1803024081c134150058000c0c0003c0104840e00000112140032034040405880c10354182d500b4403143e080c0201d40010012000020903600004403800d90044111080103941402229509254042c0c884180541d901c0e0101e0118601481148001c6c2417440400c0d5502c0102e0342910000c00c0644810745c0454802d42c400180b84c2014080c20002d10b8050001d807544d0f40312542d50005808010f03105a08110500b40d800340c88654904410000d4114403d2803a0380e1403943c82c0850324101405a031b204040f5002818610100034142070f50304410312440c0d070545480100310111540c7c0121540a00f4a00c0f424040c0304a064075030307201602030b5000eaa1040b042c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 893575179 1250 893573929 893573951
    0x1803031215050906010302071509080913020702030a02040c2607170c0a0c15020f0315100207170c3015220204020c0105070e01020d0206010302060f040b03010807050301 74
    0x10000b0700c64a0380214828000a1141d8031a50051081c184901440441ca24180010404441c08901c00715148180040c0101d403910306201340a003404149201540b070520154086030301d80007500c800134011611a800a01560301034420120040c450000c800883d00080c0ca036030341c408105540d4a004a00d081401541238a406003005109a4038400717014074180c010041100c481103041c20a69040c0130340ea0000180d801c5d1400242080171480307140d00c1e12410003641d4107120b41506c1c40080d01c140e490703194807039040307801181903000c0340c4c2c0900c06858010314203d04a8100000c0c002c0e966400768a00090398040500c00e114290122004e0742e0446500c109601070541c2c49101c0d00003a02e2130a422000504400a000d18601c510b5801d4105000404082d6001ca810b80c1c0150070008266510b4208000040c0d501c221017022082c0c00740700811185011f490081d4807008180000b9005a0001900000008483d02110000c0140701c09840d9250f035200c1a840c0c40d00614040c0314425420101200030b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 893576429 1250 893575179 893575211
    0x3b0402090303160b072a0611030108010603060f0c0c060506270f060f03150912070803070201050c040f140301110403031808031801050304030e03030a03060f0803160308040318030312 80
    0x13030300012200c5580140280140b94a04209400f03401f11241900d034114200ba01c104080610300800c0c1640011a90a04620780380341a500c0d04010010b40b0f5181400840c801c6a0105022562a800c81000034494441402007070503d014801000006c440c403141d0882c1d58094015182d128044482c030720707001e644414041040d90942c0422096059111881c0e020f014440080380e60b41010f4414200c90114075088240400c0750050081907408840100420101903028082e03035900c80030b98600755180ca818600449104000c0f400356803103410001b100c0701140c1c1c500358800a141d20303501d5059911240d9070f26005200080c50b403400303042d8840301c00b070026042c0000000e458900103024030584461701c141004480b00c0d0001007080c0d040040c0046842040e403000d200400002160380d40200d81c460508000090b14600d0713078031a81c142e034000c102c69444810055500041e446d070500c1e28501648990804807400304800e200c581c08000c242c5130002c00c00d900f2900410b0071151280c01404404200103081e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 893577679 1250 893576429 893576447
    0x7051309050f06062503050307031a1c031206120309140117270d090b04030b160903060c08040b0903090d0b0907090e0a02013b0402090303160b07 64
    0x501e44201c00c0c40840e030f8526214000d407018031443e2165841800090400040c042e480207415401f1400c0001403002c03060b40750144500000150321800c03400b50803203000c1548010b40c444c0862081c82c0c00820700003010300c01d0480c0c00a0814160090100e241c41e801e101c2d104100f4114210082542c8041c0014a020b8510090300f078085c050b140e911024110b20540c0c2a07080d0000c00c484214042c0c42d00018815a10a030040409211000200148099403001920ba2800350708a040070304002c0c0010400500035950305a400340f20803c0e80342c00c40c1d44590066500c81a1074200034215400c0000e041022640043c0c25841103028a021307002d00d4442c3e40d8019100c0c4200c00032180c100d0038010f200e030041141c0640840e08036034901d0440b0200e955071552441202d2952a0304041e90700580801415580c0c0492802020100015460050a10410182040c504003072488580d503c40405941c0340b540c41e035040c0c40d901e4030b0260940b80ea40b901001c440c0340e05546400111a00c004807408149100c7c0b0455100c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 893578929 1250 893577679 893577691
    0x1536080114010e31050615091003020d110a051e0f010e09060103240909020f03060c030106180911070c0e0105032d0106031202010608010216030e1201050705130905 72
    0x1032070032403150074040c2c402d0001300e83c00240c403820202d04500c0003c00801c0810f05c5080b6030320440000820f010b00b00910a4000f07414211811500b004c1800035907034603003600c07020799408043d10307004d000b5000104145295581c4040da0140328480c100410b40041045260038560880c0e0380c41c81500038500540726440c23240d4000341c11a1a940005030194021f91224445452210642d0f8002c0528100c4840800040d0041462075031600b0700c003011402c02c04e4201c0c4840a046000c0c04127481c001c600f42145000511404041016460320718641416101128000c0c140d40351080c00000411000d640d45130b440540b00321810111000001203503001c1800284c10b0302c1d0010083d01c81c1c0790009100483c04909000c8286211405645c100010342e030074801c00000b18416801003c88454103100a030071607040e98070400283c5d00401142c9800400f8900600c60641e0504100b12189055000b16a4145201411034015843c00381400b86184c1c00c03601400c54502e00d0f24004075815140e120f4030099420075216 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 893580179 1250 893578929 893578951
    0x10305010e03131203020a140d0801050414040b13050303180616080a0c1103190f0504060e010c0516090218060903100b0d120302070c1536080114010e 66
    0x81484202083c1d003180900c1c174080d204581413490703581c6540356144006030300d01d41264801c0342401a403030b0700844541d0040004403010030801182110012601a004000401c11900c0100283c8a00741441d546005141c21004403038581c03601c41c004012500386595401420301c2140006110081c1c8082103601b60282c0c4c4c1d503090400e807525000d00f0068282a42c501051060004030810030100420180401d080029010605105605000741c07012502c130f086902048000c0000b40003454001d00020344070002840c252007100c9803420020308060300780782c2010004040600000b1306401c0c0e80c0103407920f10720301c02d41c80500c0541c1e48204149031141d0218107416400141c1070203050945540100040c2d10007602000840e40d0551302c50703900c2c0322804601c0c00803035030100f030450500080241e088090291304214817556040790a0240c10810180c0d820101160405081c2c40384001038034008400541169164068944524281e8040c04600016111001e00b681c00021b00704440480d50b8094010360307079 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 893581429 1250 893580179 893580217
    0x16050108090a1a06012003070605062b0602162003210a0309020d030203042907060c1b11090a060506030a020c01091505040c0f05220603020315010305010e03 69
    0xe0704a04843c4010200d070f050041c0b003520105103902c00b4440007088048800516500c1e402880d00c40110745000c0c00150181e0b180700007208100e02d00000e0714001c112110f0341c81c9421410707460041c1c00382c85199200601505040c20050800085018103000390b174084204400c2006900241940d81050000300c980003400180311909485040006001541980c9008107103480c194010485603130841d00210010ba20000c0c00f0820301c42202c24030f010110f131400742142d5200d04c0d103026801c0b40c02400c07000791005589903148850580516000d50903401030500f099240e1200e420140500c220003501c2c1c1e4002e00d511800151205550310035001034038001880541035880d20390705c1d00002c0d0041c1c0700c0c00750590b5a0f10020030100d898a4080201e140314140040f80926207407400b1a05444142e22004000b01104004d003e10758508140204281c0b20300ca4072600384c0d480142e0718001e05010760020303405000313a04610181a03009288141601d014500a00149005091490380ca1007405608030040c40a00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 893582679 1250 893581429 893581463
    0x10b010212180411040b0408030c0d0306030305270405280c081f0b270102010905060601030e10050112020118030206030a1e29090c040504110c16050108090a 69
    0x54040d540050407114245d00341501e84281d00f41e1507001e504002640d61000c50020040c840402c0002c5036480320785410300c40d8a1070b6940280041c051041404002e00d1040300c25030004c50005000c0103052030081c414007031410f203210706d60824690042d44804c1c00f221a03909500c0504140250400c0c40007542d903881d5240d60b4510b420310074100c03003101148016a00f82000a40d414204040d10a440303580d103820310000407141e8002c81c4403400c2040075043d6410044101301103580800c0040e4054400e00340460b201c222280254141a60000100318007403810380041450b000c04244540d00e039201f80c81c1c04854401014940c03001091a1200942c850800c2000034000769085d04450720340507800300303c0550b251000c0d18003001e076240070300c8215207441c2161000c10080c0c0c2e014400c24000c202a100361490742000010b55005100f83e02405024a0b210786c40d8208402c00842100c0c00d01090f01d00303446074030f401801441001c50581c8520307400034001101107001d810f000302c0d09142d02c0e80d04c400e902103031000c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 893583929 1250 893582679 893582681
    0x22b0f0215040b150102240a0905030f04140a080601030314090d0f0b0115091509080d0804060f0605010f0e0307120303092003300705010b0102121804 66
    0x4618a411406100c46024603029058200340c0150700c03c0d034103901c0ca80307000000715442002c0303051801d04540c400e2075680254843e01007045646d01c40c502d0840320542e5148040b40152511404c010014440017800340c400c1c05460010740b0594400e565000030756800c0d14208201c603680d0b40141800c503041368004000180c0907402401c01d421200503441d0030074072900005100602e079000165044901200a203040000a90a550142407448244a603550110790021704444840c080c109204800003094181c541c06a02c140340241011011650540c0e50180001c15140080d1801c8460506200e2046d1802a181c01508282c0f28103940b00007112007010b0046403030850f4072908036094021aa00410a45104801441000d0090b18041003540980c07a1032200c54180b0640000c0d01003211101542c4d41d030380410740601751500c1d5206c0741e26a840041c0311100411880d10074002408002801c10708128064000c800b401c2c809809440c000140f00d10199014031071003605d1580386c0c030602600085807400e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 893585179 1250 893583929 893583947
    0x60910210c031505061503070e0603100819060c050f0d15030210030e1603240b0d0c060e0307181a090c03011712040b090f04140106022b 60
    0x200001c0361001c0c0c2e01d45841005518003107000200c0368036201085000d080041e41c2803400d00451905a1a600d00048024800c4148080c4039201315070000c08540b01c480e1024050300540b00540c15a03450030884180991030070107801d01200d0303c80c100000350000d24001c0095501003458454001e1604480c08813000003064039960b00200b903a007071038005c0096103406807015034003942901d001480250903c242807514181c10040c00001613022020b00010b01c0358a0b00b80c10b0f40c00110307958508810b511b0b40325406024640145030708280c5460164042c40014101c64080741c80c00d88441c0c1e12440d814051584905607402104c0284010080c9008840407582c000766040d06e09c2034107000c07107401c0640050f200300c100b682c080c00048004001405802c05014150031a0a0440f005000013604403c50301c040d0b004920940119104c00300d410750890b20340d41c1030301e400000014001c110300101014401d9002e1004e002d15401442149010041d403600c907540c15600c4803c0562202015402e0781d0200d4006038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 893586429 1250 893585179 893585183
    0xc12011d0d021c0206131b180b03070b0403030e0a03171908100614071e05010c050c061323010515060c03091918020301030b071d01030e0c060d0506091021 68
    0x1da000404010b2040100616014200c1408c00355121a9a200140252101500c0c1e291080e08200310400c0741c070302c1d4002110100c9a01d424481100403a6000190001d030940d4005405807850b03108984604800000800a556865100001c6c00d0241501100c41e4502114100c042c4000d01509108a5026141041d01801c0041215181600030395814100e4421324500c440d8000002c0f80d21001c2102c00e02810020040929115061546411540c1d0392030f6000b8041c8143c1c0303040c1143c24000d004840c4d9203e10201c0c17043c1004000007201e00d135400e0082004644411a07503d00d02d00c0369034a4501031003107035103040c4070b90029410700365000100b00c203090450361440c1200d409808002000d044a10a0341d0003400040c0300140c90350724504110f43d80c1c44005104004005005c4020000244507400d40502d004080c03030b0000e0312034201180c6500d041c1c0d1003290030386e00c0000458810908a65504040e100c1c101c10707500c1401940f54541040022251380c003c1011740d408040c1c2410340c50960540c2c11004038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 893587679 1250 893586429 893586443
    0x30816120c24110d201303030e060d0c050901120b1522030305040315020f18040e2a0907210f0f020307030c0c02030c12011d0d021c020613 61
    0x507086200c40030940c4114a1035159640f6501880c0f254826041691040312045d0901490050f4290071451a905140401404c0c880c42400041590301c801e41940c2c910110f1900800040300d0b200300c00351503a04881402c0d40091004141d1444231038403805080b015940162485884041074103024a0315049000d49182c0340f910444800d01c0030403034961090045010b51649580c480c11420070789400f21102d840d94107100c0c01002280c1440100c072080300e048461001c5101e40300c048071030000c0c003d8080f12101c000d0314443c41024031071291441145660740401c0e101c0c40001811080107004c00440d040703c01c140402c0103200c02c41c1c0303c2c1503110b4024164011407200060313452000124a012220080010301070781e6408010000c0c0c040c0c151090300030707070140d038182615000380560001c0d694015a040076800790021040003424140250410407150010790305070500800700c5548603550342280458140148211810b1010034690500000600d48050303014042c61f03036442c0c0c1d00c50700c0c07003070501c401311000c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 893588929 1250 893587679 893587691
    0x12010207050607080105332101090b030f012702190303020319021b24070b0405210301210204090b0601021b010507020904020a030816120c24 62
    0xc005210b40d5200d400c0d10b481d134160303030350421b01401440311818600190b00354026240b5050411141244d003980c41220b100a03640d94414802048590800344c0030710580c0403c8000410404000d0304a05c034588000c2c1c0445001e0f60051480a003030310b0000c0081c0f201908540303102001444400300022039075001420302c0d07003081e12030041c2c01e00c4003015900640042e0001b20f590100308c100c951010030000507a2009200f1407524a000c02c014100c0d0016882c4120b04e0483c0000f01f08001d060b0300091501e002041da9120001d9090520b0b68100c110b03002c072010300070500003002084604014010b030310102018a4190707030030b0800341c40c41000b44822124040c010b6290480060f5254040c01c1031040c0b04600550a5040c03c0d000685404035161045c03401215152030009903981c000280c8450a804a40000c00c80d100c6002040d4040220f41014000f9140004c00110100500d000d03940000d00c07400780210303040d84001088031032000b40c040051051442001108a412100000c1100100120800206 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 893590179 1250 893588929 893588933
    0x20114090a05042a081014011209060f020408030408060a091a070c0f050a030e09090a03030228050a08060a0311091b0c070302091305120c03070f060203040219060503010512010207 79
    0x70405150908400085001d01000740c04140d40d1303140c0b00240307947c08264031004006000030b0200c075400d840100e0102d035213092460038441544c00041c401c1c0302c0030344115600d54845510759269400350240e844c1a1203008042817124401c0c0c4500340c00c107a042400c540311007031070481e9510620400740520301000283c244201c08180010f02103480300707218030001d01d040c2d5068603000c1c1003490760240c49032244107a403081000b0480045401a81c0c183e25242c01130740c40108111481d02aa0590711488440000850110000c1e80001c01000707240d102c1d450f0021f59030f48a20030890b15055500004140e0030405500c1c02032401e280d12503e400a1450300004104840030300704075515040841c4002c46030340240410011341c2000c0c0c0015400040030740b041c80b00e240c0c4c0c6441d40d50351440c00301400028500009140c00100009205035030103140d200e604110011003e0520318041c0d0415603040e88202840c0304441d0b00c60120906070800c490a0340c5406096a280100300050907801c1280301009540811600c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 893591429 1250 893590179 893590241
    0x2c1902010516081c05090a03050f0a02070305061008070906080703110102100504060c14030408090904030c081c06060219080f041d01090b0111061b1c0504020114090a0504 75
    0x1440b80000680c0e004d558407501558400d81d040500002902e03007002d00404080380e4003c00300e6200240300f29990303a5031141170208034505812070388050050f0080105000351603412201001c1155440c404a0300300d10745500d000e6040b40c08a00c50f0b040706611800007000024840c0d4010802c000701401959049076100c0c03c11019508111405c03034040d5500c54500c0310858014080003002c0c0c000e60b43c81421445d10f60f458040510980c00501d21130450440040c0805100e070112181c0140c0c81120320392501180503442641118141d04442d18a08080005c11031a100082c1c3c4070700d0200500010350800d103da114400340e980300e0543da018401c8100000304030710110351900c90103a10a101e0884e07040d0324283c444011154800c4403181000507044010120610001d072040e0088a040c2c03110040c0144100c240010707202e44428200350b0031240211244031702c41c60f4881c40c0b1a074001e88800015a206450146880c4141020541c1c4602030000902040c1410b0340302c6a0207807503141240f144907030700c2401c400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 893592679 1250 893591429 893591437
    0x1c0f050c0a030c2904231608120703020a12030f06030b0a0614150a020c0405090a0b0c0421020a08031204110f090c13092c190201051608 60
    0x80c0c0400c03400f160000030001c1416041c0f03910010b804d02442c001c0507425039098244400303030000c0c02c1c1c1c140c001100c040c540d051a601c400b200c2c4110080703a407a0661148082ca000d100d82c450310009003d801921545507000c41c0481d0036060b8554044e00b03000c119541e60140901140020304100f66982c1d407481703d58802841a04003541c020224030682e860090111070903149650800c0001c0004141200d04544034030120401c01c02c9079616050b1100d0745014101d01c0e001c80e1840c0ca550081c1040d0900c0701400c000f15820844034001c4821003d20707a5041402a100e20891148540e08801051960104584e0f640b03042c050f24801000c2c031902c5596180c0302c5185400c50800342804c0200b54003840100f00d02200e490f2440300003611104131281200c4002006a000180500792103140000c40c0040200300313448600281640384c5041224a813205415503040c03810303403030006c196101e40030304106a0000080c12000115200900c020540d5154011034080c0c10464540031501001c01410002645280280c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 893593929 1250 893592679 893592683
    0x3072d03020705011b0207030b1f0e060913150e150108070e1024050705101a03210f040e1501032f0c0a020a030b090c031c0f050c0a 58
    0x5a101c0e0300d030b4100f650845407000724808180407050600e0304041e0300426480c040b240c00c080036400ba9610b0f9464044e04914800000c5141ca0204138049001202d88004130700882c42500c0403111030b511041c084040044048000e410004041d4429404a0041d000403121095130015241a442041050000d614081e0060800c0d0380000034140001104031944c207600ca0306080207031040381d2400032594021450044036081074052142d1080599001d00c00312141039902004460f1003150008560008080000b40552544a0313100242c0c82450001740d00352015540d8020f0000b40740c0c03080c0d9403181070b51106403104482101030000040113240c2a15052080b5900c2c032032110440000b034001070031602c0c40b9240c0c1d454042000482c1c504d1992244507007100071a44010b007599a14416500d910305440c40c007000394440700b4580003100300034007080124061420740c4111661400807008152b1a0010136156140b20b1845000c0560b9162017018050714000381c900304607280900ca5020207050800c80541 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 893595179 1250 893593929 893593931
    0x6090b071a1005041d0606100f0e15160b07030902061c0e16080d0801061b0206090433031203050c0403021c021816110c09010e15031203072d03 63
    0x1100807815090044542c031020454414244c950f1040020300100740e40000e0408100407800403070184d4039450403d00c1d032f2032441d406194898281c00b03040d28011860741011191f00d1087c43c0401d034200c2c000c5c0980c14000380d0003860a400c0c00c1c1110009950404000c18030a800b90f21002c800c1c00c410400e0003e00a0722840981200520742008410381c13420f090f4081307240400801c1801008020350105004107180182c0c0300c41e0080d9291400080c41d01c0c0100703480d680e80035240510418640c50089440d028802c03010300c1d00c0d51034102d60200301e03031030749041c0c40041d18894039605010302040c82503103c40d0744404105491803c190300c0f03070003140ca2a01d140c02d21070b08044d10000c169080d071400700c0420f0103682c84c0b8001840d451412803030200b03005094160003801e000207544503487e030203018019842035540103040d100c069a5148001d90f41c3c028140c9026010301c003a00340c07540c45070801143c00000ca400d0400098510384501100311400d0503001219550f1b000a40c000e04400025541c40700d6002c00750740c0d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 893596429 1250 893595179 893595221
    0x20303091c030806030d05030105040b030a08030c04060914090402011209080304060203040614010f1e150206011505120630031306090f15090f090606090b071a100504 73
    0x2e0050035446004e00391500c2039001d0300d8041c600e26401021203040d180e0958001c5044030030400404d1030004401e000a20100e404801c0104190803000900215609030b600c07801a541e58411541d96031030005089900301400c6800500036500441c4005007201c607941c3d0018500145440c0c080c101d8106450480d00306800009010521036180a004c10561890345d0780c20441d403512404030070150041c800d61031011800c145c405c80582850450b0001003800a4021a1584680b01c000b13440d11801d003e0b240d92040c11800a20000748104244d41030389032942a02c0642d6207441701000441c012680c10107130030a1340c0050042081ea45c02c42c108400c20070000045494130a245192510f5030001c0d00321100708020b07d03104001000c80101e00d00b00b1070310207440f00ca42c1c5100101086801d041c20360004285059075400005d400d9030907901c01001c8401c035651b02c01030942c0fa0071880200d88103001c4090944000c003107005100c0d000d01030790b8580140456a0850030705999402050998514618950505420344 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 893597679 1250 893596429 893596433
    0x90f0304090b0a0e16080c12040c0602150103081827241309020303070c0305060108101107020f010e040c0509030d020106080312130c0306090311010e100207020303091c 74
    0x180980004c1c0400b1000240c40e407030800c019568000811107036004100400c0b020480300ea003480c1c2120054050520000000d00d010f042079201ca4940f48a80801031069645c1d04501ea04c0b030403507950580360321980081c540b42d4958924445108400300490b4010021000201034042c0f0000f4220480200201c1c40e906150440103080d60002c10305007000d0031a04650800000d41d1400741003400020045c0000030204c5041c0046842d500031500300034a010240d050102c180040062914100c0703c00404880031814010107400c182c4110300103641c1618018071059006240c6842d000c02114418505403002c0d00e00c240004054405caa1544004510b0000703034114941001c2c0075804190302e550000340300b07031854160f03295520b202d55029028119014804104c000324685521113520b60082024404c441d10303801c00d10014200c2c004120302141c01241c081903403443c1030091000340c04441e006400e030920406041c20184d484248105e9050008000c26203059541c4040b5007401d14402c0403102f001c046134 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 893598929 1250 893597679 893597689
    0x70b06010e06090a050105030c090312041505070b0c09120709061403030403020a0b07060212070f030c08061f02010f0905010207050607090e280504120e120a030305090f0304090b 78
    0x3594640b80100002c000c3e01c11552207000350b000c2150300030300c1e02517913030394840031051513500980800a81c14001c0c503c800d045145400c01030415030b4401d071b01f006500050414281c88910a0740c2e0000c062410080020f140510645d000d4401c2000290550740003030802c0840380d007000104c1d000110241d0303480c4414084000c082c03100c4003001a084d401149803600396000035040a600b80700e038401c4800f0001e13591040180940544460072030310045280b00313042040c8060442a45d55105c80e00280c0381c0190300090510900626005180181400e41c203006090100d1818540b40402141990b40f41e086d2604d0300304982c440c0f000c0c1c8600541c0010785030f004515082d414072002a101d1410462000b000b03012548001d20000c1d04030b14035000e000c0340881002d80380e80305a00d041400003400e51800d400c200610a110300151200da0380381c0d503075102203040c03c0100a1000119000e4a00540c000694070000034002c0c1d22064000d41c03a0030840d1120100800c00c20718550058218009039070311030655030414102 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 893600179 1250 893598929 893598947
    0x60a05011401090e0f0402031c0201060504230a0c03022808100b09060a12150e0703060303021203090a0203061f060507030c0308040c050a030503130801050f0a15050402070b0601 78
    0x9203040200d6500e13184c5000e4543c2c00107840e5800680801000c1703000c5540400c11000d42c168105024507a0030f80000000e8000c10040c07240c030340100d082c100c8a844194401602a401020b00d0215a10585404c1c403494018840950200306060742040000800b201c0d1141002030035580201c0c00c2c001e00c5500000401c0e61b000075004000000c00a4421b00c403000305078058030402c0805a44070b41e100c03014000100d0300e44403d07607181c0080700e2400c2c10440c3c1d4082860440403e0f200340040d5000b458071142403c8049074042d1002800503081528203080e000c400354019074200003000e08503841c5520f182c0000307007411000d65030241004402103407404174000450f0500c00400890810606001c0c0540740606078600c02c1c4801020807800c1000030b01000000c08a83c0701a21000c0c03c8103850a440c0c2c0307442692030780810b64840c910750034014005590181400381c01d10a1114458010003501c8100051003d865140402030a2040300c00317003c6401e403160320183c9074050240c0d212007224140700001402001c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 893601429 1250 893600179 893600219
    0x210e1002040e150102120406020a110f030d121523030d09030b0403031e1401080703170d0b0603070c020103141b0c0c0a09090320070e040f0203060a0501 67
    0xc0144400c2061440380b0514542c080003034100c0c1002400d103000101d0800d140800c0303500141c1c001040100341c01e54000f0b5220036071441503440402d03550f00750040005a200d5000000c1c0e1687c803a00f80c000016108a076840e0b19004021004200300b00500e01040005800c0c2c0c01c511980004031800480c50014802c5080c540d860a07400b800040c54000001804400325010240c81c168105002c2810140700ea40150000344140b1020161010780300014806482c45002d250429010342d0004a80c1d10130110b151800c4a41c482c80983d0507504120158000d80c00c0107000308006a0307140c02c0340d400d50b1504d500843c07080e0030075a01c400e680c031035520026048541c4030b811501d41101c118108441c01030105100540d06100000042e01e0f4600e00a0262902d003802007490b400001c0848005030001403030300800480c44c0319032540c3e181c85500043c4010f109804034440420765104000408c4000000345406410078091a092080794800d038002c00c0c5014001e4171001c80c201d80d2400100214070b41d1000d40d650b49031b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 893602679 1250 893601429 893601431
    0x2030f0a0902060423030f03040504241512050c0d0509150414071d04170a0207030f06141305010c0e011d180702011413080d0c210e10 59
    0x201e896004188a030081d401001c20001d0038000740482c005401e001c0c101d001c0c0300142118002e00341c0d030910686030b4000384101c9001d00d00346480300010a0700301c0a07a2801c42120070800c01482c1c60b001032004030324138903080710050000161228419035038034013815200f0501a602140c0c0d0303840403582d0b602202d0004103003011070742000c142c0c035070006034401d592500325800c0507030242c42503d10b4824070300700f0300b0302e51112411009030011300304803000f1070880e1403056009946954903c08500c071140001d00c40c0d43c80302d00040e08104020300018460320049850b0318014900042c2040c0d148420008152007a0b40e07840410000787c805908000c3c0034042c51000d00010301d4600e40d903c4c0c0c079400213801d240040000d000101900d0845800b41d84030600341005000384c0c0310000080e0300342080c0c064002c00c1088559a0942019800a103100040359640b10003190310900b42441e28140c540c141004107103511014042140008104c042c21081c1c0d03503400602a055000001c041210162984c5410070f40e4100c01505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 893603929 1250 893602679 893602691
    0xf0b1e040905100209131a040b0a0801141501030e031210180e0106060207060c060b18040b15090c030a05061302041706060405040507030818041b0f03200d15030602030f0a 75
    0x7c11507141c811b4000400503100450300c1c01040d0001180c1d5056500312603003561070a0707044029a13504604081c0940c00b101085102000280c00440964050884c40b030440d078020480c0100f24450b00400a5004a140c2141d06010b0b4448181d481e4021220158040ca0b42c0c0350600011001400c1c444c0400900c603d000803c10280b800d800900501d001d418050070aa513650030f01d4003503840358403d04c64100c8000115040f0303481c1c1890704151100d800d0341e44ea41c03110240c000b8a40503080c8400914041c2036214000c50031039490391183e9020702802070050342c0145640c0300f2480c2022450010f000600105a036000b0300c40c070130789080c1e4644440100801d100d00d080605100214001040032070541e80c10410050b6208110150b100a000541c51840e030041d10b09103102c00c817100442070320581d000e03840e9070323039918190000c5088003541c00301034841517030b010310900601c2540005401418041d007071810202d02003d24000d48400c000e110b038400ea4025030000100f04000003078640d159400350464008002c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 893605179 1250 893603929 893603951
    0x13113105061e0402040e0106270e15040b130609180807060203070c21030e01020918071b060e061e040f140d020708010f0b1e04090510020913 62
    0x811580d201c442d404040e1200b080c004545441c0c04440243c9540884c0140550f92950020100410382c5d02000303240340c000c0c41034034084505918800c1101d503e000b608a00b9103900d28011101c1c00c1c501031569001707580350400749443c2c8444103006200140c0f0440000d80900d044500c00648031040c480011000403d044880069105010344030030030780100c001a140d43d0b07041001d40d10380d900342001501c4a010b4401845005600608171001c18140395010710640350240c989600741c3c05642089944000c4010307d440e255089078220343e602c21514a0f014412500c3d402080c0c194110131441558482d07264406841012010019140c0080b142860000423501a000234042c07039001410042c0140c0c4613001c003000348071305403521113400c240c1002543e852814460300a55205100d01c101c050035401c01080744a00304451046440411002d41842444d8100740181861200da450001da4050f5032030b5410804914200002180707480f0f140d40050303907842c00904001d907484039800d8202d08203044c8881c00c0c0b6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 893606429 1250 893605179 893605189
    0x16050303040e04050f0a05030c150601050315060918160203030c0406142703070b09030c090a1103090a2109170106031203140105181311310506 63
    0x108075402e041e1100c0c1c140d00c40b864002d081000c4a440d6400922503c4040000e019002c40103000ca00f100c1401c0390590a40c03801150705013507088a03118080341003840050007002643d20640702280e001040c413860003180000040c82e04503120140d40300e41c402c0c10104450b00c0c0d2000110310413030307003580011411480e100c0c0301c610591166011301410440d214021242c1c043d8448190344e0100d002d918880032001090410004090449821610922500700005460309e40502295003040010380546000a42e8506202c0c040c500904001c002e59074031003000441d80d0350710010314010a41507010342003501c03c1e800c0003085644941d480721500c0c580b842000720002d030809081d034101c0350707048601e0803101e0002007074900400c49980090800c001c40d0100143c06a4980d00018055250888809050343c0303032018000205480c400d14544802a030f4003007151982040741503403a0314456104031661307a09030000701d81c0340891090075030001588102080d142c1d8a10928401407000d070f0500401441c601140010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 893607679 1250 893606429 893606437
    0x9010302120f01061215050f0c22031a0a0533090406020a021e100b03190b010501121e110d140403120c023f0301090c0504030b0408182116050303 64
    0x2185c07550000342030350501040c111400520300c040042c4010a5940e080510b074a1068000030014cd429803400668404e1040c42200e00034180d00d220bc2e803040d8202c4c1103d03a4900c1400341c0d151704641c0c0180420589580d1100300380d200d00c6c4550303000b503285c101c0408042c1c0b50044070b0000d00c2c108040c0406038141780308000382c42442c40e141044003285451980700460f013000b422041070b80d00211141e950b4424000c20441340341c12038000303030307102d0142c06090040e00046070b08540400d80020200f0082c111802031903040070058040c4110058a071055020038141103d5903c0403548882480700200010701da04688a07620304010310030180202449600000d4403401e1060004240850a294482500080a1a80c900049500d1504011208001c8a61196042449940e51890800d078005c1c1c45903210340309403400c80750301c040900d0743c0362529652405560001d02d06002014180c40540f405507a4080503540c00c082c079504e40304d104068103020341c1d0800803c2101d0144c0440a84006c000b5920300204807 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 893608929 1250 893607679 893607691
    0x10b0d1a060406080d080105152703010e031c051b160611070b100501210f020f030406090c08030c0a03030905100c171509010302120f01061215050f 65
    0x40c4545035950400140100740b04d4000c20040d2140920304000181c1000b603060580b20100e13803191031806040c1005900e0f11600521441840f41c404401054000b10901d03036002c000c0050020403000d820902d19440d64000d5040001c00010f0040709203036014807482000c2e008030051805115000f17443c0d070b60090b244502c00c5216440d501c55442407060112aa1101070070007042025180d503218541040c0c1c0c01c1c2d19050b56501c001200c46140060036600440701d803850300884500f0b2400004002007084020440040c07080c15140d002c101802d00210440011485240305600000720180c10781040c2d0301514498100600039401042a900003079000a5180302503a45458042601401850401d09203c5410303c020030041c141080014001e4104680100b26a01201d9141c0a555800200010038820380c600c6038100003404018005401d0000c0402c488140c03680440d40502050064542101d6040e4050340340241c180c0c5a40080000415000c10501c44810003441070341402d0283c0c2e80120006448 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 893610179 1250 893608929 893608973
    0x206040303050c010603061b09080a030f111c031d0c0303030a0b060c01110901180e010509130b071d010207050303030f0402120312060f01031a0111010609050c0c010b0d 74
    0x32076100070f40940088003d950710400900c0031040194031548006143c00600d80401ca0041d4045510100080c6030142e50f90143d0305d90340e01050b1348005070b4031810f12500d0b4840c0c9000307144501d080b80b8450650749038000d89035a000941640102c100c1da0b0640403800c5591072a4118542c045200d03034001059a81101d4501030000d1070001840008440d031054420f000929400c1580c068101c04810f0017601c82d452080e01c80740d50040c08030005071780c0f50180f4001c030b420441c0004014170417420070507906540003407840c000d1510b00781151110030303010404031340c050009103241c06062030100c1090034a43e001d05023030004040485c2002d000980320300005040002c19010200042c06540d14070300304c44020340f1002c0c1983d55617100d12a45c031248107021076080b80960307041c1c1c400c2d400e0382d40b0030701c1681d0f09040d00b841000d202603401001116505070090708265030b076494180200310b0030658481c880c025074607030041c41d60708e21a02030340b43e082d42c90444030544543d8403159811302241d0a103801c00c00e58944000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 893611429 1250 893610179 893610187
    0x906050d05060a020a0e0a030f020411040b030a0902132d0e06060609010e100c02150a0206060d0c09060e100f12240f05040c05040b061b07050d050312060d020604030305 74
    0xc0846d51542c8028190b80d120703c00c0c50000080c400c2030388403111101c0c0240c80a0040700311114000c2c801b0300c964422499410010000901200f005038808000d061004204e503034a000c0d401c1400c000c0c2c03601c03003601e0459641c0c400001035401da0003001c1001c811202e4401441000c20788509607444120041c190380c018030000502d084260b1003182001c00391103000302450108048681c0003020703144030410490003460b50090002c00200c520054400c411003980c001e0407560365000601c03da40c00410001c407060030b82d181d00810010315a0042d00301400c40304050000d40d1810b20000b518800030703640012007040003580c0500c180000c0500d01005079030070a5102043d040d5140108915041180701100cbc5035280c4005030380c01c0c000716003060740254059010000300c5031b112810481103841d00c0389400ea00c600204000c160b4a041d4601c0441240d041c82c1c1a1000d4a948102141e509400c01504a81c1600001a6a0b40d000e581161068104d041901d009a030790b503d540c0460000d200307500000d800d22030042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 893612679 1250 893611429 893611447
    0x90218150901110304031407090b031501050d060b040216060b0d020306040b07050c030307030e100c0813060605090a05040c060c0c0302010302032505180102031e03091009030203040906050d05060a02 87
    0x40f00c00030b6031f204040c6901d56a0030030910380c441000e400780340d0032a030400e0700018541c6400100150341e04d542c4040d41490b6440e280030003050301d061520441d200c517183c440000650b84c8510141284003030010344958461a203180910407107c031000514429400035400304090303100014220742c0701d079101200c3c0c0110380701c2c60410b0307900c1c0c05000364003140e51100008100c103160303150b0814224044844211540070440211150a40320306040150000301d032800064944c9480149032140c080c040c1c0d500054a94445004c43c0c1c0d511030440d280a0381c95290b00c2400700300030f8445061001131146140050005449580d0f01c5449001ca100280c10550084046000c041401641c10692201190405d03001406900081d2241d0070110002c1000c400b044030300000b55002104980361001c00c0d00e840180d030b036480a000a51a00098800c1a1500c02e9011400381a40140302d20801d040c002d4000f540c0b61440c2151400aa90f4940c1107607026001c5886070800044c2e0000f1700c507030030601c0340102507151081c007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 893613929 1250 893612679 893612683
    0x1710050103090525030c05040507210207060e010b1c0803040803372301090c18092901050306091f030b040b0702010c0c0b0601140409021815090111 65
    0x2800c139244010f400c0059440740c4880000122045a200368008103142d541c4034100001c0304d0f001c41c0e144000c11f1500105c43c6c40c2c00a420b1040341503003988040182468621344030741080f01c41800d840d074644c1c2c2d5990107088003841c0c19402c0b494520080c0b11100d84111155944c002c0703500020708000c22108000c8042864052408501d0304280d60baa4408181240003100900c40f50368941c407040c01c59450110f14041c0340c00700c0312008070a4001c02c1c0840d102a444c0c01340e020014081c01c41c0c3c1c0703800c100c030700056008070860540011004004410303010501d120720544d44c4102d6207880b0f141140744e101c0c05000f030710b0baa608041601da00500890706241c0c141e845d590380d014140c0c1040c3c041d1b900c665030100044100702c2505135a50145009031100c040b075541d48403090f800ca510515940012800600c00703c400076080c2002c1a40c0102c06250105403c1403101d0f4820080c0c01a401c400400394000c11000307006d446004610200410494645011b40c0340c41c914000325110340114541041703090b407540f645000013 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 893615179 1250 893613929 893613943
    0x60c0c071a0d0906020a031427010e0d21090b0402040504020d020307080307031b030203030c0c03090a0f05030d020d12020906310b0a0f2f03030717100501030905 71
    0x4440b00c01d01c81c5541901c1d001000354420021a030202e442c03e40e40040c0c010880b82c11604c184001030030f640740040284625171101148104c180680d64903500308441c5800c05220640084106403240303070400040d45190f0581c81150f1300d00d0340c10780d1700d40000725000c5601d4496203600150103030340006d02a10740d0700200f040e4003400c000c040e4061240d013800140a40002009096642c083d645544059003291103100503104c0355007014005a00a01c04240020313a09802403029070344400c200c920740040760011425407804d81e800460301c0c01c3c00e80e03401c1080381028030041101c1540380c0702803ea00308031108058818903030603410008407540402c01e543c0b5a180d0341d044480d005944e04032000f41e01d201c80d001d2682505400e496568849000e0400501072a2940507101e00600503107036902003200742d15086411401c0011036101484800350344120b0319040c44140c0000c0002040651364a1074503040141034455040300300c51210209108021020a58010840aa402c2460b020510b5440c5041407450512 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 893616429 1250 893615179 893615197
    0x9030201022b06170a02040e0a0611030709090b0d060b010215040c05030d0801150305060a150c0b07020712110d081803060618060d020105040f030c0503060c0c071a 72
    0x200510403264050400b050425100c001d03100902069403990082c403543c40c2c8030781e003e4100c0d603c6090854014a803c0d000180700b1145030040303600c028140e0b144c01c0d081d510b40000f03c1038522000400e2100039a48440c403203000c1c080c005000d10081d0b10420200c0e2640c5841c01018010581d2101d0410b4680e200b40301c0f4940c8400c020131070644600b020b040510b81c0301c0d44c5d846020320030f10402000254031030003a81c03164100e8044100303020b403a800d00340003500a03103002412154030900312840441c4592490310003c0300c9007065500d00d1031540aa2070300c24882080903240409551000d802001002d130203400798440594071420611030b4103407500114400020400300100004408030b83c01103e060361007510305c4800e0044044542c01c0c1c4410303050000e6000b2281c4440c2c02200c0c640001102c5d400d0074000950501c2c41850560f1410741c1d0392003400d134042400e40040b0303050441a901000300781303070070010f5a8204210a903018906030400b01e2087e40d5150034414500105c8040c4000200030301c241c0140c0300050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 893617679 1250 893616429 893616457
    0x1e0f07020f0d02030316020c13020d0b0d030c020901050f0a060c11030d050a0810120f0312020307030f1506171b0d2304050705011409101e0804150903020102 69
    0x1400400f075269041101c1428040800d0381c4035090240c40010441c04100000d00410001e0360000b26480c040c1d4880c00407100c0c103984590340c1c000561140c0440300e40c400d00a0f6610002d5461350301c1081907062040c4e2109220300300300880c2c445d50343c0d5801541030480d5528285441c10b8034151614544020040702c445915004101509403610340081c010300c0030211641da54000e42e6107114500646800e140140754411b410109404001070a96030f80007105130007818400b402c4010b4001c074400341cac2d10444d00c40000940707884060342c090181c0d00a00050314900c006510f40a800c0c000010480070303044000312640501c2c0350118100c82c0e80c504824007030300480356030655504001c01416000d80390b81d0180c0e1054500806024001c40c0070b0007240380c000ea03407041c0940803c51030900115402c0d01d61919060b04808200848410f47e80c1e04119005074980e142c0710070401d5414000c0304e041750a001104081800456000c02001400d810b040e00109a240c00000428541070b090890080c000d81054011903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 893618929 1250 893617679 893617693
    0x50a0e0d11010b0d0b010510140910031b090503070e01120f1e0605010e150a06141c0e0105060108071205040804090c030618020c03070803040609080301060302121e0f07020f 76
    0x210a041c80c069042e0341083d50307250a0710130401c0b8103e4001e80b50074100c1c0148101130020140c2462f0415010b003880c2010301d0041074512100c0900300080c500d2030040310201d034150313004220900f030a00c41040206108001824150300d4000c0700b03176003509a9a80102105480d02c803560030070029002002a620741d04101407042d60161400308001d00080c012001c0f101019400140c811a9a80e11030402c1c0302c0c0988030704050b0f0329244041e035201c141842c648109803814024611100c0d801d1200c1881070b80d900001180c07005620007400c4c01c454000d04828104280e0000304640c254000d110401c1445000a0025036692a410181c1d114099508600200c5007050b618065482d40740c0c0051050712001d0300e120704205841d0b140e480483c03141040008141c2c100780b10307034404210401e0195034858012000842d000903c2d43c1c48412591090704544040b80c3d020034039070040000c40019a6116000956150b100301e06010303c10f004140060030003c0790088940005c961074428403840c40e0041300d00c0200c0300d00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 893620179 1250 893618929 893618933
    0xa1407050d1a060a120b0607060f051b030c0901140a02030307170108152e0608070e0d060b0312131403010501060503010e0c04030b1009050a0e0d11010b0d 68
    0x55602100c0c000c50010300b00442070482e25851550351080d442d00038205890941c0a86054804144c41c4140d203642070391701c1030110090f89170000200b452521681c0c000401c0d11420b1442012a017010741240d05502e16019036140584001d01281e070401d120340e41450300c0d41000c00c0101c07140c003120b040801070b0010104418a2954002003c6c5006111f252241420350030b40a8001840800904c03400382d190340400244242c000e4641c00f9641c02031200c11886034626042c3d001d50b4158a0110b4020190000722a010044070ba032152a0781e40280c0140b400c032083d0b500303d00001d840304a102d00068451079944a5400c110b680402c1500000510622016180d000c164026100d0750014440c000d01a42d800f079411545240612400e41a202d1035140c0d1070a507401d18080c642890310003409150160070801011001c20806400180324020300784110504604280b4800103941002e8210388829052003a4180c01c0140803840d072521414070720b080c0d0300b00c2c0740954030140980034030700c1d005400c200070502d2101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 893621429 1250 893620179 893620187
    0x6030f0605060306090c0f060a0309050f0f070e04150c0215010b0d0f0203040804061103130e010f090c090e0604090b0103140d110601050f2101050405011505180a1407 73
    0x1c415081181500c0b030f00c5d650b050080f03894410b8001543c3e880f00015030b11b44214a0700c030b00503200155162800085404069541d2480d21844503840c15056100b0420514144002c2041c400580112252140d003414a542c070036800d650080240c00e00ca41e21452601e868500c00c001c0c090f0460380e080c41060185d6540e900f1880c20368003480702900e0382400d03c81500700d954031070300859015644c81000e0f2894180b0b844000c80d101404042e0399070590204002006400100191f40c02c00b13880d002e4000d19941d403405000504800a5900114526051070b880c0594942c0204a4000f11103e0b0b041003170b200d5588070005002418454802400c500100c1c0000c414041610b0394100c4130030804013103a50215502c1002d4880c0c142204258090b40e00100c018071a070f0905240c1c184106001500d2544070441000450491000e102c4424040e607654104020610409000340681c2d40300c5280140400f80c2000d0110b00c03030380e0342030041c002d884a620780860300002c003a0f0f010700c003401c40c8105c09540c00e00300340100034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 893622679 1250 893621429 893621431
    0xb090712061202130e0106030215030601091a1210090e0102030a0c05130909060b0603130b0c0f04060c080903030703170906010605040e06131802210c011206030f0605 73
    0x5041072501901041c694104201c0c2c07120385400525516180855400fa07501a09040740c90103590b540390309000005031030744445c5800f203540442c1030704e0300c901d801d0300014090403003580184c2595102d1420503883c042a0302c2120001a1070940f14181c41c1d44141d015040a030a5500101009241c4600d80740c084106601450245100ca5070600c070914500c101261035000b0340700b180015803500b0301c040001194a038001c407151031044501003040580c440006109400441d101c02d21400c3d80e0024104111801704d0050303105101c2401c00781806e030424102807850085015000c10320143c0c049000c18040f41d07a0555a000c4001002c4959a4400c1e2170000c090040e0007000c0c4103521200c9003c6069500301003030703441c140e83d9542e95082c10117140c509102000140541000e0300f203100303241d04118031b5501d8016949000101c94401402c803640e031040c80704900058080b1004070f80003c403500500170700800c48040548003440e010b0302c010034641181000b80030a80c8020031007026030407180200045034000c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 893623929 1250 893622679 893622707
    0xb031e01060b0c1f0f06140f010c0825051c110721020111060c0301060f030e210f0a0201061703030402090402011101020405030105091617031603030b0907 68
    0x24000340c1d6444075040018010300b10b440c480c81e00080495807070313810426090700703404c0b8543c01e020584040700d01c40d040445015070010f040703140094100d044182048035032032880300e0013843c00081400c0180c075441a03c0c054183c0d9480b54015010b48584801003203800003000c0c54001090340c00c040c080710201a0b1600d548204800881c030710210419031f003c80440c0300c4040300c0740e03246241c812540b4081080c00314684010101e0500250b0040c40240c100704001d60ba204492032550b50b5500c0d410b0600260013181075490303400070541880335070400b0580100e000a401400d1000c86031201b4103601c0d00340341034010741c03c030b81a460101242c071030384aa6054100310125800c0174151050b005807210410f4991104071000b80d0403403032100100d001075100d81032100034444203400050501d511000002e09580050f110802a584035003a500a00013001d4035a00c001d24200000e488800760000f60541c5a0040414200e048003e2440100905010760080311950f0401400110306103001d4001400781c0c50902c800c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 893625179 1250 893623929 893623931
    0x80a2604020103180f0b06060f0a0c05070b0c0307081e0c01050103020f01030c020d080603011107030201140c030103120807120c18060f050403020d0f050d050c01230c0304060b031e01 80
    0x3900d030308003903100d44c05801290412003403201850340fa00c0710804d620b40540760f00e0b000841000704001444241c00944501d40a95031480c190012608002d0300d41500350f0030848250b4020054200c0703400340001101c000d598081c0d10544c840700b9020481071582c00c4544c4440001c400050b0181e6104030640c05641a0b03071003160150415150320004604841102043e100941c0c040000d03854202c0c01000c0b0503501020060001c500c001c10701c10500300d00d030820034040380941e455082c40700c020b11107284416400100342542078110761441e290b03136010035603000182c001c0c030246c140801c0c0b925104004050a0b1500706406008146c5c10b80801042e5402e0f070360340d07000003001aa0000c01d04c18840c140c1c400c1a59040da85503820141140c0070030441210200301125420000e80a2200168041c4007801d0040c60b60381740c954690440d64420303400c1d00d00352410091515207150031111f05002d070100c00c0b50000c5d188110151a6500c80c6840d500604500c0c402580c03600c92401c005410010140c68404a13040d8140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 893626429 1250 893625179 893625191
    0xe01060203090901121b06020d03050a090b010612092f0406051011160b0901020f0303160c080c0703061e18060917040b07030801060c0f080a2604020103 67
    0x11080780c803406903140035030740703c1a18801044113503003283c1581c07180d81c0101401c0c91030114244030508148803560080025030040c41c080c107107403a00340c4a82513100d100645d0038400d05030507607103d0345c0c070322014040c600602c480307560211101038090384003890165210034001e501028080c041d0050a8800c0514404180180c003083c0703046c20113004450803620302500d180e0381e5070404101658500e4602e4402c01030307403041c910180180e028084c0000003e11011355425543c100ba02d000a042025440e40541d5130b0340704205000c0c2048440300001d880d0042071800004003c0365181001c40e0f8821039480282c14491240080306011140d4031611540e4001c02030501e030044a444181c0c196560080034171104561160303098081520703074002280451241606082075081c0c12035164968015810009001e000400ca2008141c0c000f5142030242403d0300b445103100441d90750740d600040070880c00402034440841d800250700d00819071303504034030710340100d400502101040c007e902c0c0c0b4044030281d001071300f815 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 893627679 1250 893626429 893626439
    0x21020907030b1e0f040f0b010e0109061713080a0819090215070206040f0e010f09021813021e0705150412032007030c1406060303180402070606030c0e01 67
    0x48110701c41c0e01e0780540003c2a1184801e0710888120103a440f65030442802103c50720301c1ea6891095031070003070300ca0000007071031801e1100061880d1010000300e814400c1407601800f803260000590140307003403011030405840c1d4410b08c200e4500b0841301401081d4850110300903190300c4d0050440b52046d50001110000320201c50151001e440305464040c0d0032211001100701c0815000004000c042c0c005003003d440c1c00e69071600301c140314400d58855210140040300500c00d68030820008002000f0648056041071014003266907000203038000e0b00d11a030b60b00f0741b0751880080da0341c040c1c0c0d902042da0100032aa07490001c1f100941507000700e8048400b0701034002c034007040d400c01e08034150103150010b01c60100040038800c290006c1c1058142e04281c83c2071010100f100620100040007058402e13955081a101203140c035519504030900b8400958008104002041d20300005403403819042802d0380509428070800b060081c07140d440701920041c00c240c1d01000340618001a40304035003841c0007003141a07030382d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 893628929 1250 893627679 893627681
    0x1303050616030218060304020f210c062b110a0f2703170f030a0212060d03050307050f0415020102130e0105010c111f12060b030f1f2102090703 63
    0x1300300400f0b60445108148102c5083c050043e40d4420700c00b030080704540c02501c00007a00e806d2022005004c1c01443d9200e60900307202845040f0340c00c80256200e03030400205404140001c1c242c1a000b111003400c224050704c0aa04c541c02c42c098580b0005030041d03442450f220014403804656000c0000324030340c204c41c0c00c98281d03170020240c103200180000641c80380c1940c0d44d13001c140c1150b080f140e00c0307880c4c144500f2040d00300000041d030007002e00c10401070762244a44451052614003d000a2103000c5044d41d80000c41c0d042003c4030340c08152403424941d5030000300c203c19420f000b1500500351070600c2c0d43d0912002d580550003410315982c07192030b111080d6507840840d520312100b4041c49001642c4181494001120b02d20700720300050001300082206050100704800c64400a0b121000050611040c14070144c140d100300d001521901c0b41052441c030344800c09003030360407000e010388441112020030f810401048980301009412060044210b9003c060820740e40e47c0c4145409900c600f0381e4201103400e060103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 893630179 1250 893628929 893628937
    0x1c030b01020c06040e0f06010c051015090b012325020307150504090b010c12030902040f060605191b0c08010501060516020111030912100b041404060e0313030506160302 74
    0x1440030817400c642e80d011451480d1280030b00b149050110b181c018000180060003010200801a440003d415415a465002660317184d0310403038205261049600f070070b90b48918403203200c801c4180c02000d405085161216580300c6c00810041c07a00c1520750b48140350110b01400401c441c022411101c100d911040c03008102d0030354002c1a004170b00c04110401100b806d80d001209520014100309220244c070340c454408000385941080c001030b50f5041c1503001c501d080e1089005c080ea0341002000443e0030840d02401901c076002905500648080c81070311040c2c800c0301c040080a8402540c419074100e60302c3c0031580c800c003500903050107500b030000125202b40f0410613101041c0c0039000d410b0306180c03d80c0041d40c07800c015000c8a6500e010800001e0a01e880d69011031300c0d075074500c900408451990a030044216030000500345c1c0f08500705100000c184126500c0b0940040d042500040c01d1003104113801d00d54452002c0f007906c00300c45250004240400819441d204140d10100901c000200c00c4c812412842 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 893631429 1250 893630179 893630189
    0x91103280b060301060306020418060b0309031e1608070302012405060d2403020108011505070818090c040e070807121509020f0717120a0e1c030b01020c0604 69
    0xa544120310100e1800703001540c11420141c000207145490381c480c0f0040c0d900607003043d4410065141030200c0038035a03125442c000d0504140103400c5040c01c3c0d48407070700c031f2103813000c90780282c0407440708000d540200d48101c0302480c5107000f28180b220b0503468551b80d56000b066080e070165280590003500003e512043d05800059a240701c3d110b41d007000e040000380d801030442e400410355079401c0204400307030103400050032000701c1010301d42941c0707540700041c9042c2c4144c02102c071011000140c005115046016a440650310003c103640b00d40126520942c1c01480460265218017100f082c4061010008004c10903035120035100c9200e83c1ea20041521540030035124040000c14180541c040003c2c5644141c14101d2840c40c0c4440312a500c01f80481603130010418a1721803000020088100080d10781a00e16003400e801420781400d14184102c809410010506440142c4402c1050178405050000c081012203d03406c110034032110000003001451100c203c1d40c0948140054a00c40349805402c0d1000c0320 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 893632679 1250 893631429 893631493
    0x605060a090209130c030209041d010e010204150f0c060612060c0c0f06020d140f180706090b03100306050405060103050601051804020f06040b030403230903100c1101091103 76
    0x10803080c0c4500d00400e05d5408070400c1503401d00440c42c0d075a640380a0100700861301848041d03540c46412180d800c4421294003a601caa20400042140740c030025101c84943c0381505181401044002082d01ea90762010b4000342040c5c9400341c040392900700510f2202d12079005d010104184500c075030041c1d4a050011a0250590b1984100c0000240441d002030140114600000c40d0b450209490600403c909440500b0501600000c12030304890440c05040d0400d0307104020310f1080d00e045000780192405020310141e000002000810704000e0b029103000841c0c0c0a6400c00c03080ca42810003980f6140203000c100c0e12400341e80b00010342da1602c10401c0000b10a48541841c2c913031116070030400309210000c2801e401800911001a0040202010f07601c11402a1141d40c55140289004105528035601d8913082d01c00074002211b00b6140001c2c1c6440c40311034180c001540d000b00b00c1d006d03070705006142e0485a043d82080c001404124003c0705400d02180182c003100c01c0d69a1080007665a0500b08039118104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 893633929 1250 893632679 893632699
    0xf1c08130f051503190e01020a03090b0601140406270b0a0e10090e1305030c06090c1c0b090109050706050913050105030a0b1b070c150206010317090f030106030605060a090209 77
    0x4105903d103961300317002412500041c1041c03104805401d980100c071b030600200703560740007031000c2c0424460501d03402542443c000c0c8041c1540419404a40940c1c0100c40800204140c2010380080d154514484500d60038010425241e81d464640c20540c0401114400103007655464103540c2010190714081001c0c64645810080c2003a02030655a640188102d002031954484080030030002d01c004c11150035514064070b030a00d0800380e00740c90f00c03840c0d21035180241c01c9048003200d08103400d660856907075800111461580c0305c1001d094058071a004001e4018055910000350440e0000000c00c2841401d0701c02c6600510940c00003012100c00740f1a20342c040e00400d9010000030f8a80e0042030344004d514000307803034100c6d25914060b43d58008810840c0c043d065403100348400e85404a521300400b0b201d100800d070350340c110b644a0710740411114840010710004180328804c0e640780700c003204031524040d008000055690605c0740c0500816180c19010340c4a5031000b0070b109620b8001c80d00d0100e0081c21113121 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 893635179 1250 893633929 893633941
    0x3050d0806060412030e06070b06190b0304020d240f362306011a090f0907051b030a09060207031101050a0302070204051501030e0a020f1c08130f051503 67
    0x2c0d000013403030210100700385505503501e1940c03104041c00c4441d0081c0420991860440f0521400100707a15002c507500140107010400c6440010450340e01036410b80300d00310030107110315042e540c5010540041d10701c034002c500100440d001da07034402a115840d04100780f00c1c68400707038400b0f000d1200341450010407030500c443d019515002c00c45511101d0344521070100c1060805270005c0c404a02c0700900010170b0300b01c200104001041d00c445000702d20b00d41c030880c501d040013450018106a18682e4101d004000480024215070700580a82c0e40301511100f4070700038581c0003141a501e907841100c400020500144000c113400b840022107605980d80210304200c1e0000c0700005503101d0b0800301030501010303000c0002400584481c05500d0045000305421a105004100003500795540200302c18815848030862001503903494941e06800304098170540d25118800200310a41071006002400100300020070480c5194481100e07000c83c0c41c581c00103a140d076110700400820f000c210100d583c0e800001e03c04101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 893636429 1250 893635179 893635199
    0x18102303010c120b0d170c0f06070201020a080115050d090305091011160b0a1b0f030807200709050c07060c020d080903040f171608070f0e09060f0a060e1003050d08060604 75
    0x47c05104e4801143d403c52070215003d46440740445024005035008214050201c2e00503c40344c0c050023145150b00b400700711180c001403590094159901d4190b4982280100345805441220302c0d8050150403069410140b6801814038000c00c0400d1600d0310403010501500c001c010032010940b505000124513000228204590560140740c0750960350118454010003e4005003210000502c00d031134a0142d0715000d20003405400305e80b00c0300c0c0802050210706a82d9003201103410b01c1130b144a94000141510350080700d641074000c4003002440a0300d4108100034294000426608089081e950001207507160051651203001e1481403102d901d4500005004091401140b8000d85884000f15181e55102014160400020358004034103504107420500042c06044203c5000e40300004100d500e50808595599030b44000400955100000c040030400c1001503800500041c5507052800f4082e080282e10306013801e00314070080b5043d01c600c4625401590040340d1003413240c43e000b08002e04240c035000c03541c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 893637679 1250 893636429 893636437
    0x60409231536041416050d03090506070c0f080a02030706030b03030d051f0512030a0c0206070c0806060117090d08101a0301030218102303010c120b0d17 67
    0x403444200745010300005000c1c50b848079200000030250101c030b401c20b030510482082c103c0e0b8820040e45c025a0380302d40c41925041030142211410351310fa2885140c58141126040460b0b0001039000100180c401c3c01d0000c213082c800241c8001001c2802169501c0b94401e50f160080040250142c0054508025040c00f0340d200c04800f86019080e00c0c0791617200040007086507011122031096000c04044c21002c4c40800c18607401402c025aa00000203084164a90ba64000d004000d810080216050003c5455580544200c00d9014a41c0344200d03450352603154481d035007210580d0028148565011464558181c52400f0300c0b500c00151403020b030300c2c040403100c01000405007100b008140030300190703d48030307000c5142113488a1840300d900d81d4154810407246103000707480000811030400a000408101a0411084400c00b8940ea1000444010400c00c0050088460f55165181c8207070010a60380085415420880d0800b040101525600411a550f0344041c0d028112580041203007084164400c002c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 893638929 1250 893637679 893637709
    0x24020601081b040c090803130323071505040810050702012304020d03030e0a050f0d21091a09010903030b102c0306070f0f021b06090d020604092315 65
    0xc03624403a101c03246c0d180b075503220061240303c0d100007031020400c1c0507202c0303446040345a1140d09440030100040000c0c2d51220140074000c034900240d84824001d1303000d0700440c0c006240c01c40c142c4001c05e508540c1c0c000103002c111b0340c032000f550800e041e40e110746e4420601d0304004194041c1500355500d0325028048003070b8085008030305141e0740e1400304541100802c0510741e590b10910007004590b0f40000400c1c20901000204414449a01d9040050440490b20301c584182c9900e00003900c80d0882c101a500e0407000c920541a42a424092180311001908020080c50007a1418452500c4d58010311019001400c18600050614090084803841448400081c0c008998004a4820320000000c2c104201643d016000c40c2a11540400058001c1c001114910300c1d400901000035016507811640c485400c0114400e00300002c1d1503850b60340f509100c14000342c01406054480c0e40301d1041200900a8000da4501c03140320020051540358900740700d600c11104512080c101c5c118036024450f18403181014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 893640179 1250 893638929 893638937
    0x19060b03041221060b04030203012403141f0b03010b1f050f0f1201030b070804030905060313050d3603060203040206070f0312321024020601081b040c 66
    0x503c100030103008010180030348070318a5a80d030345144109800c4425003543e00c07040c0c103500f698003004c08110b0035580b030440c0d4209184031138000c0524061801c0031607003035005c0101c500c140071244c0444516403207035440c030405500800081c100c1d5001c1056104001420504001c8000d4500030140e01c2a400386c22148080107038241007522008501e0991b80114a04450124a00b80100180f20042c005190020310904010201c3c2c1850b80b070017455580c1a000d81c60141c8000008101000f00d801141c24610f504002500c0601120050041020002c0d8082410300142403003080d035581e1520703410322141005080e29042e6075155645200c081d400040c030030303a80b04100740108404070703500300040c0089601c2540c1b201c100800310301100044420504000c1007261207000050b010100a0185a4000c2c0b901207032041030750f03100712030140c41d2443d9810030745020900034403174a01c0c26400f0424100d00c20140d003e0f42c803240e896002c0d443d510a1108440e402c0c84104150103141070809910000c0e001030507140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 893641429 1250 893640179 893640227
    0x3051207090e090c03120a09180203071803050a06021602093405120601050403021201020702041104080303060111010605030d020c1302270d0c0e1614070303020d090b19060b030412 79
    0x5a41d1100303000354030f0358050f2b000010004d850394880c082e983c2c90030007030706012155401d6032a04c0b5036401e031207403004044aa0014410410200079011610340c4c42c1d008000c014149071100a0420707801c5600c0c084e009440c2c1440c52204100064190800c2d4000b10340d46407403c1100004640401c440d01924490503c142040003101503225032440010852650001582d0b40c44c40703105200441d88002c000c1241100c0034407060001e1751010007103c3c0c110030240fa010071180f2805000600501c1c40b0f6016030307818410b0300381c0b20000680111302251801c00440310140c0611270411494203a04c2070080a01c039509c086504490055110360078507000d440090300d11001502d00e80d0310b40008000d29006504240360390003c00544000700801e1002e01109454242c2040084884605113030080c2c06004007815004580403200c0d013159407003045070316008043c0030510306040c041904001c00c0251041802402c000000c100418120112405a90300c55101c100c01c2c0801c200c2140ca82e40a0314042c1c1c0003000c181 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 893642679 1250 893641429 893641439
    0x90c060a08130b1f0603110f0304021302040906051f09180e07060509040e0a020f060c24041208191d0f0717121603051207090e090c03120a09 62
    0x104514820303c0c1e414071540c3d034403210956440444d01143d003d40101810031943e0740b0030341400d40c1a01c00319041da2041907100d8031184001481a200c0040f401c0c9a9840440d0020b202038281c0c104000b204c03400c0c0c0f54a5003026050240c0041c86424002c8140071464142d0108000140c00420014007403c0308070010fa0501600c43c481d043c10425844040020800719400000f80742901c80c05048d0f0000c03000030000c0d1513441d404140001445101c1c0e0340326200c0070928802c544030034402d44a00e0704070041030078004000140c140740a0765003502c0640c0d640d00601e18018009004120503800b0b412032040000c081c81460740c000014080c440160003000e0340c0c045181c54003280401c5040c0c4080540409892440d080141d03040070550380304103441555001c201c00706c101d020403c0856000f41c10080780c3e2216409281000daa40d4032503512004000421002044606ca034050750120950b200030030f02010546803000350390303a100c0c2c103460350710380c150040040140f00c3c10100b8014640d44030f0754181802440d44c0c070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 893643929 1250 893642679 893642693
    0x16110d050703021002161e050d0e04020d1103010f0f030b0a0f1d060609090c010801051e0307090f0501090c020d1d030a05030409050610050f13120f0b090c060a0813 72
    0x30f09680701500742e0398000030041081e615008103687c0c98054800c0345c0180a92030b03503030343c40718202d0f0440280041c6a401003426295501143c140300107448040c492405031241203201d50780244600c0614405400000c509421030002c401c04a94001d0320a000544800c40100d00030400302492210081e66280001c08a01c1428500031a548403e0043d20b1a450010f06102441900034280c0909401507201c5000c941c1c0c20207800c40c1520800d42d1001180390805003c0d40c0a8280741d082590716200b4154005800c040f942c121089a1104e4034092040d66a11402281620075a0b600a0b0160300030410b0019858441c01c548102c18803068401c4004c90040c0022a0a24105203410368540c0c0001030140551030081c05190f4202d80c1c20758560705200e000680042542c09019420f0401c02c0e00003400c551400c50404114010b4445802903035000c40d410700d8103115412601c1d008407085044600025903081003c100c680281c4005044203190803140d4008072600030b0010200290003400f02c20b020b0100c1c560b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 893645179 1250 893643929 893643937
    0x503130210080f06030d0f1206031a0a0f15030f0c0b0c1614030d1206150c020f0414011511030d0c02150702030f03070c1a16110d050703021002 63
    0x542c039042c00d41d0034200350b00352003088000c08440c0a03501031344052020303a80c000880e002075000d61810100241741501040c000c0c2c0455400a4803403603403030442d003114080b0741030380301c3c05010600d404101901024240b00c00390b4544099610380d05980c040300b0408103d0340c440f103403542841881c01d0400b03c0e448151100080c0c03c190b50f410010360043c107450940010300c403440c2010304040007201e500c0b40d41c004c0010ba610410108680100000020510102c0140303800210162a401c2c201105420301c00000a00f40030030000c0992240400064429150a03e0300c50065103010341c800c004138582c204650180314079100b00c50308003001440305030854651018000381c11501703960f00e000700c1d8118098000900c0c0804003290f4061b20381200c010f002d800c0d60000300300d403164a2083e428030784980c0c4000041e9640d003c11007000d840c0f00d48050000207551503040c0d10300c0c883d030702a0780341c002c00c1c5001480c101e41020702c00f112040b25903c91341428042d58010700152842a220b48100c07a008003546116800f40e0b04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 893646429 1250 893645179 893645209
    0x351905011805031e09030705060901050d0c080f011409010b0c07030b15090709060e0f0a03020306040507150c0c030b060f0a030b101d1b130b03010512010b090705031302 74
    0x400b00384c5405401602c0d06010380d0b5401c13190624140449000001d40b100342d28400c2d03600c01c2c1000690104513074066801d64400301001403040000780703107059024211701011100c84019070350200c00811010710546204101010240081da4075a080061110165200402c800c003980300d00e103000000202001459031240c4a10407008003c148000309011040030058803ca01b40f101c070402c1800b01c6940304000e940021400c03222402211112801302d000d11401d608040c3d010300845041105101c0001140c0742100d4021480200c441d48600c003c80f0002c1100000030902c411400041001c50050b4201300d401c05002800c02c2c1010004800145111403681e0003103d403c41c8000400c0f640850b03064ae0480100010790740c405007118003c904611007a001000e4000c14101d60b106a0103103240b08080c5d502d403620318803012111340d4540e840d41c0030fa9002481454400d60f034880c05160303030503418010354a4500010f03040c031400c4d1b1543d40069a00c2d801c0105011840030000364400c01580c0c4411205100c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 893647679 1250 893646429 893646433
    0x11d06030f160906140603040809150708090f0910120507120c0e0606090a0e07021f0e010b03070e0117030c01060609090b04050c0d11090901351905011805 68
    0x5203003220381e0054131200d510100071480e088201080907120742c400c036540190311480d000d542e520300b10001001d540c4c518504204584012560908004d109002842540c108940071005840d80d0001c00105403822034503420003264803c01000340764000f03460010450301c1031055698460b110700c4055441680f07040140d0368007115640401800510a00b1190450320544506203042100404560310710034901c0b5142207154901c2c00140001d20a00c0100c11208200003880003071452038041c40c020308030380c18901d201d070b5282c06094107052800285400494001c054a0912686843c60961001d9041c1e02a5903150008011200311248284030b0360300503000940340d81005509228942c821070b500310105500481c40c12061150308100c3c03a00ba0766080f031250300c011a007420781c1c06c01000300e40a030421283d0440c0c00407001080304072000c3c01c403802e070042030041380a20200b14120814544210300004c00307141c000c580b84954074103515039001c048034000e20020543c00b6008400f02c0e105401040260303016 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 893648929 1250 893647679 893647723
    0x30b0708270606011103070204110c0f2103100b120103030f08072a0c081e06040b0601030b0a15030f0f020f1218030f0403031403011d06030f 62
    0x40222100000c1091030031070140790600d8014808035550381024203414141300428107440c000110410494420b0f590180003840799400d00c815a41598003c80000d0701d05004030b490381f45a40c000011080d1100000b00c0200558008104806c9456403000d8280c0c0c10503c0b02c81000711f10300078040c00030204a048401d05412035031440c28028545c0303501e602c5070002c00414100380880700b40c1c00540b5412084044000000300540003640240380e48114800811000d009840000c0600307010030201c4c900d41c2c2190b90b5207481121000700c00d8884004035001000030340081c002c524954400c1e8808010b4400c05000540e1954841c103a0b140010003200d0781c40c00194032584041140c5415014044200d0f41c6440301394200b0301c07a000c031401140034069140c40341004010000c4c0d05040d0001e101501c0718035400980b90b03100c20398000d003c40da9009000030780105100000100c800080f06007201d048504003643c581410510204c0d00c1043c900241031140c5c5842003041034651320106010b041c1041c59000046062 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 893650179 1250 893648929 893648941
    0xa030b040b100b0a2d050c070909030804060b0303120903221d19090c031a16110c06030108250b040b03190606080402120a031d0406030b0708 62
    0x41c1c0e40014980400215140307070800200303d098090f5501d01c040341c02d02203001c201c0307440948034a02c0010480b2403004a46403000040300c0d00440200386402550342176964861f165000d0009440240b40000c001a40c0040001e0201d05180d020b41444c100081c2583d02d40611000042051a0203031200c0515800000d6035413849501c07022a82e1402d8410812010410b1030070720f01054800d20800c1c202540e181d080001444075549003006400e04042c0750041200400500740500700070900d010440d0045114001d80c0344160b0080314040c46181d03280080c5400701c880c0c05048404007048422a21680706c0c1c0195500f586d0703100c80145010b091054001c007509907403036118824903541047c100400c002920700034000c0302810000c83d0151800702400ca5626183c950804400402c40c005010f80340d41380240200366543c0c80070580d40606d0088603045500e1806c0040203840b0a50100d000700420108072000d10ba5a568154440b10b80c000100300140403903580d03c500d070080900325002d40001d4141350070008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 893651429 1250 893650179 893650193
    0x13f06060509060906031e07030807060c020d05071511091305070311180d02120d0504050a0605090a151403040c0915210606180e0717030d18020a030b04 67
    0x50310010132210f0505a0920a004c25142c074039004104240c126001c58a820b2068100101e070700942e4414891581d40605041c60703401003d0701c3d4004030041c00303a681c00c042518230802c296565a5045000920303e4200608254018040090390005090060003440b1884d03440801444400c0c0c4040d2000c0380c070b441c0c074040050071500c0c0b54121074000c2100303102107180141c98403800301101c10151003203500421750f0700008a880c44030920144061045a1540d059554090054030072038105440d0410041d407101c5050300d0602036031b4001c42c1c01c900c42040800c00340b1038074103c2d010703000a01d003800301440340100c2e11034245078804c480985005240720410029007907a8490380040ea4140441411054181000c01d45071007580c0c0e1103450b400c1c1e490040710050110741c4d03100c00f00920000e16011000800d00303452001074400b24480d04807500a06400282080580211240160030725018618110000d441e2800612130803c210428410240c20341c00142c0340d034028040950b0150090030b1480c078041c50801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 893652679 1250 893651429 893651431
    0xa020a120201060f0b13030f141603020603310305040e0612100c120203090d113f0a080f1b07020103093017013f06060509 54
    0x60440e89402c50403c0883c1348030004e10305544c56100000d6035010a01c82880c0c02d200c1d20382000d44145603000d010f5040240d0440e000d03445800d92400c0d14814400c4030040203e8a540b4030001c2d40145041000480c0e000d4468464034800e41410700da00700c105800d0f001f00c11182d40b00380381100402c3c030004090049100040e0701d968010021030b40c8140c42070780c1941041e10f1792a030518680306246c0701c500301c43d141070140400000c1b400065404544914040d240d5554074140d901d4a100410504641c0001e5200080354401e200100c590080100004107541e45d080050101400030302603030002d50802c0d00d07144540061078940d40a03903d0717640b0b80c2490511048010741c042c2520700c032121481101030131140840240c42d55541c09003000260110182000b40c0000708030560083c203039440c029030ba20144500322080714101050f0b940e504c00f001c03108080e0144e491080c0103800860751100761b0300090307428180c0350155482003401c0710064551401030021012240b180d00315440b035181e4800740f08a0408884903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 893653929 1250 893652679 893652713
    0x3230c0c040504080f030c0702040504060605041803020601050d0831080f070510030207050d0206150103061410120507051c0b090609090109080706021911030913110a020a 75
    0x402150400c4e584000140c42400d072001c02c2400080001800208440c00b641e445030b40240081c0950314051030224010246401407038812413a007140030055841c3c400f03031161350940c142c0084c0f10710307424001004038516120340200d41c0da02c4100b0043d6481c00550313151030000074036104c50300c01d00000c0352002c0d0520f01c80381c0c1000745ca6600101003a2001d2070001183d0b0304480e4140c0380d81300380003d00102180603104c0c10b04042c04a00c24040307001903d40c1d001070494841c452070116104421a020011130644206125074030500b94400840e070384a107400d01c180d40c4640c61a007066052600500c03404000d0b220100c6100c00801c1e00030076404485d01509403261520903004074100700380749118001445102014107ca401491020000342d0004001d50000310a41c0d0044255a05c4030304c14641750000c2e6121050030071a4810110b8058030041c020031f64080c2c0d0181c000c01030341c04c00d805002805800690300b05d800402c01d80b250b002c03007003102d410002440c0701441036020308445001c41c240401e44590040030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 893655179 1250 893653929 893653931
    0x150f05150d02250c050306061c150b0a060e1305040b07032f0304060f05010b0a05070203030d0e0c01140c0c0409060207020301110c07050f010c080703230c0c04 70
    0x30680410600030125000031505100068071064250090550550180c07961020003005038a0007051141c01580581215011400c40700075030b45c1c500502441500c0c60b01d0913140d0032041d219401c0014040031082e89854600341000490f8410000050000c1c0000e50103030700420b5005411000700c1c00d00d40014100c0041da090b050001d4201039944980c03900c0300503e40700405a0307645110400c4d08403a0801c1540c0c1c41c1401c0c140d0004020541d0011b8981d10940e030481c4e0f842d01c1c00c62003110444180c000e25040315060080d840c00c1c86500351040e5103503400410120303070500042100040700d165501c207610a503d10400204030b966001c0001400d2080703504140310483c0000c1c016909030f5480022251002e000c2a50045205a683e00d0311101034011203100a501d5424515110038105c0c0000140c295190104100c1d80110359420500001c20600402180003c41d030b8806000071504040003854081d20900e42802c030030142d0500300b000210070001440404500290004420004014209c0c1180c2e007120 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 893656429 1250 893655179 893655199
    0x90812190b01170910050c0a020106080a02011704030e0405010905090f060f01122303071208010605030c03040515010b1b010e1e0f070f180209092404150f05 69
    0x80040c205040d22040000b015200a0028101340c034180101d400c00c04c02c51005104904003c210341015800440814005600c1e1040004090200081525071035806031101e24680441c1c68030714180f181c005206409201803008441640d403942e01ca8280203254130000010907050072140c05040088201c8215499030040c814000b08003c1c0030480c0c4e0450b0a00000c201e00c02c00c203445d000007960031402110090482001e503100c01c00c03c000c00203000c0030b80301d074000d0246a10a8982518030440c280541e8000071401e000086e005900d02e00295001400340381211400403052108404402c000d070002900c50030089409200381c0201e9a070032442c952010000d102c485400800390355101060f003618100c1c0f0046040888041c4c1d02408a040c51042e50030980c3d20381502d6414801c00385c04240302c0d0010003400007550a401280520030740c0c0e000f8000a100900c25203400c4c50315004090009881100d103c045801c076000750340c43d481102c030704000c080b1061400516200c082400501194012400f0f006024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 893657679 1250 893656429 893656451
    0x30f07140a0e040c14040e0703051b06040605030a02130e04051b040b060d09110a06020616030b031f0f0204140a06020f0d0c06090f03020a05060a0e03091309081219 72
    0x4001c0c10941700a0103450010005034000240903001d0f0f86400400c6004042010050120101c2c0c0c042d510396110301c0003081a0602003c2c464580f0540c491140050000e1020942c00c5449800511542000483c020b2009843e6207002d210000d050301c2c12502a800f410f1f120b4407201d241d26420030451402c40e010030240c2a0703403010800314810752219000301c658521404c0e040085943c083d141c0ba00015195505103500c80901079900d26056803550201d120140e40d420381c6e14401d00805240c1c540c05005890038549801849001a107d502c14003441c0b43c40c0d1640c801600c04501c0a400100421004207421070240b80c240f00209031142c02400454100307200c803017582e04000031380d004040c15500d440d49050005007000c400910200b00d00419540c50141075009241c0e0004091b04902c1c0180141da0641e100c0102c0101124107041c40f44dd501e80090201181c545800700c202c0c543c9181e140e030081105240d9540f200b0955000c3d6498030b0400941405002c00007240e04041e48220300d1424080008902003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 893658929 1250 893657679 893657693
    0x50a082a030a0611040e04230c0a03032f0c0103060b040608180703020a03060c03051302091602030408012a030b010507081b010f0516020703021e030f07140a0e04 71
    0x2618050f0000381c0b1444a40a40604181110018810452110f00a003882d10305068403000110201c640c686402c540710504050220340c003241084010510203a117407035a94107031000d0325060a0b0005c07060b207000b072810340e84107550000301e2052100c4001d41100c1c05214009000c45182c1e4011a5040b6418082449229000039036a6040156100800403a4403510b868511705103890b00000c0d00020724407000000c2000540184003892001d450034071a0f5501c0c02c2c2d020008021840004e0350002032000485c505840c100e03c0d002d10074001d807040e00d18003a1a0745c0d41c582074581480120906681141046618500c501048095401c9600d81486000c80002c0002e1184c0030b4010040c189200025540c0c90b01d04c3d801039030b81e00b901e540380004e103e010025010400100707400c4801c6840c100c0004500300d88140301144000981c1c1e802009000c20168017100b07042142d48010403150903202c1c111641403040006c1001d01d00030036041e80b03010f132510b81ca0828042c3d40c441c540d2100070700590001c1440700003508 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 893660179 1250 893658929 893658943
    0xf09050f071a070b2701020f0307140a02070312030f050c1315020a060c0c0501051f0b0f030f0a2a180302011d1504091d06061f0207050a082a03 63
    0x40e0170307901c0f90391004800da0120044078000750201c5a42c40007809080084000c00a580304c0e001684030507085c030400b03142c0c901562290511000050f01300820600025042589a030b40142c1e091400040c5030821320440801c843c0f05451352801c0c0980418111501620080345c503024180d901e0240205150040002c0d44d1916007200040c025501e404410150310710654a100d070040c1c0050086c011402c100302001c4940c842485042140300b02404003142d4403e4440c122244d10100a900c203156550300c6041c070540801c0641908034032500c4540041c0c00107000001a0800b400500a03004040c03140ba1010b8140101c1015591500d0895401000903030303001044410f11613010390b20541c4060768100003499211125440b20a02c090200e00400c4001c1c08d40c0c46a4996064407002d07026440240d05583d594048c00c54070b0aa101030450440c59605451884203080c061480c0100c0b0145d54236040003c4c1e8030010703900b2203051640300d4414135640c1c0e92600103860301c20120140c492000301d9007802007a19540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 893661429 1250 893660179 893660191
    0x307030b041b180b091003031b1a0702070608040b060d052a0405130c030f0804150e190308180102030c240a11040302040f09050f071a070b 61
    0xa00e08002414860304040040c41100d00d03220104006886000e070b084034400040e041405140303420204041e40c20000e0445002d540d031a04240403807451580c0468203480704020f403291300c0c110343d9008800540f05041d21000c0c08080c08580204d03141c84400207180c0319444d03001e801080385642c20f0102058101d0051500100181d44801d0401c0842c100103103402840d198200c81d100c4000411980120003601c070488140d001c1b00c0074442a100c81140301c80701c0250355000b80803000c501e8420000540016542000c0ca4811100b80741041d9498070500d043e80c08007115000811514034040c04280703031191454640300c0c428901c0c60b8034a400d6031111325660081d00405140001940f41c0d08e13680340c0c000c00c142d481005024080315542445844140400a4100f401801c0e054400e00411503100e0f0340d015002e20701513000d046505251450b02000701902c403080c0d1100c036803980c2d1510040450414072100723901d60307000002880081d140a00090b0050403807051001d001c001440201c00041c407004d48150492 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 893662679 1250 893661429 893661443
    0x192603010e0f240103020702090907080d030501231512040605010504140a15030b1801140c1207030209190f060318020904020a050603101809030c020d080f0408150c040302030703 78
    0x280f08440143e00a101d80013001c1d41c00744c8214100040c40b90001002d9094880000079200040724001c1e0550640d2401c0c02190f8500b110a074071100011018160003000780d0b0010607007602c41401d19156507207a80aa0b10000c0403e040300c0810081c0301c014054517004120548003049240700300030240480d100040c2c0600b01264403110468007035150108210b010790341000b085100e5040142d074001158400309002c0c1902e5080103440400d0a440c00b04540c4940c115a21291030f290001c1144101058014410f50074140e083c03001c03016135195001030024400d0f0760181810901d081c2021074200b1800740d40090101403c100500707040310030400100342155419124801c40391201e2002841448081c5c0000b034001070040b04100106001601c41030072907021081020f402c401c0a0312a070256150341c800500410908a07955005090451040100a005465035400c02d0f40c0045801080e611907484503178039500c1190300300071510000040350342008409049614051465000c00c0d200c40c002d200c080c0c442 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 893663929 1250 893662679 893662741
    0x20d0e011209210309050106060309080301062d052d04030803060a08010c080a060b12012706120203010605040e06010b0a020a0804061d0a0305192603010e0f 69
    0x200008150901e618481483d500d9000c1c0641401001084050803d58040d030030103400042450103803194110b0990070411551440e070034480c040d85ca504448540e0000e042509020019848100e4040b14940740960ba407542d44020200c0313040701200c640c10401c0e4220b00300450301f007a0586650111001c49a203c043e03951a961850300149011500e5402194103500b481041e03491f60307600c0074045201e110f0084003000301b07036100d030340510041c001ca075800c1c00544800001481425201418103030080444046842c8581d00442c002c019540f13168481c0804195886180c1c4c2180740a000d4034010300f10585040011440202e100ba0b03852006100e03480704c00c2000901403c00302d20920005850030f40240380340b0f58403036640c0700c010803100c03019400d003900b00070f1400041c1107440d0114100d41103d4100b030041544803200d20782c01094503148002100c40401070042a1050342017081424101850181d880340c90b9031404503c040e41040c01018228004000401c020403403000764a500110803090700c8007414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 893665179 1250 893663929 893663933
    0xc07020a0b040611064f02120c0d0206070f150e100908040b09150705070510021603030f0207080106090605101b060b060f0c06071d030601180603170a020d0e011209 72
    0x1a5545a90b1281031080d58020410341c1e9030006c004016261080d2081d02c1010013201c02903488503889180c050340004848580320251900c5805044503500550b01454100b800ba41d030500e0307404081c80326405454903003104040b00c0a0602c07040200f01d2040c882400f8902c8d050b501d00540e407103030f40600703031b0b100d90080b0f6101e95945402c0440f850300600194142c0c3da608940c205540d03150f05910606104440090a10400742d1001c546081c042c4051402c501032281596001e68400644500840c110310a0b040300043d410024040c60b802019001c90000302d01e0704260034409007040c840d1032002070003515124000c4003569481c007404103640000000030902c40c0000091028400c02400300c58540d40030070100312030f90001ca4007601512164941d1000b03454002c0d03050000142e80e50107550f040c3c01c200c004202502194000a401c01c1c040b02c0005405d58481c0d07a503440103100c0051020b000080441d90300d9030560108000c941c45152030600e09404541000002c10050f0412184c1c0702d040d03152048681 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 893666429 1250 893665179 893665261
    0x8071403161701030c050a060c03120c1101181406270102070f03020c010e040e1515030a0f0c06030203010e070e040b030d0c02091b030f0c07020a0b04061106 69
    0x2900c00348203460094107503902d0178a5007203000140501d81c4070f0000c0a40002d010350040b00b1200340365605480e00340d0089180c554000c002e0880c02035080030b2090825000c510301d0700038032401e451481100e1001c200702c01d40381404140b4000c0480c0782071559002e035051006c4a00c07101e1101c081045070700c5403045841c400e51601d502a000c0e05a005210341010a138500425401241005400e10281e1740c085101142d41c0400046c0c90142030f10321074941050502000007101c510300180c1c401d8104810185000740480030078a0003228080a540030302c080132200c1d0402100c0c07500388004220714502507040d03504105240b00e601038080d1000d0305016251070141d41c541c50740d03000042c3c00d40c030081c2603404144040d03601500030384c5801c40c200d1254000000003980169800d10002d88445202085411682e501104013103a01003e0310f4480c10090601c46a401070fa51400110301900e40320900c0c1d9101ea240041c080d1400d0000c100d820007a41100701040b20f01025407885d111000001c1c8500b504000c44040007003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 893667679 1250 893666429 893666447
    0x902181306152a080d020d0605120303011a120609190f050109180b04080307110a15271502120c07020f310e0316030807140316 56
    0xc2e1a0790348082e00e00707800d0303004036414858891030440c00302c11415640c00c0380386802908100500d0f4440901008903c145c0c9035000d00700c1240c014100103509030b1140005428101c103034001c05080d41c0300000601187d0f482d45040020a070309020618107101d0111070000d010b400c02818140900001300000e07800722407e0307409021100241c0000c0141c0102c04101a0240402b4011481400c1c02c000300240c2d80003a07800314940003900300355640e013035032034550f101c01a0342c3c0090b10610800c424036100c2d14000c8001c0c828060000d10034248550501f00259031107050740c0c0e04000440e540c0c140002101005c1c803805e10705510441d0301014034003000f0441042000207004031003241c00c1111032030007040001403400009143c000c2c0200d030402c03010050340040050f07034903108014100042128070852224401919103010710281b4101c0403e6600106c02141d26580100c1e14a8044403c1c3c0b03541c0e4401e0580090b40384ed000030485c60000c0f42d18052003402000d0744000f07060320740c3d1a000c1d09581612244078069039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 893668929 1250 893667679 893667689
    0xb010e09040f020108181f1b0306091413110316061d03061605070503040527090318010e030712080406140306090a020c010f240902181306 61
    0x40320040c01c0505248005800145040303010a6031040801c490751042d450b5401c90b0398016009081081da280140302085080716400c8034000d44076001c0c1480814084070001c0408055940000c4079440c4c444000b06403801da642d0701c50b4001c100401d0018001c40103071010881c0f500807051a080030040c80219181c040d81c11040c41d002010340700b01084507507206030030b42241640300b5549003401c6048010540c40c0c0c0c90a9500e080d4034401c00060b00b50301070156000d0403c8070b00407000d40303003002c0d034a030003090640481c104404a42c1032024080c00030780a032071008503040503150004504002c040211282111800c0a005040c06280b01c56403a240d0386c00c12114019020190f4100754204d400d290080b0706401600544c4003054171460700c1c0d0004c503401c80a687c443c08008041a01c16215444104000d60010004088030354895014041c507000d180203070101508201000c1e9013165603818041d140d20742c2d90704540007090040201700814001000103a680c1300c0d0840300400c110020707200e414002d100aa01c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 893670179 1250 893668929 893668939
    0x518090a0c080a031227050f0304090b1f020712020a030507091d030a200a050f0607030f090507050105160b0114040c0e0d081b030c0705040b010c11040b010e 69
    0x40030038082d5000c41d6030600c01c0c0c400e45030791034600c03500b82182c03041d03174500a194200d51500d4049048803a40c5540918001c5001f1000d80d1038820300100164159807140c2c0203c1c1b045501c40030900400d0800030304500300122424504188415a400d00a480d42c0a030700c00c1c6002d40f0f11603547c0200359a984100d00c070040d41d00204840005959003030a0000c3d1003890640c9040201c0059446d058070004070490303401d4081c0d6905e59550040807220490001000d240265043c4a0230343c007030303000031000c0242d03400e00d031042c40040c801450001d0000b003e4580e404441152036041c00d442c0e500144000034004140c6500342040c6807510a130042c07440c00e0f554409405020300861341c0c00020004a0520680b44034502902d042c0810740d5a41803d032a100c0c020507032030b5004081c41000f107005ca84440c1c05000b108900c6000800c038010009000b900e180c002064082450300300039002c203d2443c19208200f200402800c0c0381c1481031254848031260150350305018040c907190000d03541140c2c4038500c480c00c42100201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 893671429 1250 893670179 893670203
    0xf150605060d0b1504080604020108071106040c050f030f06010e070e030a1506050a05030613050705120c041d2802040c081b09060d0f0905060c0c07050a0518090a 71
    0x220b40c002c0c1c00e03903051290041c0c014000d80702003000c400048405440c0e0690041c00c150304c43c0c0e4011030f9600701c000d001e42c0800614110036900c1c507400344951b40c0130790300454058000b28144010090783c0b0450104041c401c1e07001000381307454000081240e40c116000418003400d0f668801c1000d940c25414140042c0d450300828540604000d80380c41354040050944030100300280e25281409040c0249015040c6d1650212000a51180d00c0c140f070149034074824410b0f180c61036650742c04212650340082c001e04040c0c20161741d41e422418103110f6880320741c410340100c10310081c01180094464a2240ea41c0f01e4298024464080c010701019120040e40d034042c01c2003114100c40c3d02c000300301e032a041d91100308907114949a0a1220071160544000c07603401012280342c05100d003030080c020b000300f101c4501400c0d00c810600c40825000d000d080d20407070014150680e1950342040d46410301165030400792052510b82c2c0700f0300c50b1791070b05100d00c04120760020600c81c050f203d03021201d1403d801c030030000300300c603500f80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 893672679 1250 893671429 893671447
    0x602010c1d0f03030703110c030a1a100305070f060e091308072405010603140702060a200307080603101a041e09050313120803060f122a0108040f15060506 68
    0x3541d40e2801f41d805007661803c9071450101500c8810382c50000c8e0210780c2000d18403800301210400300c1d070450807072940309004607030381d40c8c0b0b580c14040242d0110807044a078000402030107401c00d03d142c51103d022a00d16603545003188d40a150140329044c042c0001001041400070042811b403070f00041c440d40c8a001c070381d104015002d01d0280c1000d002c0c2400190034011400d28013110341013501d000300343d150080d007203543e104c04025000704040c1f0482d451419404070308541e061100300045002c0e005961b203400b030500c2d1003400c0c54507000241c0c4005024a00c1c1600034981654000010701440e5400c8402160b10780720020b101e48a5621092000328240c5000400c0742000310001c028a0380ca50f45202c0088495500c05c1c03200c0041e200c0303070030241c1100030030000103c41340740c0300213407441704140144000010005000f000e803801c0d000c0079040701c4010119036042104101941c500018010900e400e480529003030303507000340c5072000400080030850106242e100071840b0f0340014002c8c010241c40151204848 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 893673929 1250 893672679 893672687
    0x80f07050a0309090203190f06050919060e010608060d03121406040c0311030a0906110a17150f040c02010b03030d0603060f11120403091703130602010c1d0f03030703 73
    0x144500b28040f038800040002c440b1918004c0c3e0384070340214410504207402c0b19284d00c020f02849000e08000310380e200c40c04609943c07025207890043d03411001d010120480004c08100700e070515040358102000c410700400655a220081d5a0300850541d2102d02948441c9001d4a121512640c0201d8040c2440c0b980d100041e00d82c0c070a18030855040382e003405040b0114500b507049031100362880d4803070541000080e020010036040044594803400c0c0c0081c4444850401040c5a000550020000761f040d0b0b21a284407640e541106070050000c80e5070589003150000010803ca070001e0605001300d403200c0192040500039440088041c0c4054141e0765114016044603004090f03500003110084d161650b45855150544110044e400c3c050440c245820610000c0100c2c545d0003c008500700821181d02054880b01d4542d002e5500032010001e5441d0300c4100c1c0c201c15520800d030401000c580c541649100b003540e0108902100c1d08003220b142000d24009004182044141500c480e050300c400160f1600300341d40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 893675179 1250 893673929 893673943
    0x151203050d060b0306011206050d030e0d14030715060605090f03280507080a020d020112060f0914070309030503130512030f01060818030414030c031b0312030f0112080f0705 76
    0x1d0b47e803204400c0303c80c924501160154010990058038000e02d00c00002d0050090860818000b00039000c15a0140d032400d00305c0100f05007849e00d83d0400304040f020480da807000c0c40144d040d00b410610610381802d00040250156071020ba00c01c1800c1c00002450340c506002210100358540180e01d07190100072020100b050401c2c1040b146c2c0d100740e00000403076a10103e4595912a4010074912016001da0011194141c1e1320b0f5004441d595105000104551f24022a00082c400c204000c50301c07e011075002846a0030060042062608203501a40020f500c202200c3d842040b0007480440401c45040107032819035904800c00500308000244982c940505010314101d2305036540e05609070b503840c012140c58807840d041c0b00d445035000b40000e22064101c071064062600015003280c21021000340004d00e42405481102c0362042410703032001843c00c05222981c2541642141c0525604040525845110051250217400035501c5400302c00c02c02030904440716135600640140d10b035520307030801036180e40c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 893676429 1250 893675179 893675191
    0x41d0703061d06100608060307211202030c0a2d08031006140702040207020f0910060806010e01140304081204050c01030f05043309060b040e01151203050d060b03 71
    0x800c002c11088200c000810a20640d0a1000c2802a41c03500f4025124030300d02906556042c0181280490031407a800d1040c2c60703940c10100070030b401cac0f515410407113480d040d071a80368021504200400b0700000c3c00010182c41c0c2c0f0350f1001c2c0c074410180c06030316080380c00441c078a0302e03440c0848540e500e1000d015400018600a0707000c1e220a6442640d0b030383c401e440ba0800031080040506040c0900000362074103602504d020341c0064181d00e5002c40c0b80c030004184100441d10068000d0501e9800e008299000303440c1d035484102800d01d00d20000c13202c000a0107100c1894001c6d490b0301000000a000c00c540e18044d00d170008413803803c450403401e051034030545030201c1400c05030000e0f240100ca029410307454060980126081031018140d0002d0400c0890680cdc07030121442c540d40c403802c6a10b0090741b0540f061803407160203031000084005a020030402592100e8000b8440c42c0e050028468414680002d51003c4a00780044000203224501d030a0b141c034000d00815600e610707d0440c0000310411030000440c481c2c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 893677679 1250 893676429 893676461
    0x4060f08270c15041d04060209180a0b010212090603090c060705030a0f0503060d060203040f14030909011a0a111609050f1e13080d050414120711041d070306 69
    0x602071074480018069441103454074000b141d140e0791081d542074507175500325000c1c1501500d405030a00c00300380d41504500454200c02201c104000c4020300a12480200381030910103440350128603403051a041c0200b40506106d90800404121094010405c0078029040640490748440f00d0b07042154a98008005010200f150a45e44102c102c0c03050048a12600d4014150322404510340c486000940000b0811521280d20b0445400400c50107401d404006003910000d41d5900090001c3c828a45c1e0183d019a8000324002c142c1f801818240742078840145a030300d081610300070320303001040c6040005a0111a400480500810b000c0781d41d81245201780b0200030f58000646403072865030040d00841c00520001d4400c440441c003085118055004164060f105880c03c008501400900b202c1041d0380842c0c0c0820001c244040c0070b0014015040e0030807205440da03090200030b4840149003070140050a11482e9a038140c2c2e03011700380005c81d100d04a5030400441d19850745916141c0d00a11a4a070004049 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 893678929 1250 893677679 893677699
    0xc17070806010b0a0507031701030c090e0102030f04062406120c0f0c02090c0f030f0f090a1e080c0a031218080409150302030d210204060f08270c 64
    0x340c0030001d40700c2d040b40d8011801074505465450100c945802c0008120204010070941c0c6001c00480008140614041c044c0700c400d0502d06103000049429440b1000240c3e4014010010100b41a048841c0c0c4550820004502843d030302024034614116140401d45900b000c22000c2000d55004400402c440f6010b1300c104009220381d4020340c1e8400c1a40e55007400525428110340050420b01840c135000401c0102250400d4103035010044142c000300d40060080403c0030401c00f01500c111302003500200307504003a005201c0c05131910b50300c0852403094200941420b400b80400c0109071000c0b90040d00000c025510014861300c0d0080102400030b002039420382c02d00c1030020004104001d411032160303019004d94075203032034040c2c1c0c01c02610b8210b00c0303804095400030001000d40ca0a00a1241009580d51a42c0e0b1903071401007003d2880c84d070070102c0c0d0201407040c8000c1c8040c6800c601c00c0c0185030b040d402c00c01c041d0b80e11010000b404002c10b9810b502461000f0400061176100000e008607600001c444070f1070302e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 893680179 1250 893678929 893678939
    0x1208010f030b07140915070606060305100e0622090b010e07091701060f06051c020403021309062c060f04120f1106150405090a03120b0307030c1707 65
    0x80346155000141100c0c4142012400d0240500c0f5400e145526400b4590704150716400003549045529000a06980c40003a852080145c07a12400000d408036050401c16410848858681c998250141d1000d0124010110f0010f56845c80002c0868106800441c950340a0000d00c001501401600f107070a1402d040006c2202080018030a21030b013620f50300c0d04c066034600013921079125a0101079038a01c1d540c032200490b4a805855500c4040c082d60744615a46801c403101c00d45000c0c140c080c412000340d1060200303000590f1014159400d0418002012920705010700702a8000c010b03442d070203289004008461403c51490644240503201034506440c240d958028070f10400c4c600850b0000c0051040100031440d0a000303280704042c40b0120310f000740d0481040100c481c90000280d54190113101c4590b400c040914190040c1d40d4440c08881c080c150045e810707540907154038041030004c140704d0380781c0c640c0310b50b29103003007140c0401107410104051520390381c4d80c11203148515540c080c0c0c00d0741c0200017001c95 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 893681429 1250 893680179 893680199
    0xc06070c0609060c0e1e060f2b0507090e01030f0b06010e0a1e140303031602070b030903030f0a0219050f0708030a051b0a0c030509060c030d1a01090b07151404120801 73
    0x80c0c120064281c41c60001c6415034203c8551145409c80d080c001032845401881041c0c0d008420308903945038000907282007802d07001c1c0c181400c6901000558180b9801400001c600350081d5580c617034054840c2d806030304c0e2100140c40d804607aa00b200e42022800500040042c1c1c501e55410350190a0301c4049940381d02c484000c841c02880e039a4503501a401000071410083d03542e20750340444035292069440356601c94802003e29401030b02d0550b005c1d8030100500840310343c2603421a80080440804501e013a80c003c0f0b0020020800031001028848003260055551021100315102c09a102a045030341b03180c4084903500070101901e0141d050b60030f10080704620505081140e4a104450311b80c3c2c20103200d159012902540440c9506420107014050754204103c1000507088011070600042040201002c40b059070003441c100c0f0f1030400c81c1030345040000a00c103000300c80805e500b05840395001d031060801c0308081c20f510a01c07071000440010070002032103840c4510800b03862956446c00140e0340d803602c0445d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 893682679 1250 893681429 893681479
    0x6030109080f070f080703030203060103060f12060e1f0e06280e0a020a0e070e0102011e020906040e010b030f090c060306040b030c090106090302150c06070c0609060c0e 74
    0x1420380d0000c0000036002812031014160f164890240100e03050003580c0c500045410501080380803a80200c02d0102c1582c25006585c0941104010b4400b41468a0012440042190806009a642c42c9081030fa420401d2200180e500b000e0150001d441d42400094401003c06522090907400340c1c1c00410054a03a80c54080c041c0131500c1803c102e283c03050701d40b010040c6018891500035100c1d140703409006895909014008007802c04408080c1d140944c1d000d410801d0002c0c016046903d0000910f89068140c001d0402200c4d8003000140c071124030130302090161059803c08514403100d0740001078180f4028000b103100d88442403038003c00791501e2080a07038500110f0392030361b8000000e00c00035802d800d01d94441805d12100804880310b61888001050a0903000c1c2c00100016a00a0f4180306508014a004c1e620b420020065480c0241160000b9150080a004101000301c2d11809070b09203d2240c0040c0122500a003080040e01c1041c4401391400b800261400d000d107105020140c0400c8002c0504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 893683929 1250 893682679 893682683
    0x4060501050702010f03090b041103152509030807080418060803030109020703180612140603060106050a090f090c09090b1e240c0c100905040c0e041503030806030109 73
    0x246003030292543c0195410301c02410388608240d5108241c1000c10000748903140101e00070850484060141750a060506516000551a510020040c00203c10410a01882908a0500c85403010500010446650403168000b42000c2e401282c107406000201c4000c004a401283c1c166005c4a07685004074141e07112441100079a0b00305200410611819800400001d032107803402d908114011000f0740b089c2a101d0b0002ea00144e54407420007003a603018814184210002800e07c4841e2800e9000255a804140204010080c002c915100a0b90160615502800d100340720440000e450b80d6081004010304282c9000145031300d200001e2540c8288500400b0080c0a4a41e00ea1045802c2c002070868407400c800c0b6822029101c00c500a101c025840c900c00d02000d004150750310801024228130b42150b1901c040c0c403501101404d13100460b00440e405040310400d035000b003004c40280c902941c079583d0010307840b6002402d20500282610700b80c01c4210503603109803240170305c58031080113060803201c400f100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 893685179 1250 893683929 893683937
    0x20d18050304030b15061801020d031404110f0a03050a110a0b2a150402040b090c0a030507050702040618150812072a1a090105030c0a0201090203030c0a05070504060501 74
    0x184085004e5480c02940031001c000706142401c8205d01281e02d0b91300000c5421400c140d00310528000390b0f41030103220000d540f0340c40c050005507a541700d05245000e000c2c0000b04241c50b2540300007447e0312035026001d030050006101604982c0e8905040340c40340ea0b2800211514401e00c02e140703a00e0b00d000c44425043d40c0100c0922414103201030b85011180301544080000c00c0c60901400c0042e4104000380c2d008508440c2d1180220300f040e00c140810313100302c0b081e00c074400d900d0007040000c12891041038601101451901081c01c4d11900c8040c0d501c2e11594401942150034841d0202e50304068100010901f51100c100300f040c8900710ba801000000c06024201440d00a041100140c0c51510060000c6d0b1303001c0c0c2071000c01710085441c090b8919024240c20b900c079030340d1840100003c1200b07000f9098800408003a171880e20f0a03900000308648001400003802c2c00012900b81c142a01c01d5115040c00c40c0d0150499a0761054006115920141d503e8222002d01c50107a011809041a0180904489061316 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 893686429 1250 893685179 893685187
    0x20a050405090307120c210c02090108031314060319090c09020a022b050a050c010e010e0d0302040e0c160c06050d1802131e091208070c020a170f10020d180503 70
    0xf074001e040550703000405041160b03034003230a00541e40310410729008100d04802140d6500303503a0504914803a655101d1400c0c112010b0001ea503580764070003140e600103443c0c0c0b000340522805003000c3c00180f00c82c400160000580002c041421121f40c3e00620b0100d03039540071124881301c0303035003400081c0e2240c01c0b07100b00d9a00b080124403a06806440038104031480760814504041d00903005c1c0c1c1c2191020035a42c250b0369101e1a01601105c024040d141e00c40400d4a403c0d03141a0621519450002c0086c00ca00038800d40018000204009140f103203140c140d1145519119a9580000a080fa000300b081c10405900d031560108110b0880c00150032110b81c0940a0540d840070210030340014001d060900e00c250760700030b4640d10410040c1c420500032600c14850252119038280303005241220040182007440480b4440301d001d69074042c600002c9844011704040c2d07a41c84202035500b001d00c02101800b441c42a02000714641007190090305407500404010070405888c8022800ca01c02034140213815070f00100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 893687679 1250 893686429 893686463
    0xc031404050c010e0301331703090d020a0504020c0d0806030c0d060b0103020712050a03060605040503030d0e0708101a0603070c081e030a090501050105010f02030a0804020a050405090307120c 84
    0x81e2003c071881c00040c00000c9000103110110203690031036442c2c0c024055224500e15404c4170540520f0054000d55822005400284040507900c0c890a0a500cbc40740c01d1440540d0115918005210080c0c14050425510b803e800701186660b500c000e550140810039010004885e03040018840140c050028400e00751502e035515040c004240410249040503001c00001000c00d880c41a12000c48a5980c1ca843ea100c414460040803030782960006410044108004c200340d60b0000709a5220020fa40e400003122840e84448514003c0c0a9010000314024009102132883c7c86501a104042e0303030800c0014200401d50810050780310841d00d020100b00c0104080006c500342c24080c0802503182e070a08550301180d82680b1886800c01c0b036074650000c1e1180c50003800c00030280241801002c003130a2900b02405551030103500e03400b44d54425020001034400040540d55105140e000500d4003400401031400c00c2860300d51241d01041d41038405881d00b0041c05421481600d0691141d83c01003140c0442c003041c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 893688929 1250 893687679 893687687
    0x1f0207020607060612060506041404110a030605070909060e010f032003070e091506060405101205010b0a1701061b030215070206010510020f0a2409060c031404050c01 73
    0x1088050340c101d5010b0000742c0000b0701510030000500b104400f0381d02da0004901e8080280d0718001e007810b0103503041c21085460341c0341503c1e005800c582d0000c0110300c1c502004010640c01c40256002500081c107080902403102c5c0c0001000066411444080c0711907607d400022081c00d4003842207615519444004102080d29500b95010715604503c02c4050880450002460961a134102003103c00d040c205100740b10704100f285035006412107400c00601d26050740005d03000c0c0590b204840c050030046031005050b500c141c2c520158511041d10410043d61075a803402e0b82a0010b201d40d01c0405c4070480320152020080302d4490480b51646d41c0c1c40162140107000790622140610120309600c9050401440c0200f01c002c03c1e40315155507802869550700d40000c1188902d00c103070b620b4040d9004005800c45501000c12206051504280c0036100480300c50240c0000c400706100f0300800500c0c282242c0c0810409030030804040c1510380c0c05002e098011002548908002c0e1002002a4040d81822501d035010f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 893690179 1250 893688929 893688937
    0x12090906210c0806042d0c05060906130e010501090b040f0b0913091406070507051c0c0b0103060504060b01080106020c010305091e01021b010207020a03140a06020c0115081f02 77
    0x8115902d03441583c0e2080306038944501910211820b28900e2024403054200700c50040c3d100545001e0749403084c143c1c0e103682c070745118540a400d006100007d020202900c404084039000342d88100f681042c0350743c40e8080345c050f010078045e26002031340c0710034001403080c0510b0981c1d0541d034030f804044110600c6c101c6000e1071684000c14098000700078100c140a424041d10039009800d0103181c05145111502444034200740c0000c0c50401400828401200466000241058003000300e1b42d41c00e40f1410422020741d00c00001c0003004140700d0048001008200300358101e540207612450b000d10082074a08015544c01c2d00c00d001c2c0500603408200c1c02c3c0100c0d842a001250040350340c4094500c4600f21032a0414180904807450005a40005003102040440c80b09000900c503804000c50a1407115400125800711030711028019280491202c00024800d0000c40481c0c0d070710500441d0f5414440c002d0314003030010303420008000f9a04540005204101003809032038414135403960071014900d000e4002c02500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 893691429 1250 893690179 893690183
    0x8190b15040f06230a08070504180203010612030305010807030210080403110f010c180e0103081308162d06030c050403080d0b1e0603070c06181209090621 68
    0x1449003000c0c00c03200b1907841036001500e00724880c00150908150013502c54611803440c180281c0c1d1588040080d08000325208064034812580410382800d00e02d01c00e00022070018020390305500e0a400020940300810700e044a03a4860b807000e002d5a0707a201d101c191141c5c92880042e4100c1d0003d180001401d00c520503840c0d0041c42030401034401340d02602090f2a0180300c03021a03405070764030224203222640000c440c0c00a2100c80250050150800d4a660040001031100804042c804109002031402270001280544400001c654060130b60007940100381c851440fa84c9c0c81e022521451442c1940b503003c40751024084805a000754600d0803008800501d10381c041e860800009000100015580d00c00400e01d5040d50400441c0000040082080b1281508980802c1d0590b124041040b6190750090b2948860182004a4440c5007410304001802c0755903074244015035800c08010401c40e9084030314080360680c0e641d00004503140c01e00941260420700400c080003085110300c0180c000212801c20340a8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 893692679 1250 893691429 893691431
    0x7050f0c0d052d220e071707033b0f15070207030309030209070e0d060e0c01050c2d0a030503011401030b0108071211070c08190b1504 59
    0x840031241504180800100d940000d0000a12030200307119401841c415001c0e062107040300002c1c41140d040b40740b04100160308100d1500103414440c54004001d60018614103244000a1070001801810003841d00644041e20310b140d000701d0009842031180b06144020540c1038071001d01800c146e040090700071600c2c2c480d00001e001e115001d014060042d007040180e4080100111042c0300c24503851800000c00d150300319444008200f0100783e009001c1c40c202d0390196021500c54403416000c076029400b1404040e08505440f1101c010800701d03902c015070032070b24003041d42c4a0b824058011681d0748505044c0c00b0055000001007005080b0031102e6100148800e00005044c0d0288108281002003200003900425408001049149880b021000c0e03e82001d03e0f0800c010b800e070600180004034081d010804005000ea40700788406480d62081300003441c088030701c2d034980c0514540400c00305014080c3d80c0c26801030190b09002d441c00d0702101c0b1002640410281019034803000d80801e03410003100c403c0c2c1d0203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 893693929 1250 893692679 893692687
    0x10c1b05030a0602090f03010c090618171c021f0e030d0507180b0406120e1e031c02030103050309091302041401060215010803180315070309150e030307050f 69
    0x55808100b080e01c0d15101e1280540c86045030020480c00b00c00c0400a94000d904004840c15402e902000341410385000d400c00d03d220250075001540c00042179004001c43d1092144282e81c01c4000050b007003000b00c0d114101001c501a5600120785654030464188860300d819030600d044022540c00c107150142802c1e040f24100500f1070b1016054540540d072500210f0052200140c0c8650080000b50150902d003251924103841c010008052030b16824400c07052a545048542c50b5110074072940d400400540d80b801026104542c023140c4a6112a40d200250b40740e0b801000a840081e00940341201d03000800740d0700b410498014002c102000810001c446881c1901c0322006940d80d2090340407160000c00860000d606104d0081e2030500c10034010050b01b403080c001088412000022214801a10300c005180490650042490149150441c900d569550300070088200c1e0b00d580919605401050582900c4c20151291001c690b602070368811613030801c0001910050084008061440911210a01e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 893695179 1250 893693929 893693939
    0x31419020702100903020a0602030a0503040803060d0215130807030c03080a0917011d0303060d0219030b0a0c0201052508040f06090609110a0608011502070e2d06010c1b 74
    0x10380d40584200b4085481351106005500740701d4050030281501d40011442c042c440e41c0050400c0c080103100a000c0c04000001038078507164000c0c45c0c10b8817035000d403840e4142d07601b4040d1503120b074000040302c040422082c503002980480005000044940043c0710280140c11030b100c444181e407241c00b9160610a103110b00140b0b60b181640420303000000500001070000c003490b00700202c01080b4886490303550091042c003070555245210344040a604440140ba24041d5041003260f01c0350703540c4060401e015036410461110303500d81007e803180c0c006a0003001280d0383c0e0ba03c06a034281107901c02d4480070f90080b440d2405603014080d0a40c1107800b0b8100c400c03e204403649c03114251100003a08959480d141d07408601048422024401c1041d0216400c40003142481c030003c10380380d8140314024480d800c400e2041e040500030301140c006083c030401c0c100c0e00c52805080010b00342c500000340300520314424030019422502c01d01e0450041c1c1050351408c1c029031664484030010006102d11702c007001c0b160180014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 893696429 1250 893695179 893695189
    0xf03080d020415030b0103050a060501121508011d0f070b190309120c120503010506181c0b010614120117011401060e040b06090303032205010c120c031419020702 71
    0xd4000556021034001c9217032000401740d49002d080c0207500c03418480188580c2e07800188440503030840c1040051100190710740021112003d610845040d440d140395054a5402c4003403001c03410500c041102c10707000c80d8128442d5102e646109950309881c05010340c426040c281d441034200d20019140101d1014016166040500c00b6841180041602d2956841c100000720041b51403201160030590b00310362400c00825002c1c4602902d040306069541d238003600c03a0ba10610014001041c18000c883c919826180500e84040e00b8040c0b1404a49040d4203920300d0403603a0120380c1001d00300c1210303900396442c00d80204181110711103411015526504094915441001c51500801a030354805552483e04011301007203a22004d941b501528007004102d4403a180002142d82004c1801c807070280f0044441e0304000c03807503100c80004009500745490030785035030b9011654003045589041c0400924402100c140e0450702008074030300146031140700043c003120800203604012408240301525054590f80011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 893697679 1250 893696429 893696459
    0x4051204090603050d0206090c01030b06070804030804051305100608090f1209040605030f0a0201051b0f0703111e0906032104030611031b21040506040510060f03080d0204 75
    0x26604582d200703400c0091080801c2a1101c801d9540090480381c1444c084103a00ca6503000100380c103164517070700142d0301a210002182c0342240c021412070b03201e07030301c0e46010045581305c0e2142511030321140c50801000249842894080d90f40c0410f440c410074900304081d101508014040320340d6015060b10b6402c252014070031240c80c400c0c40c13100c441c0e80e00a2907042104031203503500900d0007580510700768002d00900148458a003502400e101c1e440d000204070030324a030325030455040e01a020341606400400d60010300c207000c5c3c900c80c480040f0146071b1b0009111408003244682e8107820465810700040d404c1c41e1841036041130380138054030440074400e0008507001000c0094502d044400107801c209004241c07255036411200d1031503603459401c100c1650380314102c603004c06a600000014054240c4220210880382402c030350307001c0001c00d10f0117080582e00c828080b5420381d43d80c001d4480c120161a294481c210a540c1218000741d01a400c64440710400d80049040c600b42e141e0800010071501d86c000642 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 893698929 1250 893697679 893697689
    0x11e030f0506100b040b030a200c0304090f0905191704030b04020907080c04090e101b03200a08060616050a05011a1c02010233090607140304051204 65
    0x7002c15040001c0454032461190340312000440c000d200510500000104403030300503038620340100e035100d12081c40c4255202040000d000071a00064060100707240400900103d0300c2400c401c1182c141c00e00c0b500310548180e148010155085100c0c89103030b1186580304000785a001d11075010803083c003951044141e61040d00195061a0302c001040308501e071440144d544481a403808115a084c1702c410440180160302900045075151441c601b0131000401002c08400754540c4240001c00c01a03c1c00c0c0c100181510b00e0301d0001c0d080c6020601c051004100050b83e0400d800b0400f8903081d10b10f4411903035900068400d03640308500f044007913100800001c50284850091001e001c411031103240481c211103090110000c0c078006018009100d998011460495214180c0104001c18407480103c0c100500010747d44c1e45002c42010b89008400840300328199503068000110391074882c1c2903d02e55405040301d500700014095003482c81078124090141d60840c0c49082190135a8212004000c42600f00d5005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 893700179 1250 893698929 893698933
    0x9010207060b0d0305162a090f151412030a030b010215070c030c020315010803030a1a03060103060b12030703050a030f0b0f01230d0c170c03011e030f05 67
    0x1120a2001510400c2241e80c0100e90103143e0304403556010b84076010344800300c03980c0d021201e02c1d08140040a5002a9804250300d84850440d80c05105640c02c8462030142c42c03002442c2c007440400480e4288648881028148060700a05140003641c101c400003280f20b00e0b13040600c030800c1007848a81040980101c2083c0d40340415031025103400207103009000341c1e103940858a090140320306a0f4101f246000059014544603103180c0540c00440d1030214030b0309640800d510010000180301602001660003406001003d000070082d849201608202500300da66064000c0030040000a0f2281d10804061101604030380302d444000b0380c0c071030864100344025800f05500084e9081fa10740c2c944602140e0303107110700082142115031b001186003c07840c544403505114110480b400720f21001c002104410403002c009950702c0a086c42d43d60050b059450203c0c2c049200388503008c4403e0100d806043c8684ca68000d1181141c0c0703003805004118126681e409403041c001d91700400440d80828450400c1405040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 893701429 1250 893700179 893700187
    0x190c05090a03060207122607050c0d0309170c120703020a05060106090f0510020312090304150905030105010807060f05090d020402030403030515040612020103202703010938090102 79
    0x340340b0070b1101c6d000c01040802c0840d00c083d09005078513424207003c0d001c110b910300f07134076545000c4280d42c0c074461205074440c03c1c401c80c0d82494050b41d03d030304550721503403040c0340c4815400c0284400380c03018040c1c0c5c1f10f4408140c105c4e0420002500042c0044c0ca0303514080e104881248401d1b88405050070001c2e00312900183c001d40061001380302001d60310000703000c140c2c0d10964425055200a40741c0c003035640c2c0c80e580110f030a0042501c1c203c0400c190f90160500203203200307140d20b150078040d24078201482007500a500303041c00054009030102d003240c112015511440e10040e1040000c60f03840c3d000941582e800b114002c1000090785032840034610403440380e20300040c44e04000110403e0011030761100d44c821400d01c8014400d2071201c030002c10703031590b080c00e010802031581c0e59004003c000e02e56403100d0641001c00c000c2d000c81e5401e40c00035864589880001c034000038010a15090f1403003243c001d00f034a91055500705034402d00201074031171352000480c01880918080801610b9040660314800517079000301e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 893702679 1250 893701429 893701433
    0x1030302060a110708030c13092c1b010f0903170912010b01020d140405030a061b1b030c081b01060f0501020303040c031707050303101409190c05090a03060207 70
    0x88038a10f50701469854003800c2c408a5515203840303110045c01740240d50000700e09054140910180c01d800fa00900e6014004041d40360300001d0819145076408206105048841c2c0c074802010a8032800940e0030480f0749a503070031003001940d0f0041d83d400c0303d0041103800180040420042003c9070301c01000c08010326500ca078a9410011801c014180301261645032140340c0310281e80004c0c61000030b548900303081100c80204010032100d8000d51f80215054003881e9076a5040000e2584486c140d07106c0003804252107000c5100464003010039000000882c125003060002090040c0036101203140b150740c1240ca4140416144c40752103903559001651131f919060300388a81c40d06854040c0140030203100440c19407030039441c2d0f600c0d00e201a02c400750803054118400c521964025080b142131a8110040340e9880c10300071142e8933020002e105104090310a03d010b00a01c0c40d2000e21540503054840d003e1800601108406004001c03010a03c0148201080b0440320394840c01718400046005e03c07401a1105014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 893703929 1250 893702679 893702681
    0x403050c010f05120105040b0d020405090102030f100308160602160f05010e010c140c030708130e0105010f080430050c070501030c090b130e0103080d06090b030c0f0a0b0301030302060a 81
    0x58482c141404400c1c00346107a0803403241040781c1114000c46010541c480c000740451109021880b002c0e400ca8201010090f000c1e80c1500118014850703581031391b446598410105041c0040d030b001c001c107500c01c200110280c039102d0401d54540180218001072420154500403014440403a1040b07035840911491141403040a119180c500f41500000b0b201341c207019400280b84d014a402003041c481ca000c28071060f1514100709403094250b004450665940541031541c20a800074810f0842041d5030718000700d03003544140d04c06a8004403540700c040c030035200e60b40c4803581c402c0f1404400c1240f02d28002814a2409414a180280d040b55211269038001e2400003e080010300d800290605003080311036540075901c69561002c40f613541c104203448818284100301e07400c002d64081d06124400744000310074800010010721402d0001041007040300c1d51030b64100c0a81e40700c42c2025604d41c11410f01b802040c18884403103100254028100138600b41c0b540c0b800c103003c0d0000c0e0002e078011ba0200003088480301c11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 893705035 1106 893703929 893703947
    0x60305010509031909050d20060d0f29190801020d06151404090f060918021801030f03050901031e05070e0a0f05010c03050c01020403050c01 62
    0xc0408180e4a030002400740307130501800059803049178000c1440da0100c6402070210783c1c1b0031030162910008940e0f50404200210104030214106d59079000040600300c04440c0009035000e010740202003294103400308544407410482c181c0c0b0b500249a0002e13200d405046a4442e00e002004201103141016540044041d40c004150011400b2140e04410159180d9141d03500301d03103503040350440c3e41d406001c00c81d1000000400080c00020300e56000148104102c0f207000c91030030ba5408d2500116041c414000000d00a848080021464608074600c0c2400d428000704406504545401705401c103001001814071500140250041c0d000c0e810410f84180802a0040520401c9030514081c00c012100200050700c80c511811540c0303000b0320290180c0755462079001e10300c0e0400c0015a01c080250038140c091080030300000c0c4003040b02340000d00184d07206002400c0a000e280e0009052004 = true := by decide +kernel

theorem cover : BRFrame.Cov 893525179 893705035 := by
  have h0 := BRFrame.cov_init 893525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 893525179 ≤ n) (h2 : n < 893705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
