-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3097
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:39:08.225175+00:00
-- url     : https://prove2.me/submissions/e58a821f-0e79-4ded-81b5-9ffa9d82d772

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 556834532 ≤ n < 557014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 556835782 1250 556834532 556834547
    0x18140c040603080414150408010b12070f06080a090218100b030c07110a05190801050109020f0406050f040f0b1209010515011209151d010e0a110103020d050c040501 72
    0x24040340e0420150742180c403000300c1801280924240c1102040710702005d41d8610003080200109100d17280ea13102d80f03554015020b090108920b5000e4400800040d03403aa80c086642c00a480b041000c100e08070b8034001c0100c914007800782001841942d14841400540c60780181c0d074007240d109419280c101c1c10800d5078a9440000744d8000c10800d4003d1061010002c0400300300c80c3d840f900700452980b20172030100040c0c000c91142c1e11496100d10013464116802c1502c00d10441124a04c034001c0046aa851190400307a1090030280380034210100030031721440d800b9a01506000c181c804c480b609090b25011000d1940c100c58002400701c0b50301080441602010200d100e0f44206810000d000605001c018507090300d4400071440d0500201c0080648983c0c402e900980085420600200740200c603039004c031000305100d8040c00d103c0705540c141502d001c0414010244040500700081c5050011501c1740800342101600807070405800f000498802c81c900c1c05940d0060450300b9182e0b81d103919202c000740061 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 556837032 1250 556835782 556835803
    0x20309070503060106090e0c070614040c1502012c0732040e0a02010e03010b031e0115030503041509090509010e07140603041e210327060f1814 63
    0x845d1852050080500001c0b1080d04103400c00755241e2a0001b41c94900c2c040c1040100000c2e0012f11032040000b8440f43d010180300300c90b000e29140345c035610346440480c280e86004207152040700380c110705075141075049142d2a2442c00a04103607484a41c507001e40d001d260180507186051402000310301403643c441580c1101c61040d0468040000765600350300c1c40e80b41c0c03081d84006418400420000c0000762020341020601c02d000500791818500d955540100e00e10940c1c0050b0304561901904115170034041c4480000e49400c50300075400c092400500c8070300e15890102844c1000045140040c902480340915401044c4100012801d541c6c11202e56240410340c2c7c0c010810500390101c4031686482e418102e1350050782000158541c0f00340c10b25810703501e41e402c0380700900303c100400503100c20351850400c9a800d014141d40c1031106010000f0f00031105540001c81c2d240418400c4d8911000802c0d543c00400012700500000c500008105148504c5151201c400ea40001510b9402e8000b00410721031032818 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 556838282 1250 556837032 556837037
    0x14010303083301110f0d020102040e01080105061516020a06051e030106051602040902180f0c0f09012d11010509030c0a020607030c0605010b090f1210090312020309070503060106 78
    0x1001c806046805030455044402e81400b8800360b407000000300910100c603154560b031040b03a04030b003880c16009000750f0080c030811900c03510341c0b000816000c406001c5c40d40601401001c801040d420b0405030340059001c1e02050880b608034003402401600c80030501401400c294a8494950f03400c40b00920100265000d071007032008040005010f0160080c0030317241c4200643d6108a104015071010030010a58010041d501407481c0b88000400342c50810f0192041003d20752400c0642c90740120380c8040d014060704044410002d100000b01035201c7c4203043e1441250b509094080c20220000c10302d41110340d00c80c040015000c01855140b01000d006550b00071402d60300551400c0150002c040d00c441103144000d02c40c1c200001e060f000e051143c103520003007940007981003019582d62040c603c220b91100d1405800f90520600c14841441c106d4202001950640080c20070f1799003c0741d0300c078000c0c0384481084051100c001d0b0150a90506880038521a4480700c1c000d20707010742000101454128140d1140f802c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 556839532 1250 556838282 556838341
    0x14010804050616110111041a0702011403060f0d0803150a030c0b0a211a0405060f04050c04081203070212030c0403120c0f1109180304050904061401030308 68
    0x5900014880e92081d2915210f0445241d80041100c60000315141618250709060fa507180c2081c000c4002c004850540d00a01e01c800c0c6650708018403400b030b007940039010171081c5ca041b017884c1030044015507002000400c114808003500d800991404c404c1e4005803040400442000b46061414550501c810022212030064514554540804001e280683c07c0c5001020400401c0c507070182c0202040c02d04002046028880015940401030003051010316450922501842103410b26200e4240113001c003410300000811900140806040301070001034a01000300000502050b007071182103141c4c01005000c640d00d003841c9c4002494001c08280b002210b40f020802d00800407403000c01c860499900000078032103003180d5203058a06210080e00a0140f000000c5041c00b0440444020804c2d20000c880300c0c07a240e00d46030401c000185407031701d04003099401040280428900b014909500500c94400490400c0f40000c00110045003a0302c00c6000c079100d0310078882d4000024803442c414840c001d10104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 556840782 1250 556839532 556839541
    0xd14072003040308190e0901060807021002090607020103090c08070f1a0405210c090702011b05251104020f0301030c09050c0702010c0f06020a0e01021b06041a07020a0f140108 77
    0x3041c03190110402248a003034540280e0b11b03014600d6441c1040e801004500150796807103001e030844100701e4101005004084062840c00303550310aa500005021f0005410710000380e0040d001400954026240802581000900d035a010408a4042c151940f00b000307000307103000c0c5600c05400d01402120086038041c0300a1049880b03e040030302038a90a42501d2116003001084a400c0040001c041504000020200000c190701504200411000c40841da1316a900480048543e0b0080f0b0304c449200d5444002040e441161005074031144600a4108007003001301e41c0b0010f4201d0b4080f9510080d00c0e000071004005005032010148010300091401344030b03038074140c0060351091050070002418800550316000074080b40c2041030880787d038002000c642d150300180010380103a061100a0f80140305180085111403221182c0e0406400040d0049003413508042d240f10740e820340e4020920107004140800c10159480404841c01072581e085c0307801ca030500300741800075900843c112486c1480342450600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 556842032 1250 556840782 556840793
    0x1b020306061918020c0d17161b050a0201110a080405120a120525050d081305010f05161704080a030b1809060f0f010b0d140720030403 59
    0x1150301c2041103030001c82201c0c4840d24400411510341120f0341e201e0301c2e01030348603510355541c0c002c083c0143c00e801110078038002c00c101200d81200b50101c1541032803441000c6888110f203800310380112071960030140761442d6613940b0701c02c0c4120190001c6d20191701ca00b40b12815942c2091030002d0454900380a4000300005460b104082d1180344511406009140c1c4007403001c20060003403540007503118070038500c00810303084000d203203030000d484082900c03103078407101b644903100c11151002190303009019010740796040c6070aa51140d002040c041c803606079140e0b44800202c0a1082032080350488500144500703102001c40e141c45c048011201c00e02a0f4174514035140d032980704980354010380c069a0313540d03618165002140036040080130240c011074040c0d01e1144011905080c00d2290403520f0880d512a61044446c424a1100b034802142c40408070307006104001f0160010030f110300c4c1411010a2200988894503051001181c0c11800606074244640481e00c00716443c2100d003c01c280298185411501d49 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 556843282 1250 556842032 556842043
    0x12100e090d0801290a0e2b140718020a0801060806030319050f16060e0a0209040b06190e0601090503032704230702060a0203040b0103031b051b011b0203 67
    0x31200515921100e03035411249015201311881d0001c03d00d0340c0c8410309260050105518007411611800c20307100384507881001000c4141400c1218180d040c0c240a1035210511040300c020010a0140188240031a404d80502400d801180c0d10010041c2d840f200312200a08a00040c3c04c004108a4410140807040e0742c00070550300c16200300d40c110700c06603042c00016101481014000c9803007420100c0c040c18501c1c1c032449881101c0d0300501052002c9040c40e401191034050b8000b0007940125800d000c600172480d4109116803211010b4001d50390001c2025400c145a581c640c0800c2000c0102c50400c44d20f540e1083d40d450040070180c0045080041042446001c1022480b11984d4600400300c00003099072a0380040d02884160304283c01a8480e2010400c9110000c803440405031003150003091000e032440c800c8a04c125003044061282c0c1c3d0075958220341610007015915111801c4a030401c0c0030074400d100803107001c0c1c00d1003850307400c1c1840c0700c0c009420404c200e5001050051400821000758401264 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 556844532 1250 556843282 556843289
    0x50a0b0d062309010617120f0c0102070f0b070314010503100209010903170304030f0813141e060108250e13080d0f050c0306130209030312100e090d0801 67
    0x20089141c094a002510002c05220b07001c80c00d440c0710034180f21999106501040540d0f40704040f0b9002c5141e072510041c0c1c1d03420200003081c0000c00402110008184280141c1002900071001500d0041e1544603803903ca64802d101ba1040468401400b801942520601c41000100c480300381096161000094031490b20110540c030f415000501c400c40c2e684101c00c0c1d0310107140d0090098422011500302c5400640048400710046001080c03403240050141880c02d00c14001416007140c480485d030785000e541c640c5224030200c284140d15100340b00300140700740c0d400e03418602c500605081d80f4102c60b807841c01c00d80100d8440c0b0001081c40c08100c04940c401414280e07070010450707100580312042034210a905071040a8035540740440e070700344c1c039441a411001c0680400d03c02400182c94040740502148015105035074811f0301900140240c2101d90068425440000c05403802e14000406005124000f1200d00510f41150307e0280140d4800c40e0301d46802152030380c010902c4241000d0091701c616018007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 556845782 1250 556844532 556844543
    0x10804050a0b07171e06150703142505061302060316090f0b0c070906050d020907120f05010e1003030c080702060f0a11010c08152101051801050a0b0d 66
    0x60010328404e0003114a80c200c0311500c10084000e00d0080250b0301c60b0060101c0c0701c1c400558080210f5454588281e543c03c2402401c5015450802d050f034050728290f0110b07820140c580b00c00c0c09403c0340c805e841540c580c0c050300d42c421816444e20441c07800504001004103040d0221140144040150f100c84081d260b21110314000300d86264444002a10841e1695005500e0b0042e0000041024950b48016000b5607100b407044854840e110b0762082d0a842041c080c280d0441c07141804a0090701d444402e4541181c500e0030034040b6107084980180658480410a118554845004106480c807500a840e402940038262000b0f40f4115503009101e00d003000c0c000b0b0140440032a02c40259607079002150090940201d03960b5484500c6030021704201010081156194a00200c4450050048410600c41c030b072011541c0b156003e5107410825041120709201c50b4a000e00b101034021041c0034460107001d80320408003403240602118445094803002001c01480d1810300c40301400c5504c136401d4203d880740d41708 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 556847032 1250 556845782 556845803
    0xc060a06140f0f1002070e060102210d0615020d091d040b0712050a0902120703030906030e100501031109011d0601080901090203011a12010b0a0302061b03070c14010804050a 76
    0x35601d0012000182e07100c806120204c1620741c000030b4840032290781c1d0010b1210750743c0390300040e45c0700d021f01c075620f100c0d080d03401000150030911400100303440d4000044c00101e00b5190f002c0d004010710404d42c0c901c050307030007029440115508160080c00501c0351115070041116032000d400c0b02070402030300041824445d035003c1031b0070b18003034007100c84107910507a0200030500e0041102000f900b10b01d84164001c05541403a00d000074030209182083c0c0e070301612815115454680c0840042c40391600482d914060070140c0301440380c1c10f014850086018000c000c0c8181049010480e0302071040c0e0011030121641c4900d1000c0d0007000160650100007420030f425555247c00c0a24090107007803a00075410352070a00e00010240c0f081c110100c00c42c00584517210488a003150701400c03103405200c01c561001c5080000c00041c0780130340040c0700900c4208002c110180c4030100301c030314507084840100e4081c0040b40e03090141c49003a2040a0440c41e00b440c00075140e052503100c003070b180d0f186203102034040d40c0c11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 556848282 1250 556847032 556847059
    0xc3206180312030c030403110c2d04050c0a02011d07060503040f081201061202090904020d060905030d0605010e100e0d0c0b12090705090910090512030a020c060a0614 73
    0x5204202c02d040310200c40d180c3d646000f0780c103840b00398400c4030118007054642010f0548103c000820600e05c510190842e000c0d071808941074002500d011081d20070103c0d50001c107030000d44440c002c0c50f00850100c1d811031340b40c9030200406400d4802041807900c9001030307503c0e05c10541000061070401c0b03640a08105d65a6201d030708000a017003c40c000007412016001400c404d21006285545040300c3d110340d21071003e110788003c1e040c1a1300c0b0740515654840c00c243c004c00c0c09403410113008262244204000145a11140d840606507044400100390b001c1e13945404008650700700d124662481c038121000040800500d1000d040c50706540b010b107005003d44034a03203081021901900020304030a9404a4440b4200c0d44100c05150088515442a00400070005042c1c00c00590040c00380fa1200098110400c4803080400140b4060009690318800c05400c800381b44a510011405001100c80260f540c00c20140c02a18202020701015041d0785042c004000c640454081d24a0040013126010b0407280c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 556849532 1250 556848282 556848289
    0x609061905190c0606060815060903101d0c04110313020307180f0605120d050a0314010b0304020315060f04110c0601060e210604020d02030a0c320618 66
    0x145451060820b003201d070507100c1983e000364a401c05244030f200c090200d1a1a81007c40d11180305071144000000e141803040c0c402d1500c0300141c22040d0003d4122861950902e030b902055070b80c2c1c400041c44012a0041244460005100359500403005403000d0018100356240c0107045e00c0001c04513100c3c2c0d0103441090707046550502c0000000c09030200b81c45909100142c4400007032444010fa17048103480c0c41c000007010304100d10042d00040c1c1ca600500451551604291100c0d0f229a001e030040582d54804040da043c6d03460380c034a019108200c1120340324a001c1c030615241041c0014202c0e00141d01104001c000e45e500140e04040f0403042e640032900707030800c084480c1d85004030b0502c1c84840c0039100010482e60b034406681102c01d50212602108030920f5458013404d1503819681fa4074030b40000000501504090606034100c2c4d2010f07044422540403615105010712030b58020580c0100654a00c4036a04c645100501c1d0a048100c003540c48446d4142c0060b40743e205041080c07940020419201480c1c0c1d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 556850782 1250 556849532 556849537
    0x90506130903020d0909060b0a0309020109031709091f141915020114040803060105250f120906020703060504060e030c010903090e07120e011803090509060609061905 73
    0x22190005015080e080e1901940315124144c03140e00180660400042c0701c206d5002d06400c40394030307444041c500308481400301e005c0c0480c0c0206074180041e003400040080e540485001600100c0f08540d9180e29501d01089880d41c0b005d0844c0324500c1c0003030450b00745140a400d901080798208900351070300e10080c1c00400d000401270140c3c1c0c0c2c041040000c0001d4405c204440400c0390001c154002c00014400d40300c022820041660040c0c201d100900004141d0750107070000b050b0896103103940722981801004401002c080c4103808a507400400d00e42501001101481e10350708054904118100307600f4030100075510411407001501c159102c2d80401c06100444d80302c40d2076940280e050b0703a41d03414019420f5018000c072200c02c4000465020000426000700420305008825a9840640c01c5c9800101a0090081d010b00c0301c045541e030301914150001e941c801c20381e03601d00c69100c103d0001d00c0e040800100c9000240414000d202c10030000ea19a6078107800c0710a45885600038840c1243c036004211001d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 556852032 1250 556850782 556850809
    0x9030a1218060b150a02062e060c0308090f101802100206090d08280f0c170a0b0315090c0603010b0706050907050a09020f0d0f020703080a0203040507090506 69
    0x612a50300540c1801116086030b0f41c0f260050329011590700441d160900a48241481c2e000142c0101c0045000d201540c080741c1780208280b554015100220008042c0410095010341e0215900c02c402d40304064010036103a9001c00d041c00509241c010440d107007600e84000f0010761881565800301d001e031a200b401082d0080c2c9802802d42e0400c07035060135001e503441c03505480c500b005100366001c003070b241d903c01d4200c1482030300f0200c0a12115100c01854140300114030344c1c224200c1b512200070001981d014841e01c010702140e50b85903049a4592514114000009040e440d942801c0110003400c6450000d40e145042c520746800a21584c1e038001600c3c10b151148012580c030190000000801003544406065500c2c0180020800c1382c640752101503541c5200d1040a801010700c03181041340c0c0100e5809454100b40b94044603180246489805003107400c26550090b1596003c6600001e2661044e20305902c0340d1001030451560500e611204d0b80c0b040350380304d07180d440c9854400140300c603201c403c0c0c4003110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 556853282 1250 556852032 556852061
    0x3305072405090f0c0120031e1b1606140408060408030a1d0703291303030b06041208030604091407080d020d08010306021608130f050103020309030a12 66
    0xc0050454850003030241030754080400d00c15200658030108010502ca0041c60050f180e540305200d1500e61006124155032a80e03040d400144400c404000300300d02d00154650f80d40c4541903942c0d507244010700c42c3c4021a903a100b110b50081c100d2000c0c000300010240d00307176201d90400f001d0303050b08002c0d40d2903e4800d070b4100c182c140c002c0740240020020751001071401200c1095041c00311201280c0301188280070702803140c01d5540040310800208014400140c04003a4410000e201101c0c0112411844441a10100e980c101ca124455040c9a071510504a103007000303c0340d0030310b8240380041c0740c0c048418200b00600003001c0007001c0b8000b90345d69480a14074643c85440c4c00c0324084200065a201e1119200b580c0c414020003001c5c249180c404106c20601d01c2242d00c074290380d40d0854580c0b41c000d41116020074500ca24104001d004907041801a0100029000308803140504100c54012040c5096001a05140c014004c2c40360400740402950111040c625001c039080340e031000088007504802425514 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 556854532 1250 556853282 556853333
    0x801081b121608011e0c05090405040503211008060c030a0e01020904090f0b060901050102150405120c070303030b03010902060901030e101a1f02070e0405070f0e01330507 75
    0xf000c5406410290903801c040d005007144d210090b40810555812580c4000010010010b801881c03500f41c0c4602d400c14001c6044900301450740c00151a00700880c44d030590285030550800c40f01500248600010380801c40203017069003811105642d5902015080c00c000c0c903229280348040034030940c141c1d8680c00c0024014064070307096040100c40f003607c0714026500c400107407002484900300301c0f031614121903040c0c0c01899600e1744030864007055207010b4811640c0f4019030500c1844030b1906400380241c0340c103a1300a480b046145d450083e048849081d4421b0082c0d04103030702031026940392000c0d102031000c282001314615924560007420508064450008185050001040c80322003100c44440320b0400c0d10450b00404200c90f5010084aa509a030001603201000502916420707440f82c0303401070300c01d508450410340c440c04044642c907202e400007001214480010094901807141781051070303c988010702c2848210702c0b003c21885c11255024024007071300244100c10000305000405444440b01000e80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 556855782 1250 556854532 556854539
    0x90b0c010e011415040b0906060d06030606090510060c020109030b1e0106050c0c0d0b04060b1c0602130e070906051c020f040801062103030506130203090c010801081b1216 75
    0x1040000c255005041c01103810f0340c3c50340506140c402c0c1b1444503001800f2500580e20f00007000004e6106e102050002d54a0301c0e000000501c00b0b0248001505c59a076000c20b039803400e00d00b20030014815600440402203448880c4005d45d8001c103d80d0207980d0880b0400d40c8035551480488a1020507040100b244141040002041c0c0c0d0310001410a01c0524400e8a10380010300c02008080e8402076000f42280408901140c0081e080707503c840d050400c00703005603054080d102148620002042c0d01650515000500c00600c0340003041c1080241011a40c2d00c012424869001010b007c0c0c1405180b041c80380004c0d1945d04400d440032070b10011295030005540d03868409042904640140c0b155082943c04c0003008a40c4804a0700c040f100220180c03503410310b40300c080d00c0031800b0b000080c00749a00490b2051003440f19409900013144200100300c010800c00d240380000400301641607010b04155044450050301900d614080c0651159046482d000558070081040c4c0c142400030520302c0d4610903059000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 556857032 1250 556855782 556855811
    0x8180d0b011e0e012117030109060506032503180c030605091903030c170924100302010c050c190609150e010302031b0c010e190201090b0c010e01 64
    0x241a01c4041180c05241480304282d01d051000900880140300f080000504c4202e01c2140c604103484080c40c6190081000754032030b581445005221140e014030000010301501d1340c1070241100410301039a0390b914524104605056034007405041d03107010b044200c0010708035842a0050055105c008041905a64107450100e00c003c000303200071508603080c030b0000b540e401c4000c00e4003103022510491607002c107080f546d0214024208580c040c020700510000300300c3d4501e036440085124588003002002d06000415403c88490b042c00c2000400e50300f42d07003c010703003000500802c004030f80c8e0a007000200d0003c1850164101460003801c103410811440f815420030140300780c4481155425206d000c1501c1d12004441070381b500c0186603a000c5038004940c0c0c070b502e511a900841c1e0007140c9480380b10308036410303028820141e401070255030442c0e919401c041002c1c01080c440e0110464000314507000351001c5c1c8c0d0010384041601e1140103540c1c6000710303038458003910030340029101341c180b10001c000190350710018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 556858282 1250 556857032 556857053
    0xd0218220f060b03010302191e0305101a0d080d0903050a0906020f0d0807030f0c0201020d1401050d0f230a110111120d0603050312060f0d080708180d 66
    0x4a0080350602440901e2111180310300d1081d1205424440d103141e0035a02800401400100056065115004001040e0841d03000845030a041c940c0701c0d84420b0700d141081c91078440c48c0d602e03600a003481d02824045030309803c04201460b03c415500034004180e40c2c00c020406001d803041b202500c508084500c0201548500245003548441d255016002d880b03c0080ba5660051500050b207a4030032144102080c0c002c40a1581c00851441d0100350001d4084509058070b0050100d000982e401060203a1000703c18050050205050000c0300070541c9081c0c0010303001044000003404c00550002c4e0381c01440702c4010700c01d0140250b042034003c0100c60189503951145071801c00d4545604030328500c0701d950712a00c0c0c040707140000107000b0641d0300c101407282d0003164001c160560034140d54910000000d0401d1018112030300c000341c0046600d2030040140852596010300c0c082c4900b0111409000103100c09069a8034181c00250307030f0b500c5000680c0114040501c20580e1544a1395142c000c60070010b11650 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 556859532 1250 556858282 556858339
    0x150a090515040b2808011202040b0a0518160309170c0a0803040c1809081902160603021804151a0702090c03180c0307060809030d1508010605030d050d0218 68
    0x218104c80c0c0700b01c0344048580002c280182001d46120880303080141c541a040560b20a07001084400000d42d1000040e1206003060b94844104c0d00541c20444181e9031180d82000818050505120401c402c1e912080362441010079000620008190401c0a580c10855030369030b190700122203a52030030182045084c24240c0e00c0354202041540a82c65141e00890140070740c01a400101d00382481070200c00b901002d010207801d0000c42c03190440000d000380d542c050710307001011036440042c1d90300711420080203021035400b0300038041c138104441090031900c207240c61800c44810707207104004001449444c1d545445030703900180d480741d00b1105012414403a0001540120b01c1aa0780321b407441040d10030941c8800071140350340d500d6006210300300176050088008660000300c8406491616080c91000c2040316494a080201030040e090280000745013441400084c050440050005095800c0c0c002c7c41841120018094180c0105019183c40c0c104e680f81001500000c0051100c008240c3c10325454004640 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 556860782 1250 556859532 556859587
    0x90d020d05121f1e120f14010f0f230708041401020d1506081e0117030f070c08070609080606060702030a061b1d030a0f050a0b0411150a090515040b 65
    0x98001524000003100c1c09555038003004c1100642183c0d20f890509003030247c83d20a040d502e4480401e401101449603041c40c900c1e102000460368003040b1207100101c990707d608036445845c001031005298100001c40e61081d0b201a14000200041c40700b07030301901651107451012070078041c2200400d90746981d514252001955180090b40d83c507401c0600441c0d51006c036000d03500b000740c0140315801e003a03901d40c1e0040c61200101c1c4d00d445140b000380c0c0d04a501c100c405640050490707409218400081c42300e0310007071030341d4604501540c0c240700041d5202c0c2c1014101d244200c0000408404544051280054080d0020340400580304903440300010f0380399040ba040c0008503802d007244001c500220300c1081d0040040c0040015605541e21030200d40f5040f40192181d00ca80c040890000b0114102948038030711585071400c420f040201440140c5504a0b89800d401c1c070240b041100b41ca501038550800c6520888845903140039a140241c2240b040c1c0d04560719030100081d0a103001552000d04602000112 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 556862032 1250 556860782 556860839
    0x20090c030f101203050a0f210f0b09010801020901030606020a080d1d0f06150301090b0f18030307090501020c06030f13210306080708060f0f090313060305090d020d05121f 75
    0x7900c12500c4070760020072352110f000c0c8511400070b50b03440380e0311170f0b00b201c01c0380400020111840d030001748400c40c0903800721030541c1d00040c80014a59050080000525142c0001c200007183c89e580d02c5543d001d9442113100031a0388a031001c03e1600c600244040d4101050240c821680110640f0798880300c1c12100206000014200c03281a070405114105d1455040030400c80c807501c3e260701803048844003500b005117003041070170b1010603a0313000d0009602031a05920341c50340903443c000002e802c109104070350170f224000500401c840c540540c14240e61048413028040c2d5081c0701454400a0710340c004203a4805402080b2000c1c50940d050340c00035094842d01b03401c841010795112180380c0c1e22070040f0360140c400095031000c1500ca14503080a0380e007118407013055906100036002c80a00b100c0e595030020300040d031507800748040100c09024880040c4014406000004811440a801c602c681c10f042d01307500c002e071702c00501000b0400f40704014044080c2c007690b000664aa041d0000048081d20202007240c40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 556863282 1250 556862032 556862057
    0x30d020a0e0915060d050c0c070f03110f0603040f170a0e031507091a04081518010603021e01180803090a150207090902190320090c030f101203050a 65
    0x4560f60020309003401803001e0f282810b1403d08002410700900155190074007402403c904403014003999001e81000c2c001c0d0711125141d810401d5100070031a00981c001c2002e8080e0034800c1c0c49050880b5403050700a03126000c01c607281d10340711402035254040400800404921034030400c0c0d001c140e8084a0703c00b05d0890b10306d1a15511101d00c89002500c0d03500203c0d01084003000340102c5a000c50701020a1843c1c07240c00c20f0794405500d420440742003208000940400f08006040c50125a48184048041c000b00600c80c21035012030164102c0c6007081034441c00240c10090303260300c07400c1400404d25822654482e0715071764026031940ca0300010f885c14454600d40700041684a030540114012307c07841d86c01131040c1c52900503d0f0300204404001070342c010500824241d0085000c3e00484002c520407040c4948100c07111058800030b407815040c0a01c144e00c2c03041404005104403055941101f12007248607440e498100c0301214803d0135501c4400b2490b515510b800c145900b20025180481c0c06403604071160780c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 556864532 1250 556863282 556863301
    0xa091a0a030506010914130f02060708030a02031012030c0201030203150a0305070602010e06090c240c0601030303150b030f0c0c0a030f030f0c02100911120c120c01140c030d020a0e09 80
    0x20496405103141d001410087c04500034040b56452075001030011860021185c07a5030400d0351040340c0303010302d180d0004203024006a4032502e46e802012a1001000c401ca003d40d13009000312403010010341055008004110b1411903ea03075101800001880120001d649162054544040c2e100e0400036510b4000b01c445c0e01940460b10900c11034012004e040751014000410059800038032000c94200743d031040181940000c1da0043c108990f203940101965817543c5001401c1d01d82d02101112080051a02003050206140c02c1d6a04640b900410068950b03940c04000d03094080c5907001c140920603254078000340f58003c0d008101103c3e043d6800d1041503000303d5101e0030b40f46400301c030800581c8002c0100182c668603501c040b5449200c0e0130fa528000840800040d50300032142d50000c9075400a501000040c64031801d001c0c08800040e001d05000c500c50340000e4244810321540b403143c05000581d0640a55041c0304440c1c000d42a2001151550704000d4011300c0704061003e4203001d0140000411404103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 556865782 1250 556864532 556864571
    0x20c010e0c010e030d0c0515011412012003150306270105060a0303050703030902040507050d050a06061e1704060f0b0109080c100320070506150a091a0a0305060109 72
    0x1401030005c02c0c10b1283c503117084449455400c401e0300c590251555a080c3d01d20351501c814001c1c440401d440001c02006810004054003040d07041d11144e140950050740c2d8540c059a80b0380d4440921111034595680c17040c96542000f24820f200d42c9805100100502c100c0d00c9540b161074010f2045a8501c44501265498201e03041516825401442e0613000c00020348644000e000fa80d00c80d150220313503400c290340850700b56402a61000045800424522081507840c0b240940c0300d0303003050040c00024a04000540100c91110304090b140d142449542c1409005841c1d580b41c2d4001e00b100e00c011841c0c10300701880240442e424074044c890400c21040400d6100e03038080320965020002030f03c80c0031040b1042240c20a01d071011541419211019440c13460320340741841000c42c240041d501d0f5500d0f040d00d047c07414108014581400b500380303000c1c1c601c603135202d15900710306450089071700280700e602100b10700c6004840c1c1d2041a500612920001c4200b200c0072903140d04813903041d20b061110301ca49920322101c18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 556867032 1250 556865782 556865807
    0x7120b030604060b060d05010608070224011a1c05040c062309030a0605010b070b011a16141e060c041d040314070b07020705090106020604061509020c010e0c01 70
    0x41e8030039008034010668035031101e0315048005110902e0b08985410701c01c00d0740c83c26801900440c1c1c0d08401c00a84507018401c820300d00c0102d0308942981d8204040b010581c02d0107001c1c1d030440e40e82c10701c0401d4007548804110740f0303100c8540b090641c45400d200380b84806450101c60465054496000c0082d010b40509400d0108039001c401d00c41070303030b400390003c982c0b107800c00c5500c43c5d80752040c81c03210004a00180300d42c078080d06895100310b42c1c40c2240e0038020249a01a401552004466030740d02214a8050090341d103d00a03500400021856a090a0007405580340d0001d040d07024110b08240c80c40010488002004015401d0b41e04940c0c8017200444140501e00c18100300c0c10360b408032100c00c3c18075400707035690180c4681020850780c000364410501035040b003e02264240059000d2090b1240c0421660000340000c0381c2c9a8119030400e04025120003000e400201550703100d25840c81b2888104080348040c201c0e8ac00c045403101480c204450290001c0c010307002c09401051119002540b0512604420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 556868282 1250 556867032 556867039
    0x80a17030c0d050405190609020a0503030307020d08090715050304030807140412020604120308040c080303060d0204052a0d0b040603031403040c05180109140403120e0a050a05010507120b 82
    0x2402c0500c810540903041c020710496103030007074080103042a0003101001006078007445000400328540d1040c091124100d1b04198480e43c410b20402c040360b60b000461021201d0b032403420001d251a00200d052070311075a07801a072081c858908203118590b43c44005140b081d4000d13600c031001c640b1003110940d00b42494003107801e2481c07010801171000e804800380a014140c07001d0500b82c41d0039940c02544082041020048000401210a2005200b1806c00742d0b809030103410013462030b50074240005511031000000003400350303441d200000c441c65030b0240102485003c2030114940c0110f40850b80a041e80b0500361100b0081c41c20030a5035841c20288070740420360798541c546541d0311255171007031011904002c10881d51001c01203c0401d298403032060308417140c2c000080016040d410b08048030103940d28800b011881160030000c10000c20740c4034041100c8030112140005402100c0c40099042c1504120094014450780c805801005015031249100d002c141c1d542500450542000c14152941411000d62 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 556869532 1250 556868282 556868287
    0x6010c020109290a0306030c060504080c0d0f0506010b030921120c04120c06080a020a080c0c010204031b0306050f010b0415110a03030605010e0d1509060e07080a17030c 74
    0x2603a604540503002030384035074803c50000160000c440368a81d01403004080045d40710303181002084000648034010f480242896400c1605003d40107683e4034085450078400d006154114052000e0503c00052041e0400300760b40d440d6840343e4100120f07074001c1c0c404c107001c0d20a0351049954070500d40308049070701c403841c0051881c0c00796100060501c000040c0c281071603000200400500c5c00c400c0c0910301c450303a1086a00c0c40c15945455005081200c0051021403000d0040101e0206160301030b848131344c08010f00b0a41ca8442545c0307009940240201c2d080104161841045202a040e05240c0b038811030740700b04010720481c1d888035103003441c0310340038814100041400c0c8030602880d41801c0702d40300c840d0b90610f040c202c1c078240e5401ea10700e001c600c458140d000c656a05d00a0010b940d04c134481a41510040e1094084000b990380c0b8014038400c0a01111401c079999162101040f03172a07040500255107d00440b030980d901e07013203241d07258118070904455864012800140078100c2e1820346c3d01c41c4034114400c90 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 556870782 1250 556869532 556869539
    0x703080a051005100e10030e060a0f06050d060207020406090b03100c031404030f08090c0607110613240c020607020405100302100302040504050c0f07200d080a0806010c020109 77
    0x20007604000e850860460316121000c2810f40b0307104014401c1c0002503560f403604948840500400c3c04074118540e04050802100001c903040000d4030303940113030b1407400010380c5034001c51544000f490aa00842c2e03101800707403000f0703007840707180c0e00684010b600071501004280c2c0c3e1400040105c807900e90b503490301034120741c1c600508400d0076840680d488645041c04103c8511010000d49215000c0760101c008c941e0360862052500d61003403000d68816101402490000f4030400040d2590090b0380340100f028405c40141201d80e1502c3c4280d48807001f814100b4900b0a0302d50900b0750740d01010b9802d40c1e050550301c90258884500c01d501e080542a00540b0591800d0b4490b001e110141000402c1d200c03010340764123800401038503890511100060603907401611503082030704110035070700042c1c20f500034903000340070300110054030504480c140c1c0c1d480b6024240480300305204486103030a9012280c1c1c0305020441303060034040410300509004e03001380c2d101941c9958a0005461280340070b50041e0018885080a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 556872032 1250 556870782 556870801
    0x203010f0e06071209150c0230130e04050f06090d050316020102071218080303060a2d1e1d040b070210090f110904081603050d18030e06070308 63
    0x6007820f440c4c0d8a0200b0410b0090f01d13440303443c00100301c00c0f0026680c0d81c04110040341c2d040c062403d00d040d5109186205101400740c60443c5008141240e00420000800a04070b0741c151401c500201800f44200c0500e14007810580c1d25440081c42d0007589006a10000b10001c42c003003003501101400362201030460715142c10250b0461401e2540400f5036600b0050903000c114401d0180121010695400134240c0c2511205120401281e000051580c0b0070b00504c8041c0d600d110412080c2d99a1500e961803100e05101e546034001041d2112034030f03e00c1900c101081c0c04140040201a2029031040c0400c000e9481d40302c100e42c16070701104d0141c21584c040200340064048481c05402c400181304440844d030005114004496a8101c12a060300d242240001004104e01380080341203400c85001d4010310f02511041094810400c80c0017451170350008030001c25014a00b0707510914400c540030404001a001482070304850741c0c2c41035000ca03150b0169000c240c60003900310390711164903030b90b0344034581c84541c100c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 556873282 1250 556872032 556872047
    0x3060501050402090d080a0e0d142104440c0a080a0b060a0b030406090501060b030403051606060918021302091e130e06062107050402130e0c03010905060604030b04110d080a05070203010f0e0607 85
    0x112424800c09118237070600c08220701c2500100c071408180c0800301e00b0b00081480c01a220b55028003a035441c2804111500000c5090703101e16412040317014159581c0c20015180086c40d40200d1003011010080c4800d0000b50351050040c144034400030000e80e0703158085000180811240100010350804c00c1c80c10b00800502c0c10540c4e584103800210b0000d440714818003e85400707a0749915510007804015055281550000d0b80c80e0b000e2100c00c601c0d002c3c15502007010000c605004000080700980b81c1d440d0780e01e0700070800e0358590015a00b009019450740174541c459106442d154410a021010a00964692036403e840c40060710000c002d8035150009100182d00160f01a003480b1800c0e0b03100050115044001910a00d10440101e60b03d6040c0003900040740c401400c598002d12081c0320901c0060b0000d80b6003500950003a00200841c584000010144041080014458140403400721a2540c1001c05000300c035108400901a5100f56000a0100e410b580b003400c0c2654850301c0403940c0180151350 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 556874532 1250 556873282 556873319
    0x30304140106050a1205161d0a020703140c0a060c050304060507020c060406110307080c0f061807210f060c0e0d050c0411070b1003060501050402090d080a0e0d142104 73
    0x3901c0381a621001c1c410072407d01584076094014458840342c040c01c02c40c0b14250791050103480c0c02c50a144050b28018403284001c400c20040a40000703015151100c10480641e171a276204400703000d00b0114404c010000d1704203541c100c4100d4100004984944e001150551445078094905828a481c01c4000c07106180d030b40081010a0108022010111f0341001c002c01106000301c009040c000a0016050324010009110301004c01c100c00e200000301001203005000c0b0781e2418030b404c01d1002c0b05409014031115025004001c5540c6202c83c00400105400c030f1001e6600c030340c9030050704c1c03210702003400841901032400604d59048040e07092a130380341c50b601c0320032302060f09000d5604007003082c0c1e0b0b41c0600740c6081c0c408549044d41c501d810002c101082c05014050b002c140da0550070610b00001213002101a514000c000c1003000c035800c01c0483c803841d0f41014200d0300404400c000100d508011010034031f015414030560141a060049a4620a0004d07614000d50f0516030701d807503e800318481e081c0c0e404c000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 556875782 1250 556874532 556874543
    0x8060306040b13050604080a0f111207031b0501060905150319050c06040e01090b040b130c120204030b0103050f06070f050c15010902030a0b0f0d0201030b0f06030108030304140106050a12 82
    0x11640004940d040180358030561184140c103644001c002c2002e048001122074a132708000d9101040708a858010690b9000e408c2100c4034507444010b10303d0166140c81580381c00007103030549a9004018014150001c40456401030300401c80703a182c403d89050a0005400210b40550109400481c001c403140000a0424014403d441c110903460300010090b40c001c4d440005032600d094010b000400341486684a4094100c808100c20100c000c0072400a04031032a440b4440e83d0707a03009120200c0d010395820302c002042d0400440d581d54070381ca400112607000313001c25600c40c0300304084100401d03130001d4083d020f00295150700c603c1e01c0b64003038116801d40c0072a5241c0120b0240012148918141e80503880c040e1420060240e20381c600324210004a4151500c082d21030072202c0072038040b0b502d42c9081d2034040d58081c60701091030011a40410103480807481c5480d0414400000040e1042c17004c03010714000e5110b003c15110300c013020b100792826101d80b80a0300e980309203009010040c0d10020301030078404503c80c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 556877032 1250 556875782 556875811
    0x3150f0e1c0e180402150703081f0303091502070902040603140105090903090913060c030504030e030106030804060f030204050303040f06110d080c0304060b0910050a1d060d330b0108060306040b 85
    0x85046c003c2c1c80c3c010301e0088022030b0680040c41034002e041580f02503090755180140320020302e181c038020b094074038912030040d50447d084050400340d03109100c141e020f041c6948040d503580342d890b10010000e01c00098500070440792400042003030316100e01c90314017845003500154201840c807000c128050034003426011880c4440010200040c03410b008241c881c804a0301c0c005114500381c280900515150300d403041c42a40f40410600005052806480680b8494640f00c030303081c0800c2c0030503002485550446645032002040000c0e181c0b148002d820140d4196a48100d1400e04856081741da51308100700110201e114140000c1c81c8030b1588001e96442801120040786020998010030f44c0c0004c182c8800020103c542014003007410041d078048000c0c14120b8602d15541322202c0102c520389805807040d0310450010f1030100c140501a0300104240d500e50040001e801c92aa10060043c14503450b8144581d0074a101e603011507000e0b1425078400c10001d0043d104c01d503103c0d41d4000844000408060003427050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 556878282 1250 556877032 556877059
    0x1110c09130614060109080102070c17160f0807080d020304030803271507020318090c071703071803030e040e0330010f080703150f0e1c0e180402 64
    0x22405015400d11000044410f0790900000050030350506421808090b801084004c0004884010700e2080301c1d150900181924000920541000c141c000698203030803c00c800418610101c2e01310204880109044501d91940c0c1c011040c0c98001428071000540c20611040010130500c1c0000d60344031b07000a49030700c640252403944d816580d50015881442e43c2c882c6046400140c060644c032a0804010f000450803c200d4083d043c0c2120101191103002d41100d50216014803042e8054880e0703103a00801c18480748261500c8403c0980003142c0c074000240340b5030340b40303001c9855400c400010303282c040d5601c80b4829030043c2400040c05a0506803c0070348420000031140d01d8003418203001520890074840d214040d0034000e80c0e1500d00680000e0301495200204210040300020094100d981c04003e06075010200c0c0c920070000e0940006000b1843e0401c200d8003004100400e007544010b454540e503c502e440c2080b02200c96520281c5169040014440140350350003480c1110355210344014050421401c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 556879532 1250 556878282 556878293
    0x60b030c1002010c0909022b0b0303122d0c070c0503031801030501091103270607170f060a18060b0d05040507080c010f081e09100b01110c0913 63
    0x2103075000703a0040c0d40d2001000845907118400c0402043c0e803480a5007000c280540d00112203040c5202c0c1a1125108030001c141040d080c0c01c10507901d00018240d03902e0300d9040e0412400010112502100c11404014000310040c812880d078030004c1c0740c1800d18030641d9540d800941c042c2e00444040e035181109540004003940c042004105070303642c1a40d07e55002d0520700025045c4c40c81a001180c03614181541c818000c04145d0030380f03501402402d0200ea40080000e0461201d92184a090300c25010b00820054a19000460142200420500060956110030034240303204412755009070300c8072006204209054601481800040c2d9005000581c5651440341d4036050744180d0700104090780b034400300001e0203800c4c04454024490a409808144c04960000303020b080041802c40503c400301d80400d800f00758049020046e02184000004079044c08545165038207100c0d229800104e0402c105034081c3e501c100c2c0303100070401110000300f00805541d010003e520200030320201d600c025034443c1001141c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 556880782 1250 556879532 556879549
    0xd020f0a140312280908070305090d1a062e080a060810090c06020706020316210e031e190501330506030f04060c1407110f01080112060b030c 62
    0x40d01c85030101342000620600c1284080401043c0c00500d016140030214920008840c1115031518003950741e0001400041c424414040002c0d002c64840e0217592084c8520055080c094802254040c894203200b1501c0600f0540c0310303401c280c0f015140b00300307000140d01030123050340c10902c2d8100109800c1e454100c001d01d0458106898100c0d0354940716184140480d03000c0c0c0b0809040780703101800c8c6840c14000040d40d28414401c210000c13455031500002030026031000042c00e400303610200301075040840401004c100c80300321a81e11a028840c98103011030000c051600d106e140502c064005000071108900c45480c1c84a0300352055503c500300740701007580a5486141054000d90980d40000701c0080c0c074828200035411003400ba80e0f04000f4444400b9a5203a51b640c1701c0d5126801044900240a048450009419454202100101d491400c1007014500d0300310000c002c0c0c1d40380e0005280d0000444d02d001080c45082141e112150900c000701300c0e07035000400382e2140a02122218400c0201080208 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 556882032 1250 556880782 556880791
    0x603061a150306010c0c03030c0201081311120f150610090f0b0304060b040c0f09051c0f06020904090b040b010e0f040f0f0c060504170a0f2a1205010c020d0e060901140315030d020f0a140312 83
    0x2c047095400c000722031400800e00141000213250000015052842011031651300d03000b015444800400050304110103600031611852000c0c0062000c11010309018019480e4040d0310783c04928964000700301030a01008002c0d0700100821001d6607034005480d01c0c2c409103641c14040d10f00c1a020050b500c500d850782d010342d048140c0b14210000320be10789402d000c5014503040e00040c011301d40c0441070014040c80011881e4100c0d0f003000003050405943c0c0741401049900b00d8005000442201c80041e9540d0003601500c2114181354202054211034082e80b0345070402c52100500c0760004004220110392a118100740c0300000f040441410350a07074210032051081c07640300b080005580c1c80d5030010401c0a01501407101004d000a2000304031010000e0001002c0007812402604046207101305a0700c81c41c18945580260b00c01c00e40e2301e041512126016801000c03036180240b040502803400d091001488805c01c1000102820300c25a40c0c0d5140489031032074025500c528030003408651405408990320350700a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 556883282 1250 556882032 556882063
    0x90f0f0f03110d0804030f2001022502130e07120b0604060909110103020d020f0d02070501140c03010308130503030d0603061a150306010c0c03030c0201081311120f 72
    0xc245203002000c01035204425150303900b0030b5101034002c0d03070406062600550725041c14180089559001c6410384510009801e881610000901c50300c18194000c180c640f24245610820005980b119406500341d00c02c0250018100f480840c03007440e139540601c0c2c101c10302d034041c2ca140b1a40c07101360364589856490161943c0e078040052158602d030030b10802c0c00824083c0d006100340162030321010058001c4484050505800050381c0c5071180d0700341e04903140e0000c8904400e131078044580030a07000390000c1c1000c4407658642103405032850120407e82d0b101380109146689140e085650340c0107142c000301504020201081e80200c0c1f542e070b0500141c403000f0100b00c0300244007481d5040c0364040d500d84901581c94140a4060400551030304c003001110040d10300b001e15941d0300c9480040b0f8000483d880c02402000c03031100c003c000c040c0e20210906085000341d0701d0240c1c603202c40e070384440c0364013903031100528641c0168008003c908050b6941d40c0407040c280282c4007502e1550060505040c000001c0c0421b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 556884532 1250 556883282 556883303
    0x31a0601110a03031e090b0703111902033001090b19030305130e0903090609030c0d080c1006060c022206180f020a2c061c0506010309030e0103090f0f 66
    0x420250011714001003c9066041c40081a2a21030705684400500305200f0151039501c0800d062207048c3c1220039540d501850340c1c0300c0c8071501341c1c0252a0382018008501900038182c000344c0000702c058040d20020b040084c1045180d1030004500300038049200c4954000111440b007001d80016012040002c6000e611002e941da0030200c004480e069030f64015941070242c503010f201000000009440001070305a801036514001000003a2820f00c1000106500032217204030b1104100140b0080c0c00d041d014241100c00b940309200310101505e4107409400001416039412402520748200c000440c20000080416402d003006280000e4908680000d01a108402114201e07580c0c9880780a480c010300c1c83c0110300f090481d14008102210084420381a0301c1c1c81401034184501f40143c554000e070008148955409103540c5000210018a6590080a00c0c1c540024810f500a014240c03281ea030560360740d441d542c02c1d20010340c014050000141c036013140010110303000400081040b000e007800b801c803000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 556885782 1250 556884532 556884551
    0x11040305011409030901030b030c060c030a090807030308062b0318050406050f060903100e01050610171605040f08010b361e0a0b090709031a0601110a0303 68
    0x342942c0c10040125000d000d100100205000c02105542501c04240b80208155080d02e00191034200f124024550009000902201c0008000024480401c0c0e175100c0c0c3c004980d0b152803440c0c55071010f00c0003a010992000019006282c0151100c41840148401c6d66110709488910120080c1e00d0b841140411008412400010410302008000700002c0b03406008040c03c180106501d50903221115004400c00302e892586c0c1d6509000d2050342c0034050000300020140c2e52701580c0070f010250741d094041c049045500c03c5040c440d140c0c40d00d80030100202e00140d5140c228001c0c0841041550320000c0281c2804003184060700e01d02c04000400c1c1d203100109040d400d8500308161310001076600c3e01c6590300790500c802602c1d881c0d00c1102c4c45065613000c6100319a206c19500171038407029a0280380c41030711031042040f580801e9122050110060760031207490354814106880c81c01081c00064064200c0c02040c4040140c400c120320b0b8014810b01d481c0e100d200320b42070014a41640e8000440100742c80d0740320300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 556887032 1250 556885782 556885793
    0x8070f05041203020d411c0204050f0405090604020f040b0307061205010b0301050a0603050c0403060509060f0109020903030d110909090d020c1005030106180b0412050c030609060601120f110403 85
    0x744418001d1000055a21b103c11aa200c48a09494400200003020344c0c100142401d680176103020001329180421051441c070180c6000354090702400b4418120030116200500700f602c0340c0c1f807180c90240010092030b01c50703800300000c500c41258a15481612442c0606407600e003440b07003000410700c07038503089034a403090400340b41079540c140c01155081300180300403c5541d4911149a04440740c50800044640b2065603000040c0300d540c0014280f10301b09002c0c007401e14400201e0510130813044c0c070103602590b2148085d100f032380308403a105c035070540c000c0c0071074141141c050380100b80004c1c0424201d0b141420b81d5001c528002c1b400c9409d8803040e04002d007030120842c1c06002540100804407000300e416504600058944c1c0410300650003003108859a289d4078034a040e00c648081e100b00003610b526a540d610a0315040162104201c8050081542201e56030800150b0640600303860000741c903a6175640307001111415110451b1203445c50303c4da10740500c3d910452140080c0d04404440c1e07181e41d9411420310 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 556888282 1250 556887032 556887047
    0x260412081902191b0503030f0a150f030311060601122307030902100507020d080f0c0a14010609020c0a0b090a06020a0e0f2e030908030c0703030e070608070f05041203020d 75
    0x301c50b070904804035040001c0003c1b044981c840035450f0703540815282c06160500900401310056480700400340b0106002c9240804001260710070366682c4c030725520409985032035950541e64540400c18000c42412a4405a0040703118051440a04416040d0b001d91b50201c6000558120700070035a00e100c41c0040d4103151b10080440020340c240149807203202e0340843e003403900b680300c0a4106800421107151000f10401240ca200c11954200c0d01c0d0000541010742d140045c031078000f0000e6280c4000050015914000c1d24854003462028150189d84c946a28008000080404059003e000304410014166101400103c51a581c8400c1a400020180942d0481c00c3c6041807245020340015000700c003d07402d1007a0271041203071411030040400d000581c041c0030400750050508101004002500400b10007a01e80940242c0d01404070008541407191200240c1c02142d00255840c40080c20aa00500210002d4649450b143c0d1415580710718002c6031301c140d40d60031801600151810392071154031609 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 556889532 1250 556888282 556888307
    0xc060409090210080f04060f0b09100602190c03020d030311040902030103050613150b060f04140a0504020424050d180516120201200d26041208190219 66
    0x400026500303000042c8003403604000d01c0207111a423140d090740000c1c0040d807c9084090009007500d2100e0900b00e1042d10382071424011080144100300a0480101141884d80c0b0101d1700005000300b680c0c116001c1c8035480300c1ca02c1c029402e0688032158402100c0d0444002d000034124030720010b0312541145405e40c03c1200192000c0ca5440d0f0704801d080c00b0808000030003162001c0c00d1000103d807150305004c030f0064060a42402100400802e0001d05a030b0450303400d1003003120480d03655030042d44a60821040740240e00500e515120050410010928046a41440f5240c00e0404604000100c0100015544048114640464002c0c10402001310130084001320141c120610020b040c140500c0081c22801e14070301078100301400d240c00080d4101020b1000100403100207864101c124000068450030b00c0c8400f2080d00b070b160f650b07070600d4901c881400b00e01031740d4080c1c03080e501401a07600440303d444e000781221a000004240c207050200003440203103203111083d024424010f907a0350019107520030044 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 556890782 1250 556889532 556889537
    0x81e070305040909111c0506010807080d0815060403121209020609040f0b040507030509070e0114090603150906100f030c0504091518021002030a021c020c060409090210 74
    0x1052000081c0c012090740c040d56202000081d40340e07460704103540243c2410300070341d800824440540c0d10030b80c4941c15219200e40124215906070766103d1845a40d0843c81c81082d106410801d403c1e031015214050740740e000b0350000240c4880b800b03c603000500701e41c465030044801c05085c40c00c254003170341c10201c036a8180a00c5101040115020f402141c154410b03856080d200316660342e6013041c10106d550241220002c05842000325180c070038800b074010441568402800e11031240005142070007151428180d540e00d0310100000c020010901c440703482d01401d115403501131605001c00701c0642800d45403151000c100113000d142042010a6580c0744141c000c0d04a00401600a2011940f00480701040b10400e0300c0c0000e400082e401c00d0010040c10003d003000c81810a1803100e0039116048075040d00a008a404845602d20324109030317900d124902d642d0000d40c01100605071204070741c100741c2c2410091401560503060004000038019170050700300f02c00742641c031b10b8040290b00300b00d0440c1c00007403110b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 556892032 1250 556890782 556890787
    0x109050a1b020c091b0f030a1b02070302010e010516030216050d080304150b0303040602071a1204030e0402130605030a0614031504050a0b0a020714010618021b0a081e 73
    0x1010003903c840052a0f40c9002c0c1480c180070448881e04454010b1244641030a50390710303000102c4502c4110392080e2981c0d94a01c1c2071502c0d84200158902c0e000070740003815002410903a245a0040d03801da5504142d4505004007448145170010354204c105004074400da020709020400c8400d0103140e904150003203406502c0003a0386c980092000412030341c106400680d4411101520030104000d00280714807141c0501000c11b001403d240c00013448016200eaa00d003001d0304441c540389192141c09011030110340d02840c0004107000c2030103600000042d06002c1d002500e805800e864040d001100c90b4480800900300004104490207036119100181450a0b0112540780303400f80003d90340d09001c1100d00c0d009a030340020508022040000601c056400710317045049290580c40c4500035005030905561264203c4203003030b01410107216003c2592220403000d0b96541000303240400942052000041c50480510015203d410400810084900c2aa0420380c1d94442650201800d1860070700080340c0c904c113 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 556893282 1250 556892032 556892081
    0x1150f05060706020903120a0804030e0913030e13150e01150509091f06200d0918090b01140102101e020a120f0203010f060516060b01090e0109050a 65
    0x90307804841c20741e504020050384484100f400203050200810b0008404000028940ba040b40c00039981e034840c2c2c0c0a501c0301c50b0010000c800380403040b502256003141c43d084035802c010019015060340294510050300060b00011800d000404445069000d0703031841141510801848150100181c003500f0400303e090f84140c0e00404c05070490017045241d034440c0e954000011008002d02403000d80c074540d0b10461030003195546801815807182c03d42141e5001c00d88446d0b40880010003c1c42c41c08130491941c42c000d8052500701905400700c1c502c488540d4171034480d00100040385203243c28601820342003104168030701c1e0703040001e4039124915200506050a00a403254401804c3e00c085d9070707081c008040036907206800c910840f0401c0c000b950f02c281213444c1009a08440c90907070f020f18140d529079005803000303941b0740e0300035100d60240b203503400d501c04100d40242d00040d040b40c20020301410181000d0303244a84401ca09030f6074000c01d804c42c02c102075442c010004450f02c1c0340902d03c440210070f091452045903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 556894532 1250 556893282 556893289
    0x61d030f071205161506050f0a05040c0c02030f0f010e0a170906040305030c0109031407050717070302030609030c01050f0f0612031c020415090b120403020a0b040501150f05 76
    0x20140c0191140b402056031000e124051001c032920107540c2c2109000c0d0720814031340612024112001d004095152090104d158200f10b0501850008014540000c051412041101410600e00203000704560303941c0010040c2c50410480581703034015005040c1c41522019042d00315070b000001c0e40503551107000d062010a00307500d04c100030100002c1035550b540c420040410280d120300c1e40001c015201c0003844400410040d4041d03107102c0c0c4240d03611010800a00d580b000346018441c00546290010f4008100c0b0422030030601d94543d07884410307106141e94030b07000682010021140f0200343c2e0000240c40032211f20038810310794001d00c0601c650306107040c208580b100e40e0300c0c01016680503082950000e01c801d102001500c0c420392003000000705089108460360040c0d0050b11840c1c1410900760781e03950300a8020014001620004100a410100044205500f111000d441a0213601a540140303000c034400801803803155000d42c0000c00c02c590030b110216280340d002e5103c0c8001400614043c03080b41d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 556895782 1250 556894532 556894537
    0x150306090f060e0a0c0c0c080c09060a061227080d11070b0402060d1b0507020307090b0607080a0c050a240b06090d020103060b03160212031e040f0f061d030f 69
    0x1030304d280300107403003040090240d641524204001d0302104014900041d0700b480000d41c199000ca0a41c0c1d085e9035070303e4040520144130200d01034500401c1c90704280c907404000c10783c00f040c0107901c0c0114060a0302e2842c0800c038800035000d03400341e640d440000749a0500301c5c0180107001c041e12407401c0c010700d4140725850f407008900018200038498400003d200140c006150000d01012411030401400240701c41c00262087e0700c003050407402400b03400740c001240c0740c6503c501540c420300505024504006541c03505a0360384030103a00824494001511008030f1800c22209000034851070341d402c040391640750000c10074000c80304c41e80302d034030300704060700003140c4860060718500b0300e00b0741d0540e0f41c0d40311713500c0143c01400c900c0d0001195900d02000f000341034018019a040d8051207074080d928040140b4041540324401182e000841000c4114400c1200c07607880189a4094065134400d80c0394201540c500c40b26140d40746098685035241c440000400c411403000f100c80c2550b040065107001c800d0083d003041070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 556897032 1250 556895782 556895791
    0x70c020d02090402210c190e16021203090604021206060d0b1b07150b1207051014071a06010203070308060603071e03060305120f0d0c09150306090f060e 67
    0x19001030003c6030031500c0c1c044c52407508840c0300c080000524054800355684e03903141001d4504c03803184060802c2500c881c00c404e0b1415070328002c106c456550b4541034120f6010580020400440c807030542407413001200107025500030171040010b40102d040600400102100480c200e40b40b580003541440520303981e0000c8003100070792101c880c040640e20481800c05191284903c43e84c401c50000d45c050070048440c3d11040c0320b031401304080000001110a01c501805494061700e400e5011071002d014a107014074041d20b2000003450b2003031241a500c9242c02642e08486012545000005c81c42e2400083c0d094030385502200030310085003070880c01c0e20020716505025280d507008010020204211700d10461054014080b45030712181d0001852030b0040050141e4803003038909005062090000c21801c030111a000b41d20311b02000d090034040e07244280180244969841400142400000c0340c441110700210b4065644d240091440d14142c440c109990100d50844507943c40c0c14002c0c0000a00c100086400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 556898282 1250 556897032 556897039
    0xc03071b0503060a0c050a0c020102070801090305031905010509010b03191a150a090b130306110c01050a023f0108010609060f030206071721090c1917100f02040e070c020d02 76
    0x1038048d800143e040501c260000e0ba059401d103400c000a01d50008001e40c001e2040c0003048040040c1d40c0040d01c101c07102800f8a60f07200308200010060905000044c40e0001c9003165440014100505c540007190012010ba003c4003007410b40311051031800d0a103c4050449600e61289801303181500140f96141500071034186460200d1a003039504e04009001014550241c0d00300402c1c080b07204154a0740e040303031032511155804e04c0b00103071070400540207403010102070342150b40b066108203852910684081105130f169070081901c40190311121920309001340b000e5400010003a06100c078980580c5d405400640100c0e508032000c00042e110300c0106e40303180d40c01041c40c100f14000d00135105910b01c261040c02d80d41785c003000801840c103040c09030200d0184000340115000c2541740014081d0340740804c0103440c040d68254804201c0341c0c0d288801e0303001b9031140384d050741c00c803041540d202021540444184a02e91348d0104003405507060940b603041c0c20909609000c1c01c02c0000703074009a015400810002d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 556899532 1250 556898282 556898297
    0x1b030d0f050d140f090c01081b0403060608031b071202060304150c08090d0801081504170c0706030b030d0c0210090803030a0c0905030f0d031e1d0706050f03010b0c03071b0503060a0c050a 82
    0x270340c020841610080c0d54400d005201260381c500740c0c1552038110034070390681000c0c0f000754141c02c2e5100041050071038107580e88040c000320b0540c0810802d600b00a1003030340d103403281e0300c508042c404262040328040728641d01d41004038201444c2e12480c0000b002104410b10120b00014042c0e9039000503401150200c02000340c0c00d40d560303454021030f12411611802c0249501048560404002041d010705a80c15039070100000d604210401d80c6e01c907604450340000c503411080100141c00c1048047c10041c5241c100804241c0e81c2720401455a030080b110440500d0b512608500020b41c0a400400100707411801401c42c41300e09800a901e0701380041480040c50b0782c504c0c01050071800085c0d0503a2a01d0b90001c100301c109001d5103c1a130102107500710b002280510040414854020340c141c44852080c01519400e5a0809103a0016503000307a070040311034401401040009250116941010101403c103810843d1a001c28180740460144c40c0b0b07180c09007009050740140d41d1100a1380d40660540c60f1490 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 556900782 1250 556899532 556899571
    0xe030a051b0105120f0604140105100f09150c020f031f0203070903020a03030f030c1d060f090604031212180326090f1b030d0f050d140f090c0108 64
    0xe07040d200c0c0c5050300130b00308261400c1040400c04c0300c840070302c6503c1c10707901031000c424005015003000c042400360a6001d00200d00b4884250300c248108110183c0504101408036100c14002c0703440202c2104c50300026000140000450806011000e04444103400800c54902c0006001c3d0044d044640841800d581c048001800c0d00e1041d24001d004540180c0000d00700e075160709000307080c5a15680c903000803908103080034012901c02c0c0da43e1007090619a0180100e0705043c0104655036100e00b861100c0c000d0148210a419940c54000300300452180d240c0316014075500c03030060030102c04079490071401854810f8500c00c185d40c0401104036241d062a01c00c06c602d0f0107601808c0d1501140c0d051194411242e0304002180400203401d10b400c00d07100040b01c103414601c50009410017000e0058035019004500f000074602d0082d00340c10350290903420000e0500d02e100d000c00040304c0031151070990078903400d0b09000d5200500c840d06a004054000500468288540080e000d03107400313841c2c17541440c9800040c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 556902032 1250 556900782 556900787
    0x10052d0c01060b0430080414010810031707060e0f210f030f04060905010e0105010501090803030108070b0307052203061112040b0a1425020703030212070201050d0e010c0e030a051b01 80
    0x101742c6548200210f445607228420005882e6500f10401c0c0030403401c5001c544d0040e905d031300c40d40071241e204500c0d640e0080c010035030745000d41010108403142ca8503a50b402c0300b180010701028100d000d510004110340920304480e48c607003183c1c4a40d503902c43c070000c10521008040c19011254030200e100000c1c0000c0d00d45180440081020080c050200d520f401311800750182c041d040181229026a10341c1c0361161540c811136201d11083c880c0d004990300c03c210401452082901a650104442c20410309000c0c1701103403442002905002005030004000c0f05108100e80e0b07110708081c011441c40410b08011412480d2580c100028101070700c4025424005006110701380c000c610b1899601d040200c1d9800c2030108070b0000403c040c2c91204401c1500d07a481c04181c8001810301c12030750540e000744622104030f0360440f01b640c89150240d041050411603140a416075000fa150030050760f000000b51425080300007022031310440091171003504021810b40205100181d108610f158842e1030f4600300074000c006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 556903282 1250 556902032 556902119
    0x30c05070204020706060f140612100503100207171603110712062306091b1902060f0703020c070e0a09060e06090d020c10052d0c01060b04 61
    0x2d41c0140000f880a0030407041c1d40060044030482c50034000e4880d00c440c03450040381702940541c0d422450170f114641d0b409216501c0c00790820002c220f0700c1c1c0b8041c1c8603000329042c0b03000d004030b1500e11900000c2140c100810000b100004000c1d540c000c0e070801d4000901484036101c042d81c043d0401114145400400c58240840001448c10754143c0784861094608140075001511681e100300c0310360394449403000d16054080344030359001030034008a91f881a117944d81140180680c12100c43c4c0c10302c48414400c7c0039a11802c0ad9800c1a001054181740c191640c5d41c480000a2184042500600c00251070704400640301d0240c8030b110310105602c0d0f6501c00b540340101040b00001d400349050041015008202107040360045114000355482ca11340d48400342d9541c004584c042e50000d40c601003000000748600090488404032488980c2c10080480c40458069000e4852501000002580300440c15007441410300410304142c0325820107103817800203942c6145d002c02d0051000000d40c812000031007950503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 556904532 1250 556903282 556903297
    0xa0b0d0b04021303030311030f160519120e0c13021606061410080906010303030b01031d0d020c1806100c06060e070314150f03211210060f030c05 64
    0x1007103445081034443c044039441e0922041c0c0200f850103c12000c0b061414003228400d035003410102940361580602c3d0804a529041c484040040501c19141c04200411800004880030f07a60003082981c0c44840000b100c1404080c1002684081c844880544030150b200312101c02c050401030701e0b060211001503c00b4014040209243c2c6005400f10f9030501c2c15280e58460383c0c00f5290740d081c90480040560b03101006561031051603219600400009220342c2050000c440185404180b000c00404001601e0040c00c4610000e5084100e0a48502e54100314406800604981c0d1a4541e05c82800b2150b5000c2c02600c428051014002c400340020b01070550b4001c041d0348035604000f0280c0e02e0110031240c0c54269a5040000d041080703400782d03540f800340c5d450302510a080182a01c0301c81c010230081581c500c00001501802816000b00d481d9100116110b900560010700d81d07504c2e9146400c00100c0c420042c04026890140070043c00903e1340002044584507650a000590310b1685605440a014107031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 556905782 1250 556904532 556904539
    0x8060702100e150a060e0601080108071413020d1d0d0912050a12080601020c06040315090c08011802030d020a0b1306110309030711040621060f0e03120703050103020a0b0d0b 76
    0x1d003805400803095014400301c500c040c40206c0544caa000046444104c00c1c402c2d0325a99115060500c040311300070815018681c00107117501900c0034100d4aa1050760420707030040840950f01c015603500112024840c84c00102000c001e002003004910010b8500b44035401003901d2103114800540410800300980d031440c82d04540d0240030022103120040c0348080480c0c00e280117005e00c030b003400d03800c2c14940d0545080da0b5004080c1400c008000c486600104460801619100c0074110000f07081d00d800e214080b000c1c0020000e90b0b58414960051500e804000b00303130441158060103a18020a070488010380d00302000f400c80c406d003603641e0f09009018040856141035080c000000b800082e400000050403842e1240d0500041d03a80c40e03204100071a4402c6c420700c858002c50002e00301140b81007000d014000d52181d040040e401003515403070341c101d44034899000382c5544001281c010360320000c1c00080d0310000c0c92800303014540c156400b0401c0c2c1d800500c54544181c2d00482e071a181d4940d640c0182c141c100015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 556907032 1250 556905782 556905823
    0x605150d0509150f090705030606100f0e27130c05060a050720012c041e15170102040501140d1d03091302090901050105220b1308060702100e 62
    0x1a0742030441504196000d00c0c0031b11039240c0006035400d0100d08244140001817090203040300030001138440b118106010300820100460300ca04503958442482107112064003a00361080440301114a02e0034040c0030381044520001d8040001001030340d0410a6520039242d1640300ca0a100b41034070a4001e00500030b040902080818010071031840250b0440c900036603800c44030140c0034003500d1801400340310380c08148055103140c400c0303424260004407070004d00000444420400c05418000c850040000c03241031022408108040d4003e00d2411200003486c10003145001c2c50440040d0640e95111010032401601003240c06940b140d40c0c0c080d080c28090141c11304605443c00404984030350244490501c0348040d9040d0340075840080c8299a84075030040d09010141e420400107440a4002d803007140c190f148070040c103000040c9414041001843c01000c5140c41d0709402820314040400743d000a140c9a0051003049400c40c0d000426060f0b4507207a040005071069681106400e0030f1040341264901c1248 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 556908282 1250 556907032 556907041
    0x30c03090e040803040c060c050c040e0a0506090616020d020606040c0e040203181b03060415063b090318121e0601140109032a0303050901030605150d050915 69
    0xf00b4005520461041e003400030401d0710344005031401560807801411a038407981c1e1030402ca00f03203030380b140c41202041c00440d1103180382a92003500e1b02004680c00101c90b04100240300c0d4000040c14404502c072a503001518081100541c02565401c004007402e00c60382d114840c52480d14080c01884201400181066559141403021248000148501d49400e403081c10356410380d0380e00d1010180445040100641003030303121500e41040310316554503c05140d5643da500090540c81c0302c0c1050801003150294141107a02149101000c540c8000508a00d49801020031419080110454842a555000411401405001003400b0200b40100000030b03201d010304204004545804456103070000d1400c4135166070325107140c004400074003e14030340800c2c1445070500014a40c190712a90445244e2802c81500d2401d600300c07081c8001e0341d4001c2c0c01040001403000c5503940c0c503005a0004e00420f41702d21102e08280b0389800b840b840f940550001035030b0340d80c021405454061180200c9003141071000b1070141070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 556909532 1250 556908282 556908293
    0x606020a0b060111150c0c03041e0501051306110106180209090a060e0601081e0103080a12061406071103010212061801081c020123180a0f030c03090e04 67
    0x105560a03110401c440000400d9588a03100d91000c0d034803020042e01000010491011420401401c000c510420034820500c00d004104041d1004101c145806012545403100040c0000c0043c3c0205040080c1081801e42220000180108843d01481c01c40303043d002013501a8014100380c0c104110f29404094240d14440c825005400c4a000450b0f240910340c40d020350174800c494061003209013070603808000481960162500701d501100d250402210142c28000048907000240c01c11503c600010071700c0d84c2e10a60020250300303103000b85a420044135040c65142585407180d0108031344130f01d0380050518200300308240d1504410901500035500d800c41940707120000001240c84074010003040341540e40400798016198125441e10029000ea000c01030001464080756000c00410340d034071884960191407140840000303a0f40516000c0141d414100300030000110348400541841d40000002400300e10103465880c005503050a1200d61811185029104124907030301110000c418075040009004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 556910782 1250 556909532 556909543
    0x106090503010c02010b0310150f03050a060c020607080103150f05090601051512070e0604120302060702060106030c1403181002070506070305010b0304060b04020d020f040e010f0e040b0c0706060602 87
    0xc0085000384407228080c00100d00700c40c1c60078013495240d884003030a0180340c84c643d0300440b42c092035034045c801580c1d100d030718880c00e5111603442243c550307018560510902c9080d20400510460a02c0a04018144810001c040c200113010282c0128400150400c20407050303481920071110901d0107000398940061800e41350307182441650300a241448074210004011000c0f5034984180322070b0382c0307200c0e10b0f1080c04a40000000384002d4201c0b20401c404911a0007028003003042c01c0c4a540107002620b40f0310002420300e1010f030301140505062241e00710026811941c55680b80b134620b00b03040d880341c0c2c1b940c2010607080001c2030814628010443c0b80e1a400c00150001d080283c0110210380d4903480d464000c03421200f0901c01c1c246c0408090001c01d0000e8510f420481014100608c05402d10001406c210b04a9016001c0c504800500050411030034a58402c114018900341c0c2c01e0741d120358500400078210b5040140300819412009000640d41e44a40d0180d03803d40f40c02c0441040401d0f01c070301d8080d6485 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 556912032 1250 556910782 556910789
    0x3010903020610062102090102070905150406170709150f08060702070602030a08180c0312040503062a07030c320d0504060c0804050d061e020901080402150c06010609 73
    0x10b08156000f20350a8095017000044007801c0b15610700325000740303000d080250403141c0014114024440f0005d142046401100e028803d0441c0e03040207404000100022610254032000c0d00e910780015102c84100b020418a00b2200114004500104540c00d48500c082564000b901410200840403520b90070004000d07100d10300c01e03003c60346016101d00040c1d90f24010502014006018400060340c023900e6403d41aa8420b50300084505001310800044c0c1402e4412003107d200d202d011904002501e0200102e81e0403440780c04d0114840c80d0b0000d04044001281c1101d28540580010400101071160801300340d5950003c0c24404402003e080e0f90240c00c0155083c600340387e0304600c11402080c1d0119011030b040702c09841d101d2416107405030541d40124401c2040e14281c00602c000541919810141b2815070b00c520301c0011542a221918503103044945403c100e400d1040c0f04061950344c10903612030308a6012600342007810b10910201410b403003040741c03000050040c080000b0301c0a810494a200340c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 556913282 1250 556912032 556912051
    0x4030201050105100e0a06050a110f010507170411010c08070606030501090210082716090f060b0301140910030204020d0e12070c0902031b040602030a02070605090306190b030109030206 81
    0xc07004c009421140682032260761944000381c10780410403d4054001004810a14140b160346119200d840038285441c00e002c03510f4a94640c01040080ea074009803109841c210560700403940d051545400304000c07400140d090500c000002240c041c0f011090079150030039880482800581d860b480c2070741c0a45903d890881c05000c1d0403450302d00c0e2a0080c01c196109180010b4403070400070b090a94002c103500c240c0412280e43c0124040c000c100c0e02c0d1044100007410802d000171400032202c02c90b002c122841580000c0c00d680042c8014003501c0d100c002ca00e8440402158071000756154440d181d1820302881d8802036102c1d10000320741c2d80326802c680150007100424400e07a500561a2041801c20740300340800141464203c1200780424021076024540290443c03400b015610030003c80e10005c8d0340960400c80c0542c2c03000c54144411581080313240041c10f498036200703040000318408a44c3c0c42602a21510300b4080810701e54482ca02070340e11a0070100b800400034414804c26082c0a5143c1c1c0702510003040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 556914532 1250 556913282 556913299
    0x503040303121a0102030a0c0309080106120b011712090301020409240b0319091b030c030c14010c0204022b0c030605090405060627010b0307030509070f09090f020904030201050105 79
    0x740140540034800a0f1041071300658509040351400f15400080008110280841e030ae6020425600034469480902000300c00d036408031071681401203152405a0001c51380c950440840355505130003203682008207442e0544143c40b6240000000d01a02807038005d41d039018500181c6401200c2c401c054202c2072030000710094034103500d6881c0b041c0d59110840f2030000100c02014200d8150210b40d01101035140900c5c2d02c09128480380501d101d907a080c0d58815600c05180c801c0034030034000341042190042c6a1418201071800c081c030000780003448007c0000e40305a90108013035035503039a44110000d900851800452482d40200702c0f01c0e004007031960300d81c00041c0c940f075004105811f0001200340916000760080c03a2035078452041240d800744c1280e00c100052140e41910201d041d00c00b0106002c1c041c141515500d038903040c14000c0072900d005083c1e031220391150404124103c6141d0108082d00c010100c0414200c14600380b0b44421003038000d0003500000b4400800060503810b52180e41130302c804599501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 556915782 1250 556914532 556914551
    0x3051b010e0a14011407120509031006060804020409110d20010905130207170d0518060709030b06030f1b04060512100c11251d0a05060d050304030312 66
    0x1c0150010b00815540310140025000f81d903004250101c810748612940601e440d19075a01d065007221040202c4020032004200350b8550300e03060042c008079482d51030042000c1d0b8a0910700411600d4050801707030203a0303514401030041c0246000c04800802c030142039a001a2035900d480e003014005000a00000d01c118003000000c0d41c444c9441d2422101c0052209209041a800d141c00950180f10111089200741481c08a11411040904201407050b400020a4580341000011b10380c0705041034180e6801850405c019140c20444400c1500e4020455026036900d02002c2403030052458150329540c440d80b140d080055200801074562408191000e00c0741c15030700c500340401c2440410041c0b030942c0040701103440c0508103600c040021100345c0381032002c00000c84c40e034074200426040c0000c01031600203c90f944045088540c0002003507030100098906901240c1032500c10170150540c0191501c0f00c010036002c0e96030384403141c0307515002020f507079440c0d61340d10b030241c0345a143c041c0d440130f410305141100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 556917032 1250 556915782 556915789
    0x40221062502060408280801030506060a0608181e0106140108040201020d2a0b04020405070e010c0201031e060e0a1505060f030709080f0a060b090618070903051b010e 73
    0x81c50324255001001c041d19030b903890101d00d4004803075100d4000071a440c031640480701c100031030840c80846e4480004650550030180c1c10190010480d41c000c00041e6000c001141e4040050b03031b030103090480000704d4120300c0c010103400c008001140a5501d003c0c42440c8071a0078065021000710f170314400101c00d00e14110340c0196046581100c01a015811131500d8401d220301810050103010003c5041f84181b028580300365440f1442c0c0da0f41580d41c00902010402181003030310070142c00c1144c508004104d983e080300020101c84003804024105511002410b100d44030520918015100400040c0030540e00c0c2c200300805c0138800c035685402141011901900c240d0489070000070b0f240098203280c07401c1031700c00c800440c0ea813000c1d09603000c1018045c40042d902c4400d2000180c8400b1640103884098042c0c100001591600800c1603c00c0ca40d4906100050351032260303a1654010035007100e00070b5030340c008040e11480c0942d880500075018007100301d40d8600e21003102030100e0200743c0f541e000440400c0240f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 556918282 1250 556917032 556917091
    0x616061e0c0e030f1c09080d0c0b0714180a05030a03080402100503090a23120a020c0108060a1a0706020a0e011b030906031505060d0b121207030804022106 68
    0x70301303003103802c09181c18001200315490043d0380151401d041d82e140d1741d54688585440340f460401d0001811140c165002c08c10020802c0346c008000e807034125205002c44489078017600c14900c20010502c2e412050b440e4075114084040c0092138001d055031000380c0c00b03003009045000c040740c0807403045c1b051500c042605401034040d00c0c0907483c00740040542880d01c0c0d0303e0000c84851a1190200c035168103248602141c401c001d55543c1e550b0900c0a03030b840f2044190080d00d40781c4242201414800000e0400800307480b40130b2510115a0b51042000310b62001840c213200034820580094001c500001e035111010750420f201c0025580b080e82d500a40f211000c0d810080c0c0c200c0780d90003e0004520f50410001c19109401940351255460fa100d24450742d12800503440d41e1158114828403600e41c100f0402c0d80c03034910714080040c00e8000c00340c4030121603040d61412502c01c080c9e0040501980d10003041c15501d03282c1496a41031001e03003465164403d61201d00f0b1f0740c0d150460b46035825100c456440c100043c6c0241c2d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 556919532 1250 556918282 556918303
    0x906070210050604090f0302010c031104031538030706030b061803030c010204080105011e03020102060112030e09010b071205190c1a0c07031209020616061e0c0e03 72
    0x50254003220311601009050302030302483e8041e85031120031700801c1e0004860003001e842a00005011041c220000d810f560f02040c0c0f540402e4818081000030400301d1100700494980440f0008210800c0880ca03c110f03100e01c400ea06070100c601620900c400c11030340400c44054ec0407000c035060341d540c501c001c03810ba5048440b81900040f003440f07504408010003441c0c66414400505582c10100c0d04007285003280c010398001e0f40b80ba03452380700400050325611038070f0200304c03161140c1864007801c2d600080d50b01c0750f061103a02140383c4520808410b0510904400814400c010404512940d4401c000c500caa04002020b0302c20115000a0314010f030702031401c580071104285025001030a07444011b440050341428103441c0010396080040b03440180d03140342071040d5010440d064035550320b420001c1c1404034040d0b044007500e141c00c084101503070b1904141c0b1000d40142d51058903c030070601c0e100300940340c8064440349c075446140d002e50b1594000d4108400b54000d03a03407180f446190310000c069441c0c22908 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 556920782 1250 556919532 556919537
    0x31f0308221a0304020d1209090506090108070b0309030d0f0b090a1436010903110a080313030c172d180111120a1413062003031806090607 61
    0x5014900041400b001e19071040c001844558083e0298640440080d0644c00003030010381d21107003d02610403c1e1049030b170810029602c0780410b42c10245c07496a180c1c81401901c030210030100c000390041e5400c2044a00118405000344010403c2101400c05490441c40b058819100c80300083c1c075146c0684aa1610100304030020070198130380300c20100c0300306030b24400c1507559031007543c0343c03800204008510412400880c0000038445180c0c1402412010702400c60845c5400a1143d080400d540800b600e400030251041071002c545149800d4513440c450000081813529000034104d52058284042d1144815115204188882c80711181c8100340c0b1107100007800201c2844401903000d03d480210b40c103268181040c02054803020011490900c802d20015813664000a03480b00d9168403407040c08a008640c145030b41001c1110060500d9502e060080070b0400c000c195050b07411050a1000428900000082c0d81e581c0c02d00c0040c034100d4019441041c000d42c811080890b26180c00001e600c0d2040410341d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 556922032 1250 556920782 556920809
    0x90708101407210203090a080304140d02030c061f0302120f010c030c09090902040209060d06050f0108161215090e01060807180209060d020309030c07050a0b0f031f030822 75
    0x2030603d00c0094001600310002c0c0d10a000c66500001e91040045004c1d501603400c0c0f4585c3e28a103010680b42c507041d141a0011504207002c03002c420000085d585402800511060b40d40d580300d0802e08a1200c40ca40c0b01a5010070940014010b008010800c1c1d85806d00c8240244a01c65006000b40c09480b100d4001c41c00141c110310040020744860350140164510080c0054038040f071520000e00d154100040881a49680b41010481c524040501520013202800c2c15906031500d4101071841310396400031541840321b02103007c1c0c00b40d006a80300d940032026103000c440c2441c2e241c0d8601c1d0010041200c044009601e809404a4440030000740082282d100080703007000030852800803406504205041500101c00f401800110b907514000340d482a0a41c500654660481100305490728074580d20260203074208440a02a441e441c0d821078002c0d15a100e1410b030b50340c44d4130503060072464680c1807000c2e002c01099000700800050030020850b246a0300301080c0009161035a043c1001081d2040e90005483e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 556923282 1250 556922032 556922087
    0xf1107081908060d030e0409240b090c040306090f0606080f10200a02010b040c0804261e04030b0f060a0602010506090105040b06122a04031a090708101407 68
    0x301c6c54446285009440850546070b2982e81281604250310700d1a01c0d070149502c184103201c014824004114800c0351320b240e060400d0040e03130300c0ca803140d17000280c25180c80d1041b800500c0b500204c2c0004031503208030b0030810b1a95444010b5225030700c0318603500e003900a8548146141c541070140f000815220702c050b8061528070b88205186903c011516015035496409001e000d0fa1544235501e6050415103074030340c00c0c0c6080d1800e081c3c00b401321081c171070780540c000c40c07000c800101610641d884541c0074032102941c5842c0107040402070140d980002c0c1600400300030441b00d2001d120a0500441c800d82d80c7d54070207919100309a090b0f510443d00c0941100c1c4030001080385140c203800c0a44404000303040305141203100c1d19844001d21048408444403110301203800074000a030340403211640002d00c241c60400341140d6440322035070024a003074000c62503d00042032400c4000d003d010001c01d00a800ca030341c51410f5407a0b00018006000f106480d41c595040011095802464a09169010002c104c070982c1d40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 556924532 1250 556923282 556923287
    0x801021e0f0a1b0c0602010b011413051023071106040e28020d0c0909020c06060925081906060e0409051e03040806070507020a090f1107081908060d03 66
    0x585183e104068010643c503d02040381c540b009005016554000718410403502c0014244d0325880e006130800c00002c2102000500100c0541801d070354048031a4040c40c5100b20013119443c0340c50100104d891041506065489205002000f0240c0300d105502800c10b83c0c802080024080e510400d1800b501520000395030b40c18814032041d4a401e090007207a800385004607602c040b600702c13110704611103946e50001100d0503000b840c04030013031208450039450400030440e06622490083c000303c0c000c1c00a5404134186d082e080d05064001e421006000e245044260402040e0034829200d29210303200c03d0f8003a400c07001003801175000303580c000d40351420300100c00d02c00e000050841c000300780c4040c02401030300303514841060365640003406400d00035038a40703007070180a904200010f07000d041488401c001d41401a1103060008080780ca41c00d8002174018100f090050142c0300903002035080142c0004c80108220880340604004490301480080e203503201e41082c0c03103011040d01d100b60300c03804c0302591200003407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 556925782 1250 556924532 556924547
    0xd080307030f0906020d09021201111b01020f1309060518040803540a02060c0a1514060405040302031605010b06121602160b07030203090a0801021e0f0a 67
    0x2404600007840c483e4a03124181240c0000e880c13100015141c4201c031003903251100801c4440100350000300f110a42c00c5580c00064031841c1d40d0001042c2c1c5001061142440c04c2d415580114128440207999007039040c9080300314041c5010700301d00a45015000728441c10013030320004024120b414090340646507078031400b40310b400060140c40c4035004c035041031400a00c0450a480c0180001c100c5004104c980c0340749041c0004000000030340d030b541d12042103942d44d074000740143c00b042d0151140c2c4d90301c980c0c2e1502c06e8203040b000840a020a0641e40e00012107c0f00c44c2e000e64400300700780b80c4080b040d454240c00c0006071441554040c0041e070052004460450203800640c54940c030030400011340c0b882a00c04030b68203411021000080405100c00c03c01504452400d100045141d48060f0922002d11545004000000d003c3c905071100d01103007000030036008004440480c0b00003000c40c0031495940715402d01030b51290792825290000010300008401300c00041d6a0b082c1c0311002d40b14201040d0110448455 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 556927032 1250 556925782 556925801
    0xa0203180609030706030b010219050c12100203010b0304060c0503070804021903021804061b090e04150513020111031e090612041209120f1b08101a0d08030703 70
    0x1500821600100d50f8080006100905541d100407400740950800a030400030804007000c0301441c480c14040019002060000e004c0008861103a1541c028403480e621382200300c03800c1d9844920000000c543d84082601941c441c40c0f20342c00500600000503001c407500d020aa80e01c0d00400c0e03420300402c0040c86c2822132202c1e4220454070301e5207065903940000301c2c10700080c00c212641d401003500380401e000090160f9105406402c043e049070610710301c0010217040d0035204980129901030b012404005020080c510780e0301c401c1c01c0910803030a00032250300495518283c201e0200d80704840070301310003001000703590040e42d0b4a40c1c504460491003040741d14503400400ba4a80c400d030200070707514401c03400ac4820350259008410204440c162107a0240c4040300c20b030040d80d4990784e072101010000d450940d16031152580206c041600c18910b03840c41c10b040e44c454010800da400f0340c50402004001d26440b40f40030700c0100309040c0c0c401e1448030a0001001410f00007500c540420400260124060b8101311000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 556928282 1250 556927032 556927039
    0x132405030d090e6607060506030a021e040f05071b0f0609080d0f0603020d02010c0c0b0a1d0f0619050f0409020c15100515040b2d0a020318 61
    0x2404410f8490300e4a0980c90200c00b40c84090341d00001c2d480b0210300700c0c410052891104040100300340b074101010301c5c001e0440090483c1e44820000d040c4d51400e22001000c141d020300f01000c0310b1065041c4040c1c084403581100e010390710b40407000131103200e036024072801494541c58000410030136081020302d100b802c1c5020360b54203074a00c50440018906110f000c0c1c01078007420015494039040315030f00342680c480c0c0030030a12007402d0140500247c0e072145a0708a100e039090070203680301c5000c4e24080c00c2c1c600466224001c6010003262805605030407450603c0d2a9040740010400500c40808000c0c0030200044403c1c1c005c0024001c08410b000364020341c0611580354141581402111000303450158045e030850401c103070b00401c031403c0310f0200b0451030942a02c4508444440c0c0b4050042d13900350301d81d03841424414030f80e5400400001862004440142505c40d51150359024000202c0c0400307214000404124000710700c01c2c440c010b002c13000365449501a079029519146e001c080c004038071004004403d92 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 556929532 1250 556928282 556928341
    0x14011515050f1210060201090302060703050a0b0904080a0f0801080a02060309030c030c03070b0601170a02030705070803040606050906090c030106050d0e030a0908010b0d0c05132405030d090e 84
    0x1081200e40014107030354042955401200e03e00704c070381c404114145074050310540e81407904c41000660046252030788068a440c00203550ba0b107101d00c003000b03048d070700d0940c50300400002c0502c800d014450005204100d5a900d80c0070403a81540303411551210700348a282080d4202070080801460b0490003590046411400c40f0704050124048c5415940820040800780d8800030b1880d080002c15081d842c0c0c0801d01f42001000228026030303d1021960040c0074908240d40007002800c5079014400344c0300e4083d0051030726601ca10f018603084d00204201e000301da100d080041c1c0050780300e00e4003500c440d12500b0004101800c41e413902d8400c1d103a58101107400c1490907140d0700e424150b210108040c001140c2280d4400c4a0503180901150848011081c40c40c000d201c05c2c01101c006c16100c0b0614400c5460544043c121a5401c017495070090000301049000001c0307090a120000c0e50314500001a14011015202501150745056842c1c020501c15007410b000c1100000d444802c2c041d40400250f998005040b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 556930782 1250 556929532 556929547
    0x509040f082a010f1a010f11030a0548070509040b0f07030c0219020a030b0c03040501061203080f10080f2d2a0604030f1401151505 58
    0x1105004042480c040d0758402460484503800b0074000d25442074034458040010258003c1d0302c040740700f030709480b0a040c00b001c0c410b4541c0319807148513444c031b0245502040e2622003844410080199101044e518481908034051101e1050721010031810602003984980c0101e001c01c2400041140780482c9c60340a000780880000d075911a8010176100d144102c4100d036942ca450740040600c400f001d0071100825203000707541148a9000188482400122080ca400000031440010300868485c0c1000303214aa0000c20710036040300c06070165004520400080c04070907100d9110548c00c2011580103000104c40b50042042a0185c0d030495401141d03050380000c050303480704030191902944a40010310f5502000d460441400b002c80090541c400b00d04002201001410b00d175640d9100d24080d13595011249a841c01001d1140c4803620520207004e04580d4580b596400c0416034810064015901c600300c0074096a4504018450103000c2c1c2000b032a0380703182c0707801c060701d440c04120441451010700c14100f0900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 556932032 1250 556930782 556930807
    0x412060b0405270d0e0d11060f0405090c070206251709030c0d0f142505010e0405130809040b3a050303073501140a0509040f08 56
    0x11440b07040f403214440c504031a01c1c01c8000d0090441c0d4030f4024640c0041100c800d00691010a801c110a0100c0e0845e000341c1c0c25003058030a9030000b500c89940100002102001240004040c000301c5004940c14605039680c0c00800c0c80912441070020751004007041514000058030450000c40c0d10912420a00051940d40c2c800028040c0494595041030104600301607181c01c11202507035103802d4a5101080b440d40d40c1d540c8200c281054000c0c490349841c0c0c00c800c51f029041221303604d20140d260340b1140b044040154035420000c5e500400f80020b1104243c91000e0901d405041e009404441c00c048103800320b03498809080d0400b401c070660050701c40e9200601580d40307100c480b2070032101d800c4c4005d880d5066107603100c00340000c0461085204c0d507036102c03d0104d280030040d02e034408940d040800c5145c1c40f0540c600e5003645260b0802d038040c4d00c6e107904030700ba01740740c0361100d13042e5004095480c40d8480ca07501006400f1034148225230384401d23040b0000e0f000401111541c403199200e41704150405a08071502d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 556933282 1250 556932032 556932041
    0x7020d0f0504080a11090112020303030a0b0409020a0902040f141327051e061006080603030d060b09212d03030f04120f0c0b0402030f070b0703031508030412060b04 72
    0xb5140c0d4580c0c42d05c0c0d003039245131250480c0e00400000c19170303a00c04400c82e40440d4807800024000540701d07030788019210391a1119045480c3d403aa000f000c1042c0300d83c5401c0c00c500250401c0c015540c59050031000820481c022480044600d00c1c02450400075402800038940074240e00c0700203c1e5800381c8003800112030402c507200d15102601c41c078007803e00d0308201c10203040d41b0200d8203030560090303114800340001c2406c2d142e400413f6035601c0c90010b01603541d0201091541c4a0195008103891501c013001581d50b8010010b0008080111621000403803500301024618013030304104000364000c907001e404a011b03c82c03c8846643d05494a0702034212081c0da800e230540d00201c80400c02c0c0d400b1101048100728000380201a0342c4801c1c20011a03003095010000c0040c445260014810102c104c00b25084d9501004030580c07419804080f10101078940304030aa40f5041007404074042803c100403d2908140880c114050b94001402541082d1034081400e0385601038110a690303956554006000070381b0b46004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 556934532 1250 556933282 556933303
    0xa03140c07020108101410050c03130e070e090c0a121a1305011a09040e06240105040e0619080a030921030f1d040501080706080702030307020d0f050408 67
    0x120340d2a62500c0c0005842d03001d00810128440282e0117052041058044070303603e0316207069a0750100105510001e1304d8611840c46003030702900c008162486481994071655081da01203444054581c0c84145081d2040740c4045800743d800074502001804601c4008003401c03084c0507034074000d502e41d18020401c200b141ca01610100c810030752103840c0e9032581012200500703842082d203000c00c540d41c17414050f0740ca030f481c3c010b0042810083c00a1190755683d04ca03007000e8013104205c010713104035080c0030041d50400000c2107042c9003504101c00100c3c1e0150702400549080360440500700b900380c1e40700010007031741c01d45d002001c1900c804220008124150108105070b0014881d03190b6a0350300f801e0180341071104011880604254550344540000641e00c51000150030000d4101a03408072060401038191800341071305581c010340b031300b400010100f1002803071a040f00c0366515510400e40311443c040740c4078401210044c015034410707008d1100040c4a034844650480742454410705041d03d80c160306044c8048040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 556935782 1250 556934532 556934551
    0xf06030b0f0103050d0801080304122a0e011512050621102a03050c210105090f09060c13030c08010b030c091303050f09091303020d0201090c0504020a0314 68
    0x18014410404104010907210546086c1111190f1600340915074038030580c0250311440d4901031480007003000d030220348410708100e01100800609a0344400c4c610040612814003203511881c00000d0100301c1010034490f0103a40d90390940240e0314036000c28050000a020540c00403107454030649400504480c0071604481d58018058014414001c5000d0340d00c4040da2004c01c840340c46000d00e00454585007200f00041900300401c81e5502c0746011149405001c0390810f0032a248000403041384103009110b8160340c8120342d00b041e2038403007a00316245c426044862054680c04280800d00410300c1e00017a0640e4006c0020481c000c80e00d0b984d42e00c581c4290395000382c80d50fa4480154460174a800e00451000c0d0409403209006890131000d01254244513232409001d2140004002d141300b1110401c0320001e40000d030008202d810021200c50a01014110540060040d122402420751040c02803c0c0002e40040341c0c844000e05000811000354081070410f811715a681000728240c8005024203803007143c416 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 556937032 1250 556935782 556935811
    0x3041a04090522350d051b0405010507050f031605100c051911060f01030308090610061d040519110c0a060b011b0c090f020c100f06030b 60
    0x419241a00d10103454543c07007204031a241c1c2d140325410f40e6085881c0c0c0d00041c06644006100311084420381e202d12070441e40000d00b40350b04803c03002d43e9004002e08801580e0030081590381d460690707911861062444598881004100099803080707014140c3c1500880c02e840000943c4d00300c591466100e8500207502c2e42c4211121f07014000203000001201c10781c02800c0c009032030700b998010320a11a0a041c0003a40780b018440b08586403203148180c0c80f031009482201c0050401e40392040c5461800d00c4124001141c5800084400c4404907106009502910244040d80d00307104040c1c40543c0d101060300002da0000c0041c0460343d8071800340a02603210380404000c074120b4100c5031700580f21403001c2c07001e1080c010410f41c1d91401000440070146900150000766400e280d41c0100d075641e91101d019104280b000c40d40d102807101101580c3c08075403a505040140c80302d030b81e070004243d018145001525410504103040034050940042e03115110102d40040c200780c80742d86404e00818203507444003500811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 556938282 1250 556937032 556937039
    0x1801030c050f0d0b16090e1e060102070e01150c020d0c1809030c0f02060f040906060f1103030f06040b040903030209100305131b0b0721030501050f090903041a04 71
    0x70b0042d00c0d07000c01c003a02c00b2241107045450741c01d07041c070019050b880b101580d04003900d2214440d8050760040c4c8500000500c081c142050382e1102a080140045c2e4006121000b090a5600003e00042210041c15070104203a103882c0300300c4040801e50300c000e0184074a020814006950302e0741e000038410b02c10b03048540310f02c0c04e1a01210310019a4481c01d41c0e940d00d410f418001080c0c0002c5101055035000308405040192480410000d028995030440d021202090114400710103030400c00945440b0707500c81d83c0c80d00c04400e08650342401e2040c40c9035030340c2082001c6500c0d07a603518031440d80014064004034a8100d003102003401c07290142c401342d0001c0e6020804105038680200e040b2074280403480d09100500b0b001c0200051124013820007081c003405400744034446640402c041008280244030f0170f40f249001c1c2010f003030584003c5002002042004503180c0000e010744a0380d4180c4070b001e02044150300040040c400c1c0142c0c040c043d02c0c0544014080000e501102201d5683c150340c0d08081c0070b4070b41c1d2a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 556939532 1250 556938282 556938289
    0x604060819060f3807150b03160e0a0204060e0f01112a0306010e070804030215040c030515070e0f0a0909061b030c050a1d030706020105091002040803040506091801030c05 75
    0x943c071130060502c020115445a402800c09507a00345410a910905403503102c2401740003400c00400090b01401a1400c0b4800340b807180b0f0450044400380300000c2c0d0305a485202e030304200d12650140c5c001240c96074001486605100208a90303005042c100408840c1011308454a0030f0501300d8600b0300141c0502018002c0d0100095030108840242c005100550410890f4441c650005100ca01044840350020702418820010240c1005080000f0841e50409080c11468102180801d44092091440c140d00d40e455030140d1501c6a0f0040c0c2d41c440c8203311200401160082c0c2c00345d5190301c025200700226031442c2501c940900140b2850300080d00c0040c085d19010f0a0704034140304d50905146c100300400c036a4001c000c4400000e410310301740191040d041600842d01d0140c41595803d0b01c1810000304401e42c055000a009240d03403401c840c0c0c6840c89038100c00c08d901c01d90044e02074039081801b0402050512501603e403030f45000700285d10701d032011015054841404d038401d49a400002c101000381d0f04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 556940782 1250 556939532 556939589
    0x1e140106140c0607270e011401050c0c0123131401050705060406150801020307030e161d0a18060906060501030216020904060f021b07050604060819060f 67
    0x14104403920303003404040c2c1d007a1511210000c2203a41404090100f43c3d412445882c264040c50803601c8035441081d40f10341701083d0019007405051203600ea00740806901e0760080301510003068070400104901942d2100444801484001c2c24001c071342e00410f803003203201015015000381145160460f082516211103d00409030302814107050017000c0010300040b40740421400e84c0140c101c21302080220040203c11503452840c0d002c644154404000c1c41901c1d60315030042843c09904900302c0d00b02c2d0071035500380a5289038a01c200301e52122100381c3c2c000f02c140c4540010394013401090001921030300141e080ca02050314107101b125010b41d20003044080000301c0c429940030340310a190031424034040c10244803901c1c1c10468060312030174417000004c2c02c0008540100fa201d2500308010740d05da05258208008216182d280801c503801042c8020411f13003040700c141c5040703c00e50794034280b203500c1d01040000c0440341280c0640e4104e444401c0420701005040c0300e0001407035400d000f406ca45520060000000707 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 556942032 1250 556940782 556940807
    0xf0b191b11090a020a120504020307050a08010b19080d08060310060605190e061c1b050d110901050a0c0c0e010b0301080d0201091709010e1e0a06030507080a1e140106 73
    0x1544180021003845606c6101d003400000c144070b00040503120b90000038600481d550203503510811100700070520320419003000300c01c403c0c1600d0f000e900d40051042424941c107140180b4656621008490100d03510440c0c07500d80008018080c7d800003240300c06500140c8142e500484045000054041000600c10a400285550341d10b080583d00303c022000034000d100c0c03201e0324454120401558600002c0350b034402e0401c00c0e104000c0044a4080c041e01038202d42000e00184041854420185c0c0c107110b00d001144c0080b8016500c061a00d03134032010a4034002075141d03013500c8020003104c01107803142d080411b00d4080e0444403501d40d00c0c0c0d03140030b801510b00f000b110700100469040801d01c0d00064039419940784070a4042940e2521103041c180120303442c1894200079a800288c14030442126040000012003401c01500c09250640d1141e4080d019241c05544010004030b1f160001820404a80d0151004400c94a5160040c0700c090340510150707400c0c21041000d0410240040050030342265406405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 556943282 1250 556942032 556942051
    0x90a021e1908090105091b18011403010b010c0203070b070c090504030c0209011202220e060a09030906020307030915050702030a0b010609141e06070503070605040203070f0b191b1109 80
    0xc600d006c0001945801c40e003c06085840c503028440e021643d101c0e000b06030344459158411540f0340e900d142c05044070100d0480709000b540382008494041d442030b0405600503030061700401e030092a20f511a0001c3c1c1c0f0202050f20002c0703840c02d020451900c02c0c000c41d8000d82c003d0f515807141a0b035a0040228800041c1c0c0018203007421280c07040016251145ca01c1203048016040003280c1800c4040340d00988a0410048114002d000c100406919503078448144d040c0070359600b0004039141c1105a03500d20407103c010b030104d00018402c005442c4100705d0040319500f01e140260808600d5800b1130700e00001d45a00300d5950ba0602e0051154983c4054044014180301190740500b16020300811a90b449a01a5081c0707022440081c0040341c031880c04407911107500100710390769a030040c18860010720301074908074400d014122001a80c48c58281d200001c0e82c9501000c1e40c50030412170911821009446001c030140070f800c0001c2100d28410346c01003400c250290402003402d0049908005064100a010080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 556944532 1250 556943282 556943291
    0x232101020d05061c231e010f0519020c1501060507110a060f0c02120307050a0c090605010906050a0c080c161a09150d05070f020c030c090a021e19080901 67
    0x135203a070104807030000a03000402107401c40410002a0310228440b003c00007548100c1d80d1a2543c04001745100c590950000000c00003590907a50130429101c095641c0e003c4c0304660f00c07000000300345c20f600820080a885003100c0801880000c502c0f000c01c0241c3c40300c8041400410108117006002d0780310110b1143c11a151840e4600304000a41024000060301007001200180b08045403151004000e4220020085940b01c0c8942e10b0030f140d03511201c01044a80d074400c8031001640036150b0240c00241c44050312000c2c1518100b0500700c0356900300650704c2040100303541d46040403458020081c0034120b40c19001d40b4044000032034004d1b000f0f40c07980c428082004405512441d007030034542074601465048a03180d800c40c500481d44002402103501d03c071030040c686018080c0305504075540700f1034922650240d07040e80041c0c804054654200c800119007003c0303217000245c4181060780c01410a2220342542d100740c0f020303d850f25800f40d0000148281101801d0001e00303111504170f90303c260300c241075200070321 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 556945782 1250 556944532 556944559
    0x30905012d140c090a030c091d060708060424030606090e03070b1b0408030f030412020f1005100b0f09031513020105090414070806090709232101020d0506 68
    0x524401009021000b0b2030800300341201c83e81c5d903030041d4200540d00840c0d4041c52a0700c860502000b04160f14507141003818241c40860981740100c0c0043c03151134541c5600d09141c2e904014400941000d002c2c052120034020600d18105000c110042c001c2d6000744c100246030360803c1da5400481d41000c0e194038041d4003e00c0308a0000f541c10380c8440d40013041d20322080303e0440084940b09540680e0700411741c02e0202040070303200b030303058000a5032151307001d5949a00c0c003600354041079031154032422041c1c0f82c6812141c02c2c0e40746000300b0b4100c00c0e000100940c2d90040309030303180844500c541184c500c00d00103800010305445246020400709d098200c10b0009840e11b420024000b001c10341c941000203042c4540443c0c2d8000c90340c0c45130b0000c007c3c0c034042041280d441c03030550740041100720120755840c4101d4145003c600e5581c403034a1a41c0c25101d00d01e0890f04403800800103c00c110084203003c0764072442e038506020201030215820361000026074000750312042d0b103481c0d40b01074810041525010700c00062049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 556947032 1250 556945782 556945811
    0x1806030f030c030415020f06010603140a0b03060a09020a050d0f110f01050d090305090a030b04050607020d1d060906120702010b0d02100507030309021005090301180309030b07030905012d 82
    0x11011228485d600c03100c0500115405c0c0c0c28041461154103050003080000181140c241e0440181c00c41e800e4810161952119280c50407240034401a0350540d1058002030751035840c0d54810058580010928540c4aa4400014002008e649021161200c04a90b01d82c10070251003c1e445040b103003100c1440200000b540000c00b24059251171403003080d00d0304d100d1070071b02d4003c0080321089500036100120705500c90a00c1807164005583c01c03902f07449210300189420344045403078507006043e513446003000341104481d9800401d00e12500c942c0a0400c00242c20595114801010490350022380d0790b91034582440d000c0d08454043c0d0010f40100c00017a00710300160380c2d400c0c0c4508605d4450401c0382e128940ca0800710001d1100700b0001350090310242c2e05c022a40e0308034002d010b40c0a400c800074480e854442c150b082c500182c40e540100803920840c001d100003000d1000003a408480d47c030b0b000031112a0381e11180d013580d041001e1002c01754446c00c0c1ea612040070086c0d0f81c00362050001c0b1b052201440c0c1503041c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 556948282 1250 556947032 556947037
    0x50108061603060b070609140c0109090f0f0e06090d020c01090603020a0309020d05071511030307080402030f060f0103020f3718050a06080718090c051806030f030c03 73
    0x1800e4008110088541c6581d020740d100101070400402961784078045881c040c030041113000c009651009070411414181140024165004103069440c0c0c03140d03a2400038201e0140114910300c103011038071100386c6402031005102e01c10307100340700e140108a43e04224295604040c0703564002011500107000401c286c1c0d80010009080b42c0c0a45001070b80c07080700700c0c4214020100d001c07000758018100c41310320042c0302d80002c0000c2640c08607a108514108000016a4810301300e06281503582c2080c0000340c842409000e2242d4402e0000e07054501c00c00034010518240601224106182444e1400620941c00d1a121019203540d0640e140052140281d280300f00010011351100300360fa88203850020424400c500200c02410342d404030310084500941c600002d001c0c2241c4611401d840c0c00400036075200d000a6490403582e00742c0c05012000c1d6a08440805090380e1001502c4181d0224400106502d070a240468840d0700740741c9040c0d81781804802c00d03040030325071010038605500134801d0140c03550f0007104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 556949532 1250 556948282 556948291
    0x130f08070e190b03030c070303030f090317101221080408120c13060201060533030a060b0a050306012c06031f0605030a060603021608130f1706090105010806 69
    0x180c1002c034180d0901030381c050007081c9881034140c0070200f81c40d951301c60002180e001f680c1c400d46013030041d0020a40250111115030102400041103410816002c202518019070840170940784e00c849203446520394140c00040240c21030311420015059000400e41001c0c01001d82e03018a042e686505290311920098091003060f4a08500500e0205104111010896100c6000b151425614a0381c44030b01900900203403160502036074860100d1048403c4048041e0200b02e406009942c08044111001200b83c100074807164605540302d0001c40c0e5450004042c003e40c4115554141d0f603850000b0004011000410002c0204503c044044c030903252a070034082c000b810140c0303016440b51f0750800a0104800c5441c6440c8001c14004e00c04142143d20000445c405d1642d541c09201059032130744201d0892182c060120301ea42a440d41400003d1741100060038010341030164202850740380c0003aa50801085d81c40308102c0b00e40d440e4400c00e00716080c021643d010012500810142d0b1502c1c8500391948802071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 556950782 1250 556949532 556949551
    0x4292d03010f0c0314090f031e0d1a01170919021c060e060112030203030a0507030906062c13060504150606170c191202070602130f08070e 61
    0x2610040980c6095010540e0504400c50901034a216420040c00400404032402d040c40d113400c0008641d900c00050341c041d40e1449034000c0d403410081e46011120445040c0e020350700c0407001c000381800344142e070045800a00003101010f42240e1000c2c00503000542c0030703080c0310205520030100000ca00b00441c407155030b8851403c034100028a80d02c0041c1c1d143d491844189004d000040c4003209100c0e4a07408440d154060030100c4445980f42d8081c001d081040c20401130040c1e10400000c2e10f140e0903a00066041034240c1004504a20640e8994080e10b5480d000001c5c01d01c0205004048a07607041e00800140034118080c450fa400d00a0300b503484c5806801300500200e85441c003003010010001c200c44004440f1050412210ba124100241545034403011380307071100c07075427004200d00e202c2d820704441400c030322038840740040f01c0c1440c025500c8002e08001c2c091a0b03a0700340301020100b11140010503c41c000802408030f91404c210741f071424645142c010107170507480040d040c00100464540c0541188195 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 556952032 1250 556950782 556950859
    0xf0b0d0f062007050102090109060503130f020f0d050c1e06030a02030c0408070303020d031d1c03020d020a2307020d0305030a1808070309050f01021009110429 70
    0x382c5541850280e50301660200000052030740074400b041d0b01410340e000c000d07a5031846a6035030b1078088696000545180d8285814000c41d040090a200901c0030042d102400c159500c03040000040c00fa0f010007041a074198100d140c19070b03680c2c603020200d4010782d000c032003c00c80615800b9000c1501c42c0001040c0001a42d40007000c03644420100040c0c0d0001c240e03e108132004103880f480c2c02910345e02c40c01a1030000c6800c00b0980711800d120182040882c3c54440c004190055224031016540750810800d041070503030030800d031404081c060004005208071620380411407590141c0701000c0307800480300500c545c0018803c120050b9203d481c1c10f4030070782d00352400c5a129180c3c1403003d401800001d501c0c4490780c99020125040000c1000901015806611202c03070382551003040c481d84880c0d41039014010303080f000c4030001c990300507401881e829008020ba40780204a04002c00c0448014862100c0030003000e152134959401401e01c11b914800081d184908e058035011400c04140301111407840300a41403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 556953282 1250 556952032 556952051
    0xc040c0804140f15091c0f09271d070f06021c17090c0901060f030510060203030c0c070509010b13081626012d050c0f0a0c05030d0f0b0d0f06 62
    0x41158101481c4021a81b007500e550694001c3e003038100520100000c030328071000010b140390b00c081c907200245d10307000710507030720f403255413003900006c016480300005c025130321640d01c0700708070700800114014009034201447c0381810000040c1c503042e40601c8901c030303072803200b00303000349955110340a4000288540b844d00c0381c0c2e868a20659091055441c2c2503500f101d9400c000091b00740e4045848d40400c01c1a450801c00c94803980245a0342d0381c0d076070007418090390007080800c40e490002c5c002403101103809419a9a407544840000c0c0e1425030a902031181040041620080150302c0c0080000070312455006110320884080304010b2102a0304c00c100c44046c91f81c0c084514000c100c018181d12240d114020029003605000500b09035501c51641e6480c07043d62034881400c00d4071445294000c460030007d890600d8007849000f4200c0c1d10240c0303580c0402404207814800210100060b00303c2170080240403c008428401e0340c0c0441c0c41e83c20071548151005271511011803070102e0b1b00113442e0317045840451100e01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 556954532 1250 556953282 556953301
    0xf0f0307060c020a09020a090e0109090308010e0703021b01020a020f0304271b0f18180b0d050a0b07020d0c030503040228030c0f08010507091202030c040c0804140f15 73
    0x3070b05d0788014070941c000100380104a070b011613244140ca5003e0b00c401042d90b2134100c0a8121b441c03910380100480c01c010011310030300c040c00f5020342c0c0c481c1861801601e0314140c1c11703205039280d804914140d01a0f40200b244003084c0d405010750300000034860020740c02e09150000720b2400c8804820103a0f90351100b0640c80c261943e44d13400a0b404400ca8042d9034007600c141da90f0043c81c10060340b5031100000d51000034031030395030001c28042003140c10503206450201012040c0324024846114504e910400bc4011600020001d02141a007140103010241440c5000130000c0e040c032001c1000c502c1040141e00001c1d00090b040015031307420680544201c8941420844000440650041501458030110000008018240c000300055a00f0610091542603943e00050b007681d03420740e102c4010585441c030500440c0c5948481100742da0004007203852000c684c0000c14201e03403a45500800107201d02c801c1106002c008100b190750b51020301c004041505881c0b1074280c503083d28458022079100800c011860300c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 556955782 1250 556954532 556954549
    0x90d08150405040506040c0509090d0e12060106020d03050c090916030b150a03110c0a02060f0f040e06040b0102060118090f02060307021501080a050d05071506090b0f0f0307060c02 79
    0xa409407042041e42001d0400980d1401c00301c2d011a244084c485020170141040c1811314004e1062170000d0054200d80b11003a0f0300003804c0d0241603000881c80740441365019003000194000c0c100c0d50041d140c503482642c401000e5401c010007070202c240c0704021490311519030485459010002d503081a10701c0c481000101c3c05803000c17002d5143d1054100c808001940002402803003840e180752030403c2404001d410741d4545010b0003910840a800010416000d810201c0c01040780c0040b010403030340341080030f00d03400d42c00790005e401c40c4c03d000d00150200265820306100398602d04c08240000c041c5585404290049255945c1a030250142c1f40c400305000c00061a100e007545030b0340100100d03201d14120038002d40d14000344804c3d040c0701603214000100c61001141c01e1480c1d64105c40581501c00044809031865400100e0850340300e0050b8200c80c074581f01c04c0c4a800c0240460032004121000541c0401c070101c51107546451088000500124081d5400030303c841c01c5440c5410091103180071800019a1342e0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 556957032 1250 556955782 556955821
    0x31e0212100f0b0a150809120309010522240e030705010207050106050d0c050105030c04051306030203160501080411062101030506180307060b040609090c0815090d08 73
    0x900c0303660250300409181e60015164034040c020100310300c01c4004200251654544a105030707980c0c10541c004881c0348607184159000020200322594004146c00c03c43c8036a000300d40311891650340f45d0500407414404a265106050300700318241c01d00115440e03003003904074410300c1c00841e20707090300d1800d0420005420224000000341c0650303480b0702c030a08050f07000c0d500c4020212407552030003c000c07800d1b00c0d1201c0d9001405400150b03103030001d4140001940c0c1540050b110440c586014800029250b952030221150160100004100240340d44141841d140400d00b140300b04085c1940280b1403a68003041f01580960480410000c200160340896550b21400c0c1190100360450250f0020000040220034101c80c8510102c507415998283e00d0828002c150703140070000d810030018240801c0e1076400c04021001c00510001d202c994581001084800b130100460701c00e03070b400300200314041051106035103483e0002c0c0d81c4e11651514070003141d1502d01c034040c150244000f03100800e149080740d101020b0b54 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 556958282 1250 556957032 556957069
    0xd03050c031602160305150604020f1902010902100507150b060a0e0a0306050408030912090907030504050c09011805091207030f05160609060f0b061b1606050a0206010b04031e02 78
    0x40584031b061041c0c039003c16543d4220700700e4209010031000d0805100b00e91920100340d542604105810480000d0a80840c004800315901c0c2c580c9500542d852000300b490044003521007542d5251249080c01c4909504840501c00e646499800340060300d80300c0c00c07070b6425001860036200c1c02021b48000b80f407955207600054119840c240400040041010046001c1e0000c0c404482809500600d5680148101e007041d42d00187c001002c40c0155019400c682d070440c1c82030040d07031a0f4142c0d400100d80402001d81c4206612000d400c102c6d05810840e20071950005003000150200380c1d0031a00b040b22510501d40e000b000c10102c0140807c441c0e1041083d01e001085404482000c1405170803c0409002c51a405540c550702d09403401007501c00911070785803c80c00140a95051032400c41101e0701c440310a0840c0303003e034007500d8116100021450406405800b00d500c1e81030700c803444200c000707181c4036051b001004c02c0082003109001003080802e20035903131905510400302000c95403011030041c85499608400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 556959532 1250 556958282 556958323
    0x2010e011206080f070f09050403021209120d02010219031a010f020313060905011b0209040b070903060e03180d0f0809060c010912030b0d110402030a2c0d03050c031602 74
    0x545130b01090b00821100300071100410741d9150b412035011680e0603140180507912000202d84405200d5001d0103d003407006002c02c00640e48698600d0500d100111008010303540001c041c20398441d449140ba802c1e041d949401c028280082c03010302c03900c4d001e022419060100c04c2d400c20410038420011144103c5250344001c540e2035480b0000b5220f224580140f42c01b04400701003184a07000c000300c0a4060b550001c015070580c1d25242c40d480301e00a0003030082c104201200c5000302c040b5403540204500d2219003002140d44030381030066003550040041c0c1e558030446100b400e800104242ca50250281c6401040e00c0c0e0380c6075103860018070741d40700b500040070465080c01034600c2480340b10b25010701c01c031110362003e0205c0c10302041048150f1284040c000c0424034114911110341c2000d03030103950b00000e08000020000410817134209100455001075081202c20100145004010f1000d0074001850781010f000ea401d09104801c100d000041162840c01403040c0012401c505c2081040000d000845203040d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 556960782 1250 556959532 556959553
    0x6180a0e0907090e0a0f0c050604060905040e06010513020a1e020a260703030b0d1a0403171510020a0b0702100b0a05060406050d0908030f0f060a0302010e01120608 72
    0x1150650200c6481c0e03140e024901000681e01c0340c40c0210306002c2580d001601c108906656852101c02c01c006007924015a42c0002040320740300d01b00100081d00858407011700c658a01420001510740c4c440c0340030056000b0f00b004004640f9108120204502c020f1409a140ca2000f20222a11100541051a400e06502d003400301e1f00c0d00802c0010b0158000c4e07540704803021085052041000003a8400101c44100f0844480072900ca680540d080b20303c0180031a002c2c024035214100d8014071440d414454140303080501c010182c0026100d200c0680c8038164144900c4e142202040c1c2c0d075021000c250040e0340c283c40a082d824800d0000400d21503100c20f86e5991410040e200950f10000c5c0c0f0046100680303009840c81e80351030b1405c0c03044119503006185500c0c240c20514201c0b1a5000503c00304c1e4021b0325010711710f0008000740e020b944103110346000c0f0340c85441c0c400c030311000e0400f001d018203000d0b69030000300348090703640507110008540084c246401400e007048031a800400340743d400000107008814908 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 556962032 1250 556960782 556960799
    0xa0f05011b260d0b03010605240405040e0c190b0f07080c010c030c03060b0f030412050f0706140604021330050706110609032205030f0d09091a06180a 66
    0x30083c201d516001042141c921105041c04c07500b41e801129030020004030100d900303940700c41c3c50040340140c0f81061820030f0b580d1030104041d0340c2d0303944850240742c12001009a480c04c0030402c1ca003410840c0c8428400d02441d0a803005075510421030785203213445e00050300c0c00500042c60225917082c42075000811052032513640090080400c401100c0000c2d040220005161003141d081e584840c0080090382d03d56101c565802125640d010007203003c0c0401402900340481c5108050030020313024000200c0d0002c6403120b44944044000c040701d208074410b0040004c0c84540f821501c099408007514402030781002c050740c038103980d82d1002100590b401d580d440d0041110108400040303a40300c0e01c0b4203282d4448122040d03281d00d4100c403030582c00d43c800d003c0640b0b940600c0c0d0008034111488e04812075401c0d100d4000c03d04000703210b20010603540c0a000e0022129501000e44c2e0014030000c00104144250858a48603985400440902c5054042800e0303003a141a0001f52158a0004040e47c585540d07d0188 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 556963282 1250 556962032 556962037
    0x60705120c071e11040c1d060c01061206090c090507021e030405040612060501050d3908031309020a05040506071e05060a0c09030f02090703060801020c0703020a0f05011b26 76
    0x80340d01490034248007446807401102550f0081c48031f48107a1138503101000034030001d900301d4140343c10990b48880c00003942031401602c0c100401d000b10804200c0c8000c90500b0442101641e1040c0401480c1c50200260560301080c502003500c41d00b075003582003100080710540f42d0300540d0451580140390401c001000071401c103411501c0d07445404c007481070b42c1c0d0318810011405201c5002400e0184c9110311441e150700c2c046034200c00000301c607220820142c2e500036040140360307481e0841d400c03582c000280c8992103811001d2010082c44030a100b0f61612003400001040350017184a51400b0b0354010a5107402c100710b1b6080840540000c00180000440a0030a941c1e40c00d001d0b2004103109140014120030940310301d41c5142a070b40c0203c40c0c0714005240380c0c00c1c0034490100a03e1881050303500c18010405500a0000740100014070b0020700c203281c1075004020322215194880203010044050401090360800e10500c5020400a411159149070f428505070341c5018207488414105d07002003509268801201 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 556964532 1250 556963282 556963313
    0x60206071403070e100315150c0206031312030506031902030d0e01030f11220e0402060f0c1501080f0303011401030b0a0902160b01170c061c1d060705120c071e 70
    0x10000c0e03002d03a03420300302c0c2c2d044030323a095044000380da46a0080c0c00750404c1801140c0111410491041c5030200b034072030030640c958002031100002d8440c02031100380d03c0d0810410900305500c0314660074180050b0300003595425034141c51418013180e503289001507802a800840768010410040c0800480704044500b01e40c40741c400001d5054150a03030b848107120000110303003900c07100a2750902d55111a020800b80340c00060414403c01020004001001c405003d1f0a800001038500402c49505080c6000d0800c00501d1030001c407a8808d02c0104001404045110752218081c28005001000c0901080710f5940c00d40241c581c5500005400c58022040020b44032400d000340303008586a40c1390924018200148500d148540d848020804041d00e8841c0042c01041503240203c6076030710031558803406036030b0a00300c42802c92201308203403481c0709010b010265000780a80391851174000d015140d4100708202502008410700b003c43c0c0d010420405490244111000300001090803000b45040c1d00084100749 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 556965782 1250 556964532 556964561
    0x9072d0c0f05060718030c0b0d0906020c0a02030105060303070b0a0903051e04090b013608100e0d0c05150702070905090a031205160507020a0b0316020106060206071403070e1003 78
    0xd00b41704080300c0c40c04080103490344440401ca0807481d040340c68a9540201220707058040d541c007180c80c0060380c180700030040e0910460240c520301115004241c2141c00041000e8000e8004004100000d80000706041c0e000d5079107500003c5000090404940070b0040020654406a02420018030018010050011100201001c0c032840e601c81004580038290315031900e600a812030400c8004800c05d101c0d20a510448a0800401983d05c00d4024075103001035010210580e075410200200e03060510000511644038105000b5456441d620a96241c900b60360605034814a02d011071200ba1091100e0401000700700d0050006091140400340c6541103100c04601103090a41071002038550350054600c100200d91881e4401150814103a805034003940040303900940c81900840d01c2003105002e140984407031494260301c1c41080c8000783c2100c02039040b0750305640c1b00070308000c1c0d40b550103070112451184c01c0408a480b500c401c442551481c03284900c40350b0000c5404500794003031390f050b4480350340b052080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 556967032 1250 556965782 556965797
    0x1f020711210c0f131a0402040b070201030614060f0a02100203010f05010e0d0b0c070c030501050406091a0907030204020a0302120c0c1209030d11070807030b040209072d0c0f050607 79
    0x40b400c102d02c1c883c100c40300320740203006a207426041e5921980078010f50f0390200a0700c500c201c124000501243d0180e0403019865001040c1d4801350359041c80380c44090002e41342c100050601603c00128140141200183c007040005aa651340910a02424990040d988420354407541c581c4c8001114208030b0142d1800a80001000e260390710b005080e6411040c0c0110340c50400761a1006030203150341c040002503880117000580000001d80074851680300318000d83c0009012051441c00740c190040181400303006024042c08d01600c050301140071002ca03a412a801039950210540c16800390003081c1c2085c17910225241001020143c0b00e000742980b040f10000c0d501d04074814030b01140107020380380c036454150b441503e00300b603400c8c00380020003071841281c01121040d50b80e030f143c440c2c179081c42e40d00221000e80181c42440110704100700f0881d00302240d410b101d4079010321901c1900010790600042005120b8852450821324011900d000b84260850007e4414540f2030400960b50b401c1500e8000028556 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 556968282 1250 556967032 556967053
    0xf0c150a050708011a0405090a0c030b1014180603070305092a121e010e01111912020f0f0903100b0a1806171c021f02071121 55
    0x20701c1424800d01c815141e000c50b59003810004240c4903603a11801d50034103001c00020405584071520345101d83e0b05890b004ca44290f4004d4000c05880315015420b0003014000c001500c210740000041c08a645613840403030722034a50410070f03180b10084030b0806400410000610840c10350503040117108e0342010701110b00030743c098000d880c03a86005904001c1d03a400c07850070b28411071030b101d01041c0c044084641210051007845034201c28103c2c03070b41c01c04480713a9034440306100c08203028042d409203404a00441824007011005080e02132503140d4800b4204140d1259a501d0401a5815203400340c150700078194a4200e5141d03010f10582c010380c3c06520a1244540c0b034a9941c4040c01707003d06444020301425150303031401c420000001038050100903031640701c3c14003282200141e041403640c107210b1401444d59106000c044408429071130031600c210340003600b8032545404258081a0f0781d0049040040c3c0d0b40e08941000070000c42040c0c0102e5000860170b800549000c10b11400d01009415041510080c004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 556969532 1250 556968282 556968301
    0x3030b0307140d020405040609050708160501051305010810171005010b250c091506081005030303131b330e090601110f060114060403050307080f0f0c15 67
    0xc51080c6a540f200c510b85070a001424141c0210b0303000380c03281c0404115200e00e0768403203041a402ea00b03c1c2425a100000d02c18100c241e0340140380003000c0a09000c0e203005000500c41c182ca4040340502d0b81402202c0d80460105882c0d0f00403c4010502045c24440c0d100c00c5203c4541c550319440d85c0f04025509150004c10001ca51a084a005821150805401d000380e00081000200724030403c0e230321420300d0000020400c4140c021986200050102041040d04000e0003501006c0043d1020505040c4c8480511040e100041100e070045198001c024005030f0340d250145000c4100302d00d80d0100401c05600150036031014040016441160044804900042e000103201c6034002a43d0000105103020800c007905249001d40d4200506142240303401190119103450a9890000b10001b58084c0e0010000c00203c201c00464240c5c044400074074143c0f031030700c9140d924010040094000d02c40001d80300711040c0310b2021105140d0200882c80e85456890340701c00d442c0d0f031580c110100925004000240c50b1030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 556970782 1250 556969532 556969559
    0xc030103030e0607060c05043321050901050109050a0b01020d12090614091e06010513060909050c0a050103110d0528090c2c060f0d05280c031b09060303030b0307 71
    0x1003085003c0d400001d282c200c101d641e241041e0901c101c99072b41f24070044020426004080c0300d14500800170845500d820340d42c60460b00010000ca102034034103542e071b0105a0740402e14483d29a0310f85002e0b04c08448c40007940c8010b1800f070400600080c07600445102140e9032a15142c410104442a40c1114a851040e144005004030480e40070341c10140061105e407030800110507591020442c0082d54a0315001c0200403920300b00c0f42070794903500c182001e41091600e9030b00540645004e2800340001d20390340240f100540200d844c500c4065481d200000c050000d90060070a0007450030315030411240307210502200400c929042070f903403800a5035010a080d0641d4151030030000e44891120a80702010448070080c00c0c01500a5600092025005e8919038500400e800c005009001402001c80003012410a07032a1202502144c0c0241d40050790108480b00011802c580d0040f28004680507103082d40600540260480c5800034030f401c802000303040d0b0561000487c3d2200f80c04a84009490380c0b07010441d507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 556972032 1250 556970782 556970849
    0x3060f0e01180e01090b07020a02041a010504030b130b0708100e0c03060d0c15124706270910050609030a020d0b06010212030c030103030e0607060c0504 67
    0x1841c030b40507604080190396000d50503203440980002681459135990080c80c40c800e50b04500140c0c011035003d41540750500c201810703050b00c40d4600030881100301c0041e05a0080340700142c220070741c0d140042c04500343c00c50207102c1150f00852101c043c0ca0000005800058240c900300d451004020000c604d8207070305200c0c180039400826642d41150345007001c00903290320b0114110342c030040490001032040224104083d40740c00304c5d00d5030900170303a40c0d038407075812180d000000b0074000006804030b41c0000170038014041c0a44461400d1070a0b450300d245980342d03040701c0c4e11049800800005110008802074400b240003030030038882c801d0460896208200c510007050700c0d5060f8030f030300703030340041140d8500306009100c91800035080d80c3e0f070640c00c0d40008070170700041101a1b03111a10394041202a60741406620701c01031030422000e08504040b4828410f6010500005043c4855250090300c0703542c0c2c2c0000d80b006075a000c40c003403052507802c10004107540c10511034890102c0d04071a038410400364480070a80314 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 556973282 1250 556972032 556972049
    0x106171006020a08031312081639050d210515010315051c0507060215040803040228030b1005010212090d0c06020a050c0406030f020108040201031b03060f0e01 70
    0x4540c1513444041182e44050002a0300b10342d15426840040d0705070041001000a0b0748480f411450055800c107068040f0304050010001604044107001440c0d0170f9000a00c1500c0d17606030b0140a40301c41c800300016800c0d002a0003403003200d07e40414154441650040d0803200c050007110b501d140481d81d801d903281500c480d00b080307000981444080d4447e1f4410785001d80100107a20000c0d44d12004180d1050341a48005401402903810800340711040181500a00342031008103d00090840031008101c0302420051154100001042c159640d10032415006400040001580c0c442c401d40840c0c41e251500c811201999002d000402c20012541034004440c01a0042c0812a20602048103903034824000d19a10081281c140e4002c207680720810b0f8041c0c40a90010318051f2220300304030f4641141e03c45801d100340d0516070141700141d4887c4c10819102d60a00f0013210545551006802403d490740440740c580f5080c1c0480544281c2c1604180100c071484498028020b4850100c6c840841090144209 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 556974532 1250 556973282 556973293
    0x1d12090a050d03050d09060f060806010512061603020702010527090703020a020c0f04180b1f06090612090602210f090309010c0516030303140a06051f03090209010617100602 76
    0x5c051264101e0aa401c1c440e01c40014084c1700901d601d41203611640009400b903005100502140c1003c20440e4120000000103141e545040c5d11450620365407811080101500414000c0031640140180c5411844000c035400e01c0405100c0010041110304041c0d034400c0d0121404a88214007a03c225800c400c055805048400410000d10480000a213000350700140c4c0c840c0c0d50860b000090700c41280e1075200d540d10307505c0d42c1452400d000b86018542080320301d4003c141805c104c001d07044561103044032594201484484400d42012004008400014180034000180e042c0c086003892900540384410754201c8040da25054107140f07950501f25032040c41130740100111000c0b0b45c0200e140c08003c51049045410303540403807207041e4030080329a10032030120361103c9160120300f01342c2d03001c25480901402c1c01c02101d45010002050340f490011210124112020001c0c00548240c114091940d0040d100000c1707035944400c0103000f0540d010b0b0100e904a2001c02003200d07007c042c8120700855070241d00426 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 556975782 1250 556974532 556974547
    0x807020601260a080c060a0510060f111204061106010e0a0914030a02010b1c0c06030e030702030123060607080d020a17130b0c0406121d12090a050d0305 67
    0x5451841d03651402d9441620000204040c000c1040034503c0103200d5010940c40d96010007180c0d1912001070041026542040100103031b0314050380300c00044800918101070042c10b00b030000c1d1b941c00c09900544034680105150303140b03041c226030024021603203030350b40c1e06501d00f141d41300d000e40b150020b00aa482c10304448002c1a00c200701a0418004180521181c81c0d00d841d0141c82c140c50342d446032841c600035075141d042c2030105240c159980d0f44811580080e03240780040c070343d8944110429500410081c0b43d0f0b1800ca4204400b010020780e103c01d5070140003040045401c600400310b040015000c0c01031401060002940c80c2040e40685400d0f5500c4140c040c1003c00805c0e00744041d40010250404102440e124030706015400e000440c014034005501010149040c00c000b540c03000018198030f9600401c000410100fa0b0042c41c0c01c1141c044420f00041d8526207021007624403c86030800305e021b05c115043c44122143d028000c0c21400c004541010680d50354400740b2585014404001d00800e0b018010384 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 556977032 1250 556975782 556975799
    0x13060f17070803030a230f041b05060d02031006030603030c080702060f030c030a1d0c120a0203030403050d120605060d1d010e010903081509010501050a0215071d010807020601 77
    0x1510165200d0041d950711903110405140b0b15001100d85a0a29840350b42e0b86407a440180e50000c04d020ba2400c1896452800180c2d0418011014000a01308004803c40581c403210041e982e01c0904401441c00d56035021000320302d8003a401c25a505c48264080d4038000848902a1141201300e03603140e00e415086440702e450780121500000016a0000c200300f0034109005a1070008620429501d6011600c81c1400b4281504441900c211781300364540440d00425002c80000e00f40070303102c0089400c0480c14a045890078105100c2c600020b4152101250100400002065843c1c400060382e60b840c80070f51001c00d440003a55068400d1640000c010402c1004408003600110303148407140804991030040882c00c4c03802c503080310510820907591141001e040641c401c0d141a045004030201d094403036920000601000030610405060000c00074418100034009c1c003c0c2c1d0001c8507040111b0390b403031411010143c5080070308085066003880110440801390f00506803140150401da0003803209a0038110b42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 556978282 1250 556977032 556977059
    0xa020d03111f0c030b0a0b031503010603052b0c2d020d0305030114060f0d0e1203041a18060613150815010e040b06011b0f0c0513060f 59
    0x4100700340100000000032500100b4000e600c0c0d28071402c00101001110001011600c0400e40c1c03074840d84074000b041080304500c4050b2500081942003018000f4000d9001900505003a400103156015000d54500c0c4085444800340304101c003c2241041d4031151102183d07d6100e0b4603000b88042c0700040d15048000c6c0461580c0c039005850364424003050b0503034000480c10000e0082c101c0020314000010304c15035800d84085240c2450940700e02c0d0a01c090920b2100a901495544a00c5203580f500c82c1c3e04c0d9014200041046400224100d84e40d0342006d0800c0c103000c601461180b1101602140441c54140704413429481e41c0c00b0076009010309844000400184c484c81047d940e0196485001942d0491040301902009103900c034003c0510302c66101c640540003005038401c4010040362400c00010820b1002829030200003480c1160480c800b40c1a0803405400700030340501030042c00700140003040000300141041d00c01c2181c0304e10441c1602008801943c403180618030254103450020400720004405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 556979532 1250 556978282 556978307
    0x50403080f0d06081c1103041409040204020f070b06030d0e0d0209191505091602100209060f070f0203060a0513170f0a080106090806240f03030c030d0e0a020d03 71
    0xb408a401541c2e202c2851030b001c00750380f640c400c0c1170f0030281110410340c002a8414030291010003860a240c6480d01d0309084003454000c0500070f0185000040031035640d80d0440d0317a041d0b81400c0458642040c1d06103c07001d0b14048400324000d01c9007007203400d101030142d1074200c021000142410707180e602590900400e20f4028092100c0402000720034201c59005000f032100090101074120a428941810411403c03000750581003841d15181d1140c1d0310960200d9070240f003074601c4002582c0c40c54107001107061442000c0e1036501c5c1307060214004003013114241003005864001c50441e40b858a824281a00b111429902e100040d0000900d00e00020700000300c60f102844807800b01801c11109444081c1280e0040c03e0040000e501c0d60300500285030420b52540185ca080d81c000d1805203008072a401c0c802420307001149903038490310f00784409a6111800110f02e0a0064242c82e1a2081500e01c40c0d83d98210f81d58440c1c100e8100340c1c02c25007000c000220325200c1900200041e24940054a00342e0707450003180d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 556980782 1250 556979532 556979557
    0x20f01200c0a1202211204080f0c0d030608061b0a0f02150103060506030f0607080f040f12030c03060806090d080c0c0f070f0b0c1c09051305010312050403080f 70
    0x40038140403400c480a10800380115402612610b100001201103080000d1750480801074140284d1a120300c10514407035000f82d00c40507266440310f541515281c2c900980121080d00d200b40700c0343c1c903103542d410b410200840307c10200b114119100c94900c0a41945005014501d010781400080c0405210301480403d820081c01a54445407020001c100007020980003600c0340342d101e00901c5080d050070003040b502588044060503050070b011100900d00c110140400591b0a40d60b400b1806200e9020640701400b51302454201d40400c03c0c0d64050007904006441c1800300b840c1000c000303182000031808a206007540f001418401c44c030000e007990000800741200700d617a182071043c04820803003000440c0c0150b40c0f0000400c003e5141541d03146000c04503070030094006200740314203002c41000007204400c507042245081c080b80080e80088501034401d5103c59800484c0b408100c007140715a90069060b64062902450350b5a0800d0050f03902d44114880141901030401819280b0102c11b40900100144403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 556982032 1250 556980782 556980793
    0xa050d030b060d06080c0906010219060504140a0501060819020607060222060e04180f0b0601112b02060103080304080c07050a060f030506010e0f060c0328020f01200c 73
    0x81c0f2040b81100d99581004400368000702c450603140c07401d9481da6038032031403d01c01030012802508030340d0350000009200502d03498076070010800f041002501010300e28003d4003102c184601d6400e10a010b8240c41c0b040d025640500b104000050351001d903070040300b540207400c09240c21201d42c2d03000000d611889848040303401c80f4001c40c100040e56100480205415682e440e0003001c3d0740c4c00c11003100d52103407101000c3c10240001034002482e00180c004400d400180283d0503941e0200141e40005e1800342c0400d10b40540013a1881e02d03030700010a0f440c500031880c0c480c0f2981d415010140e030740b0f00c403e01003e4a800d90510016001514a0b0002c010321101242510031580d0b944020a01c10b5980740c020b00082107000340c03011403040d4988600c40c1e10100c00d01c1d080a0050300e4402144441c00b50817105402040001208508100100111030220b0900380301360070b1400c2c0f0070111200984011210400500a2801c6000b200c1c0050090032506491040c040c40e8405600c00140420b9007d02e902c81443d0041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 556983282 1250 556982032 556982047
    0x1030c020309030a2a0b0d06091413050c041506270e070c0605040b06040506091b070201020c0a2c0c0d18150b0a0b0f1206012312090a050d030b06 64
    0x1000c910320000c000d0f41c8450b07a00c400c18280d071f400c00e85209811007682a07150103c41218140002c586a80200b20390f800e48403402034504001e401d2601c03010010380c0042c200002c400f8500302c1c4880e803608a4055075140500e62003c41000d58000c006511040e00e0b411441c0400d000e01030701e0b40500741d005500c504111003c100d0707507560903081c0c4108640c1034540d91520800c1050606203800703481d038031400403a004405440c3c100004640341d00d586086803036008000c5040340031a4006c004c02c504001d4010110095160380e40d90003102d60248111426203401d203045074080090745083d0503402404200005410303d80d040400d1002025001c1d8100015a02103915402141c1c4000842095111a00703000c107226040030f0520028800e241c1c4003203030b288005c0004000d800c0000054449050300c0841e003500c95111000100d070580841500041d20714804028180c0030f52615000f1700e2110f084a48210066541d03a04460311031040c00c501a10395000940c0c04024188240d2006081e07100040445040105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 556984532 1250 556983282 556983353
    0xc140405010f110f1e0c1e0414040b0421020a020f010302070b0a0501091a06090d0c0e0901050709090b180403140d2703140a0207090c0c0201030c020309030a 69
    0x190080000880e00885c4200704e403904030b064410030a0340f40398018904910701c100171448000441c5508003011f440c1c40b609500a42e555049002003040545900d4402c0c241414074001d108020380b07046444a801c40000e049030452102c1c03103480c90301d058014000c610500c0d0207110410085600441c1050f60810903840040c8900e400d007400707003002c9000000c166050100c03a40444104140080e8001c10403442600240e80707903070403200c41c8201940c180540e28040e00c1c1c514a01c60b92034018860403840c41701000381c0c44105512041c81480c0d079507242d43c0403a81d50082e04d02180c286031290b03134101d2803911502d412029964010f94105209203080040c1250400c0c02d0519030300401069080f43c1d450360740020314800311100000001c0280007812206055907034014181e00544069440111008141c48412030b0081c80010001c0c0315415042c0030500310404010031081d00814102e020a14119000d08500d100006460480001900420980815031501003410840c0e0343e080034490ba04801c1c920700c111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 556985782 1250 556984532 556984543
    0x1104060f09050102210c011b0f080105060304030801030b07021c0203070212011404030f052208060f09032512030c021b060d0e030d0e0c040c140405010f11 68
    0x10450395550210340d1403034801455841c003980305504550105c8038400c0110803828640b00c0c0b209111311020b50703500c051800a4098074001e8100c1d0040c1b00c5408000c10a035401841d141c494101d03c0d41e400703109030703290010000a400180c6001d00041c020700c2c0140009120b2008081c1c0055450040b650b01a8a050f0203104551a0a2b1904010303000421882d0441c10810070410007100000c0083c0506100c8051510740d029000b04040e081210b00c246030740c8810b0080d011200d80e50821600d000070409a0320026111640c14401e0750381a10950000070420b00800003c240160640c0300998500f1008051100c0c9030240310f094641852001d10f0130038005407051040000030714407610045146400d1a2019040c940081584840c8030402045401a079403403108031a0404180c5400041d02511030600e40e1560040c0500c105000303280c09a0088040400900660030f110102c0e82440702c070031500821240803440c81000010000203020500566014516081c2d1001036440c1c240700410901403c9403404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 556987032 1250 556985782 556985789
    0x1b1a041b030804080f01090b1617130201090b0a08010302130b0a15170f0106140c10060e07090b0706090303020702030613050c061c0c02240907050d0b04030507061104 73
    0xc22001030f04000702c540a00420072840c90b100300030401e48078030707850b01d00c0e0441005040142040204001581c1d0300d0086041d102c403080807003200384942c0307403000c103d03915000c640713a050340452070501d800582807222500b110094038042e5580800c5910315400d0126001c46109840403242e00c4600404054864860034402003005541342000389041c0c000250506038600320410300c014074a01040100407000c60b2490465030729181c40f421019000c040c0b40317454040c0d018102002d01070810a0421038441e9005001924242c00c003120140c0c44148013610704404901c94042000010301c54070300420380c10f6204c1c400440c028140546051040d82c0001d09000c4105c0e10800181c0c1e01581c4041802410816013028003000e850051900b1240d0240c2c0d12003038002d44650010b00e0311024803540700e520078040c0845e001c1510700120668481e5010300178480108075480103842c89500e20000f51490030845403500d9940000500d981c98031192000c98641d88070481c2580c0c1240c954242c10682d003e80300081009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 556988282 1250 556987032 556987043
    0x1080606040b2a0a05070b09060d0903020607090f0609050f04270516060c0f030e090a060608100501051233040b030a050303060f2403071b1a041b03 65
    0x100e0007050307103410781440340d100d1070f824991140842d840040c03000500c0f1070030b44460401c00c507254005070000032564880c80c8078014026060200b0300080680000301c141c083d030300c2d41c5c03034616002d40c80341c501150030306440c8903160001c3d80e40c2004001c0d50070100401104d440c80900040741201c0d9040c0002e119a9031001c403a260140ca010401043c814188801c0e540710180101c21a10140b510400808404000307801405244070a0042d500701801004001c001c031101500d01080e91030071140d608014080c40c8102000300c2ca801002403030000d8500440c505941e8141c4800c0d0070070819101500c0517220040400140f04901d500c1c2641d03040750180380d10b081402c07200040c40b1018102c1c00744000c1d00da103a003079103000e035004100c4600003c1000c0142e80e032041c030541d01d1075140046100080d844680d004404218050442e003003100030149080110301c541096100d000c00c6080d03000d000d0311811000c60000e00801d00085100014060b400680d507006030041641007110b20b40c5207803510032140d440e401241d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 556989532 1250 556988282 556988317
    0x251b050706180b030f070e030a0c06120c090f030303020304081b0304140102060423150f060301051b0f030604110d050402030c011b0f0212060103030e1c080901080606040b 75
    0x384901d02d1032003100a040c1400500342141000210302e2038109020b0a00d2084c4a1500d40d0f120498904016003035180703402428005809540340341c06004030814024803203802e030a201440401a005507130010440310245805070600303180d5101103009400103403007203508000130007803030384295a02e161a1152030342460155986d01d00e4408100015495250624150f40181040001092043c0c681c07030500040350a07000000d1220905150814004000083c2c00c2c20b001d1040c0140610f000c2110b501c91101038000708481d4551020601c038a08552840c1c10314001c1c1003100021604428000c2c42e04001d000d071000c03500007084411800e1680103003c02d022509d65850410055160800c05010302d00d42c01c2c2051083c004503440c0800044803580307006000c0424980b4139070b08540341c00e40c0003000051a5800d0f1401d5507101e1400a02180a02e4600c5d4402c83c40f1181c60703100107458880140c1a0b69000e002e403450060b40e080151110b9000500c000d0b4071a00600c07000a0361019100102030084c908201c0e9030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 556990782 1250 556989532 556989557
    0xf0b0601021506060a110106050a060c14030702030d0513050934050d0b180c0301030605011d0601031805010507020309030106140f061806040902070506251b050706 72
    0x80c6807008044248000122000510050b612813034111103d1881c0351800009842d003010350030340500800d6014507003142c902400003d800360702c2201d5242143c0301d42d03060704071842205801d658900030510003944c550841c50b8084c0c010380c040e200030180c81d6200d02c1c1d0105080c0e6030b64002050380c801180e100c0340543e20000c40141489500605004444038030960050042a0b540b00500c1400364542d03000c2000d90f1640300d80e49690b906048403103414540141c001482c50000c0c5000b125800038802220743c14145400401d24001030723031034404a40d008501040d0a60344000045004e0f20944000a800c03104e140b8054010a9080c0103247c41803d0540056513520400420b240c210392669201410f00710703008912008030356695031075451700d034400c6070304507114107a01e00b071486400c80c1030003180d80c000c0f80020300103100d243c2a0058035900e80124103071280d55440107035440040e6061440c014800201401400842d4010990713240b2090601e140700e4a42c00b115030383c0d10f161107116040500411140038014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 556992032 1250 556990782 556990787
    0xc070c150f0e030f03090d0c050a090b0307140607062c060106020d08090d0e120109050a060f2307020c030f010e07060f0f05090f0301050f040c0803070f0f02010c0f0b0601 75
    0x10440b89200b580140204c2081c41c0c1000d44034010010030520030360b84158200140302d100c1c00c2c0c48028010051058005554030300400c0010080e07001c00d5030080c0612200003903003c00760354181d0030540020302034518244859850070000d210301603140700c0d41c904003038461005400030542c00100003002e00040c602941445400b030f240c00089501c102c2044020700421010040105408500c0812414600581c085110008220031542010101a5840d04c85144140040042c8440d0014050041003003d21040e6a41d441952201c103030404059072460001560010000504d6511400c14816501982013107000242007500000381c284035a0b445842c400c950f03e2081c00640000d080d20b05140c10031001c65200a401e000c1d03440740d03003003c2c80b501140785603454441e001901c400740d030300800801c102d1900d41242d41103580b007514142c2e090715081c0e134081007070000002100c4c0182c5d000020003012000c1070340d80034541e480000040b030400c41c00301520300000d101003c0489480b03104c0c0c5003c151038075190000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 556993282 1250 556992032 556992047
    0x313020a0f08030706050919260306030d0804020324040b06030a03021c050f07080a03051602150406020d020a02071403070f210818040e12030c070c150f 67
    0x3205036245010801a0000003c00c507481c0d264050301c042025a1080840e03400e140081215400b02200c5044801c1000313440a001800f052070504440c004416280700b140160000311012034240e0f004040c0200907078080c0c44900d038414401000c845003038225120a150800c118032103002090740483c140410001d4100d43c05600000613002080101400d480007955840300c85418545510780145403507600388500704a4500f400a818602da0302d10a520342124140d000031083c000081c50600480c0c02c0d0054582888201c0750260b009117014100b12052540143c0c01902c00c031092a801c0100030707241c080d580041c102582e80c5030090302c0581d1030515550484a00d0554140c0301c1d1b0040031b801e000c002041d40b10076060328021601164603a001044d6444140c07000e000c00350050340003140042c070900303070300803104a4102e0555041c07115a0031481400d40e12048143c250b1121348090001072000c4000c82d01820006000b0f00c40780440ca5a04c0356414007041d54200c8890028000c940c40110b0340d174100c4e10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 556994532 1250 556993282 556993289
    0x23100c020708010c1e0c0206030f04031e02060a1a0d050d0f050c1209030309040905011a0301091e03140f04170a0309090e1e030c01230712090501020313020a 69
    0x240308918181344010150780d104203d8035440084107100c900742502c01c01c030658120742c1c09851b50b07642c0c2c2801030040c02804400c42e02113000410400d030884040c90140d2810702c1c0342001c2d40060000342c0f41d181d071650190080d190060300d2039000000c0d20440751f130344400b2400418018005403c0003c1540f0000f01210f017008501000c0c440101b001c4040d00c00c000030f80b100070b107646006440c0c07900e00f490b00107030540c41803035042c4c0d60140c1420f40000078004c041d0f0081e940001c500301aa0b00d580c052100307240c242c074446030000d4001844016046c2c00d0721462049948907910030f00e840981280c017070109111a4000c4030002e14010000300781408038106c4c40c140e0003e03400c820402003100740e540350780040c0152040d014100045440b0200004511020400d01324602c1450a4110001c070105150640d60782100d4414451917081503102d40240035140350f49102c00000e00d00c480c0c0035542d041c000360340307801c501040d681055a6170340407038020070000c2c80554018030350000e0005c1650280e00400c907400a40740c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 556995782 1250 556994532 556994549
    0x507030b0316051c021f1209110d02030a0b04050c01020d030b0d11040e240a060503071406130b0d110a051b1507050a030501080601030f23100c0207 65
    0x40d5112445028030062011144100c90f0031800f0940e102e5100740304080d94200940205c01b06404801b80d803c42010803015109607502c0000b500341042511302503c01904c0c0c054419616980c20040354140700e000300c0307081070029080f200d000700642d07941103041c3c0c000c8405803916040b0303080301e170034940c0e06000342c100c0c4245500e0107000307109c003c600003142c050801600a0170f0000201480d055600c90b604031070306078217987d426140c051801401450044000c2c0301008503510860001402d2855584900415160302600604503942400038110740c245175615007991002c020300c003000c01c0c005c00304c00d031802410140c64000e031900b8132040048141d079244d00050b0010003051081d07510039944241541c10206880d10704144e00f0343e0142c030a50034141c3c0100560740d000201c10800c03601c250000300422000302e40d0f81d01088917030383c2c4203959a00c90170203000003131100c002641c004000c590307004c0c1010200c00325000f400030000e84074a030031882e1040407a41804000d4441b0404081150103200350001880081c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 556997032 1250 556995782 556995793
    0x3050f0a02130b0103060f09020a021005090303070c1a0109060608130321020403080d06030209150609010e0415080d0f09081e0307050604061413020906060a0c0f060507030b03 77
    0x181e00060010b4902c0c00d000544998418000c0c8003a8440d402480c010a002c5460103405a100d19811000e07620040f0590090b01c1110040e10302c1e89074601c20148200c03491009141103465558044503420300d81c0300e09507100d000011303100c80c05000722001e0074020302000c0c800080c4140740510103400c64030020800c40250918000b4200440d41103e40c210600c00402810b8a0781e01d60104401300030f028035000604244008540c8551540a03a4003c80030b41e40215440d1101b030780d44a9241181034003a01295410090510041b0782c594003495842001c2c640c010000b141e0103000c40c0200d1011440d65100a606a0118034500b070210340048608900d1009460002515401c022901c0c0d0740302c845004d003082c0811256a118810b400904c1a42c00569104080d140c0c0e504190401e03034003502a100740c9525402035400441c0354070810321650308900e9070191044900d5601c040800c40503400002c4084d080c8401c03111410000348048240600305445024000740d5410200001022595a180218001d601c030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 556998282 1250 556997032 556997053
    0x1b150c06180105070c0b0601261f0815070504031e060c0504050f09090708030406080610030b0102101d0304090f0e0114180c040606050d05090d2a05060c030103050f 72
    0x7218494174040d40050448003661140d0004841c98844000c1e90102400d81416403500a03558460440c040c40c05002040d06240d045101143c030140d55110352526a800142e1900300f00c104c00780380315403062240c103140d070034140c0e244c82e00c0013044141a60070544050300010842008507621032441d212506161841c103150804000c00c01b2103c00c100b0161141c0303942c50015614803020441840908400001d1700e07222642d540000e045580b0a1703079114801d100c080004806188a48600c82007154168010240c2444045514008000292542d0895680c101650f0b00c8214104020001070071038000c0001e008407142c41c0da0040714400c0103d40c0299043c11060b0450f07440c0c000f41c194003c40c0c00c0200942d88084a58040c0c0340440d00d00750a034100d41000c50024100c1e412101800b4040445a010b0020f44e44450800303895951030955400070400d1010f84a4200080003035100000a04c0750004001132240d494141c60500704465074064001d0020040c800c012041c40410000c2440c0c1c0c0003408501071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 556999532 1250 556998282 556998287
    0x2a0f05090402150408060f0714161506180506040c0806011202090a06050a0f021c050a2313080c01050f2206030e0705060306031b150c0618010507 64
    0x4644941445520424081025552420003002148900d0521180c4d1603654503083d82e01d5480807101c04010544440020b400e090082009005140e0304c40942303890700e070303401c81121580ca1400b0760659a0341000170182110050601c038000c0500512603402c240003104c1c030150000c1d031b100107000e81e001c0ca0620310f8112010750003103030054000030242404032040348030040c40c0000380a585907031903102c0405000000c10580100c001c2400c00303101da5400901d202154002c4c0e81d5500f4040110215481824941648511803c041c042a00d100d10740440107034208422044038a0380060412010350300004c0481031035a004603110004e00380d010150030940c181000180c094011421440c02c1038000059040320100a651041c00f80001c0000d010407480d00c5010013402000303445200195440b800c50041642c2c982981928842d00c0c000380209400001c0178a40480f12607014031854004442a40520060a9000183c034500700e65030300819040c503040c0140c605060700003119074141c3e45010709000641c0e0303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 557000782 1250 556999532 556999559
    0x1090e0712022b03090e09151f0b0c0106151803060b0406120b07020609010e07090c1103040612110f0d2706090c05010809060a0e0c0d2a 60
    0x50301102e5210103111041c050300d902c03c40c1440c440c080d102480c8810410190410180820388011501c540d0b10b554030411881d40c1c80d01c0d90302c0712400841d11070000890191504082d807600d0038004000540c9642c0e14000d165450708110505042d503511044140102030b1420300340721807501d00c1d1408820600652141d03901c03c0e1400d0101030001c1d41c80c2c0c110080c0503100d5400170802041850050400c042c22401c005040c94020780f40d850040c01080007040f00b0f080140035006561203420081d09080d85040e80181c01003070300805420603c500201800c002980c11302c041c200509140d2100e194600011140e4011241c0e04440d110207080280141c61080e4404402e85103241007032400029180120000050340c50722002917400300c20f0040b0714440400c40c1ca0380089000c24400e500c0000c849803206c00644410740215075404042d40b2901c0090031446280d00903a0803130b16010159483c0a00d440c1c0403600d44251003e0681300034900520006000001814818480e0048031407411001d040150f20258403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 557002032 1250 557000782 557000819
    0x1905070201030617010c03140c16060608010e060f400803180106050618100e03030301150e030c130f0b090a05192c03070606060801090e07 61
    0x500820824216402030344400080c0010408802e51403824144060117050140220b200080c00c100e954a50080340020540c0201d44400e4a51f040022804a1110219080b00d041e44c6180d01c452001840d90000e00c51401c402c01c2040c0584550b1818818107a03809a000d058150f24980110200074801d03800301038068507061541a0700769100310b00b0000c4030560003c5201411041d800420b04c103402c11100d13000ea6070142c0b020b0003800300940d514204901c2c1d0140c0740702080100007a50201a451a0030b9522225581260030705e40a01d10351803001c2407131504240c000d0914085030803c0001216000390740d1101d002e00840040080b111600c02044944032042284442c42e500d91400031442c140c44c1d00302110000e00507140b0081c030300d00701600c400500700907500150746240240304c4400e0302c07885008407030b006403100100c4860340305000d2010000c804922030314045400107020110004040b409050700030407007507880d4402c0754142500c04007280c84000030b910007a84003540070045400a10f8106881 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 557003282 1250 557002032 557002037
    0x50705060a020f100b040f14060f030a061118040c090e0c090d080d0b0603073e0109030e190b030c041703030f010e04050a02120c0a08012019 62
    0x45041100040c1d00e40780c0c907003c4003d0305014001d0040322810895201507130a00c4111400d101c1da01d110741000c01241c1e48d0000078040345078442d0006a407804d1182c07480c403078000e0141c2202c040340d440391074100486c2c41001011210000009000303561031410303a809004401e0403078042120702c00c0a803010303240d8206445004200c1c02a4000500480c020405884c00c0220182c180da0307000040d8642942c0c1c562107882d151110f80e20b4020030010380d00702041030341d201d044640c032010000d80d0084070300d6007800c0e090a5991003d210588820303114071035440c400358404940e500007044440b094070f0080d01e02c082e00200d49024188030607812074141f0442007050200c49500d8240b40d5281c40d2084001c0443c861500481e00c0200d1742c5890320200440003000f98811200c0c0d008440381d50740c0301d40201d841414180c4018020743e025018800c098078141c556541c0c07007605001100c0900d181c1c0c0c00814031814050703110180c0ea9650b0307680007502580e9083d00001d0380181e18599842c0c80b804841c05440c030425180c40404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 557004532 1250 557003282 557003287
    0x1c0215010b04094208161509060518030a08071406060f030309010c05210403050106050108061003020c07030c08012c070303080709030503070b06030c04110a0f090e0403020601030215040305070506 86
    0x401d9103039404c1c10000b070f0000000ba144040e1014507440f8500101c4e2241700080072076003440d904141d1291040c0c82c00d55080b5940c0d28541080303640c055481c05082c040c61503060254100c04000100c00e0710040458900c180000045418800c8002e810f00e00c0c0140058020072482426103050fa4020040320300054003401d2901350b40c491400c05502e8000341d110707403d1000d10810700281030407142001410031a84260000d22510382c80b180111075a41c001e98a940c0c0144281c0d420000003030280d0094250318441400301c1d80003035034a4803000071414058bc0a0b0f14646d40d289040c010307420030192200c0185015030b440075030310b4103c200d076603503500f00500c070150170051008041282c4038801c100001c0150b400400300c9444400c14186400840e1040c0c4203076105e8818843c121145040c140684100104c8171000d86003000c0c51200240c0d140004407880500700100039602003001d43c1c140a40038080d078000c3e030007454150306510502c517007200d001002c040d0000f81840304100050340000c115040c3d5a080d5500e42c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 557005782 1250 557004532 557004641
    0x1205010b06030c12010f06050412050f0d0918060302060415170a02090405090a0b01090507091d060f0612010501031d0f0c0109171c0215010b0409 64
    0x9004044882209500070000401e101c0550b000e9400b80600320019120b4000c16645e5050280c801c100310310504002c00e138180410000c41d1030420502c01202d0090081d20810401c00880a041049201046001c04d403c0c0307005120b031075407946007600700e0750170102e080140900b16000a40e050240b4820302c0100403000c10703024503403413040090300310880446590035054100425004060b401880349180140e1510300010501d0000107451344100d07401102c40d81890342880401800703460001c00042c03e1140740640042d40300000f1b60442c4030b8500402c0c00003480c0c2011070802c00514002d00342e0314451101402058000203c00032481e0442e9000d0900140078048490f0a0920f4030005090400074001c13100780c032170460008185503202081c2643c074034288540f9501d5202c521041059043d940c3e80c0080d02c1442d40d0074503100d8403400e00300780340115085d148e498042c21007401826007104541013800700e000c01081c1401d010f001c0420a420003594140210b0000004a0005552091000500841a15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 557007032 1250 557005782 557005793
    0x260a080f0903030307031a010c0b0736030b090604120518041a0102070605030c07170c0a0804091a0f130b060c01060e0a02070507150207080d08090c0f010912 69
    0x4a0700d5400c0941a41d07140c2c0340c203107005002000100b0060000900260310b00d082584207802e003c29065001903803904c00e4640c000103d41c1da2001565610003501a41c64078a03100155004224940243c0306074003880d50f05501c4e115060b031034054100700a59000005100001d85888038080c410001031034803584500e0342d0019822094114024150001d181000f1002e0500315015000040c2c4800e8080741e00c100d0f541c110441d19844115081d119102c014042500020070f1050812400c2d101c12010300e0500012494242c207001c2d419100f201d030000000303420040600c5034018040c0e00c8401034003500414650101041d030701842c03e41c0e55032181100c11125543d02c451903101c110340c410083d20082e00c409015410354001c00300c9005007007032140503030700064403e900c5000322410b42d50300402030915140f4106044079810b1103012150258000e1080c0810f42040c1005034844c0064995180203090509084c21410241c40e1070080e4000d4203070401503040b6907001080d4a0172541010480420780c0c1050500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 557008282 1250 557007032 557007037
    0x735010c270f03110f09060f0f0d05030a0216060806010c060f0915020904060b0309070306020306120105151003021207050901180e0a06080f07091806090c260a080f 72
    0x40c80300b4405a04003c024060749141341d00ca56501030790039a01e59482e500801248407002c40700d007a888446140a0b40035400c00703c0e10f001600501a1901500c0280342da12103085400078811031005900c88000c800c84c074000c00c4c5200e070081425040c850800d041a40c00200700c152851409401603484000b203c500135002c0e80201102504400e00002c80e440b54040f08020790702c5032200714032a07401c281c004a15000b6400899024600700b1004205107441c43d640c010280d000204001d500c20344070204005020000e0141c0c9100300c009240980c00d4500003010000805041610202050301c180050340c1140c1e01c0317110140d048449420040c0c0c4490760b000040750b07482414074074032540c82e005440018040c500800c2050080750504424810300317803121406659214207c0c2d49202c0c0364403d1408000f01510765004618401c5028008004400039440700c4c4280e51401e01c00710307050f07030001108006003101841405a8010125900c0200d020090340c6e0960302e803035030600a005120009481091a8405000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 557009532 1250 557008282 557008289
    0xa0f030b0423030304140c03120403060504080f07080d2306091b07050616030b0306070507061506050306010206060108062419020a05010c08040c12050735010c27 71
    0xc40c1ea91785024a800b45c50248801c6407800d880c031400981085500c0d02003411740c001d0031803603800e6041c40d00d543c480c04080e28002d4426a84440100a04210148018000d1a106010706422a5110000000311084410748803c114020001e407a50144002080301465006501268480307800d45031000440782c0c4041d2100848191580040c0e0001000702c0070428910039040e2076041c0b001a001504160185c580504d00c0d00c0d4190002400034100600a10280c11014094240000c258a0108007134a40d05410740141c80807e00200811440b5a410010607a0000c000c1c80c0002503810124049171020342c0303400600311403c000700200a013000c1100c05503050800060411400556209030194840d0312122040d80c00c0c0d402c01d82c0b07464510f030150840a00640d44021210710f1035280007204200b102c5203a80484890080751000110f05551805071543d4060401950141c2c03d15803071008240a40b4003442031090341020310b100d01c029000911b01480d566038402128249008803580695020540c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 557010782 1250 557009532 557009603
    0x712200a0806150108180a1502040b0f0306030d1d04110d050114031005010608060f040b0d0b0a0e0715110321040201080703140613060e150a0f030b04 66
    0x820025900c00700c3c0c00d4040c00c9482070300e60fa0116203801c034501d245d03507440004003d6607520240030749000500d6004d1480021a1500d001420305413203c0c17140c003899005c070311031101031540070045c82824034051103880d2034603c06040c003100400c0c2c0304011400c95181901114815540c07003540201030344802d03040311030034a44502c0030070403580c5800c40101101e0341e40080b02d00900c200f11340d20441410b40d10442e07050340d009458500c0c045e96084108004820582640307500240c80d22005a050b03141c1303a50322101c462158014035a503107010b9088004440c4685408203c5900600f02009080324078842010b88a00034a410000420b070380708403514504c5450016200060154000c01c0510a002100d1380900d100360f03501c10310340d10b0f5441e0803401e68a410440b1480000008003160152030071010002804040141c00b2071000d940d6207181204010840e140000419940e60f055014a030400c50100a0074020005461013400c40d01c40702c0d5a40d50081000701031008428a01e450b06440c0001e44441e0076210f03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 557012032 1250 557010782 557010793
    0x80d0e011e1101061a071725020604180b0f0613120c0513050406051005010e090901111c060602030c07211502180901050d0b040c081e0712200a08 64
    0xb400001c5c4258080c0200303603003006000c101020030403541c004803540250b402e10340da40c82ca000c1b1182c0c00007440d12a90101d900a8040100140490440e070101c4d081c9800b080000a400900030f0621400b400c07514012031003000104500d412840b60b040d04017040d0340c000c68011051014501e0000141c203640d400c06035000180448982000c80e0f0380d00305511451181e102072229480c1e11321144500310b0b003406440d010455030002c000c138a0500d58103555000480324000314083c0c0d518680d07001940d1003004100d10800c9003a601015030425030040304c00070401d500c000e51400c8000c9441e103407500c0090044041140300e0011072028003100c2703103a00110039000f0300d040d51004010070940c4020751100950300031500010321340c03c40910b40908001d040303e070040c2030504a0329075a960340d00013000045c02154540c400d0074020603462010000300307000e0000742c1000e40d14985c8801841d40340a4459104c5803288101500d8080000c814483c4030214104124043c0e492043c05800a040d040a80e0020032603031184 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 557013282 1250 557012032 557012069
    0xc06050604020f130603200306061623070e0408030f10030812190b060306010c0606030b16080a1503020d1104050403200318060a090807080d0e011e110106 68
    0x1802414105e941d503840422800c00c82180320b8003402d04100900c09580d40c240001141c5040c000018407042480361204030781e1520b26a517948440c0e1781d00303080c01c0c0d501022042032082e00c082003040c280a0582d44c00c0604180c50242d8039080d10b484001d00000303a1761021004107069001d580c40d018003540d4444033842e2286803a900c4030310002001c4941c170409022164090203602d400344500807400c6409400759285030744e4000192500d06100e042165140d03a24000040415046054103000c1c01c2e90301103c1110318282d050041c1019000740080c88a10308cac10549441c01000c0742e02c090116541520562401c034140e040c81e0380e24440b102221074119003000200400c055018082c120403120308034190072040700425070580c1d203020307001001e125004500c3c2d01c07056074038201001e801b050392030b4900f170200c19484514060501040354008011740c2c3c811a0070a251035040090a0481e81007841c0440105c6540b4603d42590b000e20705980b02031040c4525103c5000c0300c2908440f004d0015a281407450402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 557014388 1106 557013282 557013307
    0x306090e07050f0f041103010905090303071704032f0f030c1b030a05120d1a1305070210060303090e160c11031e0a03080609070c06050604020f 63
    0x24803035201c1c200e1740c0d520302a904101400301d1000f034495140c00009019214040c1c955100c0f50414400c014249603c1740701400e02034940700c40d01182d5180c5081c10b40d00404048081840c560b820000360402c0b650016408185a42440454485000b01010f45480307000b0350304014000d030803151800419603440312400d0081d000080c03d591000b034190352001d2400c144240011191200480c2c208101041442014110442c2c05004e420040640300024040080f1310801900d0517520b0011641252081180285a16561400b000195100e003405440300714140720741105c40a0503400240c0101280c51030000c1c1807802e80311081c40c900720b0703540c420340b501c40507603255014481c040d08907640b07a46a01d2441d442d84c80e01c90180c8815601d070700300100032440080c0040d01031504413042c41071041d84124600c98440d040000080c0c0c45c1c0b01c050010300648505807540e407a084c1e005c600303401c8109 = true := by decide +kernel

theorem cover : BRFrame.Cov 556834532 557014388 := by
  have h0 := BRFrame.cov_init 556834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 556834532 ≤ n) (h2 : n < 557014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
