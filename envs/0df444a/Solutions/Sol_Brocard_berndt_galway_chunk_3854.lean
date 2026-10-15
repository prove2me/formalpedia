-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3854
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:52:50.307078+00:00
-- url     : https://prove2.me/submissions/379c3942-5561-42a9-a89a-75e52f56dec3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 692985611 ≤ n < 693165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 692986861 1250 692985611 692985641
    0x114070c0305130e04030f090906050604050603060409081903060806071e0e0d140d031b030c030b0303121602060705120405150907140906060403080702121912030b03060a 75
    0x100040c21124031604ca80a40e00c81d946e0321143d0102c00200812003c0702e50412407043c0e2500c0d60421051b603800080700c040311300a6924a840c2d0b42c540380024010b02e03038410003620a51000a051441e03801d0000e03803812030038181c1c604200141c2c43c1c040d2603076144001ca0f40e04011a258071226142703039a140d10032444160151400c0c081003c8110302003045200318441c2100c803401d450b03900d0018110b050084a09291803442d0030848280d140ca040c1e105c0010b010101c105043e5504040c40b6824426000040310f1140035003180d94900d007840d0800f0352102e0481740482443c041941d01c080c090300c04140a0300401440c0c2e1220309000703040c0d1589c48500400350046459200d042d03403410760400003080303551040041c00302420480389000d902c205810340305811140304100420070131855550350b00548082e41c0c0c10041c42500c07218107201040400f180403400f07031110302c102041a0340e802e8050010125280c0f0550188034651407500056054401c40a5505d525400990000f29002080c0c0d00c4202a400912 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 692988111 1250 692986861 692986897
    0xe0105130b1f0804060e0a020117060f04091109090a030c11061b0708060705040506040e2e060f030605103e0d021903080406060302100e030114070c0305 67
    0x381d100c03450752004440b000041040c54040000b4012644105403030101a000903101100040c2e00081103040d600304181b916285040120b03026850b9680140c0c1c0a900c0a04100410ba440d814940c1da050f0030304516034800c02c4003400150b0040b002103100ca00441e0315803920144034015545040e800b110030300e107a0360050014083c10304004040e408080c1e0a0140704082c00d12581820b011f242800c0d0010450003c2c001c0420003000300780c5444040750700f01c0d11020010710144d00c0d0351410002484d2403c3c0c020040d031054110303880e407024407040404220b8a0a0311080d00280c001017098080e2483c034803030254043c0c01108202c401c603020b10a81e03a1380403211001d06070489419104026400d846a54029174021003085202d1008400c0007104202e550030f000600d40603805d03400844114030300c002d00034100300c40300300464204042d41d04002c0241d40d0041c181c01480001c003000038224082c82d150144650700b0844001e54940c0c11945003409510541d070390f002c81c4860b903101518164000c2144003e0107180d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 692989361 1250 692988111 692988139
    0x10050a0c080c0a06140406060602030415030509030c0d02100b0415060302090f03030307020703023f01021603120b0d0c060c03050904141b0a020a2a0303090f0e0105130b 74
    0x10f214601000d4004175442046041900300303e0111002600490155413040000340480740d0244281001a01d40e46004602c0382d640b003030001e08602079207040907918400c00c1884851103402094003100d01c28800d03800c0007803030240c004210581d40e10b80303d420f102c012018020700c04184660003c00c0c00d00d0014046540040098020078596402143c0c0c000050b040300c4018011480c110903d80741c0c0036010111500c50005290400e0a0f401064814124000703001d011100c0289080d0151403040c40c00350756030a080b0380c45044c00781210100480c08004035240100102c182d1900740d902c0e034001c9803c0192401000d040503800e0f01e424000314002e4041c408144030394007050b0f84a00480c8104d50b0001198800343c20500601f00b43c2c41c10540d1615061701d01030013050181035000841601d1682c000c03450038444001141e40000c0202c10901409200c591098080145074000c0008000c40361080110b55420f550b5a20030200707541d082c00f586070300203072001421035203c081d47c008070040c140c0105412100300b14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 692990611 1250 692989361 692989373
    0x200f0907020a0f08130b0c0c12071706070f030c0c020120010219023306370f0e0c070813080d0201050601030e06072307060204030210050a0c080c0a 65
    0x20900841d15032134000f40c04406490204507030b900a0540544241c01c082810711003a880b800280c0e1050f028050602d241c421086040282100400311041344d100f9012800380482d4a52408486810200b5416110184000d01c00c0c420316628000c185d8400340070354140d50044404041040410b181c0e50320120000c80008400c1c8014144210701d40400c2c070b000690414064100300e1070300d0916400207100b40c0201c82c28000d580600c00841e0a4020035015a50b401001030320000302c20247c00c25071000141803100c0c0030211303910001c8005100c009001d00c5565183c0d40340703401c0c0301d60144945d0b04140740701207540022481c0c06800c80c1440790b13940d82c1c180400d1205254510886038001400d640c8890320642600750203106550b00710b0b0003860180b1004e03070040701c0b01da03840b0b40240800702004058082c00300c4040e16829110042c940c0b0712446a9070344814241380e006500103000991041e4110520300c40c0141c0610f0448120075030750f40b20007a24191325202d03034149400c542c3c40c00e156806000d0b0600e0010764 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 692991861 1250 692990611 692990633
    0xf0b100207090c180b03070c060e06191a01210c02060117030304120f02071523030702072705010b04140406050919091509200f0907020a 60
    0x2060350041548514210110341941c1003001c0200522180d18072000700c0841c41c0c020a8152607003040c0c603960301d4958980031119103001e240c016008a113000440c1062050100d405c500030f40c014240b00207442034040d0320034111084070a850070b4410701d0252004465014200c1c1c3e488402400c980700340344003c407200c40c0c03069559021203030300143c11500050000d20b01313a40c044c070141300102000354250700c0c15907650f600e010449049001032002840070f6810700751007084090040e01e030b510076100865910b032001a14a510062001c0d0704142140712600c003c44140013038a101f10240e9000340386851801800d0100000300064880c5402c868031810000c84c28940a03e41c0240a6030014580c9e0300d00e01450040407605c02524540300b907090480400442d5503080059410079400c002c403030002110340807141d00602c01200000d10380080e06d255550400d00c1e5a0100c07004d03500411001d4144080502111045402c4c005c400c2d9102c00c031282d202c07060f8103102025617800195801240c0910a103a141e589100c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 692993111 1250 692991861 692991889
    0x16030816020d0c150608030310061706061b071511010207110d0f0b1303110303370e0a0620040b0a0912050c100c1e080403080a0c020103140105030a060f0b 68
    0x7d0300010610019140c4940c01c2c80052900c3d01d000507094130100400244a10040d114900c030b1303040401e04020300d00c0da4511550b0300880800840e802c1907503d144410200c10507030801c40120b004680600340045041c0200e0f078095500c0807420380c881c0408002c03c408104110030680340c03a10003224200000311701d1201d4900603000b5200b030850800c01ca01c0d004140d003610413801e45852304244180301c4038040003e04003101d1450342d462810313001c082d0b0300182d02041300d0001403c24542850549189400e01146010696008050900c041b8081b1a400f0070b05080791402c0f0000b450b0300300810840425440090801c007152403030110b0400e035a40001d09440710080d001a103a0b41c00c1040020760a18107511071048aa40e58104000320300d04d00d88a1850003064104111f010600300f00300708040002580446000d0360344401c099444a5403c00014105255120100d021a00c0c0030840000010020700079412148020000c202d001d4007a030f6520060a45030000440d81a2180942003403a078521044101c58 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 692994361 1250 692993111 692993113
    0x11208040b0a02120d2c100c021002070609110613090b06070b01060806031b0d020105130f0e04060501061724030f010903030f020c25090216030816020d0c150608 71
    0x59170113044000220300340001406e064007a00c000b40e60a02010840c0b07081002d28041c0000ca020324020142e00741038610801801302480000ca550400205510101455018148a10041142d04144101c621400c0003541a1103151402000040741d103400410002d4006050b0728201021a540c182e03207034100782c0100001c18203910800442d810100140c46030101c840c134852406c0c0c9203200205001c10350211001c0d04100700021a412015180d400074002001e84d03540c004016a074031001d8442d034103000d59089402c5401e020000522910684140303d54201d22110501c0d10b03181e904208424400c41d0202d08944601c6a009402c01e540c18442c00030300c5c0b048403001040c0410300c0e142c02011501d409014100031481071150a59220b00065002203080002440c5440515000181c6100520581c0264842400041c2c032140d03d2400724609806a44a40c6440e001501c4211508410500e11100100140e00220040022511401013144620f00886110301c0070240d24407190b041d070346107401c103401e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 692995611 1250 692994361 692994371
    0x3060302030105060108070f0f0525140a151802102703080a08071e0c0c05012d11060a06080d050f0d11160c0905011208040b0a02120d 59
    0x3035003420b006140c1e11403424079001403d4509400c0150588580500b800304002049100d007506038042e40403504090882e08222040c5861070191140c1c2441c03240080307800300008450500d6000001a030b10350241c1c0e1000040c010000210000c00080c0305441030305610b41d446c5446a4003584601d19110324507a220380d113103443e0001712014850003010501c1d034645803548060007000840c0b162000da40310380106c0e144c03000c0a500e03982c00403030309400781e01d05004071400e003000024026078226000c00d0400d0710803480038166039650b90054941e0100c1801620381b140000b41c14240100b1100c0110700401024107124480c1d006014200d4581a01103410b1880c20340d4a090501220740108440745044107940703002d038074218114500c6e0300c6500908000c040d100342c40b00d039030402c4d00e625101030b150308130b00141c2e107204280680d04080010350b506100e51880b00c1d2400c0c0001c180e102e10542c02540540c0c00c00009440c1500c0d0003000040750340710b400c0350710443c0070740c1803240c1c00070032010003c08a4440e01e4001141d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 692996861 1250 692995611 692995613
    0xb060a02060609180c130212011202012d0309080c03130e0a0605060a0c170c010f051023040b060c070806090c0d06050402150408010e07091107080d1506030603 70
    0x121100050300e42c0e10344020130150241400030008420154210564824030b040c142070030a10b0190040780300d200c404c2c090540011640408280c020417115000740d0b41c083c400301c843c2d0062401c4020b800400c141821030310800d40c01d054040d81001e2420740c400d080c42e5141c101454050f50564110780001e01d070303511500004120b9403d1717896407aa00440c50b0001000314618000c0010303814410510408180301100003102c0a0107074203a8400142c9100c1c00d0190343da10744810b4142e000780a003c54280030309192501140c0810b80c032900500030340313000840b015041e04c14440d00c03034520850035002a90250b10340c3d04030714450b264600500b91600c0c1030801006003500b021052030502c14010103481c40e9510043e2031120036036a440701000a079421400004050b2141d0010541e040351600309203a10400c00100001c040d2415441100460300c0e040030f4550160300d801140c4180e800b012200c181c4a0000d02240f80818040002440c071581c040400155100c1035030b40410228080703610800119940e000100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 692998111 1250 692996861 692996869
    0x17030112060e0111030429040605060315040b27030c0106050a090c090506070303020c01140a06080601030203280f0803060a090902130b010c0605010e0714030103030806130b060a020606 81
    0x4142c0c1d42298009000c034201e42014414180401000544001d0600383c1c03201446010641c031000880040d10f88502034039150812202601c4191141070080c4207070702c01540c2c5007040403889801140d10000f0342d0a55101c000300000402141c03071a410080c28a41c003c0700a20200700000c00d20741c1c41160000c01c8c070b24901401c020b80e20340d0b154803004000d418195003a040c03960018058040c1c41e02107030f0702c4c0d403a40b10300d060441c028052240305200941c83c0499018010000c2d40003640b1070001d90200340a00c03a21768050381d45070a400e00c802901544083c00c80c1d45908840d024003490103400303580001e029042900d407000d10400c0c4e50340a890a403c0001400640e0900d02d02c800c0c06000c068006014513161980803503005604046180f9016940d0300c40710100341c2c403921400518540000f000c0c4030958403213184080c5444250350002c04600302144100441c014101a203048a416895199040c2c1d1050288501010400501c0c000c159442544010583d95000580400c1034030340d000b41007918160040c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 692999361 1250 692998111 692998121
    0x70f030b07020609121e0702040f06091505060712020c13020a0905060913050402041e05090106090c081501051911060702070b16020f04110d0c030b0a0b071703011206 73
    0x100640e60801c0c00c481140402d0740e02110111650446c0d0021010780481c0c80e04c10500400380000d52082c10203c420810f5442500658143c41507600204846c05041c00c1c4103011190511640e40c1208050246c60007081281002d010407810034010349290405035000070380380c9500d40b409200086d502051700507130a940081c0b820040c05c000c0d60701a00e86600c0200080100003004461128152610300150454840b0340040820318403c1d50f1000c1a40c010320303002c070041e010840c1d504205601e8141e001401d9582d03800f88140007036541e00c5030f003001d440301c454404038240d800c1d605034144041080101461041c0d11550a00010255501d003104c8844803420750403c64060005401c544c41500180924403000c0202e8009210ba820b09151008180c4041808008076a036115801454820000c13000080e0b2340007048011110001085410a00e4000b50100d58001150300e80105800e0800e00002c04c03a100103012640c014082151814408040c4440c5030f8000d030001c250101905200d40300b00000e038058 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 693000611 1250 692999361 692999371
    0x110703020c0306060a2c161d090f09030f0f0a170103080a0509122b2d020c0915102303103212100e070f030b070206 51
    0x18001c503007852070001c1c2042200c1c0c01100c1800c6004480c503600010306e1910106c0781e0800c00401c0c502c1b4a809280d4001107006c140f92200428141c07851101d141d282c80c01c26000c9240c006000101d00d40350f4240441c981c01d0003c15041305803000f0004403999020714400b41080b103072039210450b5a03c1c603c1f00004c0451503068007a90401e07140400510000711200181e44190307406240c415144e040d880d00140f1148144c5070402450b020301d6030700408102c4811040442c0f8815948105000911101c0c11940d60038601c06102c4110f0001c1c07080300d4801d41044c0e07031100226543c411030b030500c40502c0c00116881c03c181d480f010112040036503c0c1c0941000d00f42150040c1c03941c103102e07607c444c031410050104c415007170840c01c1c0981f002000a6035040350071804c602a061403960040d814512803c80502307070f82e600e035845107603807406c20401000e880c041a4010070b288884000c4c2c461002d41c954128050071440d8010a000d010382e020228a403402d141c01d81d802107001e0703090075400d41040103021b4180000940 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 693001861 1250 693000611 693000613
    0x408120717191112070507061b03020706080601140313021f1d12030c150a0911092a12160f0c150f0b1f17040204020c01110703020c03 59
    0x1c070420200038100e0020b010307041824004040780c0c40c0400681070882e04d003c810002400400c895041c08000200344003955090b4403800890b8203130800407072080c07039541401001030707000e0002482564802c250300e540100c0d047c1002c001c5003140c4401c402e03c0d60011502c0038105112000703c4001e43c0352810070340882c01c6a2003100901d00401030401000d02c02c50036420528881d1707a4030807401544441c15448110380780341c002d80380c0303945901e00c0c070740d40303440c07400c0980029207140c580810031403a034911480f031003542d02c03d02200c1100c0e010814066240c00c001c02001a002d504540b0031102c0f01c0c1009840d00b01900c840c1c50b1b9988a40c1c900c3c102001200203015440e004d2000e078805451144c01114405240fa1582400d548859039494100c1460109000400e4418107050042e030000f075a5801c044140c450807104400b0817403648100501500c20032881400150306010b565034042c0461071110f4210780080c00252500c00030b0220303d800d4445400440c1d4200c40001180b0040c141e040c050481c50201c210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 693003111 1250 693001861 693001867
    0xa03030501062102090a050306090f0c0609180a06051f021605301603031e0e130f090c050909071203140c1f06091506030b01050408120717 61
    0xf041c0041c0c000d881042d407001980d00084044c03459644018140c004c0c0001070898286280910b595900d9901d800303094030b0b042c814070202c1011440d10740309a80408034050a4800f52a04955140f110520050440140a50340791408942610369405515064000403844044003880c0d0030300924050380824880144031050b070080c401a138801a20560718042e01c4000141120035400500040d0882e4648c2001d81c0f0820340401c0b100c0c0f81c50041d410450380070307498114a40c5e210325407c2600c0c0c6c0c1d03103003400e5002840c484901e1040e45060140c0100c0080342c000c0004802c00c802e0a007000b182c03010002910154400407041200d03290050b400c035403140650010741a86071400d440c0080c0c16030148001000e00941c0041c071109448401c05889110b103202046401038554144d0407500d0400b025001b0781454101480410050301d14014804268003c80c00380050500d041811401000350f0840141007102c20000010711070010094542858024a80550340d4419441c01f40f0600058413403030044c0750014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 693004361 1250 693003111 693003137
    0xc18030a02030a08030717010e060109142b02040e1605030d051912090f1502070c2c0106021b090126030d02070f050d0306030b0403050703120e0a0303050106 69
    0xc180a08560340c800b440c551a0740b225a42524007c90716443c06019440c800e000240c080701091100307000d02400c1e290a14a541c0320780402190f84040c040d25500400324000703502d0040207007040507400207240322034001d1104541e4001025030f10100c000c2c82065200811001650600681043c020130f4101d0041030f44900090000d0f2050140c00d071400034170040e42d50306040050003455076401d0740301403c8040002183c64a4004604601610260703482c88031b800200340c0c04a010b10848418a17000790301d83c0302562500b000a2a40704202d0b580351a070000c0c02080c28103004508034071901034481600a06100c004401e000860303c91001c680600c03845c28040100090819070303900c6811000780342d03035481210540e00740c01481c6100e0349146201d12403001030070b2003d000c7d449801a14081c410307000c0c1c0390301985020b002c03000e68103580005481c0060a078082000a0b00803c02000164401d003081010602500701000465000c91054425504001404410194544103080c00f40c081c81c2089103880302c074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 693005611 1250 693004361 693004363
    0x10141201080c09132a030302030c0d0302090f0f0402070821060102010c080c03100f1d010909210c0606030b01080607090b090114090a0906080f07080a031b05060c18030a0203 76
    0x2200c0000c0c000084140003058881035907090155046101760444000c142e89250095882e840250a591a80030310010210301c1c604c05e008403174a090008210041c82c140040c20040d56103600c6c03981035449503080140000083c0c3e50000b520000002507040102c00c2d50b902402d51010340000c21311411a45048003501c0c4050304207065541140c0030a044944964500035454100011500044408959aa00017891042e540c21650503401149480d11950760b0b2045030b2020b807448084003c0c200310600300911084034040803c01c001032850714103003180240b1034070340d10101c50154100f0b44548020300f00521051008102c0c46820100510b400d100d12071810040261500a05451320f04108080c0c400d2040500c1710341c241c95542c14020036a00a05a4881500000b000725101f2030072240280001456520000703d001d01c00c440c3d491018040030101c0c1d607030489210100340340340703500168004844008901d080042d103202c0d10107070200c41c0d40c41d06c1c4820701c030122030300040700a8444c1d4806804440180c030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 693006861 1250 693005611 693005641
    0xa1a070b040830040618240f0e0304030f1b0311040b0603150f060705031201051207150c02060408011a0a0f0503070e07140c07090609110910141201080c09 68
    0x42c05c8030f000610402c01c124405103c1e640074030040d10111000075618240012118184540030701c00408101841c81240c82000355841a0340d010744c01c1d041400100003241c4083d0044c6a07442c85200015509000b071083e4505034907660308107441691040d242c40e0814100341c4141c2c05081c40480b040c0e07007140750503c0103c05400204000340c0c0920910454803940c0d45a0f03c0565444079807207001d44e9192801d80d6107081c0001030074480c0b5441000e417007021100034000840c41c4802c0d20411040c0c0e1a00c0440c0716820703074008807080f00c101c0e0055010040010022030a12480000c81641d050340348412840d0000c11100035019040b0041c0014440b000700700315540042c5030300c110346101c40145000e940da0755003a00c0c0541840503080c0034410014540301041c4004c105c0c413064603205c2d242000f50540b2200e8410883d40700740c100781104e41003001020305500e44281c000402c10000e02c2d0406094001401c5400550400b01d007404603284e400300107100881060005007820001940c0880c90b03894541203c2030524 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 693008111 1250 693006861 693006863
    0x120212130608070e1f0e04020a0309120f02060a020a0e0402120a1b051209030903120304060c0519030b0f22110315060a14041212080103020a1a070b04083004 69
    0x207070b45c071101c0c078031180d0003219160f801c0c00005100315100c8a81c41d07405405860007200407114008443c1000e4026401254080300b031410590081c459999400340d031030001d61100500381c00b407000030030640000f5a9507000400901041c0d01d050045030901c421154182e4402960103030041512521440754aa8890142c2d4460700007408154195113400000c213040d40f0480b260700f90103028806003a4580e44851008600442c800e00080000140300c1c1c10840e028042d031456405550802c65680740c60600c42d811903200c05400070100c2071000d0680c00000c06e1482400d0f0014501030700f03080100425a164401d65401194040c84540345241c9460b03120381e424580c204551042c0c4011519111941c89030f080e40c3c070b070408940c0b012a078841e141d40c90109186d03910b10341140e020800008940c0002d11070a000d50403a82e0181c150303050300d03082807045070400b070300d10540c1e0000000038440c840c00302d901040d555005500a43c51555160030141006c045800103000c030840101550880f4454602928040c603441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 693009361 1250 693008111 693008149
    0x14010224130c030206070b0429060907051306030b1003090210050c0a0804030506060a05031c11031c0e16060c020f01030b27011401050304120212130608070e 69
    0x71521450800040312040d00041c1d00020042807001c10403004800c01c5010340e0042e248918084c0c045041110307003100124480130794041da60007191241c10701c4410590402410705110782040764218814214000c69401a00001c3c1c60304c59510841c1030a02103511102c00d14030302440040f4540d0045000014005c44041c108100003034940c6d0300020508c4883d25595000c1c102d142c0c0d80341d483c2000340e500d120643c3c03030038441c00c0c80000010301807030000380f40315801c4804200c208401d2010788e0700307403001005200c420919005c10007005039088442c03000ba4201503000c60000429070340daa2501403034816104a8014003e14027101807045a40000449a5141d4101c8118411440300b5004802030304046032065048500c3d5641741c0f82102d9a01d05000b80000d1082002905030390b1048581c0c4251402a4003501141c402c001140104814101464103140c00e40100d0f0ba89202400440440380d0107204101038480b0440c100b0700c241c5074009001904a01c0710300d0444548200c0400040490131013088901d10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 693010611 1250 693009361 693009391
    0x6060c07050d020604170303100f030f0209060a1a120703020313060906061203110f010203160c1412040e01050f060406030e010f0518060906040c05010813020a14010224 74
    0x4640e0380d00212405001d95a000400c86c03150004010355903042a02e81c0c001103040c030407020841f18603402840b0304a81d041040c404034444c0075000d03c000c03404060203c07504034500901c0418420000d1030340b02841004540d9040e80e604510000d0051882c0190040742050f004005208801031894002c14405401800000e88041c1502d05080100365176845070004103c40d1141074213240c0c0014004104444030404d590f49091060703811401c0784411070b0000941094800c2058000c0d1088660015251050f4181c114600661851628184070100401c0d04038170001001d010303281300034098500602050f50b6403c5d00c8141080042c0080c080da0080310101603840c0c08800c0d1a80094020500b04089048200708600b00510451800001901404a580314001c0415814500012010311540d044000070214a00348001110390000141926010341407120401025075206041003000313058000b42c001040c07504a002904182c820005980c09800400161045011147e1410f5004501c00900b200b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 693011861 1250 693010611 693010613
    0x30c0c1e091f090e1504030807050c0a020901080313120203030409050c3f040b010918051f2d050c0705070b0702040b0a0b0901030b1f0201060e06060c07050d 69
    0x7607206801c0350503441501440b0800100c480107a4440c1c180b040703440d804d85282c00c00c0d498408095841c207940040c00601d5000014425508c1640a00b51000320142500c2a5207450740008414080a82011196400019001c1c1404030003002074001018203103018121040580c000907201d016910608c2c581c2510b9100180c0c04809000c121203074100308a444104c01c0b400132640709206032112004600d280c030300a820a5002202101c140d101c1c59202460110f01c0e07080207201000b802080e016482d00241c01c00250000031814403c1080c50b100d03101c010360307402d55450030001c00d8404920303212010725060b0305002c0c0402842c2d64010740000c03800c0c0d00130030243c54841f00104a4403805001600c140281d19010407608c0e1a00300400d000c1b0b00854081c0180c64106040000805813481052000c0c9070400c0300071a0703540650040003000f1002011180c2c40107100034080080104860700c82c0050b5910304050041d100040d00b0309410290548000d401c150400111648d10100ca0042c0385c42018609050380c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 693013111 1250 693011861 693011881
    0x181a09010507021e03010e1b100c080d02180a0806040f0c050a0303050415032705030d090f200303070201180b041d071704030f09050909030c0c1e09 65
    0x2c1070107502a081d43c15070321100d4503640c0c000500840b858031035401c124204404c20300009528110301c60004014841014620401402c03040155100090220100c15480461541d001030680424180d03005a03440340c02d44501107245c510008040c0c440d0688041c240844a0002800c0d5489030348290b0810188045040034070341c490f01d0b944066480030320400301004040e44030001d070084800c945111407910360900c130b0907001d58486545542c0644003018598440340512144c242505000e40162440c000f007002030130041d14186c80040e2141c4488444d0001000009000081000c848174905a04214540c00207500c80c800c3c00800780c101b00c02401680d031480b44541f00c0d48020035800c494259280e603915a184c60704c03045500e4041004128100080c017141c041c482c0008051003030b2400e4041c03951641e1303090381c0c40c508400c02e41007008401d08000c03603140c4500c00030034090700400000b552201500308007285040b07880c6481900486c5010381c0c42c03402440c030b42d0110300002c0080354603c2a03541c40c0d406030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 693014361 1250 693013111 693013117
    0x30106051b1c03020a0206010e010303080f18030706140f060a14030f010509010905060114010206040303021b0706030b040b0402180f01171501110303040c05131401090c181a090105 79
    0x390080361020310390b50640e0b8056004240803445074094500b0b80e0780e100c080c03041c00842480050045004130000500e0441c4c00784580364004120000c49142d903032071000052540c0c100c10800c0300c6203651050f000d080030450ba5500356000702041c41116181c034081001c00d417080014407460210406c11864200700e99003d101500d10407004400030095460180201030203044403900c280c0e2030380035142c000b09180c114940054000403040c1c00410964580da90114025071244103a401d60744204005060205c80070b05c0100000e0950340d4012071038110a03030030441101d2200c80740364440c0307104205802c4140c04092403502445021a048660214101d0060b42d044890503c040c0c8459050b408010640b103204000010540c403c1c0e032060056054801400e90341c0c8010ba40c00780074890254000c00581c90700b0351407009100c0b4105030109402c25090042d0301c4200c03003038016009440c0c684210040180c0d106400e1b114101440500d007070300600c0c10902c030f20101210445600000000100104564010822 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 693015611 1250 693014361 693014383
    0x1090e0c060f07082709090a080a090803070302060702010510050a0b090d0b0109021908060d0f020a080a0818010e130515151c0614010809100e061b030106051b 70
    0x510780d119440c0c5c00030703110200926002c04540070000ea0040c12418000740b454071580c41c01c8000c2c24400c0c2607807a820ba460b000303001c01404211807018040fa507120188090300e1020b00c207400030310280c1070446010703081d51002030080b8403d04d0f100500b00141c1d60341440400841c0c910308a610b80d204003120204186a0300050003400c10082d01d0000201820a0f81c0240080c7c2c084400c1c41103065000340341290038000c1560115403140c0124501c3c400309400d009c003118598402403040040c5540c40c1d03031321414001c0031401a2a00d040116910150346942e82e0b000210840034a483c405076001800003800c6501408903c050603a0f8610002d180410a81c2c0c014030b006030300030b00003039240c0d15164234449958007204070105841400158002c0002440c082c00c0300355518400c6e0069280c024400465403024020f01d000030921401d00300d44921000380c0b00359060000d01002400c010b2400007069035810b2000750483c456005d04100412010b0750010a031a0900d40b17010380e10700c0c041072182d156403620001e040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 693016861 1250 693015611 693015623
    0xc150b09070203180303040303200a051002070302150126030c030d0c030c080f0112051e06040209070503010305070909060228091706160504030b0403020d0801090e0c060f07 76
    0x81c8034006400201400f54410764200c81e203c400f4801c4141034585c0034620000700403401d1075000f052807040381c00f02000501d0240007121100030713860700d50034030742a00701d44204204ca50005444d801c2c1681800172030782d10188080c8460045d450804c00404903800d54100c007c14000118018500741410700032100284042002c5030f80718080e02c0310200003442c0814291010900d01340011000c14001d02c40d07548924103240241589030f182100e0600d41e2a000002203445d4000d004141c00c003c4805509500501c80340c40003481e1601d080c2c41844800703403002d0130301c0703007400b000f80010000181300146180c01e50345c04a00c003040e01c41c020301d000b00c041e000e8060101c0c00e450465012540d80e1220903011803000a2035918003c04a0742d640711841652400700d2880030700d402040000c0e5030400042c91082d560502440c02900c1d09a880d1640e00c403a4005a070100c0050b0040e5140d520401d5122410f5805004000000c001c1d4400900e01c150390f071134000440d6401440c3c0410410303003546224007036812040d0410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 693018111 1250 693016861 693016879
    0xf112e0f2105070f020c030a0305160c120b0916050d03170412092903060d02031039081b0d0f0c110312060604090c050703120b010c150b 60
    0x7180d01000d840b003240c0034000120054600740c80300307100144461540d00007401500c1c600a05440455050b400006100c10041950030300c9000a0b05c00208040141002d090707185248080f86480c041440b00074040f01c0321640440d540c0510700d040305108004031007086524a812100718601590aa4031140d41d10303207544e1105080000303000d03540340c42d001012440d035202a40d540d19200111103000c4000462624030034614104040c0010800046400881c0104241c10400c038035070010b403a254044d8001100c02d501e4000d240a9074a0381c9a001c00000610f01c48a03140c081d050b15200054410b046500c0b041001d1080410794000703103003605d941803101d040c02e01c95071807100c4000e01024042c800d00700030501d80b400c10394403061882030321120f0341a189040558980349204200244441c0050f00940d4480c10801000802e50040c1c030510050321601d4440c00d84550340d900340546080c0c1030310b00d01c880080c02e00005058507a1301c266070044044e8015110390600d0103240b2407400402d201611981c00c40070031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 693019361 1250 693018111 693018167
    0x902091516020108070207080703060b0a1a180901052b06060f080f06010e0708090f010507120b0f0102071206060e09030705120915070501090f112e0f 66
    0x14107480400389000783c90b800c005440f440340403aa110b00c54403550100b41c0064074103000180050f000404150310040c90081040e85480301044c80d42c0030b1540d80800303c680010b400d226808202070b020b5100c402160071440540c5048041041c000188001c400c0011004a20307140300f043d00584000d5480d0806010021542c84400c4074041106a0084007030b01c4c404c0c04500700c5041c01c0021103d060b54600d148100f080c2d1540c1405480020019054050b1401101d1100d6480c400902c122803040810755121b1040c0c0780300a1081d812250442ca400d8040d0009880810599800195200403600300b1001030342d40c44450b0802d24010074054002c95001c0000b502444140c0e01d0000203400c0701030088050f00d806070910030004140c0d1040c10840c42d040620160350498000e07002e00a0107c090240002040b050703203554804c1c0d0480070000c021a0001442e9011881908120800640b00000d62580108010b100314130041745e802102c020700100841c050030420407510030806120311080148280301000c0107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 693020611 1250 693019361 693019387
    0x90612150a1e030209060303161a090a0f12110703060501030203060f010f180608010227030d1403280f0b04060605070f060b10051902011509020915 65
    0x40003030054030a60031000041142100207562101c010524881c0d8920700b031a5500340458031000402050f45400140400d402c1030041540503502140320b01d4004410291175036070700400c080090300001844d0310a0070541c001544185000ca074480c0c0145031640003010051045a20030420001c00310715026611000082000a410141c183d078400c4080e03400c660f5462031b90780d00001e800d01c1000c0318600350850421500c05007001107406485940700105515480c1c4040d1426a401032500d58811981009881c9903440d60518002204004038044c10003111030704801444160400960000d0403c0000410803c20310801d449101107003203507800051007968008000205040045003c480d414080d03044031500e803900c00c9030b0503148161a05800c00920b5192040320038002242260103680e00e180b502001c0c0e81307170100d14102c051075a49141d81c9421546200c82600d0002c0b052406680c1008040a8483c0c07514111405882e4000d8006880d00785205c001401d002101001450360300c0000355501d10350398 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 693021861 1250 693020611 693020641
    0x91712360609101b0e01030213030f020a1a180604030c0b040e01080c010503040b0901060503120d0614152b0905060f0610030c0e1305040308070206040206040b090612 73
    0x8a071020707100c4035110011a40c065804d45000600880d0021460040a5000c2c641a004c0c0341410301d4018100000014510042c0300660010344100700b0b42044141145004441c0341c024000c01402034000700c00c150950729032400f94010080d0500d5414a40c1138280c0c039290180d90003150480d03c811045a662800351038207501c40c1c002c0d108002090030012035583c00000d81ca0f6103004041c1c1d138461856031a911034007400140035000c0d1440395285d040028466400700b045425120141158503035503446000c400701118a107a1051341c040c40000824407280d45c440c032400940089141c1e40d1a640c1103200342007207206150a0766560a03100150180b94041c88d958403642d84203100c0c8048a4140c0c071022a1100d860f6012540980d01640e00349446034894031a07044003c00c0b11580c01d0200100318403900155040d0b0000b41d0343c01d0160341c0d401c204418550711a40c402c5c0c000806001400c082d003065004100c1d5442240200c54008000140303491507074403148101d44e02001036808140c01d41c2014903030f0b520205 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 693023111 1250 693021861 693021871
    0x1002040902040f0807080a02040216060c02030a0e190506030415020a020304030c12051b0315090c040c0c03080f102c0108160504180f060917123606 65
    0x70300d40043c0454182c40008842c0305850188000b811040d1580c0d082002030b5101c083c00060280800340440001410740c0103d06020105130041c640391500604028084e0b00e00c4990350780b290054001c0e0103003805010035040c05881e800d88015580c0e507140d00300300305c0c15200e004030025503600c006502d103070341640800078100b503e2007244950384079a0340340d00020441c030445001902caa00208120311882c114035031605041540902555429500f0354912030034500704440003e104d0700140c607109041e1074a4824071b81c050540e400c0018100a560302c0040481c580205101c2c10004001f020401440a60307014500800400402c800c150002c211050102d6040e80442c2401c0800307900007052560001c43c5601c492514040d402030900c1c41d1000308405400b0b4041c91600030880072135400049000301c51a00c8255004110105000c54140751000e104178404050048048080c0301c1041c080310710000f2607400007031402c1076a114000110104c1ca1400e98400090300c04021390088110750003011518070300c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 693024361 1250 693023111 693023129
    0x9060f0503071e0207150e04052d0403030b09091c0801050f060d0b150304050f1912030e0313170304030f0816230d0c0308060d05100204090204 63
    0x200045150a5030540410707100e000100d0050b0030318661014100c022440078041a1040f560b00c9641c0d002c06140305003400145800107200c10048040e1070400d40181c3c0e40211541441c0d0859414880c445d086106000e80501040100c8a0102d824035200360004120000014258003543c200640d50503903814440082460b080c07261042041d0b11805007451504841c0060407524403043c02030104260340e80318044011405903a29000e41c5c80f500c4d01090300341c1c01040e02048955a06060410910702200d0b18100c00e129030084a058094614080d107000d003c3e17034000d4103441c072074800340f0b01923029081c02054040c0a110101d82007841240050f070000440d0300402d824440c00a080c07054036101d00c00c6001c0a0310300c044001b8104006911b4100502540e0f003450b074817058170002942c554041084500111501501100006064607401d2001c1c10a2403111b00304030003010b5041e500503180207402000603114249000c01401132007030901c12000c0c038030600c00c800c40d55191588280ca0094129000304203174 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 693025611 1250 693024361 693024377
    0x2040b0703030c02150105060a0314130c080c06180f0d0602030a0c0c0209011e090c030207060f090308041209081e06100f09150314011b05120a0905010b060a0906 71
    0x3c2e0000c10701c1c001c2002d4500a48803e6801e100c1800050703440304100d4400c0503a100c000658054904080c10300400006e98040444025410205100d645d01c4e08084000c0d040102070190564625080ba20302d00d00790749003003c2d21186100055420090600c43c0c98002e03050703083e0081008013550081d4446d00744103508210019411034101d41c0401c42050003500106d0800c018081c200c4200c11444540380003001c000310464440c2c060000765864885140302082d008207102040005e6401040f800c20310500081125081c503490003828100c014001500c1c5000c40098111124450547d45001c0d00785038044a03481440d0320250070038102d4107814000117014401c0420588050442564200c0d052000719807251410144094001d1600d48001c00100810708800400150280c401e0721030680140d00005819140ba900380c6894045641e07200104001001205031050b07401802da90000504640060410800d01d0b15900410074500001c3c1d201c031010901c0c40e0580d0340a20700d08142c82c0780741d40d0600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 693026861 1250 693025611 693025631
    0xa05100e1905010e0405091908030f390c0714100305040807062408060a0606030605010903031121041a070c0312120203010611060c07110d030e0402040b070303 70
    0x2080d10940a0300b800074421144e400c0e41d624203500300940250b004015201d600c041c0c18511607c11007440400c44000c0004000c100405800401c003d5001224081c582038180040d6010031011104a002e4100d07010024104500c2d120110240c5141104810440d002182c556280302090b01d80500c11900c00c61500100204d02403090042034042d5a02c51100d604091566907947c010380f500034a50310358850144401201100c02e100e01d040100103010203082c2c1414405990020385280360070410905003403c81c10401640e02405610443e13800d8500415612404900c49003030900c4a541c910388a0390b9510255851210302c03006008132120710340e0b101d0900008089040c10350184030300203008041d004a040000c10131031142d1072000342091804e060922154034041d8126002031f000040068035904105034807800c108001900b0082854035103051100300d50f502402e0b50100060180640b217140d004504242c0034040e0340740d8501300104150345440c1c071000d002540d600f00301b034140c00103410a00300b40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 693028111 1250 693026861 693026899
    0x20705011a092d1305010c0305190c030605040903090806010608131401021207091403060907060e0303070501021207120203190203090c0d12080c030903180a05100e 72
    0xc8001801520700078480e99000014001850310044114080001003100b40079890184400d034810001341e0604100e460300c2c0e0405900f15003115001006042c0781000780706d1403260b2080d003034000c4c2011400c0401c12000c20356040700500540c2d408142c001d810300d880001015001620300d8207030360a100032508140e0341c030101241c024105890308003004c1030400e240c3e408140308012407001c180c030300d4001514010804100d403020300070880740c1000249104d003041c0300a03952840b0128103140128014100c0741840707240c40c0d1312900c41e07124480c184154140d1185007602e081c001c0d60401600000210744606500808100c0325104990702c01c0001ca820104c03406105c600e100380c0740282c2400c6180c10280c0c508500c2c0e08020341c0050032640c451711603408207800725a550030f843d24180f4400c904040c03c4020141d40940303100c2019124860145040c0104003a803400002a55510a0300494121f40d231803c56011821242c5c2a421541e0402100240c91200c1a04070031000d18003034040da030040c040030040c0701d08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 693029361 1250 693028111 693028151
    0x1109010c020616055704020f2205180c0d0603140a03020c09041a0703060b0408010b1206040f03230a0201020a0801090b0a0e0a020c0102070309090f020304120809160902070501 77
    0x1d60703006000301d440c0c0011039455005d050a511014100514021208010740150340020014000d10340030464000b8030342403050007100007003209607003107094001601200041e604008001e600466000300307681207585e40783e401c9900115084403200c000d0300404400e850312408001030076409885610424003850400c030099030700c41e6402402420144e01c0c01d126a000c2c01e94040c101804154a8060105005030720100820050668000008481c9003840a106042d81032940621482d0480001c000109415164600314150305140010742414100070640710b400402d03100d0008280082840b0216540543c010809035000d42c0301e61035180c1c0c4c0c406c09071080e5081b04950700e81000303160508000c84690740000396002a000c800150810050039015401c9130081c400035400909400c8003003040282510a09100c0c58129034154076502d0f15446441e1031010200d0584104840d400008034a003000780070b504540c81e0000c450304001039a0303d08010280d003007194103903019441c1101e081d103241100c3d000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 693030611 1250 693029361 693029473
    0x702011803050301060804301e1407150f02030603160f090c0c050a060b0108011d010b160b07020105090c04020705100c02070905010602101109010c02061605 69
    0x50940396a08010080740d1801003d0300032604d0a2921610320303c8801c2c2507040e1480c542d200340d0740345c0700c10441c107500501e9482403d055064035800042700125850f409140c84c80c02c0c2100030300c1180e440005140110744c40002d2000100011b181c00340c10041ca524903002540038403401c60407a10910b06001d81c18825a00074840c0c40c56103103110000304422000380d0800004480c0b1030900c000302000d00e1303e6407400c00740c511004a40040e40c804131160291b0f000391030079015003498490528541d55603000514048d106004e00a000b4034086400021303d400e04601c03013002984103410040742e080424010b806050143d4842926005205c07201c0760508051003a50038454200300180000c0c26800280402407104090101c110302549601203507050a40c010503000388202c5d4010440c5c1205414070000725101c00c10b020400c0d1104100e840300d26070f44010002c9609404607507243d90340141c022030480c001003a200080c41c5008040005264400c040d400460034800101c0b000301c08420406101c550406042d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 693031861 1250 693030611 693030617
    0xb0a1407030e010626010e0712080702040902120f010605040c0905040e070815071d010f12020c010608030c0c030c03070303050d0f02031f0e151210090b0702011803 72
    0x400204514070a0b0054105040120000100144c54690651540c403183c0400d014030801c0501e654451a024802e00ca100148500030b09149400c02208403800c2d09001c001400000020401400f95692580b01803082e80d4002d000410185800b4092511006c3e12114000b080d4030341900044d42d030900d8040e038000404243d41d0307070310300270300301420000142500c0d0700301103035031261a2012601c14020081c42d004807500b000400702900d40000300504614484045007005820800b8044407039030000c2c0200ca4071902410841c90310240c0d114418000d02584801c080c0702e41c2400d0000030740b0b00d03010008000500148056036585500300080c56640e03061040c080780c0582c4902000c0001c40c1c41107000e0440620107034404a9909802070380601a4ac00a560301d0102c08901141c1c2902440c0384030065004103103c4151602c64600400303103507824141a00b145004050742d0f614801c00701c0d0148950440100c00361270812a4a1950410340c1400d48101c03041700c0590f10b050100d10001c900490031414507a41a9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 693033111 1250 693031861 693031901
    0x7050930071d04110d1a060613150309020613030c1205061b0c03180108070921060f140106090f03020904080c0a020a18061a090f032103040b0a 63
    0x2c21506501d4070050007074545200c01300a9100c10b503501643c94000320701910f1801c001d00d6412042d841c403400c01400c3d442c810301c010814404a0168911350800f2140900503420007000044001d030041c10745410025806403000911014640e504a442030640b40540036802c00181c49090050344c444403c200174080e0b0f07000e42c00203040300c903003220740350000d100308031405042007600d80b0f01d14590740000090708111564602165a5943d00259940d03100049140c0082481e18184404081c10a84100510600d104100707820600a40c0d4008041d400c4103d4805c1040480103013820901c1e031400e009100000300078480000d000904c0d403807410147d1340c0007042d0840c192204d035590685503120b00c01070f442c64080d41d249840945d55056607940140110580240a0020320181c2800c840350390300f0000c0300013800000d9603584040d1909440d41d0600a45101d1905103002d0f00081c500210030021400750500d0000440380e608402014500a920400501c0603030303101c94901c45c0c00d03504a103403461001030b03800d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 693034361 1250 693033111 693033149
    0x10b06071115040b070c140102011802150705060a060503010b03211e0c0d02060c0a0806190812130e0405031c02041502010b13230705093007 62
    0x100d0b84904008040c80c20803031a1942d80c1100e00c0d0079800404045d41e250080700302c07c000b101144a8014111710091000700841c01011241001d0340003103481c080d004003800f40040444487e00f0088a5441d600801202d4a03403400030321400181c0f885026190080d424040c10034010b08000408610070540b1444014580314030701c42c00031650b00080b5016400c0c201507d50304401d450440001c000344501940588040320308040d02130305d0001d02070400c40703070904100700404825500c8618a03411100461790a107400800b88000c2503c2180ba07080704015010f003114030354840c42e0602c0148019105a000180040ea660403000303280305080710041e085420401c400121452046030030596500e045030010300b003517241d812000071001918100c002503951040320820a02c0c01003044620f06040503401d0090f181c064650b40c20182003800e0350940303a100e21020580980c020000c1d1001070001078440da02c511075000c03060140c481c05616a82c0c400180b404103400f045404078610054490011001c0302031144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 693035611 1250 693034361 693034369
    0x111e0c07050603070f110c060711100509210307050706020a0308060306010f090b0307030b01061725050705011b09030212070b180117130c06050a1b061503080309010b060711 76
    0x100c0d41051b0354500034407402500581e00c0001904440b8003da0b4442001c4100b1000c0c8000070030444408024040c06000b00502030b03540304130810381845034505181c0e180c1c000540e02807039401000402805401155008210300b540000d0020050f8002d658880264031094107040c1c4443c0300b8060202c0e40038008509202c070b075105410032542841c016040311001552074441ca0741400080c3c020000081060965684c2844c484ca0080d411081c1c1701410200812691036048880940d40c0710b1300d060010114000b024440f003984041d0002c2000d1500f50344a2044100003010030720540022807003030000d480910401030b00041e1400075100c0003403065140c0a2a002c03030507030100c0000d980904000c07036200d2500d41203450b0718520703000d4004080427504807461860300c40f00e03100c5160010410031400f0301981c0440c6501c00103070340640d52010b445146404260074141c000c1c0c04221601d0503d6103000030000204041000218400d06d04500208491868001000001d100d990400740030603100003464442031030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 693036861 1250 693035611 693035627
    0x6010e010f05091e150c0a02091807030f150b0928020c07050f010c08030a0218030613030315080c060c0708060a02090a0f18111e0c07050603070f 64
    0x144500b0118100803000000840e0780b0035240d5001004241044019003505054410f000360801500d03240d07003043e6141100d00c0d65000140d1019104544401c0418004035100d40c0802000030541c0580328015141c1c107112202c20038010045450131820004070040314060301c01c24541c480c0052660269864181065500750943c4840c500204800e480140b0708240a1004002490090010b004044c1c038150401100c141c01c241220305001c4262030200024001d88101d0764042c40c141d0b40141c55044070b100e2184540130340103095030103100318424001d444010b0360400d40580d1007070b6800e2240c003806110046107010700d80b10343c034220707032000c1100d00031858141e01400340301c1800b1044038226995540403e14014058500d4015241c0c0002d480303000781412842100544aa861801d81651a0036440b900c0300c044a910015040e942e080020701c1103280e40d003215100e880d00840781c3c209910a2a10b11807a41c480d5a0034036044c8210301000600707040c50740940e8441c50039a11180c240340e44038003050391204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 693038111 1250 693036861 693036887
    0xf090102070f05091b0d140103110901030305030a0504030e040608010f0b030d0507030c1b0b07170a050a0e0d060f1d010b1f0912061d070305030406030903050d1419020306010e01 78
    0xd0000d0100312408640303131240b1f501202d80d202842d0881d52641c10f0400001b10352040003801550400014004682c1180403a40c20400c1250001020351322402d080320340c0114214800ea0140c1096030028003420b05400500345c40000d050200002ca082070105070f42c8501c1e4a4642001c200140b025401090103403004513070050207070510344403400d011224030380221529040b08018440100380c603814070683c141e030000b10a08288006242090484000e4243e0090180040c1003200c4541c031701034552144c002e07120440b03078080c00c01c1c007441100c046070320090101c803070511025840c3c09000d0040e60005015500c00100302502401512050b203e2200030203280440103c1070106050001a0341c965101d008078449005050001e0340220480404541c0070402c2c0c10192541d001c10700070f02c003203900070007280c1c02c1300c469040000b07169421740380070b803014002d40710002400703890210402204980a41c0c1c40d88154180c0c90070b80345004800c2c0c00f8104a000a07240c0e10b0005559a02c1d4903000d50140051451035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 693039361 1250 693038111 693038161
    0xc060d020705030c0d0f030504030e0906030a140615010905091f0b040b27090106030203070e06031911120606030a11071406010803040503030d200f090102070f0509 72
    0x84007a40e25540c1c0f4540c003034150255a5840f00b41040e0084e540001d602112940d54607052181d0f0901d610001d00b48405002020b102d6805400403c245907010480081e81d641c0c016211050038281c4000b45441e0001104c4450301481d001036020780e550b106200b82e5055070f034000e00c4060161614480c00c40c0508003014180611904c149012510079102d101500050400d140f88958544143e190b00c9d00001c1c0f4503c40494168007002018060341d59100c03c0c5055030914640181c4955034108121094410340d1400c0f07422040000034091414a2a03501070710700342d1002c01c140701d208003096100010f440b0360440e1030503150f08000415110701e0220003c5800078000080414000c410000c43d0140e9402003604981158507088079041c03100c01805064014950324024600703280ca80300109880c1d01c2801c103078a9869607160000903696903403803404a0000904080e00781c40301b0b4004a0706401e41e2001c026180503200700c0c070b4001008603103108010140e80c0068a03240302902c50726865450005600300c80c03211 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 693040611 1250 693039361 693039367
    0x11041a070b040f06060e090312151e180606040b0706060e070309020901090204210c030c060c0c151b030c08210a05040b0f0910050a050f07020d020c060d02 68
    0x1c150892200c5025902910000c03400d0b041d140b821034202e8680e98400d80246d40b480040180000700072003035600c100000044071601d5624060003443c00001c61014940c008105c900a415904408502600c900070a5401086481c2940406844030004907000e5a2041d410441400f200e0000c00103081da00d0700c07030b620100c1d0280d100e1026a8103c48215030000011740e40e6159003040d0301e4039048072801030911507021403800f81003405914010b0414040e42c441201c1028424003001049410780303005580190320101c285490301d2004140010408059804403243c3c000800d1a40c0e03000c1c040900521951a44d004881400c1d102e840d1805009200760288a200210344011890850003810f8401c101981110441c80c4080617000c902d501400d480160303440c0500700000140b983c5643c4c0e400c0311445c8a03a01243d07480400300703440c103802003460036140c90070201402850b84094109500984140a5012999807070250032039446800c00181e0340140c0c0048030304849410407100030f0911254000c00503107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 693041861 1250 693040611 693040613
    0x140316150e120a1206140117010302010f14091e0102060f0f010510030e010c030b0103061d06040b0616060603060c02030c12030a0612210c151805060a15050411041a07 73
    0x1c5034606c0c0e1040000303042200030005690ba224506058003010381d03041000315411600020552280c0500c0c41c0141702c5400c030005890821041a101c59500003000d4181d181610031400e0704071644190314501503ca080d001c101c0f040400c60401c0e02c54010514407000c035a107010100035040030b2000800d4181a6a0110000d68103001c0c05002000c032681d4034042000081e100c0014101c4100364898004120390000010b0070b25103203604070313801000449011400300d2a207070002c0d0b1a0b00c81c59590181c1c0d00d8496801004012170f82e04500c0071240590420002558801d000f6031722840f03030305c1c20511f01c0e822a06641c00e0b55840c00c030183d500000c05280004400d601d8410107001000711031800d0703808921900c0386c02d043c4113071402034003075407c2140f402c41c14003040b5075524924070001441c00100140c4501824801c0c04d44240307205c0c1e8060f0080100e495505011031040c000700040300f1f8822844042c0f0b032010580342400c3c003480b52011146c05143d49480d1401040a203403800f401810080d86104111206c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 693043111 1250 693041861 693041897
    0xc1b150a0518030a120815030c120705060a1112040e070c0611120a0506010318080904020d020f070309080f03070b090f03070b0f01091a0d140316150e120a 68
    0x445000d21900b0800348003d00c00358040e283c0100105400f4944500c40c580305408c1d100400c8506105000340c0f6840c51202040d00c0c82030a0207910780115402000210322010b107103910072040d20044054201b9180e441449100c171042e144110b003e106502860000412019817240714010341280c00740500144503000c03074414040c16401082074590412000d018014900181e1003965086002400d040018092405801000c0da40d0200007a054802c04039414955440d541c04070340c030701100c12100f1580c94207105400c44072070300207030025400900125804603071003100084502160407064009e42c20521161f03904049044024803060190041c4810020400320030005004518440d40f00b5420070700c1d01c84200e21174000140c1c00305038103608100300d4510f6800c070b00d55000c50380402034408110221590620004a03003450900d65001e20001540c4403600d86082d4003014040d1142c0c4850352511410907200c0305482020b0258030040d0009403078188003140c0f030303401429040d40500700900d003e415191700c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 693044361 1250 693043111 693043123
    0xa0f0501060c020a1d010509090c060d02040e060409150f021903020c0d0206010e070e030a020a0602010c020705091e04142e021c150306020c1b150a051803 68
    0x10720003007500342111004621300030f104c0e20094040e0b28081318035241100e000c10300321001031140c1c501445807900480d03e1110203210000c5401ca020380a203a4401e0b405590301c000b54000e2103030300741000100021441c0342c94031303010f07180d051900580f0714800307941a051040700615000640b800010350030000350000d5240b064480c681c000c61a2401a03da40980350b41d1814010f8516401c2c085410060040c4020180042600d40290441c90704034202c210030300100f071421103c4000a0760003003602d20000b40c3d183d41500060f00080700e41c2d00380c4051564403000d1251a000c2628103181d81d6070103041c0313090590608281242d000d0300445402c090703800812012400d00c0008103521100c0c40500704c60f40c02280f000c2d01c1c0b02500031a00401146000280c04881c80350750603420025400c01d840310121180540c09003101d20203103410103011951000c42160f4240c3c7c40440c602c4000c120341da00c00e5084034600d0b20305071a800c402704c1d055a03a45020080e0908541c150b0040201d40d0b00619100b0401c413440e1010844 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 693045611 1250 693044361 693044369
    0xf1302040c2a170304121818050103120c0f062d0b01020714060a0311091302030f09030f160206130e0f0f13080c07090c050d0c050a05120a0f0501 64
    0x101030041d003028140500e00724014424140f10560030418480091418032250702c080d1040c2c038004814000c0c540c0711940300c0c0210ba102100b030250000c200d141d69001913000743e04884c41100101c0c1003c0f103646058521049000000d0b05c600d18000189000c0f4034250040040c120383e01c6c2d0001e21070317882050400019034403480180551940c0392541071030355804010f40e00142864040042e01070f5400300018200344aa01300386020951201540c00301c40d104132007a40c602e290010000400c80d03802203840ca00a41003198040f10048050703001c980c507801d011040b180c00015200c103051409034104c00250b44845158412a008641040030400c1070010010640c06001d8200ca0300040c1d0400306000130b10ba550140141c003040100006028617804440f8502d001c1070390281c640c9854803c042e00e042c0c00c1400b164000e0014078200003041c1205a03004000f0800e500303050130204030104242c00b0444040c000d0900820109004100100c2044c1014941550001091501040d468004107482d0141c1e9001e82c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 693046861 1250 693045611 693045677
    0x1b02070b2503020a061a0913020f0621100321050c01061211150d1e0207060507080705070b19020d090c260715020312040c0603050f1302040c 62
    0xd140c0c03007005886d00603114070380c07412111541603504400c0001c01c200c5028052135144005142e0301c034219103454442070320b0b00030001d001e030f6100c18044c1481d00d84a041020400c0a40000200240031380560b01c0501c41031360f400c40c1c41c6113003543c04101c1a1420101c220b410100780a418400c03001129424003401000d00b0781c081e0b0ba0340c0c504420b898507481c03080c43c581c030042c413854581e005003c0c10f000101c180c8207003020452003c1203503074409035101c8450300d48804490700715000141990034881d841c3c020174050140c9580d4030000d9074603854100c0740780c0034a440092072941e1803c042034540e00c240c207200010900c1464018981070282642604440308400d0403244112800d000300042c61210729a17031080421130821514030f500060600707440d11403038080e69008803450300303c0d10391182c030800546042c000b44000640150410741050201c600241c810324000134204400a450440681e145134080c6103010985400500301d03500b00805864240101002c2004a0108001e01c2482803001603c03401008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 693048111 1250 693046861 693046873
    0x821041209050d11090613050a0204030c0602151b0d02031801050c0c060103020d1704030b0a050705041520031810020705060f0f1905030702011b02070b250302 70
    0x40c09410380764103902062080d03942c0d03c41e110125244006031a8100e008880b0140155240310028003615001210720750410710700410001c03081a180d00070400d40e805140b2003042c842ea41c1d80200d0f9a44554003800040e00c0f40640072901e180ca84550b200c00c1c9207801d584c06030030f040440781e091003243c0040715050185000072a80007121390b070030f105258218015456040c6080e4603040c10558402040c840203002e5165800e4103024401100a07400010400190460b6140d80e20b050450442e402610301000440c030b40b801042c0290b0003501114121b8552480c8910310290011080e0b40e603854888205400250800716110841410300086c50034010203005100d5003005070051211904c1810300c80800e55001400c02d000aa03180015542030f04407500115680e00c900c4544207905029400000c203072440c41d0700409100541010155101d012964020000c09100001d807824451000000a0150f04551414015880b011004040000c41c10103403070703561841e5245048190510f6403007500141c02c85 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 693049361 1250 693048111 693048143
    0x30b090a03140c070b09240c1b1c110306074b02030d05100e06030601030803060105070204060f0f180e0606010f12050103150b011407082104 62
    0x3001040b41d2800c05924001d003000f203071540f2a5600c0c02d0754055402542c8010407140c010f0b87e0f0714482100c082500c0500c503140501518105072498101c0c192211041c014440740d56200d0ba10b6140d07800c02d9142c000c0001305a543e82104000310f030211140b043d180d0803a490061030f460b440030050180156250366542d90110200b0900307603500c8404010310440c0c404808000280544c8480700c0343e0440304207400800151a8441040c1e00e103104840045c0800c41c100400c200030400140d4526017100e41c041c0d250002036440c28100364642c20240002000002d051000c2103d40d44200098200103102500024034507448442c184861003042e44036148010443c2014000310103800301c007841030403404400b40302d400c0020300c249440c0c1e50020001410454058501c140d058412091042c0b0f801180108001c107503100d0a215090800e42c245103494035017403014206040d44904110032003031070b03078480701410040300355500005076002d00d10381c2e00f81c111011580c07803800c005405054085c5114080030707514400e46c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 693050611 1250 693049361 693049367
    0x61b0905010c050706110a0501050403050307080c07021815030f101803020a020d020d06020307080103061a0303070b18100c09050f0d150f0e0a050601141513030b090a03 74
    0x42500080e040003401c0d40d0b82800101c00003450025071320503041001469102e176200d00d244c80760044010b4619801d04061106241d0060000c501555207a82c400c86545c0da85030040c20140b003001030094028500c0400d10301c0c541000c003103690b00300000741e510540382e102e058002450700306508103003e0541c1205803d041181014400c040000003142c01019861006450183d00c456a86502901803044107820800715518510715044d6035511074011916828048bc0050040703000f400100e44151919007020180c20601c18041458070004004604e450380e1075884424115028100120060191585441021080c0603d01c008000040001080420020000c0815072164000d5000d0361307048074841015203030f01c4d00520881ea0080c280d403840e800f030641da810080030316894000039586043c4519045560206038914410302070790465400d42d8aa50980901003000c2000907484007029a1030444502c4007409403c500c20070080c40d40b51680c1d0b0780c48007003200804540050b01030300025401b41c10150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 693051861 1250 693050611 693050627
    0x504051908061018020315040501080d2d2001060e041a0c0403020f033f030c0415021006030c0e0907050108070c05240907090c090e04030c061b 63
    0x148040700c0b020510b03e00100100d1084d03a40f030314491032a40000028017091b0400c49a600b410001500c03c001560355144240e031502c4a681d107881c0041c8103580d1109950040c030420790300301820200004584800c0c1007064980d0116458000500110000c40c00c514031020b1007920000c15203592a11405c2c589840c102e0000c100500461014204210500803ca03440b1819101501e41c19030f50020225005400a880c1a0203030406084e0b0043d04925200a80c0d0354ac0029043e4800c0f540038107e0441c2a5000d42a81d40001c4409a50309041400208a500300c10342c5000b03121907641c01070310000c00c90b160444040c2c46c1550401d40d4985a04201001540604e290300c1e0751107101e11000d890100d081600080c07130304802070081d40410126413410410b010302808030034800482003039118010760319003400c100742c0d0f00c0031113403031038030380507070100000c1c0c441650040c036052444c44d40e180d0b0340783c0d8284030742110348080241007038007045000640c1100003503091081c1074050400c0c1c1d00180c880d0400c41c400030b03d000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 693053111 1250 693051861 693051871
    0x15150504020301270e1b1f120b2704020a080316030f020a110103050606090a090b120f0c010309080c01020c010b040b03030a080f0a0e0d05040609060804050d0f050405190806 76
    0x13070325160500302424004100030b01018040e0301030201490000c40000c0440d0496400080b10802c00b03002c000c10107400407000c07854914290700c1030000311040010403020300e0704c101700440303814020510b40403140b08040c02c7c41da0081c0700801d50340607151030741d003094510380040229201c00700700841c100007816000301d000d00c4d142440d440181805c135000c2d40c03000f4400d00841c200e9030500d61280b02055203966424261601140064100074417107595200000141019500c0b142c068110782c85da0003c0f000300030504513150507465004040480303003d4011401440e49000a8402d80c2040c408804e41c00420b000810254851500100e4000c1c0718400708001c803250700e61076610a03031080040380c00c02c54003e51016400000c044150042d07540d11078400018006401002c0c0041c01802591035030150482c01400680c0c601d95504101161103170000c0c0c0d48002d090b00d000d0841c2c1e0125003130281003071041e00c82c0d030308000b101e00c1d0950416960b100420324ad50398507a920b0a0762111074000b03000c012410001d841d404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 693054361 1250 693053111 693053189
    0xa08040e0906010509070e041d010c03050a1104060206190912050a020609011817040302040203041a06100c0f0320070e060301020f0913060b12010501081315150504020301 75
    0x15007400c40b406407140c24807c1d50140038503115103034490581c803100302042800c0c8460009120800141000a008003400c8420b1510185004100003d103035041003130f0ba003654100d400412068440d820694610f0300e09100390260192141c0c00d000016150031071b8404466055160180c80d4006c085020b030408000500340340b41d5030b1400300d0f000c11205062500c1030510742c02072040c0e168072940e211180c00710301ca40d40019401500000920080010000c604090070290050b41d0510b0b403100e00810582c2501016400001204c411112011032005403849450718031070b0404901d99210340c18807166014580c80c4000c980d4128110801c8120b01c40003000d540218114003c51030702e000030340ac1e00706c54000d00c624580210b0940006c1011080b569000703c02408502c0000741e1102000010806105024001c031390020b00c000000ca045a07134121451800f031640503c0c43da100101c0500c441c001005a030100c40304014458200080b80d850310305c001e40c087c0c481c1c8108614040c0100b00d2002d40b410543c40c00c4007034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 693055611 1250 693054361 693054379
    0x60b13020a02061f1a070b0702071e03150b040f050403031a010224100e04060621020a0e10030f06092303070308060f190608011a030c0c0a08040e09060105 68
    0x103580b460b060100152208903a40d110007414140c40d09500e03001b202001010500f145090001c11500000c400084442426000f2441c0800d040c0070011040031703200051116000b103559851000749600588050000500000f5602609910401c2a07850940b4150003080d80d0700102091000d04100c1081001000c1c001800c4003012040e14084114411402d00c00b4510540086042c2c1003201c504440203280070310a83c00c0905141c24660004c2640c1e1040450444002c0d0407484440410319010b0056a0018004a45a450075500b5400ea00006040c100818800100400020400101c201d0038501a00c8001840710b8545491400c941418a103e088007020107a6540f80c09000011030740216071515260059440c2c54000c98103001c900c0000c1a03100581011259880200d40150000c848050380c400c5071907680ca041e80403506191030f0302120009000c0002402222103c001020748080b550200d03211569251580b4940ea04640c100c4481301800000303000210004000250140000b140c00c10a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 693056861 1250 693055611 693055651
    0xc1c0306050402071707051c090806010f1511010b0d03030614010c02030307060906140f100b0a0f03050c040e010806040b1f1422060503190f02010c060b13020a0206 72
    0x99440c84881c1d80c5c0c81e50381c800607251040220a1140d01d0024942841070700d00074841c140d0203000d5451a0188200d03520612000240c200725403100c0d142104d01c0c0800500055100c8581102c2c2c1c1030041800d07603c0781d03403a40d602c16515110501900c0d8030b503000b60780004089003040d540d40400c5d4000040503041109640622015940c044125002c855129800103075030340c1c6901c2c00d01d0161803280c044042d03901e211320812000801d10312015100d41c545007a8140039030384801203040c0074000c032611000002d003500034080c001402640565004014a14450300b0699145031120020800345c102d0103854101c00103000401800070f802e1034200d110300c8180e070340072500343c0942041d40c4a6807241050140490700000c54680318500c2d100044003040440034a1001a40041c42c00f40819100b0680a84911041000f5485088550528681e80250903070082411a00116080350000c82c0a80700c0b540d8400320414969902d8502d580d03010301480c000350b1501a0514007a050080042c440e8044d0405a42150 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 693058111 1250 693056861 693056873
    0x11030609010b031515180301050f0a020a1b06091a04020f041d0a0302030415141222050c0913260c0f1e071d06060c1c030605040207 58
    0x9070542e8000045251684c1e0303040f012209140c000c103003083d04880d0030684c1495903543c05004022885941c140c00c040c4001d40d000b81400ca0b10110303152001c003c080030118607400041d80080598005603d0055483c0e001681c80964014096008030f81256444140d038040107404a01021500d40f0100a0b440e42e2070641c020070040740c0340880c50b92040340d036000500301c491802c948414429801401716010461186030103556a0b01500405000b81c0d403031b400d140609441075031407a89801031101341f603003040c00d90440d101c0000780181c5a0410b0700102103002410003807464036114018000c400420003040002c041c000d5000000d04011401412090000d000c80c00b070400304000300c401c00d00703803561004800100c000240110700c16148140100700032155000c20020b90004c5c1010307660075540306010303640505030f0303500601c0c4203006040c1c810241c01400c421466101d65404000502040d140105110100e4200151a00305191a1224101c144440f640c5032040c000540400c0e241180f402c03649407500c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 693059361 1250 693058111 693058129
    0x30d15031403191803120908010b0d080d0902031921050406020d1d06070506090c031501090b1804060203070806010315030618080f0403200a0e06030708030418110306 73
    0x520244441804e4907010745444840c030400031a080128107486401c902c2e0010601c0e19240301e031041542c01c00020042600d40802c9540e412540000341d1361811249581890103040e6100e4241e0340740c000e040c10412074184401c1407001c076078441c4000311f0b01140d03c400e040380161124691002001014032050104640000307590b6419015402c24402c204030b0310010040070700c0100005600b100700426800c040010015130180110760900544500500040500d81d0701c0c03c01c1ca04003c1c1005144c001001180c6282d88020741448001d0300c071100740d901049030481d103800241d9017140c40a90020030081d41550003e800c0d6000102403900340846803541428602c42803403408060502c0351380740f806903407282c010407100070742d07e5203c200c4945803000242c031071180390407500c8203542d03010822103030402c0050148100001d0000c02001051042c0c100414102045002400160184201e41c40800c503100e082000e80003e0030350700300013000400e01080300c406a90300740280812074041401400156500ca0440c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 693060611 1250 693059361 693059407
    0x60904060f0608160f050402030c0702100e03011109040c140d0e0102070c03030207030314120a11070c0e1609030503090f03120c060103030e1906050309030d15031403 73
    0x881d61070039800460780105101d0b40f0500451248090450112242020504c101c0308401044642290b0303d80c1400142c5c8422541c4000d480f008014420043c9809400b025035880d0314130342940c5816401020900711044580e00e0174980001286501451401d80601c240041031031424288441a643c9007000c2d81c007a046420b0400c603121001c4110380701c82507050f503900a0f04000d00c125250b990b4200691640050300054001480c17104000d5100781600c0110b81410340d84034280d40895a440040c03030300502a000031071a0b500c0c0100b1008010078a01c500d0782c009080d110340210385034101290001410518100d1080922024a408001207070001c400e87d40f5002c1d0603240c14100030383c0d850001b0308040000c5000e1440d04030200304044811f0300013403c01e058911a45030041c200411808000d0300c2401e00e4010b40e0801d4a841092240a10039409580c10210b128112400c061000b0600025a0310322fa052a4040e0131a40c02002484801d00e103c0c00c4100c45000034500d8181e820745c0014801c002c0c41d103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 693061861 1250 693060611 693060623
    0x3171f051215070215040b0106020609070f030201120605131406042306010e0603040b06041107020603060409060e0a11030111070218130b130c060207052803080c0f06010608060904 79
    0x100182d00174000303052100210085500246003500c0c00d0180102c00f130103000d00510030030300020108800003520310b09891b403900984442624685c01190650701c440c09051515403603060005058617455841c11801301da640e00443c405070300810105188400814540c800d03420a0540ba0044080c126030f0035180031001c04001d40c0380c1d107000c01615035625400c2c01a42020b00081048148006425000d0142a00302c0741403150101d908121500b0380076001c00a90300000c10404a000c0345025444020400d02c9141e011030b004d0304040b4414240740c160401959403402807003641d20203107021702c5090100f5152030031540c1455000d40100c4c2909100c2095140080c1c00b0704003140d6090b803509460b104541d400011104585030014968111040c0300c10700f2110005135103008034045001090590950310007400e800203400307c0706100c0950f802011031112503010020303030201c0450001c030000c211030025400109105d01c0e09106103032030100164464010000000c0522015079504003000b034125401507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 693063111 1250 693061861 693061903
    0xd080f10090e0312072c1e040b10020c04060906080a0b0403111b03060f0403080703150e07090e1807170f011a0a0608060d0303020703171f0512 63
    0x1da0b0b414958803800010101c850941400c01144c80c0d4885c1000c8100415140d0040d204924255418808482d90740600e6100c410300300c1d241c1808440e2420b841d40444020408039a182410011a079042902e9a40b08010380112200880741d05013806040000c0640324402c00585250161894a40c411510000d103013110f00d9000c2018140304402e241c16852603042912074030705044448130034100080c8a40c60181c020000003a0607003601501ca03505c0799425498803002075860680c02c60040820503030024458036091000b00341e182c620660b6511a1602d6190071a6031420085100f24080e0000c16440d800c9610610340d80e00000086441004c54000c4040d5400e00704601030054102340403028460b803507601e01307040c0380c4646980348004008031382c058402600003902c50400300e60300301080b1401d98129400b000481c0c0028840e40c010000300d070007031600c0490b00314481a41035070301c0b07410398207020b400082a122070a0085450307942c200801007215803000511250b0702594a98102c4142c42135014045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 693064361 1250 693063111 693063131
    0xb040503190516241104030b01060c030806040510030b0c0c0106240e1203031303030c030e0a0b0408130603090303060605030403021e0c0307030f0c06030c050409050c1b0d080f1009 79
    0xd000851484c50380c240c0600c0050032000c1e40340d090750000d00c000d46405050100004a00707016090741040503030160350f800c0f940e54842007444041d201c050700000c202c8000200004c042139504520f80e0140c40650f074400c2d900d141d004201d60942e81d00780c0120318443c0c01d141121744007405090780c1c61001701c16410580c540014080001383e841500749010300707450000004010307110305d15008100480d0721a4030300700142a00b0501c00c80403120001010101039020b10900070100b18045509035125200f44600791500c8580c000b031041c0052140d0110380841e8641075074808060b01406114043c5c20700c4c2ca0014218a01520004e41d68210101e4514960000190490007120300340702501c42200f0242c02c40e03102954a16040709000d81ca84801e4410880c41c40010441500c6030098107002103081e80c80906160800d0402c0d401810040d01e210b482ea0030030060010403869803100c000d15980b814001d80518a464940a070400e40c0c002c0c404420242e501007000304107401242040c0503152802800903c1c1000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 693065611 1250 693064361 693064403
    0x50303061912111c050f10021801050d0207050304031a071d0904020301200a030f060e06090a0b03070e04060c020c09010b1606090b06130504050c0402160b040503190516 74
    0x800f02c00c0e40c5640f403101c121020701000050940c1c6d110041c04c100d0f4a8042103d080c80c049000700201070741040c64040c840500d5603c594081c05402c00c559800604e00065a40e960389503038031640c411030b100320190042c400003003400d44000d640400f0302e050442c0c2c82410360301d044410340d40151209100301101070225003503480961001c4485001190f01082c50340010303030541c0c05600040c048500081c2003240c058102c0e01e940c0610001ca0700c400c0b0581e4200e803544010405403003002000715140e103079180420b10040d54200704180082440404800103030401d81054415142d41c904060107640c03001c07a2403511501c0d02c10711a81110130b800a0b2503204c01c01340508041034032129002174191801e11540c141800560a8801d001d42d008036055800792549500140c1900c0c4103d5000e4616009101c0c2241e80b8185a001801c90410701c04040d003501c4050780e182c2100c90419501130311b0607030010030707040d00050100c4140008007403a070030264102f0f140c0b1100d07001502014800200344203040d16440e980015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 693066861 1250 693065611 693065629
    0x51b030d06030c080c0609102a030807140a14030603010207060218191d04020a03060f0506010e01020c030a0f0c0b070f051b18101205030306191211 65
    0x100400300344091079490403d009482014081d000c81c502450000001d6403420780216032201c0d102402031500c101240d0019203290f09070780c0008107070b000c10804d0702c0d4141307071001481060305100e610380c82841d080080e0020652242d825982d50440010000c80200c41d4000c80503200d4448025040c40d40e070750301e500219001e03000d03444009242c00e0010500c080c2c00b113403040c6a006102820340e204440c00000180b0b46041121510070100d00040c038213440588180c21411645d40301c1d0016200d481010350383e07907415084500568000c046595100c05000596a00207020001c03000709200500c1c440034150b00090300e850318814014a1880181c09080030402840803203c01011074120090b1141c0340e03030402112079100050201c0c1e490040d40c00d0201c0c10034002c0b810078251140903001c403241078240c1001100107903001d000000c4940f122500000c003002d6a110303900f0342d907119001440d1242031076001d010b41c00416484000074007807010001c0c00340c8402d203050300c40c0c0c03950004a080c610b0300c044004035403081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 693068111 1250 693066861 693066877
    0x9050a0b032413061406070b18010212070309060f05010b0d0b0d02120d1121070f020a06030b0a050f010c03180b0a0c0515090d0c1b0e0403090b0703051b03 68
    0x400b03e00442e601d40e0720f89034000003c5440c0c10240404aa00010401240d40b148800080030640c020000c120148414040380c01401e101400051611004034a4011a081c0c03c4500030b0001380c941140300100506806400c02c015502c240a106039418460028058003603411801344140e5207000c508815910905903107080c80c0c02600420800c214040c8050310703110351202d100042000710303402c0740e40c12100081d4038207151014640c1402450741c020003002103074403480080e503010040b164a0005030307440303d0746080203040c40d444c001200010360b014400c040c0c0d01d50303003c60311401050310600320590704102441ca080c4e40c1880e00101c4169075800312403055800d50814000181d0105001c64000d800030a008002d90051040f00c40d1016904c0560200c09021100050180c009211525080d401502c03441442c901c201c01e01c0300918450308841140b6155a409441c809100b10180800e05821030907035030103840d0070b4610a19000e01c940340036080340700b000c10409a0f8030402801040402c81402a16128 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 693069361 1250 693068111 693068119
    0x230f0a141602090f130206030402220b0321090f0d120206071d0a0e070e06070515071803020607060204090c0c0507080708150c09190609050a0b0324 65
    0x1403201c6a150490340003058422030041440303601240301c01c2094481385104001c0a4a0510301d20219800e0100030707080540200d80180c2c0301e4241108601c25108025800710316140300040c04002c02c0e04040c80c1007400480d080d0030250458050104900090844a1981d01a107040c6481150310021500d40108014003800015844150344110b039800329020b8098204d070b5817500c00041204007041070080c140041d095001d04095420054007525070440d0358011124185081450341035000702c0c100343d000c0c0318110f850750029a80c2c607400c0b16802c516140c01084030310b04084100d001c04007044003044607003c06440b514000c18001c1c07c00405804a50207461101c4040c4803000380124043c1020400180445650094200210b040400010071004440d41603000301401800c44c440c1000c0f17a400036000030740154041066150544a4003200c0d41c0744030070302c901030514a1410200030846440c1c1d81180348103002ea880200074440c031400a880e00011208615440300c0807004950b01c20010000c030031604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 693070611 1250 693069361 693069367
    0x5010512181c0f200c040b01050c1f0c170c0c03191101060b19030e160f0906080601031205030907090f02120a0902030a1407090f0c230f0a14 62
    0x1455800480d0140481e032649844c100d0110300da48013002d98103560802d00b02d0b58008a0501e1080c40c098001e03261400042c100280b4040705903a426041050b2914030180c0110944160181c021051260b1030344d1599a19080c50305000c1d203403e080091001070300005110202150310b074003000040c800c403161304445038203951000200039005802d07111001c0064105510301034000826012520031030ba5844002c1120a00350034000340d05030300030200e91070a45c0b90b40c42a19000403140c0045100800a031074000d48092007103190500200603a50560071202d21074006c1001000041c10400d4400c01c41d1105c0d0070030b1a00c0783d43c1c49200903d0b0000c154022031010382004601c60410806900905c241c410483c0105003690b1025001016114001002900745d441010101d0110350950003928840748901e00f40c039102c40d0b480440e0802e40f800055214502076550411510b020303002013501170104107044090194601c001d41050300d500a02c00340b07241c1020f00150080c0c98502c1070a042e07141125000200d91 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 693071861 1250 693070611 693070663
    0x90a0e0703230402010210050702030d11040b040b120702010c1e030b03010f021903091a07090e040507171c0809030403080c01020703030b06040e0106142505070501051218 75
    0x42c00c20040e60240d001d40260030309014007002c40e02131144507164a03001185007458507078a540082650030b403010300e0714a050001044074900d4000601c000c1152280c0c0649801c001c1d0780861118030b000e0402402e5a00d044085c018158125040c8040c1a000c880c1e411844041c103c001d8000e00703464104560700d035280400090f07415805c0d5020b000200d100803024880b40c0317035202c4250100e402040010702a03505940e00d0f13a00503503940d90b02d150b00c06200c0c035000c50300c25610001c02109010644089400ea0407403113092188043c0d80300000d080b101150014421803840c1a100c00241c00706100310303401c2151000009001b49801c008442c025070748030f88070035500c11021030114000d4212003403c0b40001e082050081240c03400405650903100441140c103c181d18000007510f446040c0c0e80283d00e0850240001c0c40100e400020b45a078144c140044c000c41a89039107042c6043c03115503008281400414022141141400c0134055800248000d45418440e01507143d18034200303070300c481a200d00700b01c1d2010034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 693073111 1250 693071861 693071921
    0xe0904061d06010f060e010519020102120c0c060f0408090405150a060201050114010e01021905070e0414010e010c090324022706161b0308190e0303090a0e0703 70
    0x504944c03003008800c14050310f5160844411144c041c200d400201c06118807224031000c6000502440706c47c0c000146810301c210800e01c00b1010031070781500514800b080602a03501c050298a520003890384000d2014580707541d8043c114000c41031280d020b00e40d1440054401c0d44100c0d00d5003050a00186107844c03059451900a001e07007024003580c000340b10080100c3c606540034904200d507182050700904003041c00b04100100e500b5055005079454800e0700740003d01083e003440524000c90269144503200d01240c0d0815003541c125808a1490343c0c90004200c4803981d01a12103c00c0c2c0c0c0e4425145032240107036004a8802c4041c42c0c039041941c5d44005035403c1601610010000e0400e503203641c5641d080c1c82a803c000c040d000c0c24032443c2a20350742624010004100c10320501040a040d40381c091119101d85490303c507030f000660b94190102d00354101c0c0d920950801600100312504a005525010344640031414200d43d500c60003245900407404145600d0094100c0346060401c00605012101c90b0b08044c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 693074361 1250 693073111 693073123
    0x40e06011707090b030307080a03021e09010f0206040c1202061207113009060c0d050306030111040302100311390a030215190e28030e0904061d 63
    0x80041e81c455110000b039544028000c08907036500040156082c82d450381c03a14442a80040d0650041507400c00c00c0002c01e00306850f01000075100311400d203443d0400100050810016400c0700320542d0b00c100204000103584e10003250956040000f000030100706d9201140c0d4501541300510222103620b8100550305070b004440da128092060203c031044c0d54540c20301c0d20000701d00103204511000c0c80085800041500b00240070103e009081c407417810100c02c4c0554100303d102050307480095000400e124461038240100162600295240b600e868615400a080021b61545810905840701803004040c11018161054454074440920040010b00e14070b806400104030800d040c400c5275109250010070004025843c198103400900d04040944112055110004d04442001845600604842065010b002080d48030b0f4001001503541908903c40100e03451a004140e003c00b81d01d010000c80d9000a5482c035500c0c040d03605240c507440f28100000030340880c10890614010382c0d910788007050400500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 693075611 1250 693074361 693074399
    0x611070b150f0d0305090d03090b030f1602030f0904240f030209130b06041a040e1005160906030911120c2805063a0f02040f0b09040e0601 61
    0x2c10030842d200320800080c210f4202c0c000e40010801c0c02801c0382414800580101180a820171000c5142ea41e254400c0d503034811140c01c0300c0c1000e02c00900580240c0e068a88010b400140080d5090140d44c0600d41c8081c000c002c079451090f0b80702d1010348250049038084514601c001d0705001c200b192207402108804140f44400c84c01266500002402e020003400070800c84c60f88200540b00329194841004003521442c8900e14110900c44c68030211660350780300c0c40003031f080810701900ca00d855500c100000c441d00209107035000c040d18000c0a495035400511078054485c1814005803020f0030b030034403a000d10801c1c01d0158004550165100016000041011590b40300302c0f5000c0305059183d031802a00f885008110001000c82e0f001800580352180c05091140ca803003101400d211800c0705100100d03446404e00c1d002250000480d4036034085030f80a50016001224030035882c1a282c0744020400491390311602509031000315140000d6940d50700107042c00d0107003000301e0b2960350315400c002d0b40c01c20300584 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 693076861 1250 693075611 693075619
    0x1005120a1403030f040602090a051011061303090303050d18030c05160302060d0c0c020405010e040c0e01060f030e0c030f010501061101050903070201050702030a0c080c01080109180611070b15 84
    0x4032056070314000100c9200d441c900303540c4c140395125a92150042c0d0441d192295111550213000711b441d85600309183c8804c8085c1d031310103002c414a01501424000301421404984440013900d4001ca07801100c2034044a500d0b180056660f00108105001028181d103103080c1009100c0c556020326601c80300720000140a0f100381d899148100010104003503040c44003d410010502c4605003160780b80e841103098800a05006456500c00d074000b808580c402d0700252148400201840706002c0440a600c014240001110403954142040a0b050110b0031070110100351b110070080c2030031301e800e001c8000c00709405022a41d50f039a06003601341c043d1200340203400000eaa0001a07840058050083d40d01a41d901d4010b5407402e4400e030011030302944107090a80c3c05108500040002401c80c40210004080c0d0401410854011000040c480360040c1d0089001e20f00340001640b09001e180c072080115684843d0020f0401141100d0744420301800d170001c1c1c4412014810041c840607070b1503194410142c125 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 693078111 1250 693076861 693076883
    0x12030d06090b010e011d0402071b0602060c0a020a1127060411090f0d06060810050a0b091509040201030e030d060504150f060e0307030c03050a05070f06050f031005120a 74
    0x10b80115214040103410b9800030760840c0010180101404482605400c0a0805450010151146819129100d07003034000d80c1e500d00e100300316044e414480b803034001c0017502c2890b28120240000940e00c40c443c080c0505503d441e802c9601050b81c8400c0301480b000005013940e21142c240c4062904060701c1290343d503001c1c82c141204404c00886540440e07040200050000c0400100c04d0b0038410b4104800104071103403581d841c4003040c0d1680070480059111401003011499141186070704050701c24059030dc0b4010f0b0144030600106425095491b000088251a002d829543c0c0d4001200500751b40a445910380c04001101d0070004200c0c1c2151040e5403003524203016003c042c0c9402d0007003480c18403410f610103002c0b07a41070100307a00c200b070000e8000000030219500140c83c0d8540c081c41c07880d194011a425446420410700b08542400f0003002080c0d03128102e01a80c0c07501074060454402c00c00504040c20000001a21f2410030392003000c09018060000541040c0038189160f80d41d0b1001001e5441203042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 693079361 1250 693078111 693078131
    0x50408030a0e070602071a07050114041502120609090a1b0e090a230c0301020f030a0e01141f090c180b0c10111608090a05010302030f041112030d0609 66
    0x900f12045518950003003007590f141c00504485d0740d5a4801c48203007070108019100100d0030034014414580520241050281083d1070000001c0b5111803e010707402d0700600c41664200c0a0303200701613001105a405507445e6482500583c24440b24100c010402183e1001c43d40151200c0410082a078484a07090321954450000d035681c1d54242d510b00238080c0da50114000250060072152200d00c0600340300f03c40d007002c19100041d007a030704010910189148044204a0280c6650180342c26090303225008100508080e450210011002481d0102c034101001707c02d201c1b03c4010b54100020541d0000821000380701101c010010118200300d19040400d06102069090310101110a0303401c0071001040b03d503000710240b0340034000e03034044000e02c14001d001e094204d001078031405010903c030790802c1c0c2d81c8000310b400300030080d840d540000781007501c1801000b0700c910401c000540c010382c21450302440440349070b0000c0c6401d050f0504032055800049062640c1e0101e070b030040819926501c8040c0710748241 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 693080611 1250 693079361 693079363
    0x3040f090e0d0c0c030c08030a0813021806061c0603020918071505270109090911090c04080708150f06030312071404060504080d0201020f12100504050408030a0e 71
    0x1a0020002590000d42c000300c0318078080c24038441043d2081d90900e203001ea99807a00700c00c01c041035029a100383c01c001551450b05030701c5414554440b0751700864603540f05441d00883c512104400c6605400c0c0c1800c004210255942000d659103a145032112600c08420031005401070300952008034011000100404c9042801c1d0800e0280c5200f00c1005003107140c68589503c11940c82c0d040c1c20410300c2020020b40e62400c50011a008441c40707208520a2900410000140840078551010200307616140da08030004404004044c8072600440d043c1c0b0060310340510800041c0708039171145103140300c1c2000003d540e58000ca082e60030101440c5e046000765440d05541c84a1200441e01c969064004100c2014150300c00c1c44c0c1590071001c1460041002c04801081307821650041d001341002c610007140401410100700500c98040510b40300075400d0840c501b44009040c02901c408860f04401403000644109220440c04001c000080040c0140d080a003410240c0b41d10549021030000d04103180a81c03c100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 693081861 1250 693080611 693080621
    0x5060a1e08061003050403140307020f12130b07063b120301033e03060109022a030903011a040b1e060a0216030501051e01060e0112090c030503040f09 66
    0x68050710103c5040c289003c103d0040c04001c10490500081c00c0d1065060344801c000b95104400d81e03001000d401400d0300e9064a00101d03100c1102c400601004a00b198000d02d50104c02118022280e66444040c92318100e0064208018003040d0302d201d0f416042003c03600e1000022501f540d40001c410500e140c46201074444142c03429003110b080301000100000f42401c085140e05a03900c0d4010f205400740c200f0300d030b2281442081c0d01c45002d1122411980e040c6030a00c1403d0042c00f90b100c04520700a003019190304d112204103000050101523444800c14050240201d503a00c40008008022070b50410f8015041c90a2075000d8600491800c0c145035620b003881c44800913100d48040246540805210070007034503030301030311080086015060601100700d40ca03120420103540b094001055603e4210b003c014440d2001c080501c003070400380010040540c0007040ca803555602031070207041c80340701240e4160140440102c018081c030170181c0004140107011000d002610419040841c4550340d440e480f80a40b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 693083111 1250 693081861 693081871
    0xa0b0913020303030c0a11011b26010b090a0806010f0f0806060108010b18060712020c01140702010507060e1c08010b0f041e0b0a030203011e0303200705060a1e08 71
    0x1900420114007255040c07406081e950000b1f15100905e41c05901005094561940d0900b007446c003442588902c2c1c2d81c010040c0c40012801c0001d59082458841144c1141036040c07041c5230600100080044242d00e030315055402925621046481d00d594031900d8041140351445003100021804070049500314001c2903450040384143c5d00c414941e420402a0741940c0e005840075072a150f000d00f038000309a01c4800180992034011140078041004d900c2021f4280f103084d00d1441d04024078840012941d4034180151950140c080c60a207440da010391030072070003e000b090890400b5104000044071603802500302c81d00e907602c00b5500c0d100980d9071040d42c6c0b1207a00503d2126554508144000e0100e6040d1144264102407222103034844103075503510a880d65444001e20f100081e800000600420055040c140c0d0550b038641c4101070302070f02c1d40d03c00802c045002c0b030000000c101680c8070319010342c0301080107002030b101c02000180c2d03d815008010304000c4041c00d00ca06e8208104078194512801501264454 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 693084361 1250 693083111 693083113
    0x1021911010e010e03010f0f050105060a051e040e16140408070909020303070606060801140a0605070201081e090318030a0521130b0d0f2c03040504050a0b09130203 72
    0x20084a000541d20892102252810041038803410b084075074007401540f448050442001a030801040c880720b080c0e270310580003140110010004003d20070f0784042218a04254103a00c00f0307003e0b0403424941c829106a501c00c045540c241001e2001c0c3c0791500b40749404140560711005e0240140581c0b480280c01544070709007045d04119010024440190003140c03100d44018284c0340391124075903600b0102d401a40080303000070016070050041c00030381c046040c01c05c5811550a030030746260100003040c5118443c00281002811070125000103c500019000d000010200110a1030840b4070203550303030401e55291290400c181c20b106001d0038040b80140e1690b81040203844203912a5011280400780000031404080c800c03c8810100c03080c4400c81409004441d28056a550074107401c481940e00507490780414915040445010b40c01c6000340c01400202c070401c0381c05c0c1c00c04c450207640c21802650f118542260401b0108284082a0f500600342d441c011146080c59449010b441407814448400c02505 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 693085611 1250 693084361 693084383
    0x6030607091203020f01020d0504020a0b0903030301060309230d0f0e0904080a09230a05011d041805060c030403020601080a0c0303080a11070b04230c130e030a0e010219 74
    0x800d0640e168205080340613004807081c20f59074100103401c99000b0131078209140e60b210305110841c64641034607801000c11003100b6062149900009449100601c0b9000c180741c1e644464204001c85903040082d1f211129400b0580b0705000d0390140e8440403074a003104000746180d10800c0750140102900e508211020317103080055682d6950b8040b490380b2403c81c08060100032400001e4843c0e0074645600300800314a05800050988000c0c01100358840c1c06c41814019442c0e0503210030341e0241c03403040031000203d901250080c464807050302c40311000b0320040c00c0c3e801103000b000019561800103600551103542110300583e6030302d1500c2d1b211044620001c00c05104c82c00f080001c40d01ca0b01110307030230810b007120006041031001d2075080558090340c01100d61004807001c00060000c1401403c0c503602220100d03505041c6c081e4504d540303d510302e0300d91600c1502c4078103032540c5214603940120150180202182c2e600c0028890103407496061441c0c1d0790040c8542c07403801011084001c00124442d90244501f41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 693086861 1250 693085611 693085619
    0x304060504050109050601180606050a02031606061a09030d030203011d04031815020d0203130905150406030503030f060d02100320040b0d0608210703110102210603060709 75
    0x201806019005490035900c920703002c004a001801854000c001c1d100010b004100541d004901b6180710360301c00b03401c2c01070a1003002c180343e801200321180f041c10143c10001c20401031400d00c006106640085c51002c01d019001c60643d1407480041210141c110111190360100c0d8004806900c401d00581420809401c048550640616403881c0c00c03600c2410700e00e48840405000b041c0155169111040d00c451125218117800e40520103072001a00c10310245107016051400f400721896540300d00d55503260f943c4001680384003001c244041001004009200351540d80c03c0080d0707240c1055420748003194484010503054500070005000c03c65001c3c00c405403a0301c82d55403d0b401090600747c0e02d440f82241e201d00c80c0102c03515500400c09030030030f1032180c0c1d16600b060b00c10000303c40254200c0e01c100d07031100742915229640108010705500e114280642d95003050b25048841c000d810340d00001960011805029640c00c0c40481d03950000003100040342661803c04241d940c03c415034400e40070498250042c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 693088111 1250 693086861 693086873
    0x30106020c011b05060406020901030b0301151502030405031b120a200607170c15011a1309060801050406050a1e0209041503050c0108070c0819030e0102270a03080304 73
    0x343d03002c0721406403541410594a41e9814108200c0e022520b0603400104407610350b03050b00c80c40b2105202900200140100c030399540c4581e8445004800441c88038044214150340b08200311800380801034151205095408018406507040c449124481c2c3c01043c17900c030540341e00040c0c81401c43d401030704c803035030300040b8005006214100c031100c0d60f003000741007003000d020441c0030074521100d1070713030030358075a940c40c802c2c0c0b46030b800d0180c0e00c0b41c5605c1e0901c2d00001041310482406d044080300101150060740c5003041031504030104200d51000c82c5040c104000062420f0041d07000a03c00c9009500c2889241d540003c01401c03151500188841e10b2424414030810403030341d6010700440b0342c0250001a02c220622045441c2c4007080d80100c805a0280c19910200d50f1301c0504284c0000d400c1c1132140d030072003041e03840301c01600800d06103000b060000e070401d910b120300c40d070030461840340345500031580d8118440c01c450a090364180c000c500184c140d10740c01141d081079200001102d4204d05003031700f50b0307c0e540e13033308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 693089361 1250 693088111 693088127
    0x20a1a07031b02090f0103060f0605060d1d060a0e120c030d0e0c041802040b03031303030f05040e01060f0207171b130c0c0308070504031208060118060306030201030b06030106020c01 80
    0x466018401c01140340b0042e1034441c00903008100c48442261190315625100c4103941050802c01e50050070b008007002240c640c10180d03450040b081d0f01c00720305840c64540344142200244a680080d1040d90180001d41d400c65204c4262201c4502c00c0d211003d402115018951081000380d1205034020440c07aa07130083c0b180d100140403030566003903a4880403008001421740b00d000d44604500c0c4041c1004d83d0851130a840303480b01800d0190701444c10480e10003462200c203c090303c03024051000c00108004841e219604480284c00760380f91a40c0e181d42c4034600149000c05000026015103c0c64501140101c83d0030802c1c0443c64410005040e00b03200b11081e80e00820081e12001c0e005140100700302d4a1361958040c0800c1c04080e95111003e0400c0ca0500500b4040c000d0185420700c0410842800466403070049415040800d04100806458440040f98000c503401c0c1c00f45125038004002080700d5902d80c020004690003642d0031b028420340d010400034503210a201e824050b80c40011004559400b580f05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 693090611 1250 693089361 693089387
    0x312030106081e192313030207080105040c0e090a0b161206090b0310050603070308070f0b010905063f03040305070e0403080112030f0e0402040f0e04020a1a0703 71
    0x1201e40d0100700742100c60000768241c44054192980c2e04c03441400e05020700c07805100324202e12901d216440c45d501c0c0c24045840140c0700d0300f0346800410018040c1340c02000a60020714111000304081e2505040c5100100031b03500032803a82084007004541c00c2040003406500b182d800c420a400c00e616900400441605c02d08510400d0140c0014140004000c03440348600820001801043c011b81103010103040914030000186070358a80414415140c50000e03a58041e2a4021106941c1e682e160800d100e6201241d4130050262a00300004610b800081e00828022181980d20600b040c049020511302e4509400d00014a044220000e86200d1150500c10901d09489000d82e480d068490302c4e11030810071300c1c0c0c2000d100c2a1429041c0801c05601c441c015004000444408080c1c0d0115500100510b41910300365003001244904c0c1c000641d2254111801040ca10f022144884e070740301c50f858207107a8110b40a91150000d904002102d8040d01030b2044ca110240d002d20785400d03080e0b40e090f20b40d07150b4020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 693091861 1250 693090611 693090631
    0x6040203092508030408070e0906092802060c07080f0109030c170c0a1a0601030603050307120e0a03140c0402090a0e091c080406060b0c07050105090d12050a020c031203010608 77
    0x2100060f0f0110610080010300700080107044400c0c108105c0d1101044003800308131840c0e00c55030400c80c80c01c60100c0c0c02c000404002408442d0398075884c0040060440200d00079500c103000058a42c1701d140005a4001103070044419581c0f4040180b50460807100f1450002d00864800008140041c0d0032490840d00c00c529800014100800800e44034031b070079140201122032810b04ea02e5080900510030f10180e2295007468180120340c01c659507503403079010320500288404441c13a800114030703000e0011700d40f80020141522076616600e0038400c504840717151001e0224041e07a0345112036428a40201d40c54440040d01c0019034a107000c90301400242e004121600302e02899070702d01c4144000206200f40d1042d030360b981c407038942820b00700320b011190a40e0003403001c010f0402c500c0381201d00100c0c815048031802d00344942c03039291140c041003140d41c0d41d0000400b00404151400800781c1c20402900c40c648103542210741d010001401d0590783c1b801c2891281d6080710900040000318481c1c00050f0303020080e00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 693093111 1250 693091861 693091933
    0x204060e13150e19410f0d021b04090812040f05010213030b06120c040b13050c04180203010803070609021c03021e0118020d380604020309 61
    0x214010341070403804100c82c00a03074029401c51060010103010302a905450201d002a5820130700d41d000350405c540d007843e40003161050b5200144a0b03040c0720a5000b42c07040c5c400c0d16130030703030032000000d45603c15800c0c0a442400491484102801c1034030411132031030342c001c4095181840000e144080352400174030441d0010060021480020310078000341c424a0103000070500c0682c11844c0180a411000304500e0045914190740b80305103500160880d4007080581d0006441c610758408900080c25a00007200102d0518090103050030400001340225840010006040c06411410109030310080c4500403081d40244047c10106505034491488988020048801c00102d40a0f898000f61001e00540140c0c11516010750881c042c64011586681ca600080201c441c01c2c60103c1c0074100203000c06401844609028010030020114200c1091040b0002100388194000e007501143c4d00174031034500f09161a4003181041c2428000d880c001c1da1404090640c142016145040309404280307100c84a403c0f42e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 693094361 1250 693093111 693093131
    0x20f03100207080a11010c0c140709090506160c05060103021e0301050709060f02011415030a080408030903010614010503150a09022217060a02070309210204060e1315 73
    0x1c0c40101645032003401456200d5080440c040e00b00200050140d109034100200d24120350307409001d0f640041d522801840602000d244100d103404001c1c3c0015404500d807800480600400140080c030403a030035034440648811020041300c016615450060a9512100040c80149480500c4082c110100317040b071200032a00000090070f4030815036008010840404e0140318071341d40071a0f000200b000c00d00003030082d0404c11091901b03801c001006141120300741c0c00f19a0603564148214000c40c1c0d04510b40a80742e036124402e29880f130303104002080c443e6190880018011105504080c002c08050312240c0c110b075503d10031a00380d0120000c1403580000081008106c2d500f680c40508003004020722107801c41c03400300030800484400c6030404000044c1b005880c6100140010b5042d44c409046100942c5421461400792130071000b980007241c9034403034094000c1a03000c51a10104405008680038000d080d070b0f902207000010f13010b80e000040f12400201c0c03000425088141e144410700c503a0350001e0300a002d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 693095611 1250 693094361 693094393
    0x200c031531022e0c02031002040303170609160e0312040909030815060f0d0b150304051c080105060c190b0115090605070f02030c0909010222080307020f03 68
    0x100380381c550a0394032521004250b06000e484070090100030204460f05140e6011460003849010021070104280d540c0359038110b450034407400b202d050420805644894481c50080c00d081c0d455103100e21144c1102002a240340340c90001d040c0109864032014200c504e041c07000300c2c0e104011030b6455405106660801c0030140810000704024081481c1c00561f112651400400079200507000c404a9541503410ba1059a180000c640c580c005072510141d5908000301d03075501410650201d182e110f82d406590303154621010b0000c1d44214030030740640c0c00040303d20407130b00030504601041c1000100814014842c07402c05900034a1410400021a80d8100d0741c15541c00894460b0401190006816401000401000c45504c426004c080c1484071215041050041141c010010040c01d90700b8511000310554070240039440390640050412501803800d400082c1c084c1d0b000d403410a00305900060300c2e1003100c800e00c060909035070420f400383d85066129020040c0c12180201d1302d0350b01d406a03d1101401c41c803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 693096861 1250 693095611 693095671
    0x31a100513140f0f0603060108040c031502030402090a02030702070605090d30110a020d060e10090b09011103010306090302030c071401020d08060607140715200c0315 73
    0x14042103440148010107040c4079483c42e03400201400380d0303c41200c1e034145a41d000141c2c0e074030040070b05c0c201a10b84d4135410442a43d4942e036002034103074817041c130340b11000d060280c004502ca54002e4803030701810b456101c506401c0344070407030303401c001a00200b106114152061000744180d0780d0007000f14030b1050440e12020700710704c40e42c882c4074900403030207041d00c0c0704848440c8a0680d1400794181b02141c0000c04a030140c4419003032800a10442c6174400c45004c1003596131101c030a07210a0740841c1c4d801d0745480001d0000b080b168009403941c0800400042200c03805003e0782e4a0b03034440c070a02c01d0a503407070341d9100d4021b0085240210154003082c0210200c401c010401c1c90000c103100d1031000b543d003030320500290400075280c46520810640d5401c000b00e54a41b03404071080319920010074284100d191000174100542c0b03420600208210300012613020754060b5540305000c0f440c0f0440723481502c042aa0560b183d1021070b02c1030305600700091170f684005880340d86a41c0070101a03201c51900150511850002c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 693098111 1250 693096861 693096869
    0x611090406080c190e07050a0309060f022101050d080304080705060408210115050903010b13060e01084e07120207210f1e12031a100513 60
    0x944440001c60061501e941d5180c501c240341c42013a401d543c20040b01611000d0010301c50b07414440009014000c0b28804d5020207400740c0c110f0001c011055080c010100079502c412001800c45035030b039140b1114400da11100e04d04891000b0300b499075031151547c0d00c00e000d401c01001590034030310910401020480074024944103070b01c510456551140034403400784805010304900300b84440f1400061200c4410154060120102d0b4107046458000f5040080e014042c1b2048c80f581000700320180203030160b0705070800e60565440c0e200d18400391fa00c0d003100c00c0d036800e00802c480244401a41006200072140009101d154240c01d1901445144801040e61074810716525002e0000c1d0001b04241030003204c0c8400c1070802e01c0d0344040e18610345407441000310099040c0a28007071000c15002d6904002c1510b12143c0c41c1c560203181d04410080d080d041c401c03900407608003134454407400c0d040811464440c0c400c0080081d01c000000b500300340010144420292055a032506100c020821a5508481c0612284c010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 693099361 1250 693098111 693098113
    0x13080c1e060702031e0903010f0f1b1d040e03040e190e060f0105040c050909100603110f0d02030a0b120d0f09030f1b0f1404110313061109040608 64
    0x200d211810040d2801d1001045802150401d000038081c9010030800d59041040200c426501c609032000020300400b900350794913914602e02681a40036030043e40110540048082e0002c444100305101660b45024005003080c00b402c1e41c542c00c2c0c00300d142c01d6010751100b11505003107909160301e40e07210803021181503d400a0038003018013070f0184000c05000d10b607451800c8801400d1a8142890014036814040c05080e11031503ca80c1c0d20140346200d0801c0ea0b0604000030281510340c100040503095254044c020240060f0401c2c500b5013070040340c00c2c21284e80c84000c0740445d142c540110104c1c00290006000d80c1d9403561205484030700c55817000003004020070010080d1088503001000540b421014404020500080304d0040010480040308000901e400142030007001080300740d01038a0107007540100c0420203c0c5817002c50843c0c0024181d1f18010402d4404203c948440c0100a1240c00121400500e13603040c40710400000d400c0344c0210900c450405a89400c1103d51740001d4244d0f04590032003200c0f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 693100611 1250 693099361 693099403
    0x62105043005030f1015021b04060b091513060c05070f0612090f0b15040b01110c0409060912080912030c0415121a0a1208070f1e030e010806011713080c 67
    0x42070103000000815103c200c0342001024034144145019020b07a000081c0316a5035105040000b10202c0211902d080107171033b0030755410343c45500190030101c810106884902c242d540c00b289900b20780c0340d400c0594500d070301c80c0307440268081c0f1810041c106540f41101e111284056240018120202ca00e006100c010407200c0d0b03072030a070380034030040701c5440100604100b0a0400c1000707124010505040f03806013a6404640040c1c07030b082803c007804503180028a81951000030500d80c0fa400a00640a060b1034400e94807413580c1c030420131426020030748219580b0300081004200c2c0c0a04401440748550080c00c0c92a00e213540200c09001b01c60809507810b09c1c9800443c150161490060310900140101c0a94180d000c2503684070402c090041510080000000c1801e80301480519121000c2411801d9035001c01009145001032040f00c1c0c40e007400f804580307002e021804541c06200311800c41364000c0b1113280195541c01401d60945908503050720004002c0141e00d103010000e011450000c0e1070400713400c6c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 693101861 1250 693100611 693100633
    0x806010e060112060e010902090f090106020a0b090f03040603020d150306020c0c03010510050d02010c0501020a021014060306071404080a0b010e100e01062105043005030f101502 78
    0xd01e05028000640e585044c20600c0941c40e0032138503a06560142c0700050315402c51402041168000081ca6984a00c01034000900c10758000f4030314030310a104007030360f03441c5855100d107081d960490f0710404405504144800c2c01164031980c064400340c00ca000f00401c050301c40345041c01749003e0642064412035000603114035450020000302d00c41c598150002c2046190510003c4c060351040d0207054403404140840105582c0706400a588084c0c0000003155110305001d0080c0d951910360180090791070502c0304c28002e080c2e800550314820400940907043c140d40d040c01c1128580c203107182403d041c100902c800715003105d041040e8108079101e00343d480c60310b506180d445886420b0043c4444100e4070400d10500040444188090442d0700c0340c1040925101552200050101c600451040b454035140800082c80243c4880c10640201e54401040d03524045070440000a801d9125001240d130410104403460022540d25600150903803083c0032050302d8880c05070101c10b103219035034016070083d0350f054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 693103111 1250 693101861 693101867
    0x10051c03140906030112060603050607081b070b0a0902030708151f0b0a050901140d0f060b0a0c0b0408070b010b0d1506140304060902040c02011a0a0602250806010e0601 74
    0x1021051010310407410302c81d12070002100c41c071050007015140301e044c3d500704c000c200c41504048040d40d400b10070b880051a042a00411403601114200a0040c694044c6042d142c0c01e034045070140b07500004090f0fa61340d101c04042019101d08181203800d4400c0c41c00000e00e00c80c05001c1d50090380700441d043c2c1083d05055560000d40030140d0b05202c3c0340d19200f48100200c00101d000c0300c00541090510719200c0501c100103035485410b1a010080c513003400035101e818018140d1000e200b0f03002e07100341042400d07111302c13445015000314224400030400017440c12000c26015940154000d20441c0343d203243c0141681ca882c0c4248080e80030000301c1002043d403008030b405a0050680c841380c05108210424542040200403c01450107980d034404004003107010300c00d954106014642d00540240311061208400074000d00703a45d09120b00481014610440a1400b020b08030704498540d4018208c50518007218814813201140000c1d034181c036400d0000c1c030000103001c0341d4000d01200401c8082d6140c80320001d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 693104361 1250 693103111 693103127
    0x9150406090c0806090a1104060c0614271c050405010206070512047a18130b01240e010507080d020702040e06100e10051c03 55
    0x128045814902d1124000b41d00903003580e03114408032240602900d502c40c50b1401816a400c040714a00000034000c6102500954103140c203500c40e0608101c0e11944c056100d08000c829284a0307620000c0300f40100b4200340c240440081180080c0c20780d00e0620b000c0b003542108900c072441203404075801140c10802982c0601c01d5030382c00b000604005144c566200c102d2a43c03c800280010040004440c03041c4070b140c443c4200800c1003607420700fa6007850f2b04800c55684000900780e0340e065a002000c14002070700c1c4490310b404034500900030000858003030380d43c460044403892006250700140001c5080700d01900680c41a0302070640314140d202c0071292400d16080a201c16000980b9000c121901c82e003d004105110011002c5107203441c0c00340e5031001d001201e551241003409040314a01080c2802d40a81c0c6500034400640300700c404000c0060240d01040c0c5072201240c5c3c607407840d000c10508210481d2000192580306c0780b2a00003400094649000070b10750b1070051482d0b001007411782c141da000c06400100e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 693105611 1250 693104361 693104369
    0xe03070f09060f060c06021810031b0203070201020307150917040f0b0c0d0806060c030408061501020a03050a030b040b0a0806040525050d021201240e041211070509150406 75
    0x76030518908100d801742c135045080d00c00600c100c0e4005441081d403941c112400710040310041c0044410718100301c0c001e01030503c002c0c00050a131095800400c406000000711401103034103070040d5041840a8640024226407000440191a01c880550b000184131005003141e2501480c0c025842d035080818113520041c540d00000040c0500f0000a2800180002d8910200080e07151146a5070b940d480441e01c980a00d410079581071002041c04540003d001c03540920424110f040100f40c0ca40340401283c2d10701c1c1d001000b80100380300308140300c06c6500c250000ea501082c05000442c44030350030004502241c0d0298004203264210005101c20040c040c004010081d250b40f4008410700d44602c0c80e40440400d503c200351142f400c101400e821911548404100609500c00800140c2101c0d08000c681c0319201400c000d04035a8800041201036003940024007480e0040c07070b02c81c3d041c0c03076904094400418184004509205030500061542c0d0b45a03191071140307958034951503088500105000a990f01608 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 693106861 1250 693105611 693105629
    0xc070e07080408070f050709020f1803030f190c02030334120c020103090f0c031209180f200a090b0702090403030518061017030316030b010e03070f0906 67
    0x3480b010540c0c0d80140d50039a50050503154010710981307011854074842c1d6119865050001c1052544054201d01400703003090105101d120800700542095242c0c0304080004071490b02c1404410a248420f02c1e8050760307543d180c105000c5400c001e030002465034104050340300e0700b008007103616041d00800107812000500d8880f82c000c2800703260b85e214204440381c20000810404554000e80540e807181d0400d814a60300003075203905000040c00c14240114a60005481c108080f6400900541c07043c0d030300c036045032030040030b034503481804500340c1c5c0203081554945036540352117525071107072080904225171148118101d01c07a6107019982c1d014060200c0daa0005201200500c01000903817904202258442d9141c680000c840e80d0303454294a60402d8140400d200b03100c0c0d6801c101d0515103443d0403000351031055040c400000980540650340b488100c5015a4000700001c20140c140e00a41048101c0c1d10141095181e2542401c082882c1c405181e0000a4041c8420001c0210507207074030901000d017503419 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 693108111 1250 693106861 693106877
    0x1061706030d0809010902060c010c0e0d0c1401090302120c04060f03020321270f101709070b13170f030708090a0512010504030201150f030b0405120c070e07 69
    0x25001030b441e0304018079100c0522190b0000201d01001c2035000505841d4014030058071104510b41c9140240072010030807010440005081c200303441c00c600320500059109410800160070450340841441e01c5210250601a006a000c001655041e03040d1441548050040aa07560483c00304419200550b001c0c000f002c234105010300c0541c60118400d0007170341c4000084d0840e800c03087c0d0142c405100715500d8407480c4030030319404900108075110401c10710808845501c03010704004108806011600049008110440000107000101d051000e034002e1000096940040d51103040800550160092119941c1c1140050140800c4a5900103140101000030500020291443da0b564410860040e00600000c03d04407000d85d1001200009040c000d003030807900b19004400c26000e07040c159000c0b005542804084841c580203a00c00400300d078a40d4018203070540c990780f0b6040d052003001d4400ea40038081c40105030011151000203024000328000200001c61034044001311102001c0e2440d801c001500c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 693109361 1250 693108111 693108121
    0x902010e19060315050a0807290415020a02130c080a020f1b0712060507120902060a142802100e03030406020c0f0601290301080615010215090105010617 67
    0x150340042500d10b5400c2c00103801142c44a20700303220543d81e00259101186a8000c079022101258440445140d40d2070a20700007070300c0d802507040c11b443d140c3c40120703a0002d0000300300f106510440d0380300005050050b00c4030031600c0d40115078004a01c0061103011070326030305c00c901d200c1d5000c9511230b40402221411810025424103c130414865040312000900d00d03602406840e407001c0c0020030007400f40300440c4d40d28020a143c21005007c5c1101ca6201144801f400e18401c076426004512039179070700400743c1e450000002ea09440c100304661f004612140d003031098024100d000c182e001c0d181158411180d4014504200c020b141100c148012a440c070300f400407500c0e501e1400030650340c0055203e20056216004071711803030f00d07000c2101e8000c5510b11410700000f42d00085001c0c60042d41c2d0b811247c0e201c0e0410005004002c603c070178424050168001030000d10710010208000074480b03014410b4511560b0709042a001000c8103840c0040e15943d101e004110b103d800020040e888030554055000c0c500e88 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 693110611 1250 693109361 693109399
    0x31d0313060206060f011107080109050606040f141f08430b0702060712081617010e040501020412080901090e04031215080f07140901050a031115030a0902010e 70
    0x83c10405c505124001030414440c1e1814400c3e103010705a0803000300100e085a0900a03911102514481c1c05145840001c1c26070b030500d4001c05d005007903100c2c0e01c01c9460300c40c61403148025034600030215048140034008264102e05110100d102d03405441c4903545c50003e070b401c001a240c0c40d81011801c085903a69055015545c482c0350500303ca5210f4505034480a0034000301e4001e2280d03c100411149502454420300343d040b8041d28042e400401c0c03032144062107070310203540d0041e41b070300202c1803414030000400882449111880d4002c0c403ea0002d82010f54800081c0e04062800c0340454040c20045010241035a000360054024002e1fa422200581001d0f00e024210000380c1c00b0030420f86840b5240444400c4009410400501800c012a1604406580c50b19201e42c1c4901a00e6083d4501e03018980b290716201010605950b0010034174004a4515178400c07800815a03080309410000800d402808042000099445241d07041c601180605084c80014665014503e02030321581800810b1201400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 693111861 1250 693110611 693110629
    0x50102040305060a05132a1d01080d0e12011512061104030305030c180316080f16061d0316080f01060b0906070303060e0c040f060c080910031d031306020606 69
    0x242040d280741040d108081f807450000024544807004540ca290300041030103102400c5440c0e001d00810b49612a41c0381c200903074031150000c0d09000041d540c880d0441c0b16103000883d1404809803000009240703210b8803008041c0402990001c0711610b01e80310001c09004050155030b010541031600c05107490f04654000d4241c1c00050141d0150300e0380030907031400240c0e4041c002d0701d40c1c0b0b00040480b96a1400103036051034850950240f03038841d0242060304440300b0b800007040d070050300365503035840021400d0050441e020008940140081804c50000c900c454409100045604620312090180d46040c500001d2030520100d80303070410b607032405104101c140400d10603101c400f00300f114007681d034013010f040450150503980c1224080c07803a00001c0c0144003c901c402130084451208803080081da03181400d03180c030341280c00d01404070a0100020b0141d413914680312141c00d0042d04001500ac1c08008a450152a51401c3c0303140a600005000080c03583c0c4100440040800384010415403402c840402c444803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 693113111 1250 693111861 693111863
    0x1e06070302031306090506090c04021207080402011e020109060b01020d08060405100302040509031b0706020c040921111b01120507050c0607021c0f0f0822050102040305060a0513 78
    0x5607021012510400318004210409500480b090119201c9814415140c5000369208080c41c030a0900e804001c2c1014003e94072406280103902035a0354410605403003000c8010001c074100600c030f0034090642c0503100c1e096035210485600008480d2114135108044901c5401c80f0750540d800b40803051909540007190a51002c1d003078502180680704c1c51b070003403112016070704000d40c0541064100701c02114000041c00c0c00402001c0b82d44120380c1100d125980715141805440c0058000318520b210b0341c103107a00160b0350288a28002d400309400e401090f24018041c203049400a40756546455166200300501a4200079146010f0610824640040c104820482e2180c10942d11500010b0340c19019000307680d05134034008155030143c42c0c800002901c8502c01d0814040d0300303203500c44c2d030b807945031141d4020390b00200c490b00c51000345403003003c060311150030003171070f44048040e01c04a030300c81c451800a0212409104a00240c1c40d5030031894074605180c801020118094905403c0108000460703054908103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 693114361 1250 693113111 693113117
    0x905090c040c090f0627051e0105070f05030a020f160611010b030628020a200f16090605040c05090d06180c0302030d030b01050414060c070306020c1e0607 68
    0x3940b030312400341c0d003004070381d44400044038002100140c1903800c07914002d0348441c0060310701003004003243c045400f40d02c140600c0d60441c0029100410402d0b44030392100305c40005040035400c001695451140c502c0004030100d925401c0443c44858042d0104030356100c400666002e8010300d4003205070300701480c00c0b61183d1400c02c01000010025080300b0362021511034005002d40f052850036062203175056182c0c14a0b041ca01b000d02d84841e0320243c0610945001800a5840074059103d491b4020014640b949691400e40a0301e485581c01410030010204010710300000009100c0c038007000c1c442124201c0e80403601660a040003014842d51100444500c0340e0304450100c0300d000181010300c000c2c48440007984007007030101c0401e030a10100340d00100c21a0703c01c40480b1003130342c105081181551b02800040d0b001c9002808141301032440099034005d0444042c0103c1c0c1071802046c41c662800703440b58802e40300c0c160700280003c502d80050007240c0080f00403480b010805080307035840742e40d10390004002e1020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 693115611 1250 693114361 693114371
    0x11010603120c06090606060207030507090212040803041506060e0a0f0305070b0c07080601030609060b3f0303040605070f0207151d04140106230906070218040f0c0905090c04 76
    0x8000c1c044e440070300701075041081002244c1d142c9502940e150803501096a4070320842400141112031030084500c02614181070040903180c03030350f90301030642014008035049406291542c20a407858803070356004051540c1c481210f04500c01c03d00c41280d2154200c0380c815400c001c0c003400842c0c070024203d41214031344180ca03983c80c1c50010040d0b08005581e00661424041c010000091005e141c000c98115409184200588a500000c102403408032010200c0403000d40011000c1030901d4101a100541500d002c5070820041c1c0ca01030750440d0f004235011136000342c0da0030a101c0c542e644141c00340380000c0740f80020b0002500f002c0682502c00c8070b4070340352400c01c41440b4503e4181e10303045249403036040c1d02800c140680c6101010079240f03e00240180000550451201070300b90f000b400340f58034010b115101c001e1038a00001c2c14032115500400c0c2c1030b13811000c0c00e1192080c0c440c0c8003488e18412801102c1c02110058140340410500b084c95010894460801062215a15011680c041880011540096 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 693116861 1250 693115611 693115613
    0x21810030e06040302030c150124050c010f05040c0f0b162103021209070f2312060a050c0307271502010209011b080f0a0302070c09060611010603120c 66
    0xc00340282481c00c198901544003400105030700003024200f8020440300380c03480e0341e00c4100100e041720024440c15040010182291000000410061040c031002c0c0c07a2031840c0150012046094540004d03c0c598100d581e0001c10050001075100a0040d00080305c1032039440d4a4101290824041c1100f1040075070703c000d00301010003c0602000381c0071658040702442513411118050002d400030a140e115043c0100002140d02501103004001e43e00c0d0a01d40c14289400c01d80305041c0c40c07610055015405041c04843c100316651240c00020140b0014001d011510700382503031b01c06803600680041d03c05c08041c07040c0242d040d04064040180031f1410b42c3c003403088101103030070340100d842544098100c802d0124401c40b0b6030360640007001741c1c01c020f032034007421644c42c410582e050035642580900030080070b00c0420008142507009001d01c0c880c6180c0982030071416102c018030150250300c020f900a6550030100701050300a580c00d1514a081802042103070701c1d40c0c40301521404050b1038101048010070000d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 693118111 1250 693116861 693116867
    0x1403090703060f0c08071e120b0a300305040e060303071406071106010e01090c1215050f060c0d050a031d010e06180706030209040b180402090a021810 66
    0x103001150000001d0003803200b150140d400800d0307824560307000076202d00c1c000f07807120f40144280c042d4906208656001c400000008890750360341503910f540d044d62107401183c7e40340d42d482d004e20050000203255144001503242000700907000c103d1065110b00c0113003181000301e50040d0640c1d0881d244980f21000c6656100002421842601c50003810031034040b020341580302c03000034000c0c40342c895626291003940303920700160340d9500d01348141c29254104000622002089811646800d901c1d42056410302443c0b1010b142500c007907610503030840c440450308000382c1c0f808035000b000042c0300b1380d44030b4544109612240e8503491164040350612600142c40e03200729100394031104248803e01440345003020602c0310f8034007820300c1903004041d5100d002d0109031045001520340080c0080c3e4001403100a203000c5040d0040e400231440c4980c043d558041e02d5200e511001c10003004c02940a030f8441251410b48100b1070704000c040c12580480f48140140710000107400c10396220781c03e044501091039082c0203012 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 693119361 1250 693118111 693118123
    0xd08070605060924040b012a060b150a11070b130806010b0310031119090e0708010204080a021c020303071202100b01090509040f060203010605130503060106140309 72
    0x400414000818005006041c0d0107240128003c58003035402d900e6002c1000316103101c1c1200d10348114451050101289801e501c000b00c80b0f00d040c140a43c800e602d010101c0001070500f03402482e40c1c15455505800c00540d40304400046d03500b01c85158510311803070600d80e198080d080d0303031105014128041d4040154108820801003a800b0050340e0703211002d80e06010b42c5c1d081d80c442c26120740320b2000042140c83d00e407420b90b40700e000480702400c050b03881c680341c0d0035403612003403401604403441410040300c42600345500c2c8081c0013080750103d044000b84928601c0d0111543c0000210392040c0000c0c401e82c2c0020581100c4a50111171b0706003994644004000c0c24018048000e40c148030001e01d01d01000321020341c80f002a003454080d180202c0d11a1401000e885240c004c0714001a8400c405001c680b401045042d0418080c01112184c00b03400e03038642040380c0c000e07009440410f40104542e60b640e800540040040c1c4016001303000254508600603001c0800402095030008000c000100001010455 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 693120611 1250 693119361 693119363
    0x1180306151517060a060e0d26070b0907080d030f0b0a09090b1b0f0c0307120806150421240614040905060c091c05032a06150d 56
    0x191050010110003d0304040302c00600f528001c81002c00139a1a28080b12014100c0d1960780721038500705190b00400c0441c01440307204841c0000480c500c00342d0785c014441c90a01c4d0305051060385580760114200203000b01c1c002071031302c0180d601c6140d06210046010868020103d50f034100131800d0610300d40520007419004200030703000350400000180b000c0107900326076490340c041c002011290300d520000c02d203450182888001050360812007005230074907501c02032034646180000d407414500e9603690518041d0501410400003108401404001c3c5460003104a81c844614845803805150848000f08d0340d05144002c00700310114110081071000390310400001915840110071500708880d07041004201600071002004004040600c1904041c402ea44d032160300180208919038071480004003d0b4420000303580c0049041019928101003d198068000d2046000c0d540b83c008841140d00342c50303007910311409030928002040c0100500495055004442301260050302814103010541048907000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 693121861 1250 693120611 693120629
    0x9020304122a1b05030f0a030e27070e06180d1103030d0c0305150d0b060f030d030504051204051f17010803130602070b123103020106050118030615 65
    0x6440c2c02003042c070300b807080c04030003140007039200b8982c950081c580d0342e00c91300b101181264008200030001c00d006001020b1a00c0000b01000802d800000b191400c00402c6100c00c00036800d820140304440e600245128400001a20454108000c0c002e06281c8020b0101b19240254056002c1c2c900348062004001000301005e411280e4070000602c1e5040100041c11901c0300080c50300000c620700541c1040c848280340320043c8801e82055040c0c807908140c00303010344620307840380c1d5400c100c080c941c50a01c100c485040a90b10300107a186481d0400500784100100c00001c1d44008001c10302c2155500324030710017184e0b1003a54800043c10b0004d402c1d02d02d07210006070400700842d039200000e08e030b64000000b0308000c1441c502c284d40d21603548038281e90f00c031482d004075184c600041c00704414182004001a034810034407130340030000c00ba5904000740554402030320905583d42d91710100041c135809000d540000d1100f8a0308207035403101c00b4030b111400540c50100400c1c107915484242441080601600d0292071940 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 693123111 1250 693121861 693121937
    0x2090603160305060114070b0a09060c180e0c07030f0c0c091b08010b09060702150705030a090b0a0c0311100c050a02121303080f0c0d030609060902030412 68
    0x141c56003605000380d5071072001a007020009212940b1030303141401d403928140404c03810007126079141c405106d0010035401945a4846000d00886c001e406250001082611344801c0850381a2110001e00b9154211808405a00c0c06100b03013640c0003000c407800b1507058070b03100b0311110017803c00f01c81c83c41c20300001034980e4141000114804c20140d1003401c0b030780035052030004041d030780300e800707a03880c1100b4410f02a54020912044260b8103001e0024083d59100a05200c0505201c2c2912074450b00591015900740e03002041c41241c9079000070b048030107000d805202c80d041001c504c400070980c40380107000408000c0c2c55244403034440d004002203103030009201740c00c0c030000911640c018a990403a0342c81c0c20041c070a1050303c0e00c00305518000c070342c070650482580c41206401d41d220005294032003c803000003140200075104001c041482054a042a141d801140075440e029003501502c49903080310160a04c100140000511800185040d8181c0b90030020b41034110007805400028404c001400c05a0705c1d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 693124361 1250 693123111 693123121
    0x804030c050913110103050c0f070b0f090f07050112060b1215010c02030601050d050f121c060509040b1911030f0702070b0708180406170c031f020d02090603 69
    0x602100a4840542d91256296a0f4042411014a000b00040e01c010496008030f107065110b80c200c42c0d07100720202009440c1c018806030f41e00850344842d40c01c0c2c800d40b20800c10b200034803a11000c25a0070122100007850f6104070101810b4440300144a498140400244c1c41d017140314013034000400a10343c02d50466142e40600e4030b550344510080ba518815640346c040c05145941c003030f02e0302111154002d4002c1c40035a080c013085c0220007044540c00e0703070035115024841c1503240042009040c079440d1000200d07100e0342185020705810402001054040381002401d07c8642c8414103210340c0590884c0d0000030715141c204518030380c0c90030155034907103841c1010704d01c000911012005600500d4500110055562044030403030710f4440c507002d000000c1c1003c02141000c60307030070360191010300203100d90124001400000181254219070280c1c50702c001c3d55608500b10141032142481000043c2e0280407100030a503407142001142104c0d00c06c090794081840f412182c05981a280d844801400e034075924188 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 693125611 1250 693124361 693124373
    0x201504030b06032a210d1107091b0507020d020a0b0a080a0b0d021908070e0405010f1104090c030207051203040209010f0b0f0a1b0606081e07060e0d080403 68
    0x225079a030f0080c440c4502942440c5640900c2103024800110446840c002c410104400f48005800180c44d0b0403d0548112042d681880b4000c65101551110f020640c4900c00c0349040c15101c2e4028141c0910700b0408810441240304140d200108503d4505d64403403051000840716206408083d410046040001c5a0f003201c0c600240b00c40d8803a81c8480c022a5104e00b080b00984240c880e8107500280c0049681005042c101080038100301d00700d02d45d420103070311250001d1400000381d0000c400800010140804d121080c494803100b155800c1040c40300c2100712440c000680300c1e6220b0f42c200550b0321903240189910030303810b88180b80c1d480800e40f12503203400360740310300d454000b56800d80c4603045010000904a4624a500c01156141d250f00c60038609c07400078204e001c1d00402041c1084c0001031507002c070402201050b8001c9140305800004404d401c00e500c80d86419141c2c409a180c21540b604000780303865000910501b2a10b9500d04000c0003849400071441c045503042e0002c0100ea0b002c1804820081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 693126861 1250 693125611 693125633
    0x1060b0c0a1728180e150319170d0510060f1b020105030a060801050f091c120f0204150c050120041815030c05090c0a080f06032107020405011220150403 67
    0xc070031062006c41d130112020183c447e09810880401c9400d15030b02c0000180003940384c52014500003070243d00b041c880090300030580340211004c28240e50315003403c0c46165003001e44c1c42001c1005190035a05200340d002c1301c0e4080303014810080d060100110004102d0b41282e0030010143c80300000034407041c28070342c552440e0b800c810303a0000c202c0e0045c0c641c40c08a40c070001c0c41e400704421507540c401410745001f0711030400400d0034117481d41c800d0341c00300700101c0d941c1484150078060111598501c41d10300100e040443c00c540c01424101e10703c8819006a0440c26818404c0c1c40c241e0310308054040c1c40c1c1d000f03159038400510740041604021003a0b00000803d1044500f140b01c112282600e801500e5510b200001034184258401c00303004c01c2881d00824034100c0000c60160703100001900301c4803036a41621500441c2c1c0041e049481e00c0940000d20034003107040501480c1e00401000742ca0009122081d070310075100e0303420f10407032500e00704c02e1114410741c0f40d440a1030400701c003510144640d5131319141e041c1810280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 693128111 1250 693126861 693126871
    0x3030f1d0a0213021c02070804051804140105090a0219030b0f100905130303090525030c122d2f0d02010504140301060b0c0a1728180e 59
    0xd94440c1c60f12003c1c4003074003c488200d480d070fa04140803411036110003c029080060180d5100209000215080e290f030f01d280d0301818801d41a0030380c00e14080c98409440b07121886515866410481800410400080d0344c688282d412103108440c50305040401c181d80035242d0000c0e00100590060080541c1108282806240c4502c441c1c120a51110520300036103009807041d940c1003440402c4800868403941c003590156100302c0070364030f002101801d80c038418500c1c0c0500e1a06080080c0042040010100300f0500030240030703580c403064050f542c403600c40c0d02d801c03901100507500c441890300096802019004111a038844c258803004290030703100b004040c026401034502d003c0180c00c0401d95140c54601c86100e281e05035202450f00c1c0c24020317034000d4240045110360b0103640320000810206c01c00405000744400c801d0040c98031042a081451074030070004000b1485000c100300346103080c10694944410322504205c11014400240e8049031080d92200c01c41e0b415824214000c0780b18510800c00d540a030b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 693129361 1250 693128111 693128119
    0x303050f07020a030903080708121618031a04150603050c01091410030e0102040e0a0b091b071101050c0102120702061006080f060a031407090c090305060403030f1d0a02 74
    0x1541d01d400050f0380e620154440500410340e0040d00308001031048000b80203041c40799100e0360505c0f00301000354110b540c059070300058101d910011504060b41c890f040c920307030390a4071240846140c61034554406008003060240000d81c03204000609001022542206140807603c5c1080a582d5909040c1c1c0c4230014041c5060008500c0c1302c1c006003d03d21148a81590300004008483c4180b4041c800d40003001650041d2041d5502888001004813482c002070f031254000c184042081c075080001c22029000040c0951510000540581ca1102e12001604c0409502010080f014031441c4010f850a010346400c4c9000c1e90700004e441038010051002c0b060188a040d002c440b61902d03602c1d540340801e2031038000c080002e00310320001041d1030a902c203c1c580041001d003611a500303841e0340340c2080103040038030444031540c0044010000c00c4114851002c85141c1c92030400132305800c603516961034140c081c1000d400c0580f12101800e0700181a03100b031041004000c600c50100c1c0410f941d490b11008210380907446 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 693130611 1250 693129361 693129391
    0x708030a05100b12061302030f0a1505150301030209070302030709061b0804032402041a09040e0a081315210605041503020301050c0903280b0a021b0a020901060f0e0d030305 76
    0x6c005500035240110100c625000d0aa0f6407000d070350000b00841c0340324200040108030005403a417207101c0034000d4143c501d6141d40e901c0d230450041c400b42c0341c0040c0400081510410400c07107040e41c08000201a14518074001c01004c0f58149442c800c6803d07000087d10260300020004100604c48056107040012030401c07005404541b03000104a01442c0300f000c08001d40f4515107280928410000e110000c801840003801e4051066028074210040c541181c1c0c04900160060941c40d500c0320420041540e84030340315003044d10074401005a9002455000e1029044114100d000030940181c2c0150074013900c1080420040d42d0540750070002d07840300743d011354031b064049042080301c81d00b00c0b41c0101e0083c00030001d106041a519102201000c011285200814840d03400607800d84103860251f05c5002000d82c0320960b00710902003803200c54a844440354031546a150041e01d0307840055046030f50a08041c00600081038084e070b03d080803001070961080d01d640c1c00070109509030340900d010312880700002d51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 693131861 1250 693130611 693130639
    0x1305030f0702010e01091404020912070b0a080108010b130c02030909162606190b1303110108040203070b090310230f0417030c0c0a030c170708030a05100b1206 70
    0x10381c1b0003040c081c20303520b07500c60701718591642060b400038466a08007034100811301c03a01100240c10003401d070300304c58106480011070310380440c0d01c04145800b42070701100030802c0482c1003000503000c120000c0303000d18240d140c1e240202c404e8028420b0b91041c200c082e114045600e0710011b11143d01c0c20742003070718020924242500c101018100d5002401510080000506894000401c0001e01c00b84003400318800c130150f004142d1860302d070080d0403403464481c0452121030461400d442c203608100316042c100b183e001e0412001d82d0300003400d501241c0703030b160710641e031031001c107000c03900b000c501e1119607004a08002021a40b100061441e0301c0440204075280c682d521154100d0300b1b09031098402402c100c5000c40030410b113024990086800c8401c14289506c3c0c000f0007095941000784605003500882c482c0d0440205001c50000150000f1160341d60091601800d9501e00c4414000900166620b545d03820004c1c020542c45944400a042500040340e1222041c20000380d03000c00840e25140110200c00c41d1740 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 693133111 1250 693131861 693131867
    0x180e1f0f06201614030105060d110405040606082b031b050a020102090d0b07110d1d0a09020c0304090e01090c2c0903040303170403020a0b1305030f0702010e01 70
    0x3100362074180e52100814265100c02e0101c1001504119926000382c1d24421a060500b040b4400141007042003074143c06070788000c250844100610540c000c0d40d40c4d050718170003e03100340c0986244200850300003900f900c45003080c40081200360022a01c034825120350001d48007403200c03000319221950401442140540754120140c68a034a4800110381c80020090080c070300440103024948103600c00141405c88602c00920b84110700b41c415038480c0c181909104603290301058016482852400400813004140001000d4040303241c2c0c1075940c0e00ca0460072040fa552001030a03001080c0b4a001503407903414802c1c0781c0e81c50344d1140c0f0614040901c1d1000a088404041c02581d8030150042406140c50340351a0103504e0641d243e8a000740000702d011440c020071118a4003041c011084400110746031825450060b024105501270200201800b000700f20010740c3c0040e420100c288c0c024501520781d10750780c48a48401c0b207461001812800042000790310b442c030720f2010b4107000d4003d99848060602c110015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 693134361 1250 693133111 693133139
    0x31215060a050304051c090303030b0301090804093206010206100807171c05030702010c0c1211030705010e24150f0105091309170c0d180e1f 62
    0x425001503051103500e1a6038014000341d603010707008070183d401d00d40241c0e5101100407516450100440c0410b00240181750f4580300d10040000c003a40200001d85d50707616403030014001c40c0300b000b402c591036404170340b0f410100308001400f010450f41e8140640320030403c0360403004c40403207000b4018130407000003171343e141c005000702030032141c0a00c06800b03191306105401c1c541001c056405420351089080e00301c0300c92884480c6a888031250f5440300d40724105180001c1c2550744140d544010000b02820507804030f40c400500004910084c10a01e51010032800504e0450003000c0000d041546010360b090141d940c0401c010304000c18000e1200301800c07200c0c0e041a03040405a0345c107285004869154001c500700441d0780c5d0f41c3c1c2001410f1060030328629400080c0440c054100c5464a05d440b20584030400170000740c000d1815101b0400d51381000d0340d201d10980e440e20010100001c0010541440482158124541c00138021008041d02140b9003c4812013015240340130011040e24240030024036014400e2403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 693135611 1250 693134361 693134401
    0x1b101214091c0e0d1106160c081204050f0a1802040312032a270e090a080f16170a020c1e2e0801061e0c081b0303090312 53
    0x1564028401d480280a00703810a0f840c11569035940e40c1714040d09640e4040a04034120b0101c01290354406141342100e001d200580c41074240f540090102c40700d5079001015681900c0c0141c41d4516602d452500044864140c0d038013900040c291403400c40b11f149269001001600d008007182d1030f51440c1c0302c5044003101c81c1181c40c6040b0300e000469045503a012207030244041442490500d88959035a000c600c0310802078406500c41101d400c170100b1984024110241d84503011901a1840f140e10f5107940001d0310400a000c2103510002450f401c468242010b031203c807641110b000b2500741000005c140c0c403075012000620140c46450000030603442c28818880328081202181441c00c060708041c00719280110829014160850450000c1826107401c80c17802c50b0f1540c2c1c0d03100c0d29549003c030041e01c0404480520503024481141c08030849410480c04035140b0303800014a0f989201d294000c0401c40310741180d40040b800000148501240e002001d0720b81d00e004406080300640f1402001080b1f13004c0403007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 693136861 1250 693135611 693135617
    0x3032003010f1e05180915090f070e060d031209061109090a0b0a090b040b0310090c060801080c0d0311060708010609050906090703020a18030f0c081b101214091c 71
    0x2182806810040c5041c0303806c01104400c460100129032039071820340a0071920303404c5036440102500e5280408000c2080241781b0045001a81d0600d8008103500c41501d04024042c400c280240d0510500140e000c03c070903a801c24410400010b01450345c03840c2c0e501904c50703035101d0040000400e41303000042c414049050001400038501929040105002c1d0019a101d01d82c85940c5100d110081e40b01801406040103840f0000980c000a80c5000c034501d180540101c030030041c0c008014852900d0014a0856404040710b5000b041c4a041c0340031242c1c0304000e143d11095008000a220041360045401c13810798056459502d03c10361100b043c041c140c00c007150761541c841a030780c02040c01e00f8000d82c01030140302d07000e00e4250b841c10604203249404a1136503004444800c019004001030008104162010300954400342c91801001580d4024140d40c149160348511019140201418042d0107080003804c40c001c01440079400c400c0440c0d55a9000b2030710b40502e801403000340302d4070102504603024400803d40f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 693138111 1250 693136861 693136879
    0x41517091509010b0a151e081f030203010903080a0b041104090b0607020901030b0712060e04031223040519020d08091503012c060105040303032003010f1e05 69
    0x100c0280045070014044800e1950384803007404a030341311040000c0182611040f01c8000365802c4c0c400414034065454842c9940d42d003001c1728004107602000c44d50308404440000d078020754000c0040c0950f0145588001e503d0b61800310024201500076440301e100e200341c0b01d4204032965441d0140005d0310041641c0b150303140c0781007005200d10403440d4031075641d44101a2800f0304001d107980c00720b41401c8003a041030301c51901d10001c00422070b03400034921080381203410040c412603140a1b40150080e8028000030244140f05180d1940340c4281c2c0e21500c9030f0440c0068602000321010312416152005403420f50f680d011300100c0c0101524400361a50a00368003412848420702e250b200c001c22500517041540c1d1081da00440e070b948000c0198060740c0a407032101c0d00c055103200303528000d00c540c0300c003580750989002440c003c1140302c0e03801c1001d072400c8036010704000c14400255050006004030711500703503820b814040000700780ca8101150700c40c10395003810351000400c00035010300301000806100b030070341c084040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 693139361 1250 693138111 693138133
    0x906050c0a0203030c1b010c0804050f030a15091707080f0304030908010207030518090606160606150206190b0d020d020301090f0308060406050913060203091204151709 74
    0x200014060038140005803030881e9101ea00007815507001d5550120b980e03201d4684001580d045580700300d0010000d08140e0f0004107107a40711640b60046108071807051703a42d5000141c0341d460501a4000302c40d401309070b10442c074a150003200020015002d080d40c0210340242c3c40850780c0204000c44407040d40007903400d0300341112034141c41038650004100f00e04204c106600001e550ba42400900780003031094036001c0e10307030000c03080072807c1d550a81c50641c0701e01c50301414040d581d05d401003114620350b4440c1c80180407405500348035002c1e12603070344001c6016540780c41d0301c00a1035000c5041070103080880312101e84400d21504c0c502c00d4500a0b45030075400384540c03541c030b001440d015440094040c4081c002184001080d19900c907800d0807108150081040c280030014240385c14032900026120407280e0341040d0511030b030700440801950000030130055001011a440b41c1d0200642c070010060310201503601c5403039010320410340d000404820f01003201c4000081e60190450741403403044560b01d0080c20300400c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 693140611 1250 693139361 693139367
    0x506194a040206040b0c0c0f06070c060509120f010b2d010e130c02010c032009060d060506270d05030306040f0609020a020a05070501031404082a100506030d0906 71
    0x1600c01c0740d1180f000c0000296805921014048100d40c0e5405000905000f6061040b82800001c005100d41d80c00c11020000606c1c40507440140d0307425190158332000c40e0404600546c0d0000903070041c0780b160b05921001c864054000c400040c1e419503840f241b505c981903048019040401004400d64000c11a201c01c80d4032803541d0407410b9100400c440302200008980e034084410350018000140d44a0781d00d1117415070540904e00980c0a5044502e81d0100301c00c0e203883c00c0340245040ac03445940006008040c284407030304410050314005240e1903a91802801c81010106078007c8410070b60303000040740c01249031000401001582040195296030b42c0c4030700b08401030040c0c141c6001029501c1101081c5404070b8400380c00303826207075001001c41d00b500c2d0500514040065000c541098140341c0310007203048d10101050b8005a00500081e11225041c0c05140394003000e50700899001325080030540c03401c0c1c000800d4000198400310400142e142e000c241516090800509030108440580800c4a644 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 693141861 1250 693140611 693140759
    0x509090a0b04151a010906081902070f0206030c04031704030c0512071502070f0e07020309010f11160302120f0303071101060f0b0705100606090504050619 68
    0x403082c640b200003800400030503c1120450314080200c800c590301c210101d96000281d11b0060015400d00d030a81389045000c0007424005d18505401887c1c0100fa01801c0203440411540d41c0e540c01007455449240903480c8a50f00d40003440292061501811440c2c1800070000807030701625040b030450141e045c00c0c2005d0104040c21201c1c1d800e1540f180400000c1d01511b100c4410040b13104036406080024039040444415907040d030010000d81c512601809100d540001c102c840ca10020309000e030350000011001e640c841c0404460b0a0035000303040701c0000b0f000d0340d20008410380344226080800c4001c1541041d036286070b450807903030700d5038001c00106180c0390080280014004100c800410a2500d80100c2d1503151100d60000750340b0761001c40c22208121003400226024000a4030400c565407030801e0040560703c16100c2e160250b5640c80100d0744071346607032140101e0b015240f00658001959224040c5003400381d2561081e807640e00d07118481a150104c0d101043c0c0c200b0000d110f007445560082c41d03d00040c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 693143111 1250 693141861 693141863
    0xa0201050306180f0106030b010516030f090801050a020301150513090f020904022718010e1806101a1e030601090824010509090303041b0b040e100509090a0b04 70
    0xd5003415007110f02a22485501c2068041e100c50020b516020001e001c0e60816029a818440300f8842c00e54541d4800030380c2600c540d0140342080b07034066032450540b16400f0303540001d0900d5003030004000320b140181e00114126142001c1d2480746010700c0600f02c0b10750050780206641c4000020041044040913040080000040720006260880a000080c2281c1c0205116900c136004023030200c00c002d04200044582c82801c0d50090010316012140c8009000140100081a00d512011803095070240520101034601001254400d0130408007105048003d4461101400d41c4c2504c00362002d01544151041c14001414000341405084000d90190b00000d2000b410031841e101e000403001004c00075074000d6555031152240720000d1148070420100160050760285482c1428403a05007000000c1342e40c01600076007214203098000b486a0005490740c0d0200e02c01d4440401c01081c844400e0441e00e0044000c1c0d90108445a80c410900c07448890403600482103400221103c0301080030450116885 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 693144361 1250 693143111 693143119
    0xf05090f0613140a0905070531140a1707260d050421020d08090f0916020c0f010c02100c02090412022418070803031e10080a0201050306 60
    0xb00b02e41100c0b10500ca40e15602c411090b122414180485042c4a1a06409050150f4090149191030003000d406449a5101000310a40c0c0e010640813a21030b95580f03d0120799036040070140b840d600d40c428141480014445445002407a40006031500075555800161200101510b00b03a4a07001080c0e1281034903120480001000380408500c84106005160a0458949880d61650f060081031854940d06a00001c891030000d5088005642c40d40303142407026921100c0c4c00d6844403440301194001c4029101181c0040d45107003484040d2511070401d0041c4801942102c9550391000200041c1c11601b0451038040b40840c44200050308000f49001c26005940c1840c14035590300f03070301261960508403020740701d444507000c41224950303040c4081440c80c204c46071031000550300064051000f40001e081590000c24550782c09c0440d000034400000204540340542c4c0d01c81c03a14158820040307114101e00a0200c1c0c4410002c1c071584448401c0300d0955680a0003070411446680c0107407801d600c050720035a84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 693145611 1250 693144361 693144367
    0x30c02120c0f060c03070908030406050d27050f15040c050d080f1801031a130b01020a1703040203060106050f0406051b010c020a0b240402030a140709060f0f05090f06 73
    0x10b00401003055030700803040713007180c1603891400017001001c1503000c4d00702584a410030031040080e01e038808103562140504010000d00b1005803a0789103600c0500396010440c46218804507400c1c00300100300c07a42e951507003400b038441000b40d12400205804044400420406003c0014006402d1109000074032920494000345480340040f185030b1a5080300601101b00d40070012818030650741b5024680e01da0311b140071440468040400090345138510340000d1000c00755903941d0202d80ba1306c01c10607410015001b201407494581343d4500000603a000f11b609a0103403184000024003e441101200c1000c0040c420f00d0b4149030500404031681e6200c0e1400c00d071060172204034101020800c0c1300d0bc00d0340303520030380051255907800d04d02049054801018030b426009550740e070b8030420802c81c0d6070740801d00040b140182c0da42c0e507081e00c00b001414402c648410407a90700d0208031200c2c1d044100c5009944254a404442c8442084203c441d08583c00c040000a801802103000a080191290540e1540104510300b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 693146861 1250 693145611 693145633
    0x3070f120f1e0512040602031803031c020d1505060d0207021f030903030c030606050403030e180415050105040b0d1103070b0a02070905100503070e0703090c03060c0807030c02120c 79
    0x3030084508810740b0140b0110750303241c00c2140812041d030883c0c80804030340e4101440c003d0041c1d220301401300c9020090359064481c002a43e800e000f25000083c11000d0080307040c07a114100002500b1030141120810315240b8862089012192407400300d5400a010300d00d040c03007100044019405c0014105d070000704a0000c00182c1303880030300d480c118007d240d80c000f80e0380c0f400c1d080041c11395000f04010401e01d03180c0702c400e1100e154050115010340ea054148400054402c1c004220f03100c0f1402a01d6182c0200c070014003040100600c0112130442102205110507603d40080008030741d408000740340d021420444400000d0350090b01c95000d00c8008041e0ba80381542c035005215503500c4003450b140140c01242d020300100c8001c0c840c69400910410b00c03100c4150601c80426600c201ca4002c40c0030143c980400540400c0c070030707080010442c0e80500b4840e540e560702d03c0d0a10283c03024283c050085184c0b030000680080c464864606421460341c020805048000c901040b20786c03040e8030200b5140a034201e204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 693148111 1250 693146861 693146873
    0x10f0207020a03032d050706051b09040c1707050702120c0a1203020109050f010e3313171306111c020c0d141501060e04050a0b0415060e03070f120f 65
    0x201d0308152540f00d031b81c4c0d43c0341603181400c2110401000c00e0845400200301075070030000f91080e100400415100056152500141540c09000e21610361020360705400400010990082c040c0001070b10a80d000c80192007030b5101c01d6145c0c11043c8841c0d401441c004c10070450414030051207060107019000001c2c4200194544904001c85001c0e00803840e034480b10440114642003203400f01509440003120400d003481e805040340c800b142c90f80f6005041a110201c1c2d541415070080740645ca0f40b05254000744240e149001c44581c02000e004c5014460001c3e001540f2405030704031401c0300c41e41e10058001c009405031201064640e00000404511a140d8417600e03a46507007443d100e8440c01400c6407070180c0001003056240030042100c901c0342c480740c20010448203030400750348c2c00e0700350742101c020500b0707502c0d82d1040e0000c103423403540c56038040e0a0900300d40b540240e5420b21020b81d81795a403041e103a550b03000d05141c2c0e180c1c05849070709901c1400403420412500da050f6844059441030085041803903058480e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 693149361 1250 693148111 693148187
    0x30b04020903033603061f05060a0306150c050d030f200304060e030901020d0c050a060903180801060b04051908010608030a11010c090605071a0a09020102010f0207020a0303 76
    0x10403400b2060246034805000018201101010b0050519400d80241000b10346c55003c05003140f44401c8450440f021480d25640664010300380203004152585e203070710302c02000f0304010702c15a629214402d640019440c403031202c60302e20a0300709005001e107507610041107009010f9280c440400590780d50082031584031403460312000d00340c01c107a501d4481c107150400c00101c4d13805d90101e02c0c1c25030041040300d14a98005c40d0381018034809080c01c114080807410b0503070500c00205e50042404e4a4009260101038120008801012280c5111040079445111550072100640509001c00c00140001c20051400c200390f41400c0002c1c421611000b61360b44103103425901240c00c290380581020400c442ca00342d009200385002020310000340510095500080e00254060140b00100800090100c0038080c0301c030a01e40300140100000c580c41d141c003140040003041c0c6020200d0065003482d20f0314254440398020303070300c9481c1c0017058405c0251079540e0541b50000c55800418080d101035032210426a02c1c9240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 693150611 1250 693149361 693149377
    0x31512010903030b0307140d06060b0f040e1612271101080a050c03010909030522060e01020604150e150705030709211101020c0d0f1704060f030b0402090303 69
    0x2103141c010354074026040c1ca0040c203038280a0fa11403241004198a03130b400d0514410b1069030280418101824240d0142c02280c0000807580e500113052602400900010811038899190340700b402d44803d4401307440c5035500c11550b400510442040030301002242c3c8406000c20319141c00d0711482024824603100d00341600350030b071010b500742c11140316256041b04555501c501c406408000610b0006408810390106014110505a651740000c080500500c200c80030300c1a004010009090302042d42284d12400c0d000f02c0f000520301822a50003035000184d4031780200c2d80000700141c0c007618425044020000c2150b050b05900c00c40b00344440110554031014042c140700c2d541c603662460020030140c149825076000070100c00c15003907001c6c15000c0c1c440700707960400e500181900c100141c6000403440d20381c2102c9140e501414a0b000802001544400140498402c0300c0140001454940544080c0600c1c49a000410118160032213958072a6100d0a44024014030060a01c20200c1c0071a03e9a040411 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 693151861 1250 693150611 693150613
    0xa090917130f12050f060c0a0305040213020c0a05010e0a03020303040615030807141c0f23040b090414101a040f0905090f070b04030b0a09060c0206041101080615031512 74
    0x2908280002801082081141d440044c80c06e800c00c0e0b030422800b40b003801c101d42c1c201951040401c0442d641c010090140000c900400d640302c0340302e0010700d84ca41480c2901240e05620f021a070310300580021410741710711074050700030303505650b1213072540c401519034000054030325440c100c0003200180c030503000381c595207000e142014a2080c00311030041c607241400d4410b103150300500781d00950f8a03a01000c42d4008800750301d0304031440f0041900014039021504820800f204022902007410030403800a02042d041c102d4042c8031038110007500a103003d03419511680480103002e0207000c42003c5040303401c3c1840c504e0303942501d0550303100900c202011144c0c000550507034543c0103000445508100390b40b02c001101014181c0030b45040440705803845980300050140e800d80c0300241c00d14500e0760240800907049030341030042c80b01c0040000e4a5010442d401c0b2245040b00d82024255481188550b01c540030103020071940c9140c4407142d9101e0f400045c00b410741105ca80009168980303446029030003071052130b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 693153111 1250 693151861 693151889
    0x3140a0209040b0f130b13090c030501061a041e08030412030201050109091a0c0c0601150f09060912050705090f010501170103020d170c0f0c010207080102090a060e0d061107020a090917130f 83
    0x1141481c00e5940dd50b1010080500c2c074166401c0d105071700c0b81280e0454031072a20000e4043c016916500740864282d02c2502d00340070104000800c00b284144405010740b00c0e40c020003050303884140344000c98072008009840003040103198900c01e060308140380d0700980698055424000e122071800d241c004240c102542c60150106084001904040a1940c020050620800d00ca042c00710007002e02d0b03403510500b510103c821080c901449030900c1007a01030040a4117030038081c600000043c090b05c1c428410540040c00b05441c0c844a4200e825405058a500914410101f5001e444102c40c812035510041d03500b500410003140082410800900300c0030030b00707002c3c03c0b1016000c00060f0400d01c0c035074059186a40108801503150b41c2c0d10703403020151203041c1001c2582d27030440004120303070019048000f0841403510451703440300042c400103402d130103100b159098841d1b52507454000c20f4406c81c1c80003c059103032403480e507408d408080700a040c0c202616400b6000c44c5a43d50300348005845961b020181c20384000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 693154361 1250 693153111 693153113
    0x161b090f090b15010c02040c0909020f03011401170c0a030605031e06100608061002120f070c050a082a0612040b16021c03140a0209040b0f130b13090c03 67
    0x40e0080b550001401643c001c005084000182c1050071080d0001d01ca2a59814091042405101c4950191002c00c07811520350198a049a45c02e0303000780680080d03c1234442030b0440755840780301050000074440d000c86803540c4682542c403000b07804c4000200305250312290301054503101000103c90003818409091080324000310403500340500500400e0448280b1882803081c690420182c541000080c0d9a04144948442c0124148025990510901c500000f8034110040000002e80486802404090141551030041000c407221a00c10481c840d08030404909030300800306096107940c803486160b080c03940001e030300003041a400030300c808028080a805020030b000410303c505500c4821400a100e40410219000c0d42c0da07840c000408041d00900d010303120342d1a1080c0c11001c40d10b03100f400104080e0800d200003202a40004007500e005614103030a01d827141c9401d05402c40c120402400a00e401c004240700c03200038060b000c0b041034110700e260810082c406400d01c10b040c0068012030000034072a0031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 693155611 1250 693154361 693154373
    0x506240d050714071127160906090b16021002070f090614100c0f21030605090604110f0d06031205040617061c0507060212161b090f09 59
    0x161a1804002111482910f00c01d10441210f501d11780001160f10300c820b503100014118016404420a00b44428503000b000d50020006180200300914844242d000380c42800c54038601070340300c4c1100040310410104a560038076402040c0140c82d036052303036140c507a10350085994003071004034000c0142c0c4030706030800c0301c1c0c5805c12030307800603164107402813160501c0c08002c4208151161480c1d0300c100c2c0318149481480f405060000c910303550054842c81c0c1030001c8d003402409050003010104866104c004000d60903817007445008c0c183c03a4010016119a22a50300307110043c50306456220440800300542c421003403250740079005650385904003141190070340c9085642c9092507110101808014401840b000b03410407a041c1d03250000700c40c1626590746100005c2d00210702d507000200c5000100121505000012035030700b00f60307082070302103900048180b40b02603624803800e0315036844d000a5424440000c1c01c00320000a104014600c0d42c4100d98072003007003c0840f201a1148a05c86503545803050405c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 693156861 1250 693155611 693155621
    0x12030601030c0e0a0605030c040320040b040c20012a0905030d08040b1e04030f030e0f100504050c120703020f010509210f0f010501030b0105060405130506240d 70
    0x10007480e00203c031401071804500621041d00414080c40700100003e9900c0c07038820240e40007150003100e40c079007003200c8100084490811004d00e07801642441c03031a07001801c1a0151100d040520703903500c0d1000b059040c0900800318184c00304a0390b0354aa0f9040e480d01111311408041c04a8030100180c4005030441001e41080700f107512541c002c0c0c02808031900415000100294030640250f2241070580e141d00100801e1060312804031450880e02062106055001e00403007004021031300d0411100001045e500d5607040150a8084c041c2e0207001c51318104440c0e600655045032040741116000203d5400090421203051517004582d40b00210400541c40d00e44c481543c145820700b041c40c030b001c07980004508148001100c0c0050b401c591515009038440802c03035111201000003d488084e101c0c0f070f8095018040030301c0140d484c4240040041202d14240301118100c3d40c0041851b509098550000c8015040c010640b6034002d480ea03184007102030010080c0c42c0265000913465540720700341451402110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 693158111 1250 693156861 693156881
    0xf02071a0117062a0d0507090e241f050c070b0f0a0f0c06050c0d0501080303060d0f0c050913032c13061e030507060e060421051203060103 61
    0x1c580c1410340402c4000c0802c0c1076410018200c160200f0245215400f03242003034411507500d0800c800108900c0d003042e02d0340711303070b0060a607a03980c0d001c91070341c48030100f004070310944401040850342c4c1d003401c090002c402c02c449542c4601400c40401c54890180d4070020440800c01000854800900060a4001171100d28041d040d524603482c101800300c101e10405002d980700000c2848144040c0f0841c0501a004040b401039110405000360b1504d02e10110050b005401d00c030803da4140342c008510140d01200340d134403c0c500075018540a0034240c84054924000b13020650f094052183e000c07440d0344a01428034450481e100342c07211165618980144980c01668090030342105081325a1640c9503500c24910000b2f100700c51901c81d42e103204045030f00820080c0d03c0180c85182d0551817030703044079a803a030701030444c2d020313605540b4925500c40c0295400c1a0284000c0c0d40010100014010315401d4030341e5112410070052640a64007043c0d60342c43c50001e046d042d40102c3c25021082103060740e07060203081100703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 693159361 1250 693158111 693158129
    0x1209032003040e0c03041109090f1204090c140a1803060912081302130213091e06050102030708030103241a03071403100c020f0d030510140d020906040f02071a01 71
    0x5443c154990b400b0f0078036407c1105103e5041d000c0821000c4608009035481c0355210b0f8107894000707044441401d425403040c0b0500d8a114145640541201c1c095400e2040f055501c0c8031036481c0042c103007400c40da42040800c2000b0007050119000c03004c074101c3e200e4004040e1082d101c01541c4a481040a4001c450040c203045101d890403404500588510000004007007215102688030b0030720b0034a000641c0e00d035420200040b4544030714405030901016581804640e10402000340e15200c100483e00ca01c61100d0252001a04000400c000340040a04103040310480d42c810300007107061180ca0003a58005840e0170070b0440e802400a0241c50305014101c0245400c0000030b028048190209446215107480440000c0d13032a104400d07514000e028440030b0308504019075040160788080a0b004003010350720b03079501940080010420000e02c000d0b800d0b000d10014003900c442215642003040b02030004044d2030300b2a44a01ca030b00c043c0340d070f14005401d134103100e86440e2001140700c6942c030f803c4e40310503884500c503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 693160611 1250 693159361 693159367
    0x100905060f01030e03040503010c0206010510080603060c0702030703080412051b3d08010e090c0f0402030411061813050408041a0c0d0503071803031209032003040e0c 73
    0x45665045072a001c044401c0c203011034050501c2c150b242c214020365000c1e541650030002c404120b103a0224820f41a9003007111148800e400443c403c84001400b15140b54040c0e104c00c021a01c00902c01000d0001248010201e5218989940d1a880e80b9040750340241c00d41100e600c1c0c400c08110007845010403603201c006100d852944c695000401440c1c04900c8180d0844080c028082003c0c46074180740500103003821921144002d000c00149210400d1040c0c030804462600481c503005c402203014914540d00420340780061843c2e80800c0025070001d00101d4100c1c0d00b41804000f9038540602030170703810503c0c510803c1c109220005004410400c0104101c21918040030003000503001e4060300c1c2942e0f554071081004035010b04000320548a1500c00034020b201d07180c628603480303a103c1c1c020342c810205a60340c1681181c40080c0f81035140918000100483c9424606590700d0515a00480c2d02d04c0c040d150044071070b261000c1c0062142807100c03420300c20b42c0000900703000048980603a0f9030881c1000c0c8510703103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 693161861 1250 693160611 693160621
    0x30c010c1104240e0f0a05010803030408250516080105060a0b0a090911040906060c051002030a09061103040c0e040b0610050702060d1410030809280e100905 69
    0x3258400d10440c4901c40c030b990341c0f040880d08030f00400a0208007000c0600107a0325455800c0c59003022411107800003011691400103007689880d000c4c0078100ea04210003075055849503510065260088501c00e1143d0314025030710340c00d4040030b442e00a480c80c01a00500075404040c150040c40700d120390030400050781003005002260712681880350407100d102044c2da8032803081f8401160280400c0c1c0c440344400341010049404c030035018008000310b0b240c40b42c0c00c2207110ba50b844240c440b00800f5401400d1034100d08042c8507a0a00c0d0740055500000c05a000503141920b80d9030070088071039a900b003103036558000c03040104020235449114054524000004050300d001e41c6c6035802d4000042085019080d48203d80100601803815107a41e03542c0100b0490f11900342c1820040242401d01207280400140e0003c42c0900e12a160840c041d00d401c079403114a0459a542480413034000c400008030071003403071901020243ca1240140e405042000145059400c0c81821980b02440039008401d1142c0384c402400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 693163111 1250 693161861 693161873
    0x1080f030a020a06021b030301140f090402010c020d051e0f2b0c030912050318060a09030f0f02040c0203030f0a0b010801210606082a1c0c09110306030c010c 69
    0x150015801440503a440c02c0c4002ca9a03080d40c0306e207075a2903030b91001000128400186941c0307a603807164152181050380c4148820420310b00303010344019002c1000081010050304001118203000c50290048410307142065441d41102051402e14039401e40103042120700030741080c400325889416801a4594054910252000d8480c040604405120010640d42c04040c017031440c0d800244800400f00001d141c040c200162a0760040343d4a170290068000d44924901d011815160b02c0c55a1b981c07108001429070f0303100c02d80da64192074250b4000c2a13143c40140169201c0c0284074003100c075a8082e50710380c10044003009101601410b070041d25820080c0d010856607011000302c1c1161210182403007960300010000b02c962884070409409507082030408109144000b61902500328994811100e0b0150100c9030740d482803030f24040c140d001600446140141e0b800d001d0003241640540c0d040d0700001d503200510b00c12140040a0005201c20110401480d0328041c01071443c80803080c201050403103a5541c40c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 693164361 1250 693163111 693163123
    0xc0810050609010c050c0901121202010510051c020d050703020907090810021b0d0e011202090a090504030519080103150507120c21050103060506033c011401080f030a02 74
    0x145041015044100c018004c0c00c01c0004100e00007d00f6070905541c6900150426032092079043d03404410003642080c40b24814031415108041c8401100c0b0598140820003840840d5200c080000c0c03d161000307480036035180b2440f094441e100e400148955403451043c008032031f2000745160b090040c4d98030b0400000c04007040e080e400000005006958007691501c94045c0e1110b41d02c5841c66228190903d040c0540110038043c03c10300907200d641c10260141e4002d016441024000c58000d203803c0400c205413409038000c1134006200e400c001d0304001f403558a071001000701484880000301ca4600410a110802d18070014941c2100c605001c2403600d4103020740307000400024807680565404000a07d41d1044010184214004140009908140c441c002c0580310a00060350107a1500d80403035602d20780001d4910406080382c4060a108090001d007039002c1c102c08451000d001c80c800504074190000b0b124040078424580c020988030f50401c510140740c080120801080c076401040710650301ca80004131 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 693165467 1106 693164361 693164377
    0x51522060e0105060f0d060b0424090513030e09250201050603071e120303020f37021f140c0d11310f090c08100506 51
    0x10401445500149194019003806c2d012000030700300d0300092484000288005000074464180030454a002c107010400d10316108802e2103034008034454a9000f100024080103e000c3c1a0342c040c2081c80f6041c0342c0c1c2e00c42c07900040003a42414084111a03401340d0080b854851841c3c00c1c00c4080d02038481540c0c0c540c401d004540340412100740d99444414090f03580c00b07401c0d000c10b00d050030003811180c540300242c003015002c02040215501d031300010100b4020750741c6018000315980301140400c3c00010200e000401800c07102d1401d8560000e80a4400004100700e003070354080684200b001000d480d045061040480401c00006503041d00c080c15104546c0b450a2000172003e40140d50f071481410480e00c1521492250252401d50203004443d0015562000381c01042e10303603805900030189076000403203040c3c40360fa030303121000d130302c0681607030400c0403110010200d40c05c06001445901590308 = true := by decide +kernel

theorem cover : BRFrame.Cov 692985611 693165467 := by
  have h0 := BRFrame.cov_init 692985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 692985611 ≤ n) (h2 : n < 693165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
