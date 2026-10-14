-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1556
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:33:36.930381+00:00
-- url     : https://prove2.me/submissions/51cb249b-e750-48fd-93a3-e02f39ae4e72

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 279676258 ≤ n < 279856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 279677508 1250 279676258 279676301
    0x60801120b070f180b0910050f16031202030a0b03070b040b180f0d050d0807051c0507170a06140315011a0c07031109070e01051c14100612 61
    0x220740c220f00d508080b108100d50045102503e060703a44035080140071380b0754110760f26019101403141c0038412142c2041800018428680f04600010031100c4030008507210400b041030700e1805490440d13610040446607480402001440e02e030661141d40340607412800c40e01190b655006c40b00070341c0700741d0040e4400142d050282004000f403c540a00300d02c000240b1b4502d441020b40041254900000b01c140c906601650740040d00c2900904500e4001d10245001460070070f2620048020518811a00c0c07100c036582c80002da0f0036407280404414651285056001c2420b000412201404e02c0d405207460010b40b00d40e0040c4549000544d2910049200000010581c030b00400c49200b50001501000450020802482c0b800e90a100840186204403016001c4600000510042600c000c00020030310800405401075a80c120040d00c51a100180c90011042108100031000d030143c0d48691203814450024807158800b030203160401c0e030711b0f180c2ea40e00d1a00c4904a6140964240c0098400a40704104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 279678758 1250 279677508 279677521
    0x14032a0112060e070e01090f15080403171503010b040204030c03080f07050a06050a060503060f0f0603071e1508010b0a1419020a020906030d1d190f060801120b 70
    0x185540504000d81d00064150703039000b580055120840350400054291450495690307000300007800500100303905407503c1c504201c002d00100d01d101c040136082c007900700e0004007003501c1410001801e010000b0031511a0030600c80070501101c5102e80d4030700c071307500300080c803141401d0501c262000ca9410200407902245551202c0c0c19582c060441c110304403400b04440d2011503020400450420710407000003a940c541001c0040450f0001e41015203c0c1e0004003e012220600c85000d540000c4a480488000c0c6c5503000024a810041e6110400407a071480c00307103030800456000f002c11151010b40300c1c1040d4815141c00c55158030b00b40500c035000d082c10300a03848000d00c616030700300301850807140c42450b00048043c0078504040312020800142d00c40210034046080010f4101e400032000d5008110500b442c1401403d403d03814070110034010380088002c442581d0b45203444400c800c00b0318141014584400724408110001d0140c0c10115400c040001404514040718482c0b26030000480002a00c2c0c81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 279680008 1250 279678758 279678767
    0x10e0c0609040b2d010c020904030e01180f0f05010305010b040e130204090f05010c05180405060a0302090106090905060a1d10080607090305190302061303050c030414032a01 76
    0x2110076541003036580388503100a4960002c904006a4064103a1908510349000c1c40f989441c24050181040680310700a00103031200c001e280e8110b17a060401000003000e40300102c038000e074111003083c107402c3d040d040000c0402030342941005459000c071b00e07075010548032801501a00e0081c41212a070240c2000101318594005513841e42280000c82d02005d601550340008041d0340c85018250343e001d079645004000c12509104111001c2c01501380203040441e0510fa04030080440280320b4002c2d925200003503011381d40c17481c1c0f040103154000c080d200196140e51008144410300d018240d1441d1508021920300c0c80c0c0849400200d419030044240d10004120f00100c8001010784003c0d2000c8004c0030105010301d09010142c1f040700c0b20341d202e803061441c5042151404451011201030250244103160100781d0102d980c0d039002150707000c250303400d0001d45403c44942c0705864141a1074040072a010403240000700d100750b000d6204504039a034100000c058070011402c9040d20321a0030740900114201940103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 279681258 1250 279680008 279680017
    0x608120a090b03101e06080a0c020102070b090a050610030b0a0b0301090f2604120206071a07032a090504110903010908030414030307080604021803160e09010e0c06 72
    0x5514201c0441603407a24680380680040d200d1498a0b07030485020302581e4000c11000b40b07044410944083c0c2070b0320700075028010040103865800213903220000480c03000d0007501110344055001d070b181c5980b4901010116190000e0040842c1e09003d20307404036681d1404648040c00303403600045d508140c0d480e040102e100074581c0c00c24858040d529201c1400115103800621200700740144060415a0034112848a80c8003c000340f228294805000c00e0141e44640001428510b41c10f840703580e44e034850340c1001c0c1c1e82c0010514125041100840812402c0c642c141c0010007244802c550070039800d021a8490080101040042d20010b55003080c1004185030981000c2003501a100e18a4540740c0c4040110b820b5035510003041d618840300000348810001c00240340c40700e0028683c040c40c10350808480060103482d02400a51080c0c6e004a03902d0044400160b1500c4c1c0e2440081c01c0380c001c1101e02104106230320003440b4080500d610940064500f003018041d0075500c0d0055005030010b40f000380e00b0001903400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 279682508 1250 279681258 279681277
    0x112709070203191115070216060e0d03140f04140f0102060a0b120a110909030f04032d050a020111060702070611100c050301170c0f01121103011710060812 68
    0x501010001e5030100c00d102c2180c0342c02812601d52821b01c0c26001c0a4a06225660000c1900307165001c1000701a9004204114545c1c0071109030703400015a040c222401c0202c014940c1c3e4200c0c0000300700a40c900304400034021501c48540f04202144074200300076401030000c1003103015070060030001d180c1101c258803032055076130b0052920112890f00c040c1c0390b00d099010f0708101c0e06c00001142c1c5035900d180240c41a80d000000000840c500b1b2140e903040062400780d44002401c015100b0450039002c40110044602c0d14420482c8e0940b004c250f0070869074a1b81600d0080c5e02040540c0200314409101050170b9200310705a07002001020f19154080341d440080c481d40c50014019800500320a071114011955400c40550b51a0703140d50601443c0644010300340605005a48800c3d0078046944840c8140d0b0528003090030f140c0c43e240ca1141c00400a010240410008440300000115503c4d240c0d6400c14042428101254102d0b40a0800c0d4012250240180001c40d408028158460781040b0001c140340c81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 279683758 1250 279682508 279682517
    0x12170c01090b130302011512080c0102041806032a140f060c010c081602150402030c18070e090103020a050d02012c010f020d120f11270907020319 64
    0x60315101d030031146030142c661000d4006124409428036509021f031022006108080c0100c041c42c0401c1d0602d100240c0c140280018408500110600402e40c103030340082038500d5003c101c0440031b51f12203000b08414001291000000e25460015644070402070b0602e0b40555080b00d10b0505102060200190702c604003a844070a0503085120350703c958005d040d00c0200301c1c00200b0010503030880a00a19001091b4408691000500c64241e540c0003480090943c02007450600f640c80c0c0d400481c6c00d16400d42c40c0f80ea00828400081044118032841c0f2074455546070b030b00c0c08100038628040103544030080c0303c0603500040d81803003841030340f4080c039021070064414108102c071309644039100220310843cac0000403418400704603000200d50300180d00140c012031030301c00340227140d02c1028003070311001c4621080e86007c1d03615180d03000c0c2c0c41e890381c1c000c580080440542c0c0d925014003103c9003c281c540c001c8115504801c1149212041c200800c55031f020703101c990013650a00500d034841900b10000c20740c0c14030800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 279685008 1250 279683758 279683771
    0x2070c09020d0c0215040209060a0e040b1006020106030201020604020402031e10081605180402030f0708030d0c03060608010605160b07020f010b0a080a0206180901080a030912170c01 80
    0x186541500002024000d4016032204104a070400842d0f030240030742c005640000da0b0000b45203880041c042c1e031041d81140c602c0c0e400d456540111300414200c2e0811204070301c1c1807052009000c01803200394401e019444222030030342e859036004c0342030b120a8440240540d025001013001450f02d50051588070080d00c48005004140b0b072850414000b050b1840815140c02580c24000d611b0b0502001c40760b00a104040c3c90400e00e40300c081102d01400044000c2d0245088000c2000c654050001d020380b0080a400c5035049522039801640326441110041c038007071324042884100500034001c10080312600d88418560743e1071304005441035407240c03202c1d07503420200141540000b41900c40c40360103003560354000c011028140f03841c0f5084810340000d144c8641c08c4a49d0400201b4000105480195415141981c03124003210b4254029041c500301075034080d4104001140c84000040e01b1060349010b035841c140900d80e64001c0b02203202400c040602903e4804101009000010300240041c034101760002640303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 279686258 1250 279685008 279685013
    0x6040b0a030b0f01060309110105030a0b03030406110717030a050c0f0312060f030a02090105010f030e0708030a021b0a030210050c12031602060108060a0c091806030b1305150a0207 79
    0x300c149400032118001c921041c041e0783c20b60007903001d016140d00e003010480c07a042030b2110303110309100b07801542c1000b10010004582040540245102c0e020150882c0d460b25200d29010f4081c010300c80c603160b1140b0580b103000808038000c5030303002045158900518504040640b003110654801079810701c00307100fa42c6400d40402d408000900c2d040015a003654103a08000042106850034420b915210b40d2150b103600e40581c0c3d40c4910641181e209007841c842c0500c110b54250003038805010000014058400000b8046034040014400c0c20a96820740f554500042030790042401d0300c05519800c40384040062005042c003080c4441110414201070f4100b4000c0002030f49802081e00040c1c40c1240e001c000d0140741045507424162a0125001030310456040c0044c9598400000b8121049951030700781201c00e081c020005a0f000c1d012000d40601e6401b401c81c1484040c1c001c1e40710452308903030348000041d802c8840010a101c07290780031000d0720130f551281e50b59289101000e00302064403030382007014000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 279687508 1250 279686258 279686269
    0x120e040203150d0314030406050a0b040219051602030109050c0306131208060a170106060e15030a11071416060e0913060b10020a021008100905070201020f0a050910020705060f0306040b 81
    0x32030380c444e48d8080303a503182442d600800d42e0285070a0034092401030103031010381e070030450500c1780c90901c9150084c1c40c0c0e490a504d88118024507c001380d019441c101400c0c05204000c10030950900301a0212030780c0b80c039060443d80380071150480140c1081003400c82c85140c6449401e60940014000700b600081984034104d090f41c0a074001850410b60f0340d941070401030603802c900c0603c52604121500c44101012030300303e440501c070051140c80005e503500422a208820b0300250f1f6401034101616402c081c1884184035a5140b600307042c10070b482c0d0a10300018540c2d210301c840c0c1926810180002c0000d485d5400809c1d00c103482000200c0e0f00644540c6028070070f0b00d980c1e0740c0b8100d0441590040444046a0040c400004450740d0807008000d004810054015030b410402c0d0300b100c60044001035240e03540e410880c0240602c6112048280d0000350480c0c1c015072200140c00c0210b001c490001078050829010780c2d41e1011803081540109050100c3c40d40454801e0185904c400041c20100348980c0300c070005035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 279688758 1250 279687508 279687511
    0xf0312050f090c12030d020706020409020301030507061e1205070225170c0a050d1103030307120c0314070e031e0114090a030e10030b0904120e040203150d031403 71
    0x101114000042200e0b029003004209140002030f6031803a00c074034020341015101d1150b034410200481d0001445400c000307940d0704403001411750110854070f0356128076160b42c403010148030301000502490036056071160307481c1480203000743c5034803020b20307814150711440301820300240088154003900942d10a150010190390361442c00481401c0720302810951400e0008212070b15140341c6c1d0303010380958002078560b0703419502a03810458440c01320048511345240e523980c24a540c2c0c0e4041c0004000e01040d107400c41c500c0600d84500c200c0900600c046040200c1c100c80100d41d11240d24071184c004104680c0c01001e099203040e1000e41580c400101802419600c1901c0c00c10b0440f481c0c0d0344000c0000b180b000640f1094100e44820090100e580c09520000d1010000d245410b2185464000881045020f54000b0744040000f40000c1a10303e06400e11548070f513403010210001c6010408890350529161084078400c1c0c0301c90b46050382600040d01030140300111084120280311428500b010080308040246 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 279690008 1250 279688758 279688771
    0xd020714030a034e14150619090501110303090604062403140120070b070509120d081e0c0307020a15060303140f1210050406230108010e040f031205 65
    0x56005402900c40c810020010102c4040894038010380740d580c0c102c4400350305070419906c803446070444401e040014064428101c2c1035205485079a800401c0c0c1e0341003842c80080340c0c0d00341ca88041e0f05005502441e240e200032101c040c01134004000040002d00036034003050382c44110000c00c0c0316500d1015402c034000f440c41d4000b070314071003130203111112400c209006411180c44408440d01c00c1074100c03810b00c001030244503c024004807002c0300203041548030b070301a0f428052004048000343c0300c02d0b6410fa40c903040401c80400000301564000383d5001c0c2c4441403003103049400d80c0f5040301030b51540c1c0041c07040c1c3c201601c0942180120f00214001c16100c00903121300c1d05010030009640c030310f50b240182a10540340d010500b042404d00610800340c04180c203841810055107002c440950b11146101310500b202d030442c3c3e501500d081c0e07000c5a048645032000f882a40442400f54010b5104001503404a209105041580c1c800c10005400142403e500100b802d10905164056002402d030f02c0c02a250219003c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 279691258 1250 279690008 279690107
    0x1218030c0c091003030206010e06042a1701060203090d08070506010e0907050a06050307120b1c0b0604090804060f020a08030c25020105031303090b0c0d020714030a03 73
    0x180780c140c40e00089082d0808581c100f00c14909103544e80c040c1d29424148070303d401100c14040001c180c2e880b83e81007100c4003194445055101018840101c6010484207180c1c00001c10005400500001811550f03060381c071603070000e5081c101c08100300b0181c034840c00c20455401c4021301461300080d070300300070503406404030080c1004075260065030300b0f00e040500e03400a44280400e1608000f030f10f81002c02c5a8100d80640343c034000c81c0100319982d00180c000780071015040308910702082c6402e07000c00d40000c0c0e42ca20032240e80e0030300e454140401040e0303400780d103028003464003c020803c08940115019551207101e8015a81d0b5542c071612085140d030402c60b02d0840e8400e000446004012980e606515441005941e5112450450300003c103280001000800d43c2c0004610b65000e0501071071500b0000c001880a0503075403c24003603007035100d03481d01140c40098401c0c645c0c0801c001020210494074007001800038040c0248580741119a458980c00b4005d00c1414540031544d0500c13014520060880f080300e6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 279692508 1250 279691258 279691273
    0x150409060f091401050c030403080603030c0616030c080103020f060309190309030c0504150b0d0204170a0b0f010b071509080a0309121107030f020f03070603060510090b1218030c 78
    0x406842111000f450382d0a80c0c0d140c003003000503403041d80080c0e0740c12a405151071a015511500400e156100d00c0740356180f035206041c208040720034000365004588010742d4051003040004042640c2d152001e000095002d4800c403619996414010041c0d0340c0115000304403880200b0f00708040c0c03040c80319400700750006108a83c0602c2802561421000148002e0f034080141400703c80318007184084501540548410008100b2810308254060750090602c400c2007040a00f082400309035294103064080b1964180000002c0c0140c401c5002c00b030480341c48103010351230a0392690310416000120300c1514000c0f9034540214000c22020381c064070380000661000501000d0504200924250a00c400020000030000c0200d018002040c11000c40f80d03c0304039121140d00d60f00c006a141c1e521840d029800d445650400288030740d064100e0350440384243c1c0c0035a09040700306030854410071103005003c0a554100a2120b50306001c00c0c100d64000d0051003030040096046214a007140d100b00052621a402001b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 279693758 1250 279692508 279692513
    0x6040b031b0426120c03030402041e0204090b040501090203130303270b07090e0606070602031308031905060607030915020f0706050912150705030c0f0f220509150409060f09 76
    0x24000d00440d159441350401003160301d030580c0e0f440007d100a0046071202810384000b00f901c64032026114101c0400d549642d180c281d003800400c000480d05124a091400004100425101300c81c016460007110726809252030714103901800b40001c04d104002c400c4010f81c6440407c01c410391081c01e100e044407000c00d00f0090030040038039100d031700050030600c84503082c800c0c1c554036581120440b0b540950090703284d03556550001802c0404a00103003c00c440081080098001b0044000056407034400422003511103100340100c0e809803c00c0100403410118051242c400030450700c0f08103000074411580b4003007207148140e0030a241d55103c1008610301080030703600f0b45840d00c840306001381c40c41c000301041c002405030046c0d101800b030120000c1c4a00007000c10b11002d0200101c0c1c81517521b00110980c5c404122503c07020303a904c150034610b00c00607020b14088081c01c1140611044400050014840791541c1070028509050141c000358031a41d500d4000e4002191030090400c22220301a000600740e0050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 279695008 1250 279693758 279693763
    0x123120f090c0a1e080703030309020102100203060a0b030406090516061413060f140a0e040c030902210a050f0601050111070e13080d02030a0c0e06040b031b0426 71
    0x740003075100d90402c44039001c582e10364140c04000c9420301242d40c4000056100e0b8881c01a0301504074266502403120044145509070300000d03002c1c0e00c03e9013281d84810003240740c42d00b00c0c001582c0240d0f00ca22034040c1000340131031801c05141c015001d1400001c024009503229440c0035003285450840324210101002115045028124500c080d0700296140100c41002039900c001180521320510886214510b45180306969511048024034045940c8103085c00c4007410500c41d03406103e22803820107620300f064074881c0c002c2d11642903000c0e01e03000c1d0751405000e04109003c14144446014411800b2200100f0000c2001c5000c0c0c1140e81c2c080e0880b54100320005143c9060001913030000d0340090b004000c801404828079510426007030540d61038513074a10740b0100c41d2040c600b56203403c44c00171051044801003a4403980c186000ea403592103c000f03560003808664022403040000b0307103c0510011302c4940c0b03c107068001c04030b000140c0500d010740b07550030503513401c402c908841d844000b0a8500d1080c00e81c01c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 279696258 1250 279695008 279695011
    0xe0603130c05041a060d090516030537020102030d111902062e0308030106050c010e0d020d080a020415020303090c04090c05060a020a0501021b0c0f0f0123120f 70
    0x2e803010b100e1382e00060b242d1070140d60020304003801420001151014260b441d8800108950302805803100c000c4486403900342410315001c240d0b000c0c001d00c0280300c91805035091345001407071400074500100d0314002414887c1200600181d040d40030800c03000702404000c0c41000e00440300c1e85403041c1c42e40c07100c525408102002000040c01d40d40701000707100b2155840c0003260440ba0203030401c48118a081c2e031204080d8052540300070000c43d004000492040e07003140280100000401c020130608880303848003503139980c5140100000d600036000034080544500032080d071006145401524107a6541441040903004500c020016040030042c17202175001808a48495102210144003522035a01e40351003c05081c821184190703000100c4c80b50b07460091001c80c00c410b400c90000c540302e07000d402044000071351410003401540030b1100708032602d2800a0036402585405414035101225070801034071311866011100c8658219882d802000180a4004050a0003e500c1148c8241081c0e80c044154010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 279697508 1250 279696258 279696269
    0xb0a05160e0d060b12010e0c04050c1e040302150405030609060105060a1101020f07060207053702040b0901140a0501051201060f0908070f050f03030c0a030302130504090503040501080f01060206160e0603130c 91
    0x8280510502686880c144c410183310f07001c540e5414011003540340c009200e154002034125120800c001d01098095010b041110025019100c00741e85001425840303103401d00460b43d10003800d1020b10070703240c4202c0c42200f0801c084000103190003c0a410b08a542d040308800b00c0d41141c000a88804114050061001c1e2aa0050701e07811303200000e00e517554040080740280400f030f40340b095100c406e5503559080341e42050f0014092404c156161032501c141c003254003202c90700800e580700b130000392940710344200ca066032001040b40c0d80903402c01c1c0c01180c520050084110070044008004141c1e40c400f8009200206918542c0c100520b01e01130520800a091218091080d001841241c1d110503000c641c110342c0a0349468016511420744840701e0510340260042c58005140011600802000100400c29114262144034141da941d201110005909014100041e0082c0c1c0c0810b80e22410020b46041100380d90504880d0440308202081640c0c10840302601080b5424a48005024800003903201911 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 279698758 1250 279697508 279697511
    0x110610030611040b070f1e111f090302100c050f0d080c0403030507151508010f0b0604030320101e0e06061c17070b0a05160e0d060b12010e0c04 63
    0x92504034081c1140c018118042c000d00140c3c0450002c1254014100c3d00c03071240c18800415940c454100b46c03c5410304031231413902840d40c070b6000b81c40281036494800c0341010240d0b0303840314950959003804210350038180c003402807181d0142c0082c0000c505100031310b54003400e24014082d8040020b001064100060429403441004000500200c0d43c403604981426821a0040b10100451120307a4010041603404d6840c00c03100d007101007031002064020902c48504218180001600c4904204051042d480000d020620700500750500308401000303510744142c943c1c2a82d1f031002410240205813001ca01091081e491030840031001044940b00e0fa114180b039650040c0560320303140300402c5045106131028801c90440081d010100100080982c1417019000f24107900e0309410719151660040507180c1c441c0f100c0c104000581e880b0701003005e800c0c4070031160b6120b030301c10f08100c0203001014601c840161407064480d458500203031100f00c08600605107000000a4000301c8007070741810304c0141c3d400984104e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 279700008 1250 279698758 279698767
    0xd03050c0607090f092c0114060f06090114071a01061e0206010b07020303190822020a0e06030c09101701020f09011103120408040e09060f0c0307110610030611 70
    0x500c4861184405d03503034103000006111100701110817102c00c4010f01881d540300c600820800c99141904001000220100b41c500143c85034410010751039000071440750400d0042c0540821907100b20081c0000450004880d450807205459115030641c070b17483c031403c0f03401c11400100920b03940036003006440603a004141c3c0b819102c10000a445100610403d03110800205516040d50b074140200c0d1002c1e2004144038900018002c07001e4440b9900300d80c28840381e42049a14010301042c034240c03102c8a40d0040c5204a5a4200a1100400c1c0005007941c0e41500c42c1d54860851512400300460003a000007000104952904604000071800340e91002003d03401408690401e40d400010703214141c0c42424806034640b030b80e0400301d14501642c1c12a5011018150901080c050204c0041080d40c102c1c0e0300c441380035070324110b1090f603030702e41500d100e0000a510400502000701c0386024580248451500b00580e507903c5103030320302d1b011066035003c92200c0692404c00c108140380c0300710103c010341500c110703052 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 279701258 1250 279700008 279700019
    0xb070807020a02040c11010f0501170307050705090c04080105090109140721060e0d050a0f050a02100b0307080307060b0a0501080c040e0a180f0b0604050105060d090804050d03050c060709 82
    0x200c865070b10380207000c0c0f40c55549488282c0e00403051040540d071240c0003000060441031a150281c0001e11030070300c0380812440d00d08000740c4040110f6140c03980000060801d1454541030062049000f0010400c003002440040340200c03084c01110300900482001113254200c50400013a550049440c5c1540d0340c0c041c41080060010909094041260819a00d5000e1005060040160000308104200341c000c3e90780342e031503440d002030103000714600990325003a609150b08001d581c144201c0b050500540d1001c0316030b900b2590960040e44000f071024064412859039515000d203960401c0e10b0484507140c40d2100007030681000688180240000d1030b02113668100005001202e1089000d05640f01d5840c400060195407240c11400c80149290301c14082000342d401c008481c1c1c083c1c00f4040315002070610200d5003c0c07816000e1641038a030000d06491801c0582d1012000800c1c58400440e5100b00c14080060700e99a400701c40070390a8001d455a5645008508250b0301f4890014150f42c203225407034100b40076 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 279702508 1250 279701258 279701263
    0xf03030c070e0a091205190828110a020703110603040305031501090906060906120b1c0f0f0f12140d090c0b0d02030912070302030d0225050f0c01111504020d0f050a0b07080702 77
    0x201c000f5100e40004844100f41986130250948503124ac070221400602d40090960000c2c406040780d0040402650a804072001c0005030712040d140070300090028800300303031484104030003201d1100050400e017401a40d203c070140d043c0c8900d82e024101040329110308201064101c05209220300d94101c0811001714854000b824892038100c2090300c81d071024001070104207501c000051456001445890102018a01481151a10201200c81e400340301c810065060003040049450580321200c0b030304014a2100c950003c042040c010342e0404180300c800580b14404000402402003404d50260b034914180c0380892402d200c0c90741212015604010103004254040b00350784c0312004030200969a80c141c1200840d1010761028260002040108547c2c01c018000070300d0600c41040c40141d03100340d140c410040d0764002c440880e41160b5088800401c0e007842250b50511391062000f41820400486625404103122005038100c40c80c1d44003100c0780040c45031911446078010b01e0351034201c0c0e5030b1410400094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 279703758 1250 279702508 279702541
    0xf0c030b012606061303050c1804050c01051c0e0c0307050a0f0303030203060f270a0603050709091a09070303030b060708120c09060a0306050f03030c070e0a0912051908 74
    0x104504180b00c04a00540d40c0c01c411582d404150038144c514003500c0c2e04101e92150030700c0b0070b0701c1d200309420507041107852103a000951260350840090040c61400c1e03801940c07035a20444000a0300f407d800c0920420301ca4910035003900d1000c8000070710341c116103903092500d42b0601d90030540c40340403c80000c0044107221190042aa5407626015131691a24008100180964402282e01103580305100710803110012460b00720656240d594845a02ea8002d07113021100e56000142041d0411401407040950903041030b09024401e48001002003142000c12001c0301d0261103000d40c036000190100180742c1c1c10300a42d8000750080351a545011a01d81e9480e185105035045081488404400074103145a20300a8940000002d80829958103c9d0135009006001501580d4410304104002d40a582000425103039005003450040c01d0450074003504003400c0078000c01c1541040c0e2140c1d640c100040c14244505009070040e1101d0b6203491140344102c04240c40084c00404102a14081002c4612244402c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 279705008 1250 279703758 279703817
    0x60324200a02031303120305010504051003060b030307020306010608160302090109031103100510171209010822150e010509030a030213030219030c0803030c030a050603100f0c030b01 80
    0xc0d50745100e5404107a00b14041d5032002c190f07101440301c0c00170a101940c17124244ca04215502081503a803500208001c6400990b00210300742c64034101880050f01540c40368041000040480f4100300c030587c0000d02d062400d03002400014560701c248803205591258000002d6031500781076042020b85000242820003d10000e0031025600404070520b40781401580101c0c4c50480c030074400c40c5000c40e5240c1000e1850f1140d40310203111001001c03000b0601240e406002c880e0540801d1074034008034011102c46401038550300f9440305030b002c1000c1040348000d6104001d84580300c00820928142d0b4108100c40c049000d0601d0b03641000d04210103100040f0032070380402094140103881e41c0c0040c00c03540341c2e80c00c203803c000c0d0003001a901c0c640326041005421000c881c85032034920382c2181c5440410b0785a00096485a0023a0b50520200c0da1000132500500c0d4000303005411503c0324031400310758009951000c0c442c800d0309c0d50740b51481e60740aa854003039081e092601782403c440c2c40715142601c8800320301803c5035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 279706258 1250 279705008 279705071
    0xf0306120209270102090a08010621080c07241704080a05040503030714060c070c27050412030b0d08030a020a030b10030203010f06080c190210060324 66
    0x50b500c50f45400300d50070703140d50f4007505803d80c00e4600041e038001d5010008040c8103e8001c0400103030400140181c03402d40c2c0c3c10382d12004a0040880202ca841107910b102105d0303280c0107002e2845901410040480140090001c0e81c401045900c503441c0d4940307036450f18008110008607210450900b4201080e0000e50100320300d592881019022920ba00440d00000d0f0303d03000004060701403240003140303005c250540106075801c1e1b4032898200d0101c0c2c8100c1038010200d07245410308005d0182c91011030f1006071450205440141400c51094048800840b0225841e1034081c881264490380740c82400700490050ba50b503650031741d184c0c0310300b0b5140c04000c0c21441c100b5000100000241d219401c513910020380a070024512038007242002d80030350024054010380032107420380080c1c00342c03007068042c0c000c40340360100c1440d2104a00350351003816035950156066110f075540d410344112103440340c0002540580580440004402c40ca9050800c5000400c04a20b00b8a11074410305102c0030307410460080141070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 279707508 1250 279706258 279706261
    0x2011209050a0215040f0f0f090b1509061917070203160809040e060112030201050c160201050d0b0a0b0403020f0915190905040b06011b0503040605250c05010f0306120209 75
    0x4901300f68451a00070209043d407a280000d43c0b088411002001d031440b00c42c0004586440b43c0b4400c040310000345440354041010824200ca94010000410243d103000d0002c901c1c042c070002050310b00c032840116200003c0d07031030500f40205006525005400003586d101552808907240100b4986070049680035004000010300541a561581d1003065400f04a005641031981d50310301d0003002c54000750040c0d000d9401d10001030060801d8008a500c0e4813006032528008003001e4004407034941005072011380580d91f03001490090b90351024404010001d44551a503a0307411841409040e2030f00d8001240030310707901c40074071501c0c65030f84130004a49002030f1010f000703a810303913641040540d1883d800000f03420b1920080c4020700040030280b0303115920a03246c032820f1404000e411b51a8162412001c2c007150402e001c180242c2d4400c800400e54040b00d48141c003080c4544000d400b00300005600c0c200c6a4401c5080200075958020344e80010100f0b250608002c0103103070a034000341e40e00c49400c0c0240708017841070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 279708758 1250 279707508 279707539
    0x3030504170f0109031107060c030f030e0c150912010b0604030f0203100c180608060306070f03110c03070b0709030507050919020a0e090a0606050d0905010b061602011209050a02 78
    0x4103544010b96910020310003407400c0d04000d8007600a8456003070312400f80e21400308a09010f150681030559159440d0041c00d140008100d00904001040003c4e0f8080d841c0312840c035540d15112700e0710958800039026500c0b4021000c02440003940e1001e007100741d04240e4403020f00d075210000c0e41c0880750068500714000d900761001a0a00e2a0000304c0d404882c031707001c5080c44269101e9000fa007032041014060100c55200c07141078800401c219071040e41a071084d00011403807845800409001c01f40d508001c41d42046101035401e9580100300648115480420b6880c2031140c3d030458503400ca521810800849130035600d4854032480036028031802042c0410100b60008005109007030220b680e40303411500c3c0c00d8803040013004220068040351040b0f141c480800e107200301e01e02c20b08040b9682c6413145c61820b003141c071210307000d0040d502066555542c1c40d400c080c1c4644900004012081d105000c51100120350f2001500c49617920151000e0b061800a00700300095001521220258048036503440065089 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 279710008 1250 279708758 279708763
    0xb0a0302090a09050601050111030a0f140f071109010f1211150c01110306060702090414070807090e070b03040f020409051218040207021c03030e011e14010303050417 73
    0x55200a400032554010000580040c1c3c3c0250070040c803803401c3e601180d030307150011280214003080c11f4503c1c0c1c10401402c00c56500500a0701c034a0700c028245030300f0f9034010005e410f01a40240c0003900e0440c1d0001050300402070040d2042c0608442100c1851142d410b0011001031000140188044124840541000d10a00302c4e8002e6035100d00412404100090811039030075500009040d01441d8280b1248848400006066a01c10080604070505055040d020820308202c007034001d9849010610128080740028002c0402605400e0010303c4000d2604401c1c1c0215025400c0800c0203400059042c8001074411040343d400a81016a4031010341050001500178a040070000f00307103102c0c80c1d90351110014400043c0c840107403030002c14803580b41c141c0c0501090348034451000358050101030000d0300400e20011444612030107403400250074446180e81c1421640e4031103800c00164110f40080d140141c00d40034444d041440403400c10681d524550300030b01503000f18002c6102d1900d9a1142c400f00ba40d04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 279711258 1250 279710008 279710029
    0x10e0610181e06030302010c02060c031f05060f07030206010f03020a0e06011214070e09060a03020d050a06020c070f090c0e0f041112040204110c060103110a03060c020d080a0606120b 80
    0x401c8042d00710039801010401090341c1e00c022005542005032003402c582c008a0303818482c4402004e40c521b142e0303820582641c11804902e16012910041134003080075100d000281055034511009681e8500701810040d14180c0140d000744001105080c0500050300c035400b07a6400c64614039009991526a940140da501940300700812000d0300c0c00368400189101c400e0b0950080c4074179100c07401628050014881c14840443d8126084140302204100508205d5080c3c6511805001611982c030402e941e0201aa40b160b1188035541d07002d98402c0c001180d80380790500040059400c100580c240404c00500ba4003010070107648540351000815006891b1604080ca9141d0503151040c2d45207084030201c0400f030b03c10383d030503405107190101204840b050807040307850b8010300750014800d0b80e2840da0307850403940c100f001e02500b21403132407800000070b212030240c0d4000483c144c025040d04d61a141009050300c2d401060f105959040c8101002500d4000e5584c080e503001240011558a03007050205105a09 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 279712508 1250 279711258 279711281
    0xa0204051506030a0c0f020d0219060b0d050d0930052e05010605120c09010302070b01060804200f010806030a12020303040519081b070503010501080f010e061018 71
    0x40000030442600b00a92100800c5e103070030b454454040003440400c0b80c0c0c42c4118004400075921100743d040c411342030400c1190843e07200301008101042072402054112408100c101e070350b41d000008211850781c0142a440107030403070260307010600e501619205020181c8070851402c2d6000c0b10b04420030b120041c012601c1130141005092250b0111803141848902283d04007084540380100100b00588a9800c0383da40301e03c01c001c096419100c90307002048907032020540b14103159013048140c00007020308030345070300901081e12018414501414640500030351501c0c0c200e084005801040d1103a41d8070107003222028001e00e00900c203503840d5004a89003900045024002202c0340d031000c00b010b5400002507208a200d842520304500b40b40c408000000c0c0da0101c010540c8000344800c1ca442088560208104003240c070446001c40d503500302007030840388213070864203498200003401e01c070300c00c400d00508241c040c0b0305008050720b213021601050324590303900480c108442c2443c6400308000c00c07074201141111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 279713758 1250 279712508 279712519
    0x8090a030b0c07140706140f190906031a0603220501020d0b18010f210c031b0b0f0f0a022406040e010203060109150315120c0e090a02040515 62
    0x5000c00e40040719004418110b411000074103100d01c502e4000700300c800484409840c0e02404250041030203016070440360314092440014442741145503886140c43d2800792081d00c40b142c0160a1403001002d441f200c49205d452071100c01c100c0f202030740f981e0702129841182e400b4200c3c581d0200105070800215104405412980086480f494106040e40320040148044845403003242c40c5031000d00008400b4410178403a0301c00c051041099195280c40c24520500d040882e450419495072850a1614030b900240c0f40c01c4080300a04040452050410002d07095000c1a031f410503a00c94110030080c419481002007801010941400150080010035040c620540c048000c8481d000c01c140004c50b01100c2191095040c00340c0703804041c106200b164019801a5900400326003400d44000c43c91001410b000101a51a6800f2103048048080704001c1c044005d11000c0c0e01201d8100a540d141107900040c0d0000e0100c018041072400004603902c00d25411340340429180e0321400c4602507400c00a20040c2c014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 279715008 1250 279713758 279713761
    0x601030212190617060a09021c0302010b0f030f0c04020901140f0c19050a021207090c0206100b03011211030307020a15090f12081c090f030906050f0708090a030b 71
    0x60b04081110003601c0b152140800605503101c04c81e502c44400c0b10102c0da440d801241c045605410b194003c000b0490000d407095608110400001010030488641900141d64505000070a45031003a03004410290840007001090000c0e0000c87e12609510038040c0314a50001b40450145d00602c07445803001e604803002500c48140302c0940919901c00c0703802c0c0601d0301600e031844025a295849600e40b40741c01200074070201c021507082c4450703034140b40340101d654032816000040c0c090b0039004842c1024115030140c007090412900e981500d0600741c104000510381800184443c40c6002c141c4c005954020300202030011b86200400d0451082200c060340005105901240201c40c0004000040b04c896503140281a80c44880750204116805034084401d0418108000b0440800103000d83c03440300c444a400c1400085981c4040710080d0100700c440500354000c160070701d074002d08020000e01c00350900d02d180051079182c4000d01c1c455800002e1aa480c0801e011300c2c0303602e8941c07a9030099075016043ea0700303e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 279716258 1250 279715008 279715021
    0x4020708070b010603091e0327050a08070b0901080705090a0e18390a0f030b0115081305030c010c03020c010b0d0203030910021c03090605061f080601030212 69
    0x81e8400403080e81c1c1e02c2409000002d00c41d200e48035082549070403503200a084004902c0500040d40300704c400f6010801b801400c107684091400e140c40d0201c0c242550003801c00d140c401488a181d10b1980a00da4a40105404104481d003440c115541e0341000d01c2c00301019920098180c0c1c0d5030080e10350740da030004040c0c800070403045070105000d80078069000c0d4a64507213445031625a034440c4030500010807040c00e00070f0b400c3d417443c0240d20800030741203101058a96480840100f10714280b1948043c1101161040c1041400640000d90f80508180f800c034400000d449600900f039000040c3c1700c0e8045807511003000042c0b02d010300c20f0f01d000000d404024040750f0030f109070040c00394218030780304102c07546000030030407a51904480c400c0015502078003a5007880300943c200051100d010710120203600908001c1054510225900044400241c80008046c041d6050540480d02c0081296004000440751183d05030f1090181101007442840c00c901141ea031040101c01a02412035840620014881803021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 279717508 1250 279716258 279716273
    0x70507060806040c090902130e0a1413051203040f06020c010501030501060503010e280c061706150d090501021b0120040f0314010227030708070501200a02040207 71
    0x100e03981907461940a032200410403040343c3c800b480c0702c0b0100c3c240181c20000c0c16095005820f020707001d00b5841e10503035903403c00000016004c0303e031a1112540c801000f60320400d441d030305a41080302d0102e140d84464080c1c0d038150743e9403e03101018030384101c0400000c04000415100030000c2d0b80c8510151745500b1400d01c203e010740000e000846140d4204000800d4a0405108154000e030900b0001c3c07280c8036401995481408000105d003484040c20076048000c01c502407036510044c455592140214400c00c0301ca0550b08030090403082c0300d010aa034070329003a0311a500940d9004070b00014005a450068034107a0300a11071110000d42c3d00301c0c1c801d8208082c4a042d0301500c032403030b0800f83e0400031071210800c054081c4201e026100a0300795140044c03011802c480100340c3c44050880005141c5008004a500c45448603c180004140b01c0d002c90b076003504040c010701d001013088400070001c003420000081d08100b01c00a000d40b056680d200c4002003c0d804000100031990054411503940420741003445 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 279718758 1250 279717508 279717523
    0x50a0f0216020a05220e0a1b06090504020f071103010e070f080609121b070305070e180d020d0c1a010b07030906050a02190f0212060a06090203061c05030f0705 70
    0x284101e20302c0d2000a024105412a00055841c0b00c0200350205d21640442009001c3c0440314035086c0f0600440748001b910040b80507005650340402c7c002e00341d10380140280381c40c1c5550052400750b4014030111003090950003e0f1000d01e40d01012280200f8034078000720780101894903035100284a207001c0040c400a8030480700301507500c0001551419070701e1000303c641d66040d1208a0503101c0c41041080000c0816140c0001030094842c1500e00f481d580342c45144c94501c0e03e03003205144180300300a00010301c10907201982150f105030080c00300c0207020800a901c178040203011000340110301c01c5100c1081001c5045a4400084010b0310080e541c5070100251650091402107003c44d0441c01c0200f1240c1c0284152072012040d640104141241c0e5011540900340c0c40314110340031132480008900603a50b403e5248404051134001f08003610b451511031055841d65809864800d2041007840a161102c3c0c0600c001c410020321000c0400b0510315003907203140720703514515501c40c5000c102c840810901081c44c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 279720008 1250 279718758 279718763
    0xf091003060501030c030513120212191d0d0213020f07080307030c020609250504021b0705010c030c0803060a08030d29010c03030e01150803030103121e03050a0f0216 73
    0x4200402c034103d030507801c0310300a442d1224661a1803000c01c0000d000c005000703d20680510555010320701220352990a9080000c8002400030207043303c0b00f401d80d010380301e800c141643c40c0d8040094000d031400310fa040c0e07a0b1140040d0081440d9641000c4860041d0100d0b03411407081c3d07040550f155981e0400c030955400a9883c040080d05081c604d00b440d920003d180e502446600f00a41119a4050429002c216000a51a280c49608040000c40d6a1248060b00a4242800c0c000c1d1116040381c00ea2400c0078070580080c0c2c184803061124002207270380034100c04241a0700540ca25604c3c0c0761503000801c40d00e034036440f400d05407000181c0001c231a07a0a42001800d01000340c3c228804c4443e42e814101c444406090507400030b17201c00d000c080030034400d030846620328130746000008640c0d45407088a0031400868015652503440000104200008890007013a0300c41c1920b46491144a41400c15509940d102d00000c20142c0320004200e5050450303001151210456030700b156152079001241103c01540701c4107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 279721258 1250 279720008 279720011
    0x160b010e1b0a080709030f1112070803181c031e02030405060901052107020703050f0d021f180f02010210092112050a020306270604020f09100306050103 67
    0x1240c07148403060000d039105044841c0c254140039400c802103500800007490f90040042c022000804602000900b1341810701810b041c000e04030a0006100c41d6100c0f00c00c000049500004007000704140c0801920020043c60802c1a00207501100045500000386407042840300310504c1d9000700350700404524818043c0c0d0b083c409000701c40340e10581c0c0320b000b9882019000a0100207504580d0b218200900002040c6801e10720310007200800c1d8007180101300e5080c0051303448071109009000c400c000c50021440260010f21100ca0300c61802034541501088459000d2045403107a14844a40d4101207003505400a0342a104107083c14001682c2d18281001e9002d0b008590308501d000707205006102c601c0350040500444922100d0500e042a610303840d05204100501e2088492000d240c081c0da03014410058001d600c80c02c0c1a01005800c120345580c0000172001c2c402c00041304138202103402d0b4003580441300103842c0d0744032044178503807449008001035100c9882402e022915405038410310a803142a40c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 279722508 1250 279721258 279721261
    0x121020a0302030103030912120c050f010c0f0207050405010305070e1009020f0d112802010204080a1b05030a030801061d060a090602060c07050a02060f0c100605090c03070e01030908160b010e 84
    0x811844d06940710302030f1007482144e1921480324011114040600c2c2f20308100c907500988078407070300d003154100408070b030001d200c566201c03a40950422070880a4070044804011a500d15a50565200c0181c0716103920b40c1c0c40d0030001024540b41d2040745000f00f1350840c00390340c1d4040120558540b0313446031041d000c2c001e00d4502800e0910010384261481d42c0310002c21420b4296420380510350070b114603014442150740802c00414100c105000342c0411a100d20051003080d04a12401c0f0400c8810b070300068001c0d8000ca01140119030302510441c1103138110705142d0314801c98000f00440034030600c03000340c3e0000800076034240381070b0303100c9000012205194240d4180751103401c0701c20510311484902400300d40c06000020094a442d500070700d84c0d0703204010301c40d1800b01002c41c05810500059811480c0d29039a1408220504003004016805030138441c2192652a1070b02028111000c600b4104d8105230b9074404100070000401c0071644e01c00c0b410002011703400090300d40000406000d0141e24000d0040700e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 279723758 1250 279722508 279722519
    0x100c05060f09060415061203080907080105040512031b04030302030318010b01021002090a03060501150e030109020603010e090a0b010b13050604030206070305031504021602040e0c010e0121020a03020301030309 92
    0x8500340600b0300100500b0041c4c81c0da864880c84003184512400c24150398590025400c1089113068072000e05c252690340241c41c003001140c3c1045043d03803040000364101010070002420128901040c2014141c0143d2207807602c12402d95144440c101c2c882c0203100014000c014190004051803080c1101443e8990b410700c0d0b105030300d00742c545400400340940c3c8032020b14400103100b82c0142c00b440c07001a03e0f00c01026543d880d990f095400a80c401c04910f940e00c5840091290306c004525140d550a43c0207104d004a0703640851254401449180249860300c00411001d40050040f54007058011010691958444070194441c0c1d2000414401d400c4410600140c1c90a18005890813640c00800b190b04050041e2419100e41c0d10090802d040d20083c104240516900d40c03003e860a41c15601d104880c43c07441c1d2062104646a85980c80d81c594030a80f86d4880030381e4001400760b1085428a05451610200021460f04031020076604030118004260086010352543c0614100c0380256103540001d503554 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 279725008 1250 279723758 279723781
    0xf0c0c020a09110903011113080607080105060307051909061b0803010b1614030d110c06011a07210801120302030f130e07080103030801211b0302100c0506 68
    0x61000a4022034921401c0111100b2a880a0140003c0040080c038004003440040e003107859100480465100100e52152442000180880940507404c0100582c0c1803c0001810340141441520b105032030001c00101d0443c8600103441c080c40d4040d08000404c103810001401903a6a0b00620b40041c16204902415803008420401483d800081d450700c0c590a02c007072402654031020b00c01c814526407015000c000707800c2c07203006c49414049101450b00e8150300186034090f00c50240d00c3e90284032041c0900f0303408940c0440c4080c11182d030030a0380c0340f041c200045984402d02074900007504280c0034205075041a0742c8140d589520f4012695610103ea88135401219035801c50440a00141c0c4180404070502407080c0050000c4a5801544442141c1c0c4210f11581000101c40b910005030902004000b05178212200d2809820081e5039110b0503144801c0c0c444c0070703d001c04800703090031030160b50f42d90441da0201c1d42c9102a40d000f410740d21150303100c10390190000b00c0c7c0d11000ca82611070754000070890b10b00d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 279726258 1250 279725008 279725027
    0x70b010504051b0906070609050f01020d0510060215040c0504090b09060604020f040e060307030b0411030c040204180b0609030304060908120901080408030703060e070c1a0105061e0c01020301090f0c 87
    0x90326085007407100800600170701781c20001c4211511a83d6801c01008554100f0060418000150000da52080c500d103643c02522400350425008200c50340b8140560b9401240d61418417450000ca0b1115655a00f025a120b4029038805900580341c140414184551035405a200d000e4a174100d400035100d10042c0400c0744038040307808607080c005100074442c81007641c070501c0d00030000504880c403031b0382c40c0d80b19940f56040c2581d0894240001035450000d5003814010302c0c074014400c413821800e051501c507041d110000b2001200c40c0141e56007404624580d1024103840c202d1a01804480d292a01c07400040c01d0242240030301c49107445141940340f20f429440d0215030403048103a480c1c26040e202d90b81c69170800c0c3c00c0508a007081c9a200c83c3c0105410442c044403c0c400c0e460303941c492076000300b241012044012a480f41005106442c1c0c010f00c840d45460041307802c412510301860442c180e80400340903590141c0b031031000065000000014003d0120b0b0840469500800800c1101020020040c0d840704103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 279727508 1250 279726258 279726301
    0x60a030809120c03011a1f02100f020f04031101021501051e01030e0f01230903090d02011101020d061706070e01050a0215090a05070b04061b021302070b01050405 71
    0x142002010790908000840b89810600358040303502d00101c2d880020b00392600f14041c0c08640d070040107800402c0c03408003400c5030140743c8003c6003c90420005002502c070446400c07200d500603100c4026058490540e4119000041060801509e8944034074161441c0400c00504c94010700c100c81d030850005c04885000d070704840008051034540004ea211880030b104d2142201418107a4841c12200480c40c20300800c0760f80001d0b0400018142480040301c8d00e030200140000d40144440b0b000c0011041d000401c0b140900411038805840f045584012904207c00d001d416426500104100d20a0b0b07008d60001d01c01d60b12251001010030101d00001543c2d00ca00300d500000190000d905080345502074002011001d1423441525040c0c0c0c1602208040c041095070010700726480b1092440074013100b03000500c0a040c0b07903a500e5142c0751810714002c3c074440207080f04107910034400345100115900c2c0b00003410b03181c003100b4003552201c9140c200360b40b0254003440f9241c003950404c0005120340e205641c00099681d0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 279728758 1250 279727508 279727523
    0x6100f0504051b0304050a0209130f021e100905040516080f060103110c03120c0a0c12020304030c12060c08010b040603050c0d0e0a05010b01020c0906010f0311031302010206060a03 79
    0x62902007040040c04024110981001c0c050300e0301070b102c90159004510690040c0018610703804148180300e5509001800048049400c58a14000884001d5074034001da404442d10b603800d20365030001240a07800f601980d64010301001c00e5200441d04802e0400072102c048504100a9540c81190b020b00600102d070a40040c92150001c0d0694440c6800380d90001018540002c0040c0150400351056000001d410069880884c00158400003da042d681c04804504000e00b40021548050441075040000902581d03c14202c040998402c00540d030055070041c0702c20b0414bda85143d0440e07141d00c2200156041c5003400705910942c0d0103001528100e07080404c81d00d01d00703860058110000e20000c0c1280c0d030300341700c200064511494240140c03106001c03600c1c05000c20043c0c03031130201d08558220074290b0543d00070303540120840d940c070035406600050a082330750340c406011100720004c100701004248254804018000384450700c0c04a40300052023a0202d0700540c440c1010008400d1003440014044c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 279730008 1250 279728758 279728789
    0x402010c0b100819060b300a02030303010f0815010620010b180f0112080901030b04090b0408090102070602030906220b2b09030f1d090103080a020610 66
    0xe88200d4402c1c0c0c40740240200c02d0032a5140c40302281840d00d144414101400701c203011401344280c43c4148248480300300e49500c080300e1500740c43c100b2100c480144500074554902101101c50090207000007a0f0b0f4028140c0e81d90b503840d00248540440503000f41c0c0150b104180d1000b4403a008804072038107940164a6098249030804821484d4070346e5540002100c2d502c070385d501112510380f1418040c000b000040740c02c1082c41d29aa19140301340e01603006034944260100a6404a0806012208801000c1c80c011542d18100004900a0f0950a01c0141103440b50300400040c042400c015042c1c05030260f09607890665640022aa40d000c0c410303010394031820402c2809071182c0c2c5000460303030340703080c00301d425281c01c0d92801418400c2c3c03c002e00700171240c200d06c82121149090414001410540701d04104000c1c051500c008208a4240c0d20341010b201440846810039102205140304082005181200d250b17103e103400c920300c2d0403445100740580b28a0000c90581055410401d040d50916203580c280c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 279731258 1250 279730008 279730013
    0x1206031605091f090b01080907030305090f010507052b090e150312030702030405101b140c040e0f070504060e2e06020a02030d0327050f0d020706170402010c 69
    0x80b210068642e4040c20030b0120800450902e001030800201454040050921074290024003240002010004940c10032002400000e0300541554007009054a95990050716080182d40034030030148090038a1084122941001c0a01c01140d88003d11001c01150601d116207419500c0c0420380c0100010400550300003004050045030241d210340b401002c81d01c8941c81d405591038154016150680181c0000a00384441d042103103812008416130b04e8480d40c007a605d51000b030b92005c44a44014070284504140c0e10b000380301046000c80601009008000411901d103106030380702517200e954002e5018402d00000c41c2c0c9058401ea03811520705c40c2c0c0000141e0b403480805503403241d1524500c00c415060030040541e01c1088443c1c100900300903002040e00c03850700d0040500d0800c04a0102c0f0805052020f8203441e01c043c4207801c8103120380d84103101c3e1485c07480e141080c100414030841c0c51f628132410b0481c507011540010108116201500e400500030a40c503400c8103039000449020380030420f80b000e40e100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 279732508 1250 279731258 279731269
    0x201292404120f0615030c06020a080d0509010e070810060e060108040b04141b1e150a0201091a01051002060c0a0e1c06020c0d0305091e120409021206031605 69
    0x19052207811050105105551035070100c0701708900c42c0d124414001400c4c8208605020b40c407001e49654002006400752507038508201c0d00c29040e80d484101d4035400420003040342500320064022200068640c025100c14482c0e9650803031420501d0503508185c070005500264a8985004140696500d903103a6100d07100e4602c60400a00116881246030f01010a4888140f010050f00390803000740d0700d02450080c0070885040c00b107c3c4040400307480041d02a281d0b54910302c10083e01d105848a043d202c5d983c0240070790040000c80c5e00900031082d1019100800700d0305100c117a060f664101c602c211840b413601c4003240c3d00c00c0100d4a40e003606504110020707040e0300491b450544824010710724070f5400c14082121031015211507089034a10f40100d40700404000501102d441c0c402141740400c01c9182c50750740c0030741d202030003207004013403032216280c11302c0d24075060003218240e000c280c040b195282c2d81c0b800c0001c029400b10a0a000413043c00004c20304500e13001c90048a00070321b4017541940740342004200324 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 279733758 1250 279732508 279732539
    0x105040b0409051305030406050a11030a20010f050a1b0c05071211030d0206100801090308011203050c06041401050109110315040e010903030207060b0f0603070503070201292404 78
    0xd82c4c0c106403d03407200004000704000c00107440383d2303541c0f2511400c0b0510044c00051124000910369041071000c9101e107a4412900c2450801c2c1624144242141d094460b0050007804801c2d42da0350304200401c2000103c82d003054400052002145a034640310074411035071500d000c1c0000700a6048031104100110f85110180c5405004011984244040200091801d07404580500160b0440810004105501803a6200410b0704a00030b1002c0c045598008148038814015901d5071b26480908106152003007058600440c1084212070403428030b8180101401860700540034190300344000410404910700400c59015a0f2501050840d01d4048100c45240c0306049210703002a03440340740801d00344c0240200d0784054001d071001699450380d4184030080c3c800c01511315004d9620304601d0944e0f512801d0440c1d070300003084d03d007054503611483c90482c090010b044490500005250403080c0c01060315070055400f0200301d44202c3c0c00310400625555507146100762011091050104100900d0b000c003805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 279735008 1250 279733758 279733771
    0x306030709020409091b0602030f0c010e01050709030c140901050402070609080d020909010e040210050c010905060711012f07230c09130b01120201050c0105150f0105040b040905 78
    0x296440340e101c000a1040f07030065400f8408617034039040b1420a0000d04c1e42002c0e21861040e0301580d0007410403002a581e03120b1800a40c40ea59400100441c201d0400e501035403014076084024001810a044010510150f0340019602d01c0212800003035451840c0358840108240a800c9001c603a203081c04210080d0890031064814079120100c10380003c40c42c00042c079507003031003c00050b102c582240501102d0030303058001055105004040c80090399424055594440c0c03145009551003100d10081030261612082c02041440789030207006881e0703049209108107034001c40c020091a0740c001040020700302c0040d4101ca02c0d003000c22900c003c0040301402415075900450a136250109241c00c0902c0d04035500c07410400e16040b07180809514580620034170780144244040c02e1001440c0d0700e410300d5100061148641c4051854103420031a406813007a40c106d244414002c12451614103403000801e10401d804900c50903140c01c24444035030040041c0c8007511500304c852810182003544c103030000e0402820700d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 279736258 1250 279735008 279735013
    0x30c0303021201061211030603150907120305030727090e120c0a030e010206070e04180209090f070b16170408030406030605040c050316210f050f0606040605030705030603 75
    0x20710070302c21008400900904039659402c50160107410752004849030002011b03100401001800065900002c4881e04001d8110701d26009880b2401e801d440c1100c50760200d0307179880e44090040c0c14190028065813040c1101c0d29205031307a10394031441c4850783c02c410044502c03412400109015202e0250700805150640c1030031174607030b80c10804059020b41c100003190302155100c40d01460030190310403248041c0c10001e0004052608103020003801310388680c13181e940035594a413552800b00804002ba148010380262681c0e11504010700c8198907510a4222900103100c3d8503030020305840342030210b40c8007901080748182804907503603401468028200d9601000141400082241401030000340700411850301c00040903860002880160746402900780144481031080040c0104043c14502103c0114036248008070450848409001c1900d4405a2054901071082c1103940b10b41e803007140903407400403141c50166207040410071103100c0c0e07005190000d5001e2003c108014001c101641c0c202c4c500805 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 279737508 1250 279736258 279736267
    0x31b01091d040c09021201120f021503160504120f020a030c080d0905040b060a050703090e16110a0f140a150b010e010201060b270303030703091403030f04030c030302 73
    0x80c0e055000c032a501010480050410a01003002460784800c80203208151040d03007826203d14100d48210b07014810700110a102001d00c03010048141070400009500414548a2f0381e4641400c24041c0c0007161545140190200c025a145001d641a14112600400e0131920248981d441040303420307a05104030f07004510180040005103032484505c0180854000070080d680346038400415031140f41d4001c5008034584030038000b054540c4001c540c400c0d5064202203503502c00c1c503d0f0882d080207641c0c3c031228030600031a043c051140a040c101c4455008035030785500c0c44841c02803005480c1c00000400070030000075035440c0d00024002501c0c1c1c0e1a500440416940340205c161600e0f20380b002c92600e450b881980c1c40207040051f6070171416020200f5002c1c030080040d1030034901d94121500c2542c14503031915a05c003a5004d811502c4a05440345800040c042e2916401c0c040400b5000d8210341c0e00c00c403541d0000a402803000080001624819020701500d00644d4990ba01c050703400e0341035600e003902095000c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 279738758 1250 279737508 279737519
    0x103110712030504050d0e0306010303111009150f02090a150c0b040803370509070302060d020c010b0d110402070204091208090601060c17031005221406031b0109 71
    0x4407102100c40d482d20041003a1800d46045401c2c0381d10780010360180b150388001401242c9001030304605603a89410054512046498100d00d04207008019081280c249460b034002c02c0311484010f0785552040505021040c11813003054168010100580d4114403411030400c1821070710f543c40c0c034070f0354420304118500b90059116500d02180031107040c0d40519000040c4810041c80b40103a0303002a0560282e000c0c10010a03203040e214000e040000c120181d25400070948441d400d22245004540c01804990b5030300e440418036000e034001c2d00c0035245951800c480040c2600300382c054940b8032544a01c0c01c100000380d003c100030003500011002d9030029501c42e0021b00203070254281103d8072074151203a070f00b146000c0c2c4c030749071038510160007840c1042448032f480b10008034121400203424480148080d181d950301d240501c0010381507404142d102807919a132004980340400d0300007007580601403c1c45404200344a04200280640d81c1d1501640982c03092203d005c6410f01c3c6480e0050149000e401d65903994 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 279740008 1250 279738758 279738773
    0x50408060c070b15090f0601030b1903110d03020d080403020a020d14060601021207170f0403080408010b0d02220b0a060314090c09010b070f051c0e0111070501031107 73
    0x8a8001c00203140c00201e00c0e050104022980341d00582824101001599000208100c004081d0402c0001031041000c20702c140e000303412488401401400f02901c07008400d4002d10020b00522090342c01000694558006080081d0f600c48050b0b0160010590a10480011140944014003d80450203101d90010041e51401440c0d00c442d40100d140082c0750041d80c166074184500a80202c0c1990301c40320540710103884140c02d507415940c1204404a5440d0310000c9032505100301c07011401c4006002070040100802100980280c401c000c0003046208008014060b070102003205c00395200888181c02e6401101d00d5800040e04025090040f41a103450004505134558903004200413948072000e1060040d841c0c12550351104902000b85588251200804e403640b5060082c140c1d2520005452001d1048044100840c0c0343c1c40740c1150007007400c1270618004d5245800c040300000e48a040500103a40c0b1400444000010460291802c589410010740c018a240031000c214074000703221840200d00d12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 279741258 1250 279740008 279740011
    0x30a080702030609010b011d15030f011e0b0d1d010614030c01090312050f0f07050a03090605030906072006010f030b01080604080406030504020612071806110604060c05040806 77
    0x50004940c458406104150401400400c1203826038074065a100c0c00b03a0b0301040100003241036020811804805002181d0031b0b41e61040100c0b10010b000041c400183c84030000241260406040350707200e50301c0c4010082402510b441614010f0409115400145065910031803d03003810389c1010400d01c084a5515080da127056009400030703449101c842003036040901c0030702a461800d18007158003070704550b900302603100b450032032000304000445d07015003e0117030504944412020141040d00da4081c1d15080d0703655003c03040110005a013103c0000744950141d02540e016580b400054041c0b651058003c031081c11545a440800b194207206080d024603050100c03c1c0a0074109000c2103415045080043d034240040e0300680259000c102004042103808040d40d046d1201480c0215054985000141141c0640450404422180c3e0280400d142e00325102d841094151081065010f81e0f030701c01522b40c14642d00d12aa15904071600241c0003500503446031071035002070b06105007429100c404a6181420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 279742508 1250 279741258 279741263
    0x615040b041e052e032a0b0d0b0405090a060b1507140d051204060b010909021b0f0d20150705030108010609060302060711040e030a02161203020a0f060b030a 69
    0xa82e04280f021008449503074040b07140b00c10383c502444038401c501007804550340e44800380c42111b500441d103190ba0001e90f01e0002c81000f5407256150651114032002d25070740198546a856450045074840c00c0c28240900c6204004c08005884036544a4442c9800b070140c0c40c00c0c0d164030918034154031400120600c058080540a01440682d0340320b05a01c15207451030050141d82441360510a0500151a41c40e40d654444c1d8400d03808581d048001d801681c04120640000400c1170000c5506060507c135074290b5041841043d0890360b13030a40400da81130700c641e00d00039000009114039034402582606404c1c0e800000c0d85600885507001001040032584807020b4546400141d0000010031100a0074082d82001d09801c10303040200515603070010f2501d224403180100f500c3c1020240209954841c0d10002c245200c03402034940c1c078440f01c10001c0d1211a041084640031001400202d911815503080b40103059040d00113000c4000580c40c1d40001d12803603070044400e81d407100d01c5001503444c240b00c0e00d4107462 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 279743758 1250 279742508 279742511
    0x14030d060303110613080c030f041d0708010b0a0f02030c0f0105010302032a0103050601050c010507030b040e07051c0206040f0305031209030306010c0213180807140615040b041e 78
    0xa0070340c40e0081c007101002d00c80610550000051241060703000c81c51960b10340c0e000d038030b01d5542d1400c0d610050440c0228031542103070403c04900040c44049030780f02c0c101e1040e0300c1c048070360341d035520702901303940750764080c061480041028045c5121481c024500d002481c1c582d401140d0421100e00840c1d89000703006042d10049075100c1c2c1c01082141801c1101402c0006c40058003564541a03101d41e481c039809000805042513140d902159899005004540e1034411701d2009010318a01210090301500c0d014202900451410b103910500c0000491500c041e214010300d400c900100494644114004141d0b081c3d91008040100054113407058600c180103503ca60081d64840051220412010384000d14076401c6800400070801c4580c1e000700c8149100798100c0c1c640344440c5518a020380280304104d8841100d03481d0311151001d04c941f81d00a064030610922802c8520300505002d60340b10fa4040e40ca25802c0c40d00445000c0700703450f158002c0450000c1c00760000030000820001c020703c000841900282c04c2c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 279745008 1250 279743758 279743771
    0x307090302040f0c020d1e0f09080f1605041a060307031503051b1e12010f0606180611060a0905100609020a0908070b040302010315270e011107020d14030d 68
    0x454041c400345905016a0400d0a0807014405413208110207c0c2e00b110704200318001284046d501896880001d0280d5408030364081d6011042d15aa030081010102c80c09004409c3c00156131810303001d851041294010b04002501001c0705001040c1c001910200a26844807070081c440081d0032045801140103500504190858003141829958240340081c09803414100c0e4554800810040d5180c00c007041d00d880800c100b1144e0954010132140341c2d84110030f82008800620983d0100520401e4aa64200001c206036034990540b500c49012355014610340100c0001211200d8541c4564003484c0244190351000b0030001090085078995081000f03115400b01e10381010903404110000540501c03030080203214180107174401d66006a200084c101038a40c002c2030420302c20905c0c80c40040402c142205040a0403940c1c102d1403000c000c1c0e0700c003071441c600008a640c4031014081c40402d00204074046140c4804e039024481c00280c841025140710104240c000c1544004000800c1901128200003610 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 279746258 1250 279745008 279745031
    0x4030b0c07170306030c040606110c1e0d0f02030d03020a030e0601061d03100509030301050102160608040201050a17041124190c080309160905040302070303050307090302040f 77
    0x152005030a051006105201120018078071079440c807002e0b600b0400300c503201d81d5200002403600420324469500302c5d061a400007040c1741c1101d11001c42400903416907200c1c050074803d010311a00141c00b00d8000132820010540c0c10306000440d6102c0e580100c511081082440d0082494109103002c41c40c00030b94001800c10283d039241c410401c000300803070083c00c01945020801090201c1703c40d6089021a4000ea8840b402d94040016000c4540301c0d41051041d0b2601400d0550bc035002446403c0c00343c0100003800c0b0041d40300d0010740c426070b1455101c50480d44c485400442d00b9412080031002400f5072001c43c041d810f1825807003244210702c101d120303c17681e007000414409d0401060010150602100000c1c4040030405d1040d240000e10948a10400e81540c010486d4407444c0b800b0040c010040000501c10142400306009075407414440e01824035540c0c5094040451310119405001600700903014000244140021900010309144c90039403a500ea0300050200c900c400e1503e10705581e40c03c4113558 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 279747508 1250 279746258 279746273
    0x20304090617060105150706051003021503040c0b09040207140705100e090f041113050901051305030a080406020c01020409020d0b01020106180b03100e0307200315180d050403 77
    0x140c0109006039118500b4141aa81e444006010b1144038090ba1414822414001410340705916000308080c042e5041c800254207141a20740000e078040c1c0a038031007100126680804883c02543d10524991459180c5031541c0000d4002c0c0012a9010340c0812080780810205959492030300e6510b0080d1007040c1c80c107410490816400f052000921072940c078480c0c00c0e683e82000f525400307814100b03144419a100d180844084454111032580008541481c10010b9200d0f4812072042401c02c000b00300585910500081c1380d40320002c018503992041103540101407191141c00d40261242c0c001604207421070f044142680c0054102106d8960b0104181905003468000d50742a85801e00007006120b06119501180d46d480b41c001d41115901d41702e518616480c01c2105810103e0403410401040303444420845e183d0f48440000d07600a800318052014a0f40c1e203503085203004a004001704130a03010b07521007078180758008051400c0c1c1e4541c0030a0b00180030007402819408512551a43d40d07503403d51a1548 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 279748758 1250 279747508 279747521
    0x901051006030c140c010b0405070203040e130f11041d0a0c0905092a150702131a190e09030c12070f030e040209040f020d0e01110313051c02030409 65
    0x1800c1505000d070f0003ca094001d284448004600b02e9400d6664000e044000c6c050a8541e81c01c68201c2c2c9007108001031181c0c048068801d441d0150300c1c000d041d88071007600107170182d240354015101e000100c51410000e04100740d282015003001d400820300001d80c0c48144e400d072044091410454010040c808104074201007404040d0108400030405414011082c80c1d8840303a0101091031032500000c5090401c070b600400c5106510010181c1584072000d0240600e140c111240482c0035015034501024000c800c0c2c0a40e01201c544100401484c140700b00401907040071503188400541c0040e4408910b103490b003414548079010b12030007507960341000ca100500d0560401c1c1004400e0b0018051880043d84009450501782d03090714018289241c0200090020300c2084002c513449850318540c000f001b2405d40242151650041081207031290341c42400d4240c80c4202036000084004100040c01c1d0b1221507041e2502c1030207802101c1c014001c03406a400801140c0102501682c804030301001005224000e0345c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 279750008 1250 279748758 279748769
    0x12090302100b01081b03071106070306050f180c22030b061f0507020103020715090614062b06060b0304030825050a080705220f1202100309110909010510 67
    0xc00e19842c2141ca091905d03480c050344490f49102c008080b4110910a6031900d1224850b80150f520500b49540c1c00780003810580714a5009816802a807042071408d10295450b48480c000c0030242c0e03070790308005c0b402558001100f0074099030030310710030346401c881100c580c8014610034041441542081010883e001030740000011005410381d0070b440c0c0c05a03001080d501c19540c2801c0140e01d946880c6040c1002680c0348803039189003403402e225402400541c7d0040c107181d94003401721036002e4542c2c10510048050f0101e032020410103035941c6d500c40c0000791179840c9019003d20b200045031501c400404800b9401914154000381440c01805028402544107404a80c2010b03148008440a00c0000e4454028100c2c89014402c0c124000b0306081d0181080364024030320b8501d8079103407141c03810402c030f101c070031038040c00407540c4d40d680300450071105071098105402d80040c8140d0014810604c01c802030803c108085070980ca038400c11604a484600c101070003120010b00102c1d0f6032034000f40c500c0991940742d214 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 279751258 1250 279750008 279750017
    0x803010e06040920030106090c120c03020306030309130204030b040c08010b0102030313020609040902120106090b03010216080c070e0a0504021311090f0102030f220602010c0203040e040312090302100b01 89
    0x1c3c00111a0b025080c40a0461640c1c180106031500020f8014480d6034028002d00d42800250301001c2d034407040f400c0c14a000c0c0e0804104000914000f1800c82c04122078150f0180e104202080e000e280c203110040b03840a850401525180d142e503a03a09912034141d400b21008a032406060019003400e00130203038101400c0c4015070861400c512001d403080b04001d0003030b0003071400062055640c3c88941000c1007040d00900054041e004039040c050090000388130360711000e45030440f00700705443c040c02240ca1121f0140f0510300010155140c3c400141d11141c540c000901c981400002c09007042080984030762000400091140713003030700601081c0032301181e42c400b40751700d020400e0182101000c29902004000d41c0c80540560042e401070313145104440441e0300302d60010070010030348608080160f8000103c45008101c1c280e0300d40b010307400d0b41d125200400c0036070400c0c0403d101078520308171404e41c860f0181ca4100400811610510b084030f031041070503070044e0440014403520003041d001e11074103040207180 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 279752508 1250 279751258 279751271
    0x100e030a08040e0402031509070509130210110d030e0a03080702150c041505030f0103080d0e0a140f0601031709220501090b011d1519081504020403030203120c0c03070803010e0604 79
    0x8403944500c610301940d8418102f4134081865003d41c5440a103110b54054100b000c03010a402c0d0203041040c02d140019850722600c140328400510901400600d4400040140304885803940d003a114000c0040c079580452003035104c0d403040251385034926400384642c44122a903490a00d0f81002060a809042d441400406c0050000c0c04543e014121f0440c0c1e00180e02c1030b140c0108a0031f05001d80b6007541017034614440c0c024840c0500444090501c0c034407103039604592240803a6151151507410074070003c2c02c0300c43ea182c0440b040141c1c44004000c440c000600c01044891250209070301d00c055039840c5041385682d000140400d0815228400070841d003404e0150100709901190300020b00703000c0050b0b004071900b650915030300c0d2280003680c00c014900314000c1403142116070000c3c01c218044a000c468580d01c0640185182030520840301903d405a000d03614102410200c0ba64010010b0221382545004005180401d0401c4c4042d10000d40714070106660ba5142900e110b1064102606c1c0600c99845c1c000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 279753758 1250 279752508 279752521
    0x605040b0a031a030106030305121015030c1806050307020601050f0a03030c06200d2304020405060a2423250f0b04030f02010b100e030a08040e04020315 67
    0x20103907168000c181c81d0224007120255508203040303c450071440d8056003042004401c041e00107028200152864409404995500364a8000481c02d403107500c0308046603098031841a03109401280121401d402e20700300300700e40d11008420200e1140d000000142010040c44802507050003054014a801c41e0140c0d0785d85803280003c4c601660504c001810700c201d0040d42d208226042c3c1204401100079010100c28400304042408298442070f0040b1030146407000c008034012044050041e206a0102034007240da4481c0c1c00d000c01020080c00003a0700104c15440012600f0215400b030141004000a0401e6660b030007001800c0a80514031074104d05a000303075158400c81560050714282510301a10300418500300c041d1520540d03250b00050308900c0381001d010b05204200c90203a004a220340d80b02c0c0c15203c1c1182c03040b4200c400307040a03284d02500c255850142c161040e041950001d400a096030001c60300d5035100f90055120b0742c0118000c20101080100750701d414071280c8240240e11000d82658540030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 279755008 1250 279753758 279753779
    0x160e040b0603060d0611070f03090b0f040506090f130f0b090642030f0601030e1e0f0303130506060612130303021b0610120201090311030a050d051201060504 69
    0x106014001c005200b030b00360500c581134000ca200144546001036403071f80300341420b0002c030980c0d01041d00410707848080000c0f04d06c203100484160000721000582414289010804650300c0000c3c4143d1050012910302c22640d5114030002e800c10300c40ca000035600309500440c03026030300051000740c411f6800100b00a01504c0b8250b0340007800107807040c0083c010141016114603250001180031850700c04d07540b4620030240e07020056001e8040c13003207110101e60741d280046050303a120b0300f42e119858000b43d090340f00e070807000081001c00e4041242134a003400660000c00349950000c9070340017040c01034a0b0504043c02070900a0307540042c2c01340c80e11803410401001c18480301602810b448440340000d9549024148240c1c10b90f810040c003038010764000e07206008541d98820f0291841002080c520100240003040000001d1000b0350603140c500b0054a140c032004907100d60002e100c0e8040c021445804000385081c019541c50b010103455980e15884041c6034100b80d2503050f04405c0c1804000c12050100e800749 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 279756258 1250 279755008 279755011
    0x60a03030507120c0c0b180d0302150403140d020409060e06031902131409060a0e0a0305070c170a050c040510050d02010306170f0c09062101060b03160e040b0603 71
    0x400705400740010030400c070f8480031320384c1018080e0001d101c1d000c03400d0054a4001c2182c0c107211165100b1181d4040200a500c0807000c1c070050159015405030b0b5100e412243c4440e87c01030090a065140b60780503598840140d10090911f0300c019800103085c8003091a9201c0d040c0030706200100d4180300c0c03805a0100b03036190f401c441354001c0540404401004c55880c4a0401e1028010300700a0161a1401f00d451504020507116211140100d200003001c2410903c00c3c2c0b108960a00010501c815023500c0586060740f02d40000e0f141d094254a01003408288102605401200d600040c4812462802c0150620b80c1d2070890070b1090703080a040c0011407241c05081019190121040320b20380e000740c40141c005056036840300707024690b84600940b00082c0480d5004445024000f51030341cad1010181001001c02e800c07200964080d1510030140c569211503441451401260000000c12644408000791107801c01c84910841d04400445100b890b0b0703103e00c02c040a890f09581c2070165110380e40000f00d59000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 279757508 1250 279756258 279756263
    0x7110709060e2a25030f080601021204150318050c010914031506120f010506030f01060320010c14160905040c03120c02040501140907050f0301211217060a03030507 72
    0x2002c201500f4688003404c0302c0000c6404011214006159464058400d507003581da20004141c0450000344154008101101c1000400c0641c070714090034071281c0c3c00c0c02d50300842000105540c0e03007a0800d139a02c0c001e8503d0840c6003d000100301c2d10b807a04000500c08107050304004000001c0d00e41c0800380351400106154003119a10704440190781d12000b142d440d04141c0da070010a4820411519011041035000500800c0141d00799501445402c1040e800ea0f16140b00c010a0b41c0c201d5034122030b460b104180110010f44052400c270f4000552a190b54651003036208084d0084d800078034100c0074400040880c0c1e00103021085040c0400c1c90030f0345800c1a15841d81c03202424140e000c0e00c441c41340724428001310341c420381d00900802295845d1082114006104030201c0d006011090128400c103010b174041d501b102c441f84c14000e00e542e00301410500543c41104848031001480c2600a00141980074040300c04440d5030381e005032009640111a010550150000d40201c0f40c4e0102440400da1100880340b0303454 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 279758758 1250 279757508 279757591
    0x30f030909070c021f02011a01020c0909070503030708040e10030b0a0b190b030109150522291009050a0e04020f0a03080a030605031204060807110709060e 68
    0x90742c50005852840755940d00a500c051501c0407403800044403c14482d6540d440d42c002c00110720356415030801400139a00150140e40580061051894034051075030344600c03000d023920b90b495a14004a461a000018211049000441d090042a0030015069031000045041c040d10503d03544480800c0a030107088039100b01e03110054400d0944403e0340054032200a80d100740302c500c1c1d840340c040495800a01038405003078106441c00500c40550001d050603108000c00c048118000841c00003c10f902e276014400010349c4601000c0004500300c01c03c0d60788a0f00c022000d401055288041001171603084205e01c0c11b0055240040c00240c4518a640c0b0030f40b1507000701001503482d5800007941c2545081c20031940034140c40300c044100700c0317204041d010003242502d052001c01e84170403c043d120b15901130068511001800b0030841c0c1e0344220070b5190410680d08200d101c800d2a10095402d00100b0f17003000081c103450384010410000ca0180b00d96010032042081507000020001d00e1991000c00e008183c40907 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 279760008 1250 279758758 279758761
    0x60703050a030e1608010b0f040218010f1202040e06030606030d02100b010e0603072303040305030c090d060e06100801060b09061b03030708060f01031e021303050708010515030f030909 81
    0x194020002142d45020071161030755402c1da0340303170317458060881c2d140c182d400b8140407019001142014020381d0411148458804070506a0100442c1c81d0111180540108010800480c50b1074030544001c0002c0d10706d8448190303d501e801d03400e0500e01100544018001c0d40300c0010030180b203501154080b0749907032004000c50305002410048400d19401d08115510a000200b407049844c1c10500089090044021aa14070103040d0110603a60204580c05001710b0320810000d020b400740d44005080c02400205000504203c85d1155021680354004100c01070f80000d01340160010000d07141401007484100130304c03040d0b0401012400d0350080103041802504081800e10030142e100d50501c4640e030f001e4084135203078035000030014140c400075902c103400f651440310051802c0d4441d000c0c000d5032011800c02000d40c03007c0110440000d6020300c2c111102102c2c4180302100103034050150070024000d8200200300350034410303200048481c949001c58030031307440900c12041c440404415101c103c801254181000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 279761258 1250 279760008 279760031
    0x709050c07080309101107030804020d29040501050604060305070e10170102090f0607020904030e03030c0a0506090601090b011b050118051027020d1a090303040b06060703050a03 78
    0x141d00510100a2141c0c4002c41004424040010a0282064a0403050004c5044a030762a0402e21454502400051036400020054200071aa0342c407460300c03030010800d0303400c4100e04150f2080048003104d84404140c50a000070311909006003a00054122005c109140c81d40c2c0d0b80d04e0b583d0381d0520030b1036900c1c41d50100150407403500d424044001c0103c031042d00c0802c1c0f46a00c0c039034000d40c03050300814800d00707142048512504150003030303038050340d03002e00001c80070784594030f003603408010916400b540346c0b0040000c001d0541090000150781780c0f0840c02003610781080d88809040600580210070440d2524420b040709a80c0005401003182c0322451074505202141031460141c00c0040c01c8592200303040034910100b010000c0e28007d014084072042010000c07c0c10300c14820242c503200c200000e0a00d0f04110003600d0b00200802000e403089403503500d0004181c1c00440d042d48200c40d411039581000c001c00c010700c0501d96803954040cac011101c0301c3c9030004a54014003940554607010f0704059850300107103070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 279762508 1250 279761258 279761281
    0xa02091305030307080405070605040b03071803062301090b030c060715060f15080708060f0d0501050f100e25110610081204230a090906020414030609070905 69
    0x4141c001c4192540c030300c0c3c81a40609410000d460485941c41900e500294440c8900306031010b41e10880500d0f17156850342003040740c10b10740d8076113440c0c1134007240038000000801034403074a1000d250380e179801c501600c040c400c4080400c00c16481096083d040060b401d2941d0707000304070020f030468103d0b01c454440a4600b0400c0881072a90700c65414185040000700d080c04a40d0801c0c821a1000705084074400354200e42150100802d40d0380d0700200d0b0415010980c10302d00700c2e10700311480c040500800002d07410794440303d0a4980c2901e05560f42c0c0440f200b40103c01404141c6030004d044517044284007410032400d074214100205020440c1040f9189041035900d110300c1c6002c00380d41001c8111502402c0412540183c03048a22070740310b103403107a1070b034104d0010100c40c1603800f00e0700881c148240c01d0040e1888030b8208070080c8913150740f24118880214001010f881000002402242d005890b0b80c1404500c20962050919003480782d40108100a009540040e40d801030380c3d030b00c010204403603c072200d9500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 279763758 1250 279762508 279762541
    0x1806061605070906030b390f0315030d090b0702090a0f05070315091e020c010216060614091512120703260618131203020d060504020c0a0209 62
    0x240305002c0c1c07a00004800006030040c105a03800341d0b0503504152940b5107a80402c080307032446040708108000703881c030703121000c00e118240350703540009100d14203107001080c041180c1c01110080400d01050103500083d0400300700100c001781d280e003030954559040c100801080c0c0140c0e03000910840156001420b0184590410080030141c9a414469410a4040500540a0541524080c02c580d04002610461900602002079862010918a49030085201c400381d4041064140199000c001ca6115140c2d403980c070034400d0703000d441d000840c01d080c010301c640d944503407526541c880c110b80c1007032084040b00e07840b40329401d850441d5600c0800b20f40aa0745410901044000c07416104049144418584c01030f0a40760010a0b01c40d1111440103240306c0c41614090544009802404611811720420849540c0b03030381007220120103040796009907170f845c5d000a1600c0343c2800001e40126090036454100d0040c0d00290008036030a43c2048041065070b0703034500301d45002a100f0000040444c564402140405 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 279765008 1250 279763758 279763763
    0x622271707080d1107030e06040f0902090409021c051213090b042c07080f0a02090907051504080c0306042001140301030507030b090606060901030c050c07030308070201060518060616 80
    0x3400754000d0081001300a420040041c0e022580402d000f00280c0707000d01c1145c0540380d803082100f142604100d049002500300c2c60b0300d076070040c1d0341e190100c001d0b170b4554007294902c83c0800300d01e0044580901e0180d046c001c0414802824150500400ea081d40000c913080c016a015039000243d80134646d00000c01912440c840e8030700c0707210181548451400780c1e1000c07400f81080542100c0156540351801a501c00007402101069000784105000625000003415000150300080710080e544590005101800f004050040590000b030100040d41041c0108110914100c2c040e001c0313480d1949900c005e800300c210070000030121074101030340e16038066402e440c000240c5900c1c3d40d86940c1c49241c0315070317102154001503078040080c00001e046000e0011320b40d841840054a40743c240103030750700150060507081c00208103000c01400a441604400c001c2d400c0114040d036614070307440c140070b070000c3e084a5040d04454000c1c03044810018255070300c10f02141e0400b00a8404030b548003507505c22661551180d80b0300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 279766258 1250 279765008 279765011
    0x109060509250305030d02090a031406070f031e020f0d05040804090e03041d0414031201050a0503210a0203041d07120e10050622271707080d 62
    0x180680c207100020400c1c0c8031003003111849462814040b81042c030014520000b0800e07401000021032019464010f824690400313048507040c036407645c0e901c58400e050590709000642c055820410815400512064064040d040c20002c10400300d889281c00b80785001594152500010441c4040209000300d540328140d901381000141424039103c1856440b03407041c028080e04201202c203a00301c0100407101100d0207080080303000071412440000304070000304151071280c00920702c2c0c10300110910040201d8842c24080c0f040c1581444100180300c02a40c11450180d401402448689100c410f200d42071980c802c101e590f00c0f201c00701d1040b40345d4411500f22081c80140840b000c801c00300c1020780c40380101219216020036110000d041400c0302e0303c40541e0f46090b07005401b0f204405505602c0580c024002620f107140384501e000070a5202c8030204403840c1003560b9004001141e80705601c00044042404840c414981c142d903c8800103075503125034011a00300e0000c1c000381040620070454064104c20b040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 279767508 1250 279766258 279766261
    0x614010806270405060708090303040f0c0e0106200c0105070b100f06020a031b020f12070b03340c021e180603010f0c0f0e04060911091302030601021e01090605 70
    0x200315030944094808813003500c01c800c0410032181c000c607282071040303d02d0b04c019401c5580c2d50b04d0390700d00c58101c0f680654992121481c04100141d04014080c003810450700c500300440c04101030702c00340301c4446559006a03044400e0542c2c0503070b40501228580c0c1c0d0003819600c03154680c01d04002c4455290340c0301d20070030500d880000580640114204690303d00a4469509060940b1846c410003200c000000354000391a010704001d40c0381044c440982041a002251480b82d140c50b041001688155602c1c482c3c10910160701248699400ca04410100000205881c4925540c0040c02c220304056009102d00030b520451600304440314120003080c80001e28242066402c03e038000c0c0b100d041910210f00035401e1210000c540340c0705000340204039020356070320a24104079100868042c58101c440300d50054442400003440b08443c01a182900401c080f2140d03200350881c20481c00000650310840a0303801401080503036a0085046144c0604446100b155001907220382030040c044820b005208616100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 279768758 1250 279767508 279767569
    0x40e0403020a020315011a18090703020912011811151602011b030801091d030d020901090609030503120703021909060206060a080c061803030414130614010806 70
    0x5402c88146009400340c9803082050035a003011a8400d010304c030302000842c007181b003c07640b002c801820360b8006461003402c404c15200009085203c15501d01000a402090120840c5480d440070202c03658500d000300401241f0031030803080003084400180100c1401c0c1500c560320748520606c1648a5080e07a4507603964541c1200c4041100a4031405030f0005080120000480001c01d08a00300983c042d03c614141e81e1070b229600c0040d115400380381400c0e04211107440220a02000a0031074103440da0809a101c2c000400014043d01540d40320004014401500700003003030b0003004465480c1c0c2c40030901c546654071000190302a22860303190101180410500028180c4d02592030b0003600c050303900740d81083e200c070810040c0085450040170090f4100901c01d20507803401c08010607035803032102d400210415003200003a0035604140d00c80304081100c1c41205c15940f401c03102e503080300c04143d2000c026a505160044488103100c642031418400e00a001c50441d60714801403000040d1200e184065140021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 279770008 1250 279768758 279768763
    0x9010e03071d01090e0c0f010e0a17010506040c0507080a0c0212010203070e0405070e0123030702030301061b03050304030503041505090a0311060108120d021e03090d090f1a040e040302 81
    0x18600741d455082d0007002288010701030107001c040904080082113200c4444040084a0f401550800e06000105000f0302480d200e10f00f0101c010001881d0783d15008010301813607400c0d1400201807501c581d207414600291031f41c0000075690980d030840d40498481c0280c003002d81e1036a03181003019500c4502100a804418015001103200c0d084030703610344000c00480e00900060719420703152240441c50007504000d05500c9646401d0315803450707460400c4020340e0b490f9610526842629402c005030070020060003180c1d0014004008007100c401250f80782a00c580380200f0364080076000904000c40000490244203442c00182001501c800042245090800070556624415081100491155180d4030300c0c1c98008100f9a0480d41102d0241040700e40040f810405039001c0780744c8440c0c0c00d07070910031075034a50b4602c5858a65100c0c1080155a03030b00f441c2d01d0203031820b525130301e8400401c08982402d100000c08140b1103411981c40b000d07840390006000c5940328490241e42c0200c038140c2c000c41b04001c14103600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 279771258 1250 279770008 279770039
    0xe0f07080a08252f2202090d0c080609030703050a03021812071a0c030a0305060d060609060f0b0c0c01120e01020d02090108010f080c09181e070609050306040809010e0307 75
    0x507203000c10440c1220701d0b00280440043c3d256541c1c01664401c0d050718407000c103ca44285c25101e01030041c5003000240020b104a0350910302035444203c000c8081c02118405c21001b500001410015400c01113a80c0e40100107104001d040b400301500801c8074136455481c0e4402d400c14410040005507000c0c070306581c2582d81d510511035417200c090008040219100f240c012a40d03084021000395281808110098015003030240c034450b04001280108000304d52140b0030100a09407886010400e540f0b082541500240180c010104155007000311428400002605010185003820a004401010803031200103140c0c45d0344a6406500020740c0c00800b40740ba070300500340200e00b62940c03401640c84005810305044140510a0300ba030013141741410514001d071010303a2080151803101c0512031522205420090042c405c03c2042c1c07171440070801001020300c002c1c0c000e0005490503280711494840066a1060003620140900c4070009000b6a180d108502c0307041c00020150403074400359503d101a0041080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 279772508 1250 279771258 279771293
    0x20041d0a03180302030a06090507030b041b0b18010e06190e0a0b09010527120a030e1f082d0712060612150504050a0e0f07080a0825 58
    0x2401c0c0407818082410b041442d0030303682c02500801c00d9040541c0c03040003e05505400796128450003500200040c0b04d0710076540f003103200d5800e540c2c0d01114040d0101122046412045c0c80c09000d01c09190b40039191000034810050900c0c0c0107600c20038540109030b01d4403070a030b030003580304410729098640560003c0e800314030100196a2002101c0c0ea401d5208681e0041c0e07140180040d50820008109083e0607010301030400c001303450b080310690241c0c0000c641c80405080d91010b41c100310b0100e4240340d00949280c4190205440440b0102c219919004507100406542c2d01445030b04004170700c4038000f20fa1030301f00b1041c020350900110301c1c1c40740303a201c1000411100c01d400110080b1001080e0344c070b6030241d1800c89400752580040300c0d0b01c1d1369040c07024007030145810810340c400100003e1107541da801110700940c262100042c6188001072003600709281064000c84d5a40800001c001c01c002c00103284080c103400000440d00d400c00c02442405950340c0303040c00c4800c143c1d40310640e01030004110304141d5101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 279773758 1250 279772508 279772517
    0xf0a050a1b090815070203040b0c0f0102070b0601030f0501030206090d140a030e12010c050f090d050a03091703040e0105010305040c0e040c0501030606020c1e130f0506040e03040320041d0a03 84
    0x300d840c600322400e1204540750310058000b400300b00042e0b27800502504502840c1d8042d40c00300301000c01c50a00b241c000c0001643c4205c2444240410765805200703060b07100c11413040601047d030640d00440d03071034814401c61a02488400b00498180700c002c0e0034140720024214251410b2541340e0230010000b061003010700340300d1161001680d107401d1051080c40c02c88000c6440b40ca0510211981800d80c50b00310744442d0b50064207200c61a000640c0c00d0100d160742d9846a01c0b036013202403c0c0f1903a0080300140482c0c40045d039004000511104004c00d031454115102443c001c0b400340d5403441d0111801440f94001c1042e40d4841c8148000c0051160414003594020380e4100f050aa40300c82c1244d8405582075002d81140120711441d0400320018402a00c41d0806445440304488510700802202c0010b1100382086030703294107008181c41d250082039051204803006604140c219140c0d0422401c541002070b8a01e036950102c1750b810303255138120211140500410044000d04c0200c982d0300d80c8242e000c200c0005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 279775008 1250 279773758 279773773
    0xc0210120f0c020c19030605070e041401060306120c1806050d0b0610030c08070f0207080f011b0306061403060d0602070f05060604200c01020d09030215010504050f0a050a1b0908 78
    0x905002d0008030314045001c03038030020300c1e00d1507c4090081001610400c1084010b00244200e134842d070041d00180c001105041d413041d89080d2004048400303d81080340342c000e0500a00000c03540c82e60044090701e1074071341180021417026020030001c107890b41c0200e812402504070b060134002842c44643c0300740c5007560082038118610700c0860456442c00341c04404039a120f004900300910603002c1d0300d408100c40c0120368030b05440308070791441d28085c6520a85a41c0d1102d50035200028210310900c0c0700c41e824142809510b041c0032001e030801440201d01070a110300880000c1c143d135507500965400c80e405c64011540d60000c0d003004101e0740300c114400c5c4d4a522440011071511305091048116208211070b00c4811a203001c02600e030789a011801080281d9020700c2901104035141c814260014440d0300181044058034079800802101603014510484c0ba100401c9410010030b10238a03400382c0309603000141c0e681d820008100401c002c00320307051503c42c0b80a000d440ca613080001c440c00d540c03d0340304036101c1c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 279776258 1250 279775008 279775033
    0x90c03060e040609050c040e0a0c1d01050d0f02060f040611060903040605070507050301060609060906020c01020a0809030109150501050a09020f090f1206041b09020a0c0210120f0c02 80
    0xd86803188146614a404540040c01240c550350152201074818000d8480140046000a00b601d00700c2d207902d0880c0d04641050710802c04448070075001880003407a142d0603600b07145032044002505118050203001100412030400c01c20b2204110141d138024010f03034031071142d8014401d04d0703081802400e010400300034040c604c621002038034900c2003031840010f604d080d040400468498114000881d014410701e4400310f481d68003070080201504250307036002049071500200802c01f4080c1c1e8400020b541025070002c0c45640e0210f2000d00c0329402114896648040001090040c030124038042e1800e050039820203042a483d4000b503040700c504403240d4100f940c69039899000c80c41038243c0b40f01c05271801c0250100c40c4c10481c194907280a0010882a10f0098400340079080c01c004450440c0c0100074800c4080e0035854880600024241d048411818195803440c05410704200700b00107881600b030720402a50706446080c9507000002c075940701388072102070f8542e4440500041152034001d400b403032422940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 279777508 1250 279776258 279776261
    0x609080c03120a11030706020705010518070501050f040b0d150801020906031503010908030a091e051f0b030a0303150518161403070e03150105030d081f0f090c03 71
    0x120008001c0c0644250302d82c00c00d2851080d4060310341072041c403103507014101500c401030024201c498050f91001d613680c42186403143c01c41e030700282043c1e141007a41c0c256980302e02c4006154801c3d40d20a080095a801b0700781140140d90190303500c0361101c01d0700024084000401e64101030b0040601401c003400031038032098003900740e028110003a50000c0c0b06100141c1000c0030f40743d1030a5041009400010003001d6a00c40c031440ea8011030f4008065a2110424002c0052100b040315031a460301030304c10141c2d0003684d10a81c5800607003580e888032620b68820a481e81e1180d500ca405140002404ca404100c0e4600d0064054441d00f5084803200d03017189400074141c145500540c4425000c102c4005542daa11980c1c10350303506001c0000003c00400c0c140c5000140900b4009501421090300d8121080d0030740420145080140c0103103c1d4080445001006162000221102c1700d441c2d90078040303501d43e140d018004030004008a00118014414400545104d455000b00141c4603249428485480c2d80d170310540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 279778758 1250 279777508 279777523
    0x4120e06180d0809030102070f2a06050a02010e33070c0305130801020403030905130603050606060724052707140429030c030c09010e060105040b07060204060908 71
    0x1850903209000038601d850040e08000714103104402c0719041450600200b422030700f0800c02110310610041c03500301441303c000d6404108041d00200e0001e24844c4100c00d9038035650038401e01043c000c000c288080024000c1d007040701c0e5440382804031a03048903041d510400303c4140c0e050040302607100409030f07010455002c0d02030340725071880c0c1c885c2c11040c0a81d41d0f04480720750000070340a503081212240802c2d4103a0031700082c4002c40c041d941c1c10000504220400001e803510030342c0403d4651902e84200000f880c0480c0e6168001c00c221041c50b1240001d080400c00510198251070340701085002d412160861648824044c034172089a000c011060384a0f100300108001e10304100c00d60100304108540e4101c1d84680700f140700c0140c004600449400c0c00400c0041c94010a8205000200c03d104c00c2c5007802c00a0182c148011401000d10b184a00d010401d1820103005401e00407801c0000140c03943d014504a07001048103070402540c4100c10300780140250400d0180d0350000b058081e0000701b103000050900c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 279780008 1250 279778758 279778777
    0x50607030f06080a0f0311070906051008041113060b031801062106150b0313030e010219020906061e040f0b0c1c1b030e03060f09060109090f0b04120e06 67
    0x10081502c02d40c82d82011a004017500318200080d10520070505001444400020b090401010405605001c2040b81e140103c00c0d2074405c0002d43d07804c220100d10b404a00282e01d038020f0b9900040711090182c00000b40240c2c0d0004588500d0020a0009000303ea0348180c60b04801b940003006a182c642507000090b142c59100d21018540d03801d541004603009038400542d81005c1c14094265680d5500d001c40107800844941d44140c50108d0140d0506400c0340040d91020000d202500c0d00888411a10f07a540080d0880a4068080d000008005403101c400302c0e092000098451045100c5843e902c0c14140d02c180500048000220000240004038509945400c5400c0b80600954004004503590750048400040100b0041101d034440300302c802203d2442c1140290348026010108800340340c036080c0c024282440302c2c0c903c04208007020201154041c1901c61188011030800b8250410240c031a4241c00c0180241e15090305000400151003407802003c042a1680b44100c031010080142030b00650300e00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 279781258 1250 279780008 279780013
    0x16020601060e0112090302061608060a06030f0e011107050115030b0601030e1f0e010513020a0b0304060906060b03090c0301091e0206161112032d16050607030f0608 72
    0x1406498095141c006007850b042c94404403c10140d4060001d85100500990140e08814240044100400030035000e00d41103007000c40007410f02c4400304000300218440c0c8010143d071410608660a00c5421110021101c04024010403002d1320310394900d07a00512040350290b20b0088950f551040c1900040200c0f50045021090780e0740d96001900501403201c800c1d40c66000740100d0002c0340d03c07401e112058511244a0010707120104404041c211100034040c032807038a410710014bc00681c0c5480710a001d985034400015140c0d11285009c2c0e02804941c1001000c0034148403001c503e4140120185100d0709112041754034104400d0281800c9803400c003000303089503140c922003480003420101c100c1c070b4491015252510340040d200009001f910300c0002107404000c9022800280d240600ca00c408075050341d0041d51501e034000611900403000801e070341001d0300a440d9006400c00131401902d9400003225265000704001e46001500d85c1c0c0304030b4000e0042032401d03aa0000a44040c4034502c15036030f00500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 279782508 1250 279781258 279781261
    0x1060602070e0f010605160204111309050606040909150c0c020a050105120a02090d02040905070f0b03162a03090936050c0d060519050408030a09020a12030c020405160206 75
    0x8491b03c3d8411070001126140800388040141c8a0384a6060002800070301a9101d8030314030514100141c4070340c80440d62a041c2424400d00341d540804880845002400c001404e2800d403500c800183c10b52180501d0442c034024075500c07120741150603907102501c200c0b0050005a100c00064910340114011686246100d2001504510055000380034050300104080410301959001405a40c3d1000048850f50130040e0104070304100030340e24401800181e40b40781e09601c1c0090003421001c840d841741d5000c010303d80c483d02aaa41d40243d0a440701c240189034103009034110b060140601c20035201e01044185800300048044294010703403001d8460042c014840000542c40300900451603800039601030051300020849950740c0d10258201600c81c0201007001d2038501e26840100e5070650b0100081d6090004000004020f14110781e80914242d0000501c8a11070001c03580c80d0940b50000c22440b1008030940050540004d000001c20f48211018881d40c2d46a8080041054001002c0c20141e07104c0c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 279783758 1250 279782508 279782519
    0x14120a0e0c0301021303060e06061503041a131703090705010c06060924090908191101020307020f061e04030c0f0c091b0206010602210c0f01060602070e0f01 69
    0x108149811420901241d0005011400080c2240c0c8502c0103181c00681c06102002048024064a101140314030050445032402e01c01003040b915201040500100002000804014480269500c50703a0188401c0c2c2c581e24000c0100035880d00e03144c800f5500310124403480b542e140305030800c0340c0c80303940c0700c1c00507240c07440c1780c5001980c041d1842941200d51584404011800700b04502c640c04015002c6d00300c102803011b03540c2c0100b403802e400c1e410151034141442240e00214200b0310484041440c900c4840c0e07210041f10310115858204040c848149500003c01c0c40040c540c0001c080e4203501201041c0c803001e4032207040f003446c8002080041c0e421500300c0c000040200740150481140c503405000d645404d18265518201c1c05011900501e4a0560703c02d50810080079050359000a80414001442c4135414080040e54a402ca9004012440c820480840002a150054030060701480f000c9505c80c4880380c4006002c0c241c01d0140c1c1d0010f1044400c00034130366203108101400303104840802d95042c0d0801c0d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 279785008 1250 279783758 279783761
    0x1a04050c0d0503091504060f05040f050625080903070e1605030c07050106080304030c120b0c0c030f0d060e0f040b0f06010c02060307020d11070332160614120a 70
    0xd80700ba0106220301000d586138080b42e280c1c424801c0f41103a40e601e0500c8005030001a07007260203c00c201c410b00c403c3c004201200c44c42000d0f120103d8042e52191030071100320794480310b45000c0740550351100c42d00e00100030140002e0f03c0d90740e41c1241035034156a100c40420b80c0203401110001c61130640c159605c03e00d140618010b5402101801595103000503d07221142504d806d03610012255100207002c000344030360381d0b4801c8040c003101001820748048130703140c0c81c1d5603902c00b40c4516581580020f2601310b8101c1001140c19100d480c2c40f01d151a00000144e401c0100800e00c10100d1001003c1c000400503107090303031840d03c255440030f009001070f01d401103c841160700081403076040c042c00700c100c400540ea81d480514400d224503802440d01c80390340c8000070402c0000099041c0c4507484914284000340351340c1080f44403001400140c40c106c0000c0c4034a40c2c0b5050b0103180440d250700030800c16002071007144400e00c00399a52625801603002800251007004d12031f0009417a9070035000000320704000400d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 279786258 1250 279785008 279785029
    0x903030b03010615020303040b061507031806030b1e01030605150904050c16030305060f090c0a02010b010f02151b030c070b0c0304020a18060b0d020a09091505091806010306091a04050c 81
    0x90a04c050018628030bc00c84147e01050056003c100000e98007070301244c05584d444064116840c0c01d10080003400003007551030a040e00c49905414160309501005c0e4403d44c0010000d0100810940c03030403c01c04040100741e07101c016201d0140d81800c1c0000e180d101c04900f1101c203e1882003260050312590b4604038010308001d008140c1c084000401c0300442d5590304005c0b03014020300c500079645c0d071041440181c212405000c05034137100600905114064010940c01423941820700700d102107a03580c01080788401d000c4036941400c80c03404000d00c503d1107031400251048912404143c505621351140344442c070b0108483c029402460494140583d0a0440d800e0318032010400001c2400c80d21003421010903040081071413101742d8082040030fa02540245410001c0c0a2030070204040b000c0030b1000100050320340944d174010361820000c500f030555001c440580c00c544403015682c107940c40c0d2508001412041c0001d5821422155104103044000e000150240354040010240aa8000b00f400100d504 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 279787508 1250 279786258 279786271
    0x20f06150907051204030e0415030b0c130b04060e0a0902030405030702010f050c0109051b0402040b0405060a020319030c0905030d08040204051302030f060406060b120a1508010903030b03010615020303040b 90
    0x44c003100101c02c003000790b21401584683c1700e0351015051a4144021580000c1c0c00c003146001c103000800c041000703c01d90a8000300c00c2580245e5034031710036007080c400746100e0b4401c01d095540064006003441c1e101100081aa0f41101d0100232203070707940500c500360f0100b41e0b80904150020030100c40150b0140003210f444d003c650500c03504091600b0107003402c6480b100070a55898005002031203076016040518414407030125006c60406042400a80386801a400f0b51341c080e450020701d014400340204151000714050030440502003c016400a0103008660300034400b203000201c01203024600401c01c6011407846990340d124980e103503000c002c050310b0301404054031601d258642c1000f5880034440722041500d00001800907040501c0c01c40c0866084c4d038044616003000b030003240d90089000076050307044000000c0109000500401c1428194942d030300c01f000710761901e5815020550983c001e084000d808900821480380d48030908050303219410818001a001000000e0002d640070700042e40054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 279788758 1250 279787508 279787517
    0x1603050f4b0105040302010c03110904050c090a1508010b0a231903060e0f0405070e06060f030109091b05010f030f11040816060309021c05010b091303020f06150907 72
    0x710564414a200c80100340740c090b5111004c000c18503809004481c1d20200710328040010039020f49415105010761300360113110319120030108089010354070650b20814002400460702e00e030340b58151101c0f500003848110100301c9003000003030422409015154803540c0342e2680e0000904641003418a140760f5604001d850030280110301c0035046882c0311411820258800040700b50400312001d9852200820b41e8590288120030440000d002003000342c100c0d062510b180445490725000030b140741c0203009452828040210001074a005c50390850005640100c01a40000d00395205510020019008040c0401c000c80d010510b9540f095001c80c481d0402c5c1030000170038100712000b00d240c42c3d20a5100d494664440e817280800102104013000003000d45090401404a0356404030b02000e100680b1041c0d004110f0400070f081c0b0100f90480c000da080014404201ca1030024680c240d0002e4810054006216a00d07060445000000d4001d008100f1180d50480c50343d460f004110400000400010410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 279790008 1250 279788758 279788863
    0x30605060109081e12030124020f16030b0a09030807180f0603020a1803030e010509060c150a0606020313090b011803110915010c1101111603050f 64
    0xc4041c4050139040c40c1a00070643c901e14240700729460400300515101c00740004000410400507003521074680740b404d03040713441d200041d5103200740e040c03107104078580005008083c9100200b4980ca681c01c02030700d03c0341e22554070039111194800c084429070100107000c20000d9001c00c0896001d600841241c95001c0100386200f92103021414901c40140d0009000c02d8001c185c500072207805c98120301e184c04006598500320f07460f545004108451084400d81030040015001c5000d0b203030802115202c4007a482180d0b40d81d40301051810415804440b03a50189182ca0f4000c181e0f140b011089841c0b46182031455901542001106002850321660643c14050101001100c08100c4074240c4011401a95a18264403d1005200b01500c00034580e95095150846040451b0707040100031909940110355034007001140c50059420031030004015805204121070380300c140714011498015a80f0450a91ba1250307802c945d031a5480c904048140072400800500000815204402a500540c90340c40b00088 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 279791258 1250 279790008 279790019
    0x1f030f0803060a05030d020a06021305091017010b0a051003020c07060507030f0507020d03030e010b060c1f0c050f0d1d01140c0421060f110d0e1501030605060109 71
    0x111000140840d0300240200400c030303071842c10740f030a60002d140a9000d0211040040f6000703480b074610100c010b0a0a60118500e504000c0a1131188081d14000d0444201c038140414501034140b06031080e01c1144480c0030004510860601070912102005272419102600f080700300890300c400c2e54441802c141c1c0c20302140c9a021420001354004044549800382d030340450b401d0081c4089881d0f1154011f004082084070010789480c059802c08507003510780095012078501285000d001e82469480e88071402294040031510041480c001141c038a81310314602100b035841c0001620391010074080811824082301c480340700650001c4c42600460b520000d01d0101440603645e04003006c0305103003d969900c00e1000300700201040ca09403c4003843d41e030030341803500c0c5c140c14510640707049603440a1444c00d03103800703003c01035560040e190712004c1e40e03410300174520350496000a6412294200440030308182550a0080e00031902d448018030200c4010f44603070858580d00c0190001400050420121050001d031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 279792508 1250 279791258 279791273
    0x41508040f0804151209150e2109010314060a0302090915010e07030507230c0a0f030309120c021c0218070201050a060504050c090f0d06090501020316030507081f03 72
    0x3601d500004d1542061444100808501604080407032203441c1003038500214002d1001c0900007007030740d0b40102d060864101c801d03007005142c03044413658115014081c41540d4641300500341c140c07400ea07401c02c8040e01900e2030350044001a64040e420450301c1c102440581040d654841d4006404000c40303104683c4109400d801d43d000343e0001850744a80c3d0300f4860300b90340c14018642c110390720745400c0c24070004010103002da10500f280f02d02540040000c2c461102c001c140300c689030302500f000c1c80c01003499140c1400b4000c0c19030038404642009400840e40d081501603292440c0c0541c0150180340454008180029500c05020701aa4007124004141440c802c0482ea41c0348924106e90002c0f8103070030304140e0381041c2c803466003101b0b124a0420042020400e2000c0c140d82c46800220b802c44044074408001c00d8a9115690014040c1414420350704203011054000f1130049005924050405c10600790403000c840e0150740035000110702c1d201146100e00d400380f20f00c0400041c0d400d2100001d649584602 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 279793758 1250 279792508 279792517
    0x40f080307030c030b010c0203060f060d0804080f010b1504180b060304050a02090a14130303061a090a0f030206090d0302030c0114061009060215070c1421041508040f08 74
    0x10020343c480f040c8050b450b605009880c0449404c1c01d1110001119a0000b9187d072001400310502e4505040020203550f14254609101c0d034000303544035915501c600301380e80c85611a075140400741d0300b0140c0002c4642448043c1b55540d0250314880d0303003014180581d64a82c04868401011919103c3c80c284003030355200300c021401244a940141600041c600c1441610f280003070540410601e0708003c115158045500340e0341c4041c020358078640445030f42c582600148000d400007400c0003c1409078074070800c0e40d80300501185030204ca0107140e042c2e0b00c04614541802500000790800030920082c2198240710341a001c1c0d8034441e0050303a003403922002c1d501e800c541001b03d41d508013111840600c60b103030400d41c2002c01940759600d40b01c1d48035414058041e580d01605c01d498a0005000350005840c030f03109170003c140c030a510059180070850340300c0220b80d5841050b418032070400510201c2c0c464a00144007250102c1c2d004159101c00f032050b41c0001d603042032004102361075540e03d130600c68002485290060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 279795008 1250 279793758 279793771
    0x60e0606041409190c0807170111030705040308070f150911030c0907050a020703020306182b050d0906050408040e090f0723031203090c0303070c03020108040f0803 72
    0x5121500d825810841900c400300d040580c030708244803c2c41602c40300401c04641407125240c96085800c41c0340790100138881c4030350295105001e100c3d00414003444c0c110400040d071001000070f1103024401d60f03400302103220030745a80001c03c100b00010000944000064242075005600c9119220455261000c66407109100d5610390360b5a09650800c00444011944008000b82c00038456a0105004280c0002016081100344440071617180003061080292102855003d4107861144c2084400d11140071000c1030003070418060b8500000303660000220262001c022a0320040d0b81c0d2207560402c0c0d610f43d115504980700302d500d80b20f400c404030324036001d858001d51103012140d9642e841d00112000601c0080e003d42129009080f11402c54a00012020b041d6441c0003c40c48201052403044440b54012801441e0140601c081148200501c3c0010b14031903800300701528103500112007015124410440d00800142001c1401d00155201e0104a60302901c0340342c2c42c46d00d0044940b5800083c0c0c204803400d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 279796258 1250 279795008 279795013
    0xd0609020d110301230d20010f210e0312010f06170c040e0a0b090f0a06050102070605180126040203070501080f040b19020705071d04081213060e 64
    0x4076024140d4030030b400b401441104200d085504001c414400041c0c50040d000c500980744101040507aa10240f00c10400d0340410703a1461440c0202400001056001001e0b01041c030241e16903021030b0041030124007540c44444400c62350240034145030028032a404403032000e403106110520403004c51650283c0a04040c2003004103092500400030840c400102c2130384c10001900040c0b09060819400b40d905440c100c0680040c03030f41d224114080105010000305074490030030024881142c25181c4014003801c085401403000390745907401a1b035200d041380f0030702c40000c200b0000d800c03203075004044190b40d0328014504400030307103100c4c1920302c2c900342c90040301a5440c55000038402103180030400203008110a00b0204d050b4a011a50282c0800c0002d10140607140008002a01901c200981c10a42070001e0811034843c0d4050030110750302c09850144801d040024526001e030b444021418612503540802a245040301d4041344400b5864003410781c500d94151000b02000084050050300c5241350041c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 279797508 1250 279796258 279796267
    0x1b210103050610050102030a0f0509090408181c03030f0e1f06080118060504062408060c070c171014070305060103090c05010e06160b06010f080108210d060902 70
    0x500c1c0b400e10700c002d801d4150242420408200a9030084141c604164440c1080d0300c0001c2380035401d45140c4a04040c0729030064038001003004001c1403501030440c1000c800350031040b00038101b00b03200c0b001c01c5030012040944040c41203100001d11a4009000045030035801190482a030700b40306240c05502070008503000001e0600e0803d5417514801c0e000101141c10007444401694801040d140d200c40c000548960f1303c4200203014003009070001d0001090000d00018103024035616850207000f00d002d40c00c2c0c20700544022030040000034054a103519003240c07075035613150302c0e0420b000034100d83d514410f0241d0080380d682000c200400c2c0b2130345e0400441c18078003d25a04d04108004c040311030080c01907040c54642a550800b1642c90484142610428249003000785400c200082f0240030741e52005000d07803c0c65040078108404065164065102038a4030102002c1c80c60b029500c20909024154841c0d01c41c5261a92881c0f01440365045082e1101e080b071314250081824506480064204082d02600086c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 279798758 1250 279797508 279797513
    0x50702031207140301030201030218100306051017010e04030903060e010f0516170a0603050a0f03170c0d181b06110714100201020f130504051006081b210103 69
    0xc15150700001c2d92602c040114503140c62110240010302010741015400b0443c121440c1101c9100d4001d254002c24003c5900c01803e03000300580303681c0c0251760048540c42c52410703900d8001d8084541c0d040703030300c8083c900903801c14490042d07030f42d4003c20540c10440480000000315900b8446c4140e40300c4440c001050041d0000c074000180e50024004001c410300140c50041481d6200600c55081005811000516105d02d9010310180c05141c00c0a0301e035000381c40e401c404010250084642aa2103522650343e0000205010020914116405018504200184203507248164000c83c54001841007181d4500c085032201501c0860f2a1003641c0c600c5c0d4816420303c0000e420a0002200d481004000c02506041c80c2d43c9402c070f0302440c0d405500034040f4107080310703030b00d4000c0d015034442c5280004165211030083c42c42e54406022803191501642c68a008541d8032803a00d0308407030503a4040d885200e030644940d61050109681c4401446105500b03100400310000409594101c0d2001c1c409601c1182d411030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 279800008 1250 279798758 279798787
    0x200301050a0e0906040201080702011e09140c060a140f19090503120a14041d0f07140a180e1003051c02070303080a060305030412120908070b180405070203 68
    0x7600001c400c82d000008102102000080340d0380c3c080d078286458141a100d00005a0252039481c100142d0b104040d10310a0051180b68000c0607118014a2020700b03141080031001c1d2036004071008141c01c80c008029014409008480700111203000080302031618520318404070103900b00d0010070b0011808100442c1c070300c9501600d1900603040403009080d80d2047d1075044074003486690100d40611141c071b005280b850104031306490041460103821903610400c046415072081007103c4d40e0607002c0c100c0d40440c13822032140c501c2c00b143c01181c650542c07406074905025684951405082c1d41c0c0120b040c600845d0200721a01d00c580601181c0c690b1001e418203520b0840c3c1404007400c4000360710b8211000350384216a001505404613038250500001c90381f11402441d0103800c654001030981d100018000503510000301c0802040340c02200700d070b19030b50301295040312803e04600c01c1019650110800780000314018004040c44d0a10402d4a80ca648407440418141c441c04c036802005600041041580007841 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 279801258 1250 279800008 279800029
    0xc03071d1f030b1027030206030915070f0215180115051003090203030906070212190201080f100e07031e090c120c030305030402040b091008010f0e0a0f0620030105 72
    0x480710311400c03415035140201210b00d918040a507801140f1800c404207906405c0b020041c5401910f15640da1401c5440f2507580c502e46440320000040c2c00b030001e18007d01c5011101010501507020f004003d414410148072483d000d8a0070402d11440c440e0000b14540034490f080984803c8900001c0c4103240c48100300004036244005018103080000300303030050f6400300c00ca8614200c1220219126a0320b4004a80384000404001c4458032a0a03030787c2901c01c1d062020034180601c00d80c0c0e8101c441d5100203000ca4855000d803804c40c0d100c01071081c01d2200c843e2540140380c0c007801c0d503e0002104510044c800892455401c541030003159240c042900f48030807192100090142d118241c1d0445410341c1d1101704c0190303584070260401c540440030404540d00c1d60010010341070014049001410511040c1503c1d082902c00ca40f04c0b503103000280e1045142d03d00440036800c40308005042c2c00d08180d15070480030b00030300c0005c559081d0765080e02510146841d900341a46d0a2041e5803680701c0d810b000c00e00203440c48 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 279802508 1250 279801258 279801281
    0x15030c2109050d0306081009030c08031003020f010c0b0a11130b03060a09060b0711010e041e1406030c0d06060f0609060e180a0216050d050702040f050c03071d1f03 72
    0x14454240880d010000b1f40440480703031000001090501818211402e50984500400041c4000240007440740d580e245c0c801528000c84501469070300702c0c2c006503030b40146004000c00f861100340020713620001d1588003055100c81007203014640b444039000a030345c549451b003200c0b51500c0c2c08000d12482d41410a982c2028205000301041541e0600541401a0044d01c200504000c034520009010764031034110b0344140702c00504240020070341d8900d17101981c06000c3e040100103180424220324850b1041040d03006920181c0a8000100b51205214007000c4401043e25032981b02c050003e44c2c200a003080100814459030b904c61803505102000b807c0113500a60640f054000082d048444102614069000f6032004c1c1c00503550809040e21442c050010240508240102d04e401034441d43c00c10300502c5900d208076010007408118061503801c82e43c054580400c05030381440014100c0b80911489079010a003122102901500b9000003403200c0b6061040611b1040307896000f140090b00b5014081c1c0031071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 279803758 1250 279802508 279802511
    0xa05041d0603071a04080d030207020f011707030e01110a020705090a1a011b02040606120605030304030f020909030408060118050c16080d060905010308180a15030c2109050d03 77
    0x200800041c0e0f4400842c09001c41c80c030982c42c030075420f60b41482c0868008040e20019110800162000038000b034000c05403c1c0d0003601046003101a56201e074801040c0b020150209140503221004100c0c020044481c040d20f5640d65109400043c03640c1c4005044000703401c4c0c1c01054864103140920020a40107031000d4401401c1012084440382500d00c982038246017131a050160023007103203411680108070000a5001803074a01c2c00715038568007003090403150000c42005d00031956075409059403403140344000743c1982070408003480149050303600980c120b410a030460b41020f03181c40c0d400782409801e074009003034103940d180c604506548600032694002d407400310382d600f440303070030415500b8100aa0000400c0c01c5e90000d40c01001a42d00c1d40008050f20f40343c0010000b568480c90429220f500015800456401d582a8070a084c5046030107003043e1010341c0708060307004c00750070707030540c003608a18402e801800000c80c0c0004510b0b291030041000c0141c085004180072440e030401c1e5040c003240310100c20405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 279805008 1250 279803758 279803761
    0x509150a030f0509300d0902010e0909010b0118081c2a06050c0304020108041211030a050702031b0607170403020907020c0108090601050d26031f141c0302010e030a05041d 75
    0x40409a081d03604541003002e011420b0720048c4010ac60584c00d18121540c05201d0006001c81c01c00158884003044c038003030303c5e20050403045540d00500001540f0500c041640481b240d09031106c2400ba110040e88400d08040c0c030b4040b043c400103606414004c40c80700c210550311a81d0700c10300c00715020301600040d00e01401032541c20181c000030201c2c04010b1024140342c03001812030035103902c04d0201480b05d04001381071700c3e1543c100040c020100c1d40f00f0003080c0e110740328075814556400340c51003002c45d228000030040c03403510b031300365507409481d00c46811030380344000080c000000503881d102d050b54450402940904070080f00d120014000b030001604034a91035000307100601194441101c0280300c40e030401d5034850460310540000700044401581c0300c8409c040401400080c045030210701c15070b050f00c000100010b5448040030700c0340300010003046174403649c4152089581e4261407001e2640328040d1001041d4030b501c0806103840c542c032915a46000400000f801c00c4280194414003600040185240849 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 279806258 1250 279805008 279805093
    0x90b0603010902220f05030c03070b09190b0a09091a0102071206020403050123150a1211040507080a11160206250302010207120509150a030f0509 64
    0xd0005010740c801d40380c0e0014060804040c0d1307031455102e02101c14816894242c9649401a02840501c01ca070b001c4c0c4620f007000d070b9442c5400300b4404203548440300c16600f071240b103000b00315901c08850910302c06007928040100c0c120007403600600d008190340d03c0d15180759160400a80c1190b00c1c581805a40d100e842040d140c0c50703070b40407409004840160021406403507090828600904c5190302c020042d40c64003210203070802c50881c51000502c035a40b6075280c6d555402400c800c00d201c102d0b038101e0784890156414081e42041c00460350f0003a000f1040780c1500604880401c080f100e00303840f100c002c100140104124142c081c0030365514141690002820309401210415203403a0b0000000d1081a01003000065a10000600b004462407600c5003d00902c050a01034000d5100650559107040307240307041c0d4a441c0c0218115005001c018048141d40405400031242d01e0308482d00c3c40c003c040d2203000f01e401d02c0d0300c2401158080e003030441c0078040d8900311341d0b10600c0082c55151044c0d00a810305a80925 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 279807508 1250 279806258 279806269
    0x130f150c021810050901090c020606060a020d05070312050a0501031b06020c040b0301020f041202011206060503040201140c070801020c0105010e1b0309070314011b0e0a090f0906020a05070309090b 86
    0x42c004010200540305864140d403800b41c950180d00110381282048000207520703203103a04103446440154080c1d4049480f24002d100c9244120100040964004041c1201d2148103030000c000e090301030314081c4c01e4081006000025100140c4041c4035141d121320060051040c0001c01800c040031407005d00d2a25443c111001c2c2d12220640215407056944036484140364031300790100d078581480c0407005665184c851010f40e6039a1407804040e400540d03101000707082d80c0d40310311400c010380d2120349a46041d903541d940115280c0c4141030a40d03012800500007941e04c2d0300100540303006401ca4100150b03d030340800f001d01d402c440c07050b80013a401d2001d003424002c071111a1200c0d503000c51041c0380d68583d217070744103142545403031100d500007010049921041d042c81c0c10107520103801022040d150815139520008101c5600110b014600e5210103024020401010035520100c080d4689641c0031441a200351510400c9810901c402004100001191402c066000c0c183c0c5005e0400840c0070491011208007050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 279808758 1250 279807508 279807529
    0x2a1202130f05370f0204050414071106010302060f0a020f1b13050c030117070f060c0516060f20030c03041e1a070302011503050c040b0616030c08130f150c02 69
    0x40f91135452000441072461a01120042c0c0f83c003a2040c071520301418060f50790850101ca0007070002c1e40040301240b403c40c0105d007003030490b134000f0021418100180102c0030b06920145503030095101e40405410802e000f4001c0754400c400392100314001c40142c7c800d11464030010b100015005207070108001200f041d94040d281900e14200c000c01501c0f010f001d40c0e52414503550041224410788600000301300742c0c03108442528900c5141a11014030b50f0003081c000303524880c0164000304e0f182e4591080c2880c8104080c9115801100010810039500c2503558159440000e044805800018080c044030321044100b048003062030720030260443c0780051090002500c0c50b80140d0038600001c2000c1414070035041b15100440700e0021501c02c2d41c1c0c901c1c2c1b840d03490350001101c80c001d0303060aa01501c103142850646070202940d030600144264550b0b4101c44080c620b010444501005201c1c890751b1030f0000d090b00007e40b035400120040242004114060407850316001010800740552400040c4c40765140b04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 279810008 1250 279808758 279808861
    0xd030b0a1a2a06060a140108010b030a140a050f091606030c0e03010216020f060a0c17041205010b0301060e06030a0308100812072a1202130f05 63
    0x60382c6400308000a03100001540054205580041241d4114440089003031406070104584141e592079071a042c1c000301200100000340841c407032000401c00807084800841e8040e4140d0340020b014a01f00100080051050300c4422040d03aa50b03080140a0b41001002074011005900030009803c1c1204c21800c0c00c480c5004941c00c050311688207410300ca028050400700c40d00300500964440c201410320500c181034a0070140e200d007204500c00c40c614200b01c412100444810307610075108010300e031992005d01c202015441d290303402c1000000784a07004a0400c01036688104004180680110101400d45100b60811500b06045d001481540e5a0005602501580c10304003081e29690340d6032540c242003015800308825000e1507403402c000f01c06210050640c035210314000c800010100300400c2000c500202d070890030b01c90a220a01400046418400102d8030050600c507468610b0110a415110107800b80344c101e41d00d60040c803c0300c49100900d403a20f07018940c2c1051504002e24444042920200c201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 279811258 1250 279810008 279810059
    0x6080708030f090103020910080f180d0e0d060213080c030102041401030902030f1e1606020c0d1704140f1008060409050703020d050f0d09031502160c06020d030b0a 72
    0x3c42182d003e50190780034900d000f4820200340c641ca03030340a00180b000301c440300d20502106000488c0c0d1100b20020712a00c0740514001c110100c6081c0e415103400c04200700c143c0d801035858542400240450008140320b40f44c6074288604245046040c030700d01a04c02c0a00d510076401808248039000c3c1e840d40f1052148402d00c0d01146902c1785002081c1001074005c1d98450b01d004e0840000955000c01120b02407007942082119440c0102c1441c0c0b031840e036060b00034000140c100e10300744601e6213801d048803017506000342c000b4a1500003090000c81142d2266020500c05010031248641d41e1510413031001040d441130301c3c0d104280525120041c10107600a2500744655543c241107000d00804101032006583d010304400c1c0030160b14142a5035030044d86010030312900c150500f102806218056510840e5801440903102e010003141080103034100d1040a5505444070041e040490380c031400c82030040c4601d8002e05110040d642005050301d49407440c00d401580c60000411007100044002400455540719 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 279812508 1250 279811258 279811267
    0x302090118121112010906230c0f070812040309050f0409030806090a020c0f010506040b060a140a0e13050916031109060102010207080c060609010f14040903140f090406080708030f 79
    0xe4412070103620021300313986802141c00400c10964000c2c52000800c08940c11004c0c542043c1200104c41250b80246104043c4007030152265240041c0060307d205502140c1050400452141c9500080f5402d83c009801e490040002c1d08200700d800841b100156014010b40c0c00d41d80b00038101d643d01404c901d0141c0303c6070001400d02d0520f0760590704088610820b403030140d4a20300090340600000d9840034851403500207181c0807464450220344842d2010703201c18000f402001d00301a8950081c903109000d110034404240e0351640c8080e020650b2481e4882c1c00641414541403140c50402e00c0448a410450001c030300340049044151802d403689802c0340d0350380083c1c1e207403c0100d000e030145003001050a800444d010340352070310106803d03106000588021101d41c0e178941944140c411588110710703c4540703e0400b01981d06150300031440c450301904101c0302140c03029010200540c404011032054410106001500d4a428080c0e90010030f0804010040035090451961322442165491341c080c05c1c0005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 279813758 1250 279812508 279812543
    0xa02100504051005040302041107020102060f0402150408010e0601050319060b1306030b01080d08070504031e05030a020c09010b04080d0503041a01140907020a170901030e0d030209011812 82
    0x600301d80140401601c411055010484090201c1d04180002c81c071580c01c002200c0361071075100b03056070020780e01640240220f48401100141c55030015200303a030400821005141e07845044c07401400246000c6000044051341c180f0400d0402c1c6042e00254070a400040103030b00000400b0002d0401e140c1c000e07000280e040038500005210300c4600b9030700c104980c1042c40004c2030000b5104424100e480c0d4009680c0c0d50f4160100844511904845140c081602440140042500b036041201c420f0311103c00004403040c0303a10b600d495a00060320240c0140e0081c0d8000c0c14074101a1a15030060170303d41c002030700b8141000502903d41c01c1501c0c3c288200f000200000341408095483d0902c10000c0d100c1d0800c81e96140c240c1000030701410301c0c1a80c0641114004a11403034400241052840d0b0090401ca4803850398614101c11a030005444034101911544c0007083d514050141d461109241d0700d0050b40ca00302d0701c0000d4040c080e00c6025407407002d42c1380742c204100b2a806004260701a403040d0390711461103141c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 279815008 1250 279813758 279813767
    0x9090f042f0d030c0b090d05030103060e01140a050115020c06071e17130b03190e10020309070e01050618040c0c1a0f01140d06151d0712020c0a0210 65
    0x4403501d6070006164201d541815000340303a460300b150044034101e02c1640d62169003607460081c00c24400004408000400105a49071701201ea0300000c40004907000000c0c0301001c1030035130245c501600207030747c5500410019800e04009080c40c00c460000c1c080145c1110300140c00d60081080180114107851196541c1018000a800001c1e6222f51507040f07100302d0800044d500d40028a010415841c5160085500e001500c20780c0e200740c0c03105449035480500c40040340c0182c88641c0241216108207424600c40454074005903228480d440000c00301540b4080c0d85002804040c0c0c01503018a904000d40c5111300042448054a502e0641f000314400084070012211000002c901506082041d540c03560aa440c07030f0000c6004000c000c61f840c5099880f0540102c00216014196901a007145408800280c1d03076080826580c460140d049491a40c03400c1ca550403c05001043e480c040606040201c4150040006803805810706021820301d004881e40300e907140d21810001e03124500e00350480422a108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 279816258 1250 279815008 279815093
    0x405070305031902150402060702041a18060f06090102191e080a0201050a020c28020303280305070c030e0301110d060305150403090303140c03070809090f04 69
    0x1c4212075031010030f0f1071040d40c10282103035004014014116164005000010750300d0003140c0040c802c6182c50345a60801c0020103140b00481080c04508100c0440742e0b60303420305220b1218481030a8021850813004000e0820100d0030100d00c6140b041c03000d2809030340d0000b03a84801d0018480400420012350030056803841a122010301c884c1118440b90041041d2072000d440080e040d50002c2c091a00d0f907030b500600740e000388401c202c03141e80201a5413040d11413000c9092084072110044c489481e02c5a0041703130940e40304004ea20f003c0301d0090175210305007407010b44c40c0500c00f081d85010040c500300140018600d401d10074015007000001d4151200780d503400c0d840040c00341e04141c0c3c1c031650385041d148414003802c80b0344010784140c0100102407a010700120010b600c141da0590b6504821400c0d550192071520720740d640080c03200c01c113021031302250f0350400c02005043e028110a60700c0c0c00d130800070850021001850680c1021507441403000203070003d040341d00000140f10618205007070958658030005071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 279817508 1250 279816258 279816263
    0x170a020a12030c02010b0904170901050d0c0809120c060402090a1401030c06020d022d070e040807140115090c050d0911030d0914060d06030501050f0f16140304050703 73
    0x14a500c1c0031259400d980a00c240c54402c1c1c00078031241d50045d0410150010444015101081da0600030f00910a124001d210781041410140d082884001d41d08003110f5443d44a500401d0303c5805000007404204050780760300f0380800e000703071074803084011050321030310082d2000303000701a03032400f0543d030041320342129020b44050515200c4541c1e40e41003168002c5102d00c40c600240c028030702488540361000c20140094102c282c0f00c002c45420150440c02e1102c80b000c82c58035070380a807200c0030a52908901c40b05001d01c1c0100c3c2045d84500701c2d820941071501c050b0002c01c40c9031303242000320706a0540307003032002d01107a0403290001001d442403036082c2c0b240d11802d841060581d1402200303800700203019111a0198406600f00c9008030240e00f4203035665400f500520284115a44d441c035440d281601c001c040350100d0b0701c4045560f660700d6440f83d09444082c2e903030040351415001084040511840e049038402c941284040351540900d1020780f8580c0103101c0b030041c1001c0000040d06000702007008000555 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 279818758 1250 279817508 279817523
    0x80d0c090918031b0c03200a03110310020901020a060f1112090606010e09011a0d020f030603010c0f0507020d020312120a0e0c0a05060a02011401060f12020304170a020a 74
    0x1018994091400b90030150440109a0310503070002e00f50058190040c050f0782c800d0704d69201d01d0a58490380c5010a501e02d0380d40d2800c04031221914a038480490900086100c2d91b81d9003c8540560201401d1000c040c21030503000384140248a881d80e0300140c0d81d01c83c2070f0858000190741510445010151038000300d80c03240d004001a90003074855210b06014411000074058540517296103004644140e6a2410158401c000c003005002034211000c41c1c8025503884008039180803003a0824900340d03045108845c60502d804000c00116040038010303031850315483d02e800304030903460780800380541c01001c1e40a4019103640c0c500342c00f1074404001440724024882c01194460344090b00032580c41c034040303850001c01d90904004807140400001d0f08200031200170b2102c1c51403401c2c0414420b5541140350792004640d01d8448060109000c605c0d21b42c060000790f03640c00600c980c0904040c049995000101c1c100340e10410400012550f03800c480080032000d1329909030f0300d02e03144000700e00e0003101900142017074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 279820008 1250 279818758 279818771
    0x122f01080a1d010c021609050c0304021201090f0f050d0809060c1b03040e1806010b1603030b040c1e2a05070306050a0615050306010c0305091206011211030703080d0c0909 75
    0x385c002801445550003c02e805a205443d01c02142c00ea4200307940c16042c1a405101140051400980405241d1645800011051219280c00c211120340d40402e4070319200e15545c6805018080c03101d400c90f0ba070307207040901c03180c2450030040d559044002c0c0f801007846004605000c0c0a43c100350000c50549950007100e8540c0d803150b0300400701041c250352076100e03054400704003001c7c020301203213440c101c07600c007080141050382c0302c480a203840c020100106e0405564910320316a036079880c41140101c1c40700380d560030202036299150703d0700240101d8047e8144071404504000e191950007a2148240517001e101a10050318a842c500e030611582004081c58100340c10014a81202e45c001300851700c00d1641115a60301148d0140da240c8810b5a0301030020b029441c800c00464044c030000d240d454805048000d9080c01c4c1100141400404e17000910b02d29906242d050602c20168400103090304120f0207051214a0741ea00c40c951486003d030760406131038542100000150040c80703000010b1510340c100f4802e2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 279821258 1250 279820008 279820031
    0xe0306040c09060518060904080910030f1d060c0a05120c0a030f110313020310060914160f030519050103052a0d0813122f01080a1d01 59
    0x75001c2500461050034030340030000a0510344015048000c0c1da204907414107680700c620610850b448014015214034004001c581d00c2500c80002198407c070b01030307400007090703072155044900b510210071100b0225612424104400b0502203003240d008204883c0d055540d41c40b40800b514507024400342e00c01c06840c804104a0f00700c000c20014880100940d8040102c2003002c01810102d640410345c09080800600019008005044030914200d00040444650b1049501600259040ca40180e10441d40f00d0444194a5150000c041d404ca8400540c2855407103400b05d00404005011084804261f21003000c0740703d00391404607910060800310307002e011700d42c1c5a0804a6580c002c40c80d06000341004c96980801e104400b10b08180040001881089070940d25143d8140b150000c0315070f050800241200000e801e220042020f10580c461000b0a030380c0c81000b000141d0086004a050560030012010350f00607a82c00b454040d0f2018442d00001140326140041c00f243c2513013020508403940c41c1c00e680110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 279822508 1250 279821258 279821273
    0xf05030d052125080717071106072c03151e0106050a0809060f010b0c011b030506120f0d0c03180e0a1107120c02060d0f02030103020103050f070c030e010e030604 71
    0x401e41100a81c2030503220303403c0402c030340c1c00e1000c0b654100044e00f80298010b003005880380c0550885000c0c5400c1401c0d1010300d640c02e0070213a0903214a800300c0d0040510035016842d00d40c004014402c00311800762141201e40100380c072001c081503603988000b030250001e40000352810507040c0304041c10691400568407440c000d401c90348103985020101d1410000a25101000501d4522031100710000d405c0e1039181c51805240398128001100b030395500c5880c1051880c062000e040d20b011010380d008501404c0500901003a6000d030b03e5001c4041d0840c583d400f10100300060b07240041540c615204107020402e0030301b120440351420751544001e01982000840c88010000103010340343c4510b04002c151260003002d40c562140110003401c42e4803c0c039507050441d02420110090700d001804540c90401c0120300d400c01c9480c4c2d0b06201d040700d507000c0014015940c1c1031151913444001a040841541064040545400401c000050420106491150b0139034401c500d04a0305036000b8003143d03e541018a407180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 279823758 1250 279822508 279822541
    0x803070320090307051908060f060a0e0f040b041e12020c01030e06130303020f041206060906060e15090613050f0607021822060203100f05030d0521 65
    0x1074a1a50405215403401620890301003060040040088615100610806181543c4641c41690000c0400181000f007802000c1c0300f1050f40d14410003503e0840108098074200d60041102000f0b01000c0196179401385102c241c0040c2c200b8544450b6583e94605020a0340d60f52400041e10380e81542c80c03408200708010551002030594094030a00c2c0c41c80300044041f0f80c42c0790100c0183d5030020010580602c00d4484044ae01d50191401515001c0b106001442d154040c0d44031401c180c9a0300c20701c0f003c0c800d041c4107100241031110020701040380303482401400311080304090340c446c6e840d00078501e008200d000c0c112421300e00c0190982d40c039400603a01909130310a4a10030140903078111494001c403440c3c044111a0404e50061490100f001461302070f60400348000c2241040040403444407040d240427584081c43e0621417031000d03a82e441d05040300c80007804254440700d21782c01299420300c01964041000b6007240100e1411b0f907142c4c0e41d0071043c44005030440e024902080660418041e001c1044004003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 279825008 1250 279823758 279823781
    0x20a0f030e030c0705010804110406080304030501050c090603060609040b0a060c060608210304030c050601030803070f02060402100e040605120705030d020a050309091305010c0905012007031e08030703 88
    0xc01101104820341c980b039105007014041c841c0c10101051040f98000c000c002d8016003c2e10030510f8400301c00c00442d088907160b8010b800385070320201e030420401c9002d0060750380c840c810071002800c10a41c00c0c0403440e18000031303010901c80d40c1d010030f1944482d22940c1c840c4080d0b10b4000c0c0b001c2e09441da1840b02406101905400390b45c010708151000c071704090000781d00711100e6103030101504c5400900700310480580010340200e0802c00103501240103e00c04204981c0618010319229660341008400a07026a04064102d1b0a40d0050410400983e4904075103603041d40f410f06000004400c4400010010581908581c2c0c0c00442500d102031014000200c440640e601035041354085500c1c00b0781070740d0b80d42007000000d01550007004030400034217180d21229001f2401348a40c2017a01846d81d200340c01c5da51085507910000c1c8910008105560b8004407992800082d0707040f60386d10806030402c0c0e42e02c40c8254000036113402000340160085c240e0f50002c45c1070943c0c001d48100d8490411510003800b401e00d20009 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 279826258 1250 279825008 279825011
    0xa0501142205190804090c180801150e0c04090207110f3f062a040602101116060f39050903071202090903030405030a030906020904020a0f03 62
    0x1c5140759000000c1112405400600500d240004442c52083c1c075010740b0382c1100c070785030305010008001007a4041c0403540c48650719400d002c000b5207108074071020510703031214086030b0400c1070100a12401114500584030000004840380d40c480412124030320031a80402100d43c4006020000d10111604803070200c2c9080320706900100b01e650400030741c1180f42243c2c0040721f40010759061501d50500030b1410030360344041c0f0310040c12003100c1c82c1c6050103001c0b6004900d800c4526003180c0c501c000080c01c2c14046801c0c2099508103070034010300942c1d40091207036000101c1d81c0c485280107802600700c25100081001c006000617402249010000b074070140c1c00ac070000a08020010f10b8803019184c4450500c01072030390390740c072020404140200d080602c00c40d030320900400f0800c9078029203043c4a1349000d403200910200c5900903620500000600c0140604429081441480000b0b24080100d0b08240c1e503c1c40c01080f00b0040d810070f81d000b80b00fa0700849610a20028046c1201500050180298111500c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 279827508 1250 279826258 279826291
    0x40b3024090607080910090c0b0a051c050c0909130206040b190201050403140d090206030a09051b06033408090f0703050c0103110d0204080a02101b0201050304050a050114 75
    0x400b504c0300c140649048200d90446035010706207503115400f1a41082c011004001403555510030700c21554005481c54001820009004aa8940c0c0d051000f0b1400b596190400080c945040c14082c0b5008a0308100d104031380c5200410508146043c0b07420aa940081034079613104d65558a001041d8400c0140d80440c04683c03d00310211801807088601c2950161169100002010900c40c1154002152001144e40c1c071300b529009038907a40040c2d44248a95040021600c3d00f500b442c91a219040001c10440082140b0190940d01c8160680c1d4100c0303e1000c3c0d170030440a215840302801e000f00010074407040c004501d40141d80c0c1e481240103000d000b865094800130221310048946402c543e00000d0180d502200f140300955201e540010110820700324085d040489030048003041e40c3c80340d0301008066100304a030070194641105186401403450030b00c1541e203840b410aa903482083ca05029050001c040005804e12500380303d024000742c1e00030020071141d00c80d04002550031206a900213452802d070309 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 279828758 1250 279827508 279827521
    0xe0403090906080705090901020c070311011d0a03080702130510050108010806040b04231b0a0f0f0e06060705010507020604121805041a1201020702040b30240906 71
    0xc81ca0080c3d60b40880585120740c00c260600800000c040c090001e5590b08204480544038180103100103035220789083d60f620014580010054507400c042d0384031400610048540582d541a00d000450380d110b03244544400f014000a00c007003000d0810b180307400d4107007003c012821540d41d05000c2655402d0b02c44c000141d884844142d44c2d02d00489004103060340390f03804200484e65003c007100c1c0300000318098414138408407203c0c0d4289200341414194100720410420703050f2402d0f201210140032000351004034646444c041d100890f00d50b00c16540a4140d05000c40c280307849003006c440805410500902031410306800c0299505c0e0100c40c00c0d01c924030060144081705210314041c04540d0310041c100c44407941418204001003485000540d10801c0c0c8101c09a800d8446080c09400034510200040e1102094010f0106031070b5100c21540c454502e0044808454075149440050500d22018180d95560001c52803864407410108090405840090850040d00841d46c900d11601401c81034450a4a811 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 279830008 1250 279828758 279828761
    0x90905070816080d08010308271302120105030c0d06020711280603020c0a11130c0f080901140a0207022806120516081f060309140a020105160206070506010e04030909 73
    0x87c04014030b005010094201c8040622401840c41880d8000480c0c4461003800002c81000907070007d00c0b4613503000714100010f8181280b603240140010b03006030100c0e2442d800011015964004010189507000c10b00ca0140030030740b00400300904014043c0e1402c0721540881e2101008078005401c070910210002243c41442402030701c0b1003042135402003030454000c0d0f13644803e41e56548071058211840020310b2542e07400c1405220b04840c2c1d20b4507140006500054020300e03100c0e00400c1c00750280e0400c1c0841222035010600f40f070b4804c9600c0d40058a610303143c400a205a2121400c8151403075009110109103a85102c03010120745c03142e2164110090700d42c00c100240c030011078044e4503c070fa103100c902c1c005500951040341e0000103080610100b10200315400402c115641040000a60314000402080f003c00b84840c0d6401c0380c0401456200601c1e80020711b58460600401c601008146041302107450301811b8400081e40541658803035a140e0884182017031081700c2c29000180410800185d0401301e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 279831258 1250 279830008 279830011
    0x1020d081506070618050f07050d0627060614010903020901090c1b1a01170d050a0207030203120a0e180103061d0604050c0a06090807090905070816080d08 68
    0x980c4031048555580c80300300001c1d031074425849400c00b404014640001d5400c0c465a48461000e82c18440718210504026140c25014a80203810707900a403001c4c0079664484000442c0c0a60150b00402c0700c00140d00a1651000ca1440070684002c104c811281001025003021064031156184030b005244c001c07004450101e80c522010350409901e00050201b03001a8106c1c0910700364a007440950403034401d21480d440c2110440944149584010048000c070300950360300c0c014071414902036180658000040d465501e601315101c1800000190302c2d0445000340400380095800509a4035142d001c03590040c40303030748148031840015502c110036012600d04181c01c854102c0c440300741805642c0c203581e590001040e0b6040750782030308a2803010500c2c41910402055100d5803042000d0142e880214050150001440c0c1055044c03150108041c0814007000411008944919001146410f01c3d82491810030b805504261140c2c081c0e82c1c0311a85400840c111501103038210401c9500d00100520b080fa0003140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 279832508 1250 279831258 279831283
    0x20d0201020708091509060d02040e0106050901050a0c140d18080d120c0507060606051804020306010e19080706110d05161407090509010b0306090a08070f15021c05060102 75
    0x3844130b0021030034904007070380c0040152209907142080380000241c59400c846402d4180030380008040c01074517085007a00b801044281001c6090000383c10018007a80103c400100c02c102c3d02203200c1c0d081c0320500395803031180c00448043c0ca41800e103095005100016044d2640c6c0d0b00701724a1400a5840c0c4c000440c0340190b0403a5030703400506100032041c0301c040d104645401040040510481c00442c21910640b00242625150300350b40704400040000500300b03c2c404680307e1441031081000c9a60002d8041c0000f20f0304641e0b400707101d046000303030000030400e80d007141d02c640c800e0391804600d0a8201080044055058045a05900381c0990031100b42c4620b00401c1d1440e2000700848000800c03a0ba0003540280e0884c00350303280c040e00e88100d4012290103c480000760fa442c4c1407181c0040c141400125041203203403014003460030007610341d130f4840c4c800c040d0b00821030f440841c203d8080c000c51000c02000b65131092810355a074120381c85040010f0310140c400403a0540340c403000c52038940c0000703641c0c4580345 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 279833758 1250 279832508 279832523
    0x9010306080d080c1c060e04050c0d20150c0c011205040302190213050a05011701020906040e190e0a03030507021b01140403020a0b070b180303131112010c020d02010207 74
    0x1351038a00d100c0c0c40d034000d4154080c603200c000c180c0a00170020f60080340050107001c1703100e000c00d20b8281481840c1c044107929050107840c1c040102c030041061078070142403c0507031148a01d68401254049800c10306038000c2c060382030038049204142014080f4003518115001d07a5005500c3d5401c203400310484600783c030010b0141e4800c00b001070703543c10804a94400b46000500d0360785944003643c007100503544120751107007045585800600a400c3c1c1da00e106810002c401c0005c600301400240451710511503805242c0420044c4000143c4282100c4041c0c00d00044a400621002001700c071207a5845e1120340c41140424108000034800138030010710700000c201c0d0114000e807207543c103a0054032080c3c280e42c00b48480180412010001d40c64203409540240310000d45c8035a15051420500074405000e008001140503040181c1030780400042034a403c04442c4400c400c001d207251800781300650002036000d411010a0350107140420048d40112441000340d001d031b86209045010403400c0b072054500007040c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 279835008 1250 279833758 279833761
    0x51809010e030a300c080601020d09120602030a18060501062d0f050c03040e01180509060f06180a0b1318032006011503060e2401030b041109010306080d08 68
    0x4282e03145180b2051000001c0040501451684c07101a02d490401c2400801d0303101c8140842c07964100710750106990309181c201e172003904141c0c01e01c0c00c40708100300280c13100340c010001c40c3c0c10709595130060003841138903201d0510405e4207140c9400544000d10640c8041200c14100c2861120300b0043c07600c2a04060109449990324240140e60203141d100340b40c2c003044030500018038241d404000600180c2551082514a50700d84005000c0035401314920300c090301d00308818000c0c8080d00060454010301c1c81d00d04a0341302e079a10000304001459407068003212110340000e00601145991000b120204240d50025104841e1803800e03059416000000700070307503c0c1c1c5403807001107881a00d1081c4035a80140181c10010141d4003c146021000cce0843c0100074140320091030a20381510601004001c502140c0e45070380341000a0703079030407118007800a50702e00001f00051a260304c6903000001151005108010032242c002070008203410140031940803a2910902099100c0c0014210300c4141296413100c203036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 279836258 1250 279835008 279835037
    0x1805250f0612110a03060f050d110108090a020904080403060b0a0b0d020f13060504080609070e0c070812190b0a0e150a1701020a0f0c110906010207051809010e030a 72
    0x8444811105040c20f41d035021070610700c030f0014020010401035a501040e0a406c050010680300019403100c1c1c414100712007558006168100c0c008203110090a100080755aa841c1c520305260100344020f40c00007c000c2000200108400030380152801030404014814112040c802c000405014005c0410f00c01c3c41500c1c0b8840301074000f4091116a1000c0d075003480e110005000410340650071400220780041014490101c0070015580e028000100030600c003481c007030b418200c0b000042d2851850000000e10b12040c465030308121420740060749202c801f03500d400d400a00c404000b03600103c1981d802d040a110707032460801c111105840001c17103007490b02e4454940425000a2014034545c10503c0110000f40450310303c500c01c2c07030080e01c01002503511002010f0041c030b60415a40b40c01c06101114840c000401d03001c0ba102c245450040e500700c2c1607034941c080180d14000050340034075031050040201359181c555070b40d840e071f0084c083c3e0002407001c2040859156203034000c0401d50000035540c0c0c4583c414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 279837508 1250 279836258 279836267
    0x91504120504030503030a0605010e180c0a1403070915030c1b06181104150602030319020904020d02040f050a051f030603060e010b0f0a12080309011805250f06 70
    0x100281c00c0540c074056899542500390b400860742e068030195902c40411165070415001e070110141102c402e4165071080041c1c0b041c140000d000e03981c02c03002c040340e1280c07110f00030029940d440381248480c54680c500b4110003860324500340903008003850b40c40702020005001e4010b112080e80b0726102c0c1c45480415020801c2000d9002c40140d03401601e0b1850000c8480885c06120050790040703808503800070803042403101307580451028090400740700c4001c00c045903022090707940240401c845c0d40c2d03800d19940d07100030207409400012a482480022140c038584c0a9a00500489450780380307000450ba52003003000343e00f000e83d1154a1b0012400100030b010b01c4203003100300310f206260b8140011541c4c2c480c4c41e44070840314a40a03181282e036680ca0503204901d44044514100d1400700d4084005c0c40c10076072158003000035440018508000400400c0d202c11080d00b21403101c0c00341052188900d6100c0c100580c3d40c0c00588101c0d03e0144076036a042c8250302000c1c0441d000c2d18044002d2030040b40c903004c81240c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 279838758 1250 279837508 279837533
    0x11010e2709030409090507031103060606120901241a12010312120908030105091005010516020d080f070b011e0e040302190503040906060203031003260a080f091504 72
    0x1a5800b0030000072440750b03070b00d100c0c076a07081d8001c100400030582503103801014201480e419500c01c1e403190b410441e069680808903004140ea50309a1901915044512409000812400241000c160700441c0c00c0f038440421005c21510050701c00b60440340c141d00c02041c1485181207400c0f04001320401407001c10503e5188100516061a280380740074060304400c002c0358031040084903445000001001580b42c10750300d80740c0024030707200701c1450300d4036102c006010303403040c01c0240044400b4204108255554000304401a07031b0071400ca0f5aa407c1e485c0e1415602c1c0c0d104600807904140d6003800400c02d15101c8144003180c00003002c240200307604281005a003003800601c03c4045101d00c4900e1603005442900d625040c0c1e1181c8000c40d200da0800d101032060742c0c050f40246003150700904c100b0640704112100c150440303400058061101a41c014207000e000880010240d9000300010000f00c00d660001045128185221395404591141070b202c2da22408001c040342500311142d804200410301884061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 279840008 1250 279838758 279838771
    0x3070e0612060709030204060b0c07091a0616120c050a08030a060b180405062205061807051201152f0d031a060712031806020711010e27 60
    0x107510350903084040780d1070301400b1600d2030001610a01c003042142414000c001c060070b1010303165410312a00c1d10340780759500e000d403185200064035003120072445580c0d440c8501d0040b20140c901030baa4241c1019000208090340310032070f144000041e00d0202d2911404040c1d404513032003406460880b01c103495285503904081d2041120503583d4200042014aa40003003000c40c482c400031840581c003a0080208407440201054050b400d0000030f13412100313801c80503030b0f8a030900150001c0d8540315030000c2003450498034a80b071110300881c001c0c482d090343c0060142a00076000901018185e0b26001143c01059281c0468000300d00081da038a05d40d4440e400480ca02c05002d8500d202d840c4149500d120701d82000d1440980100342e5500c601401003044000c80d600304503040e200d6616146007030fa610303006200801c960204155840091016010001400c40d80c520b400c0f83c801d40d1206440d00700704242d00303490b4076210f01040400c40c401c8000e0910030015114103072502681145521416180400d5510041c041d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 279841258 1250 279840008 279840019
    0x120a140103240518070e06060409180c030b190b010f0c0302150c0a020c0604060f0f0207030b04060c030c02011104050d0201020a0c0617011409130221010c020d08010503070e06 77
    0x45001c040c840703100f03841c403560540c04e00ea140c505030001980d09000058201441d2009007004010080c1c5415044404484c00f581c800541d004440c401100c1800c0c040384024200c06282c0800814000f288a216025105a1185a404125049441e011074410961445c046510001500c0446008000d8004898003a0044da1800d442d94108031204c101c0032140e80e2450b1101082c1a4240c0e5410400c0f9a00340805880711481d00b07003080b40c044d1045410030f2070704003001103000c52030300458801e206d81c0e0b0007190301880652090030b05191a901900c0039528140009150240c1000c003548140103811a03003001031041ca18160801c0280800080a0b0406a0652045408940004060021400041096075681c81e07540810075941000c603041a48038101e528401e844460b8a55201c1440c1c3d0341080c611a020f11440300203101003140d4121040002e8903000c04410700c8101c0907010b40000307828071541d038241c0384201d0441000350b9002800f80541074150380102001d0000e8103003403802c81e4112800400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 279842508 1250 279841258 279841313
    0x70306230d0f0206070609080a09050a08120a1b3815040917030402030d0507050303010e071e090e060126130209071815080703150801060605120a140103 67
    0x54a000347c0740b0f150000c840d8807100040c003981c49070b48100702602401045804245c05454069507170f5403003040f442012403400303000075908011130080c80396a042604034100da080342d07819800c01c100751044501d411925000c40c40600c2051404900008940c16041c45600078240c480c00c910382840b1a0040c40385400c156101c8104010800d514084194402c03ca01c86c6580c03843c00e0f1051504044102000509001007030003141c00051010050b01e041d44c402c03202d568800d5030f84480403201000040f10f4030404802c11845201090742c80241c1c402580e1400e1040c11098072200011100b010000c59510785021400c07409400e9031410000c4117411240f480b20700102c8036038a80008050340310942d122008152684003000c60300032140d2b00003001300030588040444000d00c96002c0c0600d4001044007003050b688140c0b2100581e0703941040c3e0040c00d2003030020040d5a03101c00000e415030344040c1c0c4150011240b2000207410b402e0b40c0c09003101500c0c1c80c2181395070592865132069194110360700d00303d908191300b40e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 279843758 1250 279842508 279842513
    0x31a060a0f1412010f060309050312070306211202060108100203090109080415020105060405070f180305010f0608010f0231120b04020118030b0c091503070306230d0f020607 76
    0x70094000d03c012826100182d5250498869181880c2ea101100b41130800440c003001c10804000d841d0754003450203a00181d580c491604270010509500410101e6000e40400340c00c500520050340c4019100c0c044a808501401c0d02c11380c0d64174803d01c81c0489179030044440a010050507005940c02c0b4880400104041c04140d40d41041030b04a6003000240505824103001c4d26582401082d8001a081d81d0410180c00c2000c0c0080c45803060229000a02510302104245143c444981d0401160840020015100481f1009000d40f0b00303407092680640c00c00c103444800b07941c103101315445c096500c007494004c40d2a411580d20f0703105500b0300c0b0800c050181c044c0003403a01940040c800c140e41c03044609101e54501840007403c203408094031708000405140c020710006010340085504070b082000603030303266906a800600c4506501d086041d1084000c000e010802d500f41d008107090701d21a401c05a111002c64090b40f0088040300c511a500040050459003c101d48030404230016001400c075500e00104c071b8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 279845008 1250 279843758 279843797
    0x30504090e01200f161104090803180c060301091e0e01020d1a0a06032c0703050708030a0e040b060f070f0615060806041d060702030307031a060a0f 65
    0x10905030890b40d440311070760b90300c0381c0c0c0b20200c00340c0c0c100c11105502d043c1800b00302580c1040c0210300c0040500d10030701d0b44100602c5103800141081d00401002404a04440e2400304591340040d1020344c01a020b0a003801c0000d06e001c03a80c014220009452141941c0c40d1008144c05800e8400c81492000c1c4c0209050013480e40e680500f1205000c840700241e50f41c82c0c255030350402c8071060901029402000c13001d84210755128558403080700e2003071802103502c4407100d10310600a40c807041100006100e4484880342e450000c5a0701c01100d01901c19106100d542e0a0500e4030307072040c02018400210011002680e40c6010783c000c4090f00c0307014001380d090a10408022100d80d0208506a40f0300665564880c00c1201e207006191080d24001c5168403001d240610203089170740050b210038440d94549404c1060074441c0b40c1c1d68240c1440400c1166464105540f001e520382c0c0c41a81d1100000b03041c10552405940c0c04441c0b0000391070054030381740c07400b445a07908884203e200c40b007003400c02c0030032000c0d0b2000300340b175 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 279846258 1250 279845008 279845021
    0xa061a0303131404051e06030304170601080f030304031227110f04200304060902040204030f0308061008070509010c060606030e0c0906010206010315020408010203180c0f090a0903050409 82
    0x2480c01000c0c22400c0c940d007580075600103d03825210700d06102c00c11018a0703400100d000452000007400896449150009083d03000750341003411814007001f20b9041205000840d24129103209058540048280b03507055100d02c011035001d400f040d180070300505448616880303d81e03400d82c070007298041c0c03c0d88010b12402c0d601d0800b50544101c50801200304451500201010b40c00c0f0049030200080742d0002140b10404961110b071143c4a03401100141c14008280c2110500380d44c0204119559922460548000103c80030182d00081d1804001455400c25091154445015450b0f28132165140041120303154010003003641040316400d150000100580150400b030000c50328040741e51180d207401c5526003503040304114031074003204040c022140d0b008620541075941041e5250340c9032007a00b00305c0d4007900c1241d00000341c1e03610000c10040035503070040740c01d101c0400e800255107074a201d01081048012010b1040c0d03501502031000b040102e03a00750f0050802d2442420800c1c03c0c81d6607040d01200300c2e00e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 279847508 1250 279846258 279846277
    0x30040e060d030509150304030315051e0a03060207030f021002070b131b0906053606181003060f0c0906030225080c071e05040207140318040606020309030a061a0303 72
    0x5c012003800300709034250042401e100104d5001d44006481c010001c0c1c546403031848030045c0c0c80d50b42c1c1c0304144240c4415044501541e04a8400c0d952402549001050100020714040042c002c020302e046030900b086c02100c615981003160029a9120204072041d2140640812030311003442060200c604460142d070400100810280051054a0241800180b81c0080c0011060481038580b42c9851100c4400c104486900f42c00c0c588110b0f81c5000105089203954015048810030742410000001c5000100c002544d200741d2040c05180c2d0b103540d241003035400702da0a1002280b0101021b1141510aa0141008680350350084a03101c1d00c00c1c1007200015001401513034203101c0091000c0c0c00c3c00d002c03c03040c0700500c0006c014075044551070004071004400ca009583c4903d4001a80300107210365440650503910035042526a03641031040c0034158007224064150090741404030001d103090000c0152903c800014002c1c0c903200c2d02d02d43d1620001e040c4820049050413107582c200103143c404001078012401c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 279848758 1250 279847508 279847549
    0x30f0204051810090b1e01090e1501090f0506090108040c090f0e12030708010b0f0f030106050a120b060a11030f040b030f01080a120c031130040e060d030509 69
    0x1d00d011034002030382d400d800070040982007001110171174440c40380079442c40c0351410050000c4810703140129400b0b14181e05c0110b031b07000c80c5014803408001e403072014402d100003600d032546501c2c0d841c01e402e03401014a12810398082001c0c800000194003e00003da88140320720300e5800050b466082001c2200d01d50000c07444821740d12404201111070405c2410540400d41c1289800c500d0080e50051081605001c0c0c40398000b030206840e0712012406040d100d111461281c199205d40e1981001804c503045071034490300003502801d40c0b00c80c00a01d03201e140060880a0041843e00300021800c0d140c19201c0c0040707422501c81003160300c1a8409100c0980003401420101640c0d0b810001030700881801c041e0400d40c82a080158480001240c042c5010316244d55800c10003221840c0b414103981c46800ca00b4802c00342c0c041c1c00b00d00782003800c040002001d2403198542000c00400f4a000c44003050003907008484821580b000410914681383c1056880c3d548645001841c201c00b4401250049084078010381c16036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 279850008 1250 279848758 279848761
    0x180b0403030201050c090319060b0a0611060f04030806100c0203030f0a1206060906030903050702030d0f02010e070509150613181a03100506040e0601030b18060106020d030f02040518 80
    0x142c1e080c000c06400c034408013a62400c01c5003000000e034403068581d0225035410340c0d2100d01e10802c00d01d0b400480400c00d00038502407100d9039401024081002b01603070729000f8000e46000500340c070055000f290159406503540082503540b1018031032007820840c844818480a8800e510059404000400c0e950640364007141c0c41e015240005007050080d04811069542407490512140e0750045030801110010310300070480a05508081d00c152003034980182d014011054440c03d855044041c44020411641c020051904113009064640d11903014845d88161108003144400c90b00e0601e184442e0b400030702c043e10f081c4030711282c4103d103502076220083c00001c18030266800704c2144076801042d0a541c02030452280050000303030700d5070000c03000310b59500c1d074400100d03045032690342c03201c03040601c42c00441d0b030f86503181c2c04c0c02d154010341183c2c1c1d0051044100d020402e94840400c002381281e078250000c03d0b1412203650b081d40941007418902070b6241d400d200000d1203680c0c80355495481c00d42c80c03808510a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 279851258 1250 279850008 279850013
    0x60a0504050907090507050f0a0c08040b210603010b01020c1215070c03020c0105400b1308120d09051504030c0c050f1302070606080d1106010e01051807180b0403 71
    0x2c2d170f01c004041000f48a01031150b08100c2261608654002d001c2d45400c04883c503240c90010030034040c42d0002490b4640100c0c10003601c1060203a1f1814020f000000000250348500400d400e03034418946050051300086080700603800d003601308042e020b900c0c0040c0c540420010441302200c4004403070300000180026484418940c043c0700900203c0020701e48580390070080404c103140190708044040c00c0d0307030810039182200003e00d0704110031940c1710190100b900b0340d01e122002090b00460f0440071003410304000011603400000350080100071007103e40741420303060000d000003802c40300c0e030555041c0541451102001080c1d0007951140b8429101d90340c1064007801d1103556030303a054000034020703000c0c50110f803985d81c0c5000c140c01d1401c4400e400560b40d01c580d441e0500280105501c400702c1da106829404000c40c1e003125001d41503800010071601a1780c3e880500154044080c17250300c1c0c00550410030301030407661444d8000d80c415110b0601416083c1480000b60080d001ea610240304c8500114042c000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 279852508 1250 279851258 279851261
    0x10e0a050619090309050d020a03150621020114071a010f1d0c1803010908040902120a020a1205071106070815060304170307090306060b03040c060305041505060a050405090709 77
    0x118000b124104001da0720003540d019001c1500c5c1e008251240c0e00320f021071000c6646210301000955405000300d009060b003400e115020300142e0144249038000f0740c1500c042601802c0c1d90f0b030240b5405941d126001085250743c103446a101b603805545115141076029000c034010f1421b00d00a08a80000c6d1030410314101c02010268080c441c00c2011413040d0b4288a0140981010703100415140703002d41c0112101c0c0000a13004001002c0010420200844e0001d00f1341e20581c040c210807150420313503190300d83e101305101e0304900c2100003220105070303010501c921030100c2703521444d405950f1f400d04c580030f4003040c0e022525088045a4a00c0080c2c0c20108110001901c0f9000b2060b0000980d0424154105a9140f684465060078541209480480068421441134940c540116041041040129210000c8104a50080b5010388002100d000001521842445124460b80e0008000c503000c5209108a0002c0c020290209600c001c483c040421156103910401c1c1c041e40170320004241c05440e0480303640 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 279853758 1250 279852508 279852541
    0x200f090f060c120c0709060e0406110c070306020f09090414010b030714060a02011107030f020d05120a2c030408190c031b0b16020f1906030e010e0a0506 67
    0x78041e51040c889500071100c0024500b505421000409032141da0845900f131601900b80e100700c6405003041070008480340b80f912544d010790b0044500340b0096404009441e21485070714507a0f659a440f0704410008981c20764060851070522035045498408507030001801004160340588540040c103030304612074074003403151040901040e0b0140003200d103808100c107071b50520800c45034000d80000074404201c41c0b0039030107140425800d0011607295403517030030000d000301e0a0036001405403064212205641d0300510940e080c000d0700c0c0d014203401c1c0e520f4580a1003c1c00d840c0144000000c4e10003071400f240c8581617206400713000c0c100010354070b81c3e00d0b11026519203004004103000043c020400c050108200d500c42400f6250010109030482c1c011000c4158036240b43e9000703051010021802000c400d007090324003240c0c28002c940007022000c460007040002e00940c0490310b400b045030141041810300a42040d120300580d6400010440040106581007044521045415410002c100070902100c0c48020303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 279855008 1250 279853758 279853789
    0x20d060617060f03030747090111160203070302090703020c070b0a020604021903150e010b09012322061505030c03040b041b150210110409200f09 64
    0x8090750f01d110010035103d00c105100680514166810568405414403201040450000380d070b101c0305050710300b00d11841900c0c40551001c00741001c04203100160501440d481000c940741254079140e01d4401d00c540c040d400321001c98060040c0807000000d6600c008556100d001603480141e40d540340c03071100c10304241d00d54000308817800040c86460101540051380c1c0d035005505880c001d5100341644100c41d0001b98641c00148819101d204c40180e0101d40e402144441854000900c1104110010081c140500b400703240d00502808100a0001a5800040b40001000750003400443c00c0c4c4140e0384400c4904a41d107010164071850308001624140c000d0700e144070414a866401e5007049903a0760140e02c0007401c050515050500400c05200351080c514100c0c1c080d5000a04280ea41c1c3e0404007226024003500c2c10141c000c0c0d10140101805a00544088001d480b4105180c00c0c1888140700003081d0302040c814005e100d94403801662001d030301c01080c42c0c4d40c0381c4000a8882114004100e010503091131032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 279856115 1107 279855008 279855019
    0x90402211302010806030613030807050909040c030c1d010b071406160212040305070b1b0706020a0209060d051c03021909030c051203040b030a020d06061706 69
    0x15601c00e8400c2c4c80e2064650b45001c105a15150100c0b2804030411211441200080c41030ba0070716031021560410a0804410801213440a07204840c21100c80e040d1fa401801400490400140100300000c1217003000c4036402c1c0044180304042c4202060020702068040070021815141d42100304500f0842c0c001d40303400d800d0580d40401241090000d4050180502e4902c1c46a00461b004d90340c000c001040b0b09458801c01c400d659116803500e110260140c540b001c10b00c0001d00200b0001d010640c01040c0e20304090040203800031000c0d142e20720414080704810001030b40401c00003442c80c00380307000100440310800292702910503058403409140510a421084980103245034003928017540c400d4400540383c2c03060142c046000c5401c1003060380280010800c5400550085502c901c07074040140c140300d000e450010a03038040340c02000105215040c20a040020030105036803248007100c0c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 279676258 279856115 := by
  have h0 := BRFrame.cov_init 279676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 279676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 279676258 ≤ n) (h2 : n < 279856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
