-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1434
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:58:01.929416+00:00
-- url     : https://prove2.me/submissions/c36574b8-9027-432c-b9fd-ecd5855ccc27

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 257733812 ≤ n < 257913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 257735062 1250 257733812 257733829
    0xb04060e060a06030309050d020f0402091512070306060c03020a170913020c060105030111070f020a0b0f120906060102070b03060a0f0e0109110909071101112106030a11010804060f0501060804060b 86
    0x59000b02b80ea07030503100c4103090000039000740034080d0f44400100f421010b1034603108010505080104404829403505004c0581590001d44c040c80400c5004042e0401003a07010460201ea0396000043d0a030440d800b4192030030b14041c0301852580a41d101200c000900203982c020b2003840c4000098580680e6254109400c0719400e07203841c00905000c0041c04001446070900100441c070040014a446465940084464202c0074800c02c0c1c000000620704125800d0152580d80010b8800050059250000c0000c0d143c5509101790800c810012003c90556581c0c0341c081c01c0038081c4400122007440c0ea42405458144003849503c1901d0305d00038088020070007240844100703400182c0303964000d44904408039101c0001c002920003030f541c0c2e101440b600740700460085c010300309440d142c1c0d200c90480f203019058040002e000544294400302a102c002180340428404410007401c090002c1d5032a401d0000c09400c030909820180d0b0714003000454029003250b4014002d500800c02000312500031001d101009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 257736312 1250 257735062 257735089
    0x20118060f140403051902190305031920010203071803031b03030b0d0506310605060607080c07140d0b1914010803040603050907030b040b04060e060a0603030905 71
    0x60345090044046078010b19500440c040320060461905a40e6114142041b0301d101c1c945078901b40b01716a80043d031410504103200450120450a491807950ba51282d803441904140b081f041a108500091b4500544204010078140050601c11440e0082e03128000d50081340d4410100e40c0c80303502c01c42e2021141d2003190503a82d05844000c0030000400318190b1160155404608162729203c820301d4030344801440c5084180718000905050501004082030003800c07040084800c84c2640c1010180c2d4440720341c0021540c0c0001000406032608000328074644142040a0445540003c261100d00e40000e6201c04a801440607192421201c2080100344138017510042d06c8402e8040109940944481101122201780c11000036040010403840070000d509a00c4460745400c045000c22030710780c050041395403101ca600702900c40e9074215541c2c50980c81c1e0207040030b026407201030009002c1140940c060040103061100b180c0b03003841c24543e26030103402103020450019501500c0044c41d800d01c8500c4040c030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 257737562 1250 257736312 257736317
    0x606060804081c540b070c050d02100501050d200102030c0a0b0103060c0c050a0b06130e06060f0301020c19060b0607080a0e030d050702041805070b0702011806 70
    0x20980304001c6052032941c1c066545034401d80d00c002103158103150040300141e10182007082c1c80e000200940c2000c08185000140310030101c0482c0e40000b004e80c003c40041c1080d485080345207940c8903451b049840c0b0b144154000c0951113646030811003a40c00142c000e030003460403542840140c1c4c8a00a101c000100c00b9001081c0c200011000b81011840451901e250070061048a082222103c05146803503402c18055034440310b00700040c41401110302a10000c400c0908289070140b22680e14160346900444002d8103441445001c54556a07402c0b0485d54008504101442984081c0c1202c9441d0035055a04030700c251081008142d01d81418001c0c2c5064801540c09401d10f5407520390840e120f009400c1e4200e840315a110000f410903a160b0000e0a0034501508a454850005c0040980000401c0421038400d0388003604910720309510104807049160705035808140c070302c1800d007649580742458000604030300a220010961500c500d000c0c102c218001d80c0c40e29200745c056031001e140600d850060400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 257738812 1250 257737562 257737567
    0xb011a0a03050a11160b0f070203091909061d18030d18060f0605130605130b040b0301050c1e030f18070e092a0109060e03010e03070b04060606080408 66
    0x44540c0694400c5603c541c8000c0702040301c10780802d941c11690f0110301110700c2c4942e540b14200c1441224a480c0ba40301982d01403030078082c149620017a40c2c90082d51003851064a00d49411501e074695030031800c00070116000305000054480040c2401442200c101000c4140c0603030008281c540c2205c0f40d400d944800354003452070300c699189440060485440c03103446910403555920001551480f43d0580da180960700015024100010401c175441034503400e4002a05140d002e02c400c0d9142c9071100b80120180d400090302607008004103000c1c09a1200d0a54594a040100802002120014100000441d40800640602501c1d0b105140016580800c484194800103800c4441c6419185403481d6402d00b200c000680ea0300703001c070242c901120291000d40003035542c0003455486031072a4280c000c2d13601c00485030001c0ca40000345082103901c00e403402c00c407110400982c151429401209910b001d103096aa54940600744003d0710f1030140c0d8100c031340300c1c0303040301c001805442128010b000c0c1e0b074400f0b0042d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 257740062 1250 257738812 257738827
    0x10302090f040e070e0a020703230d0209150c010b0a120b060607050a020a0f06020d0c120c0204110a0203031b070816030516050c0a0e090c040f021e070b011a 69
    0x200070030083c01844903e10030707400c0200e400c901440c246442a99031180169a500039403034000c1480c003d031040044101d400e20400303141040c0c0041912180130502c0d0b80140c88509100001c4d12044a061020a010303100207039469030070406400181c07180340250340b1400ba1079503852545030900d050000c0641800b0500c4007144c41c92801d0002444000d0149007164600e542d01e0300064119140f03030380001c4c185100900d0401c103054040c0310600803041075050080b1800c820361503c3c5001d23052580075030b00300000200700c07070308658660f030004a0301c01409001c9520350981d48400303580c03a4015240210a42e10070805800852940c00440e40c85070752219440e800d00c074413208000b1900404081c04c4091000a000c841001811700b4a04008940a40001e1160400d810203221003510300f074002c0e84040c1d448004000341d00c180010032007401c0100350f80c0050740d0b03510b1582d02d82c020b024900315450b5151088a0001400300840041d2880c1030160000c032813030340da96840c4140701c800f1040000207104d20600265 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 257741312 1250 257740062 257740069
    0x50303130b160c0b04080105010504091509050f01051e0c070c0608070e0d15050a150501050c031c020a091203020a0b0c12070206090115140607150207080a0e010302090f 74
    0x400001d0100c05070b2903101050780c0c1d211107804010350410407454a0200d420031545d030090080ea80140000d5074200010345c0c207511650541c28641000c2c3d503041b51034100510801004110b6251481c00c43c83c02082a414500340302c04000126030800c554040040f408648020840021650381591042040381454a0200c01341c44ca11002040e48052080196126140352546440d4240c03203403207480c000c2d00481500481c0d0302214000b400303640d515494842c18101d04541c14120328256042402c1080c0c84903400c4614926600c20740d0324200d840155003001a20160460f0040e0041e4406525415900b90316010201282026464080c005901040307039a400b1681f00515030344c0111515804d9440d15001501e5005a128162103100069200f03008100c50441b00382300300104508800b0412008a1401d14940d0100c0c44505480e44038103000140d0300100219000d00880501402c0001e540360f400034100400a90400321280703000c211b07040b8a214641d8401d10840711040c0004201089a00a01060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 257742562 1250 257741312 257741317
    0x6021518031306090504050c2d0706060e010608060303030c0301140f040c0f11030909010e0702033c040b030412030b031e0c0a0501051c1503050f07050303130b 70
    0x100c501901040158011103a5450b40381c80c054101901c0e0120b03168a008140710450300001c20541314400d042c041001041c1d06041400348107c01c0c00d10712a040a50070050180510800100a181900d09240045d0350403a5140d018126442a194140e4030b6032034009054803840211500b000855007040148008400c07640c00b000d085102400350721030301c03244c8008142107904011405000c5940072400750f070420f5001903c40240040344016500308000030010503030481c018014940303410355003c00540258401c2007500c00c0000f140c503008001c0c0c04441007050b00b11112580ca0309602648200322990b41500004607801c45001c0c0664a14640c1ca5458426909a4102c00c5034205038454140300441e41d81003100000f214203034618800304042c4295002e28102d48543c00c0c034040c022400c81002241c4e0004151403c001001c0c91000c000000041c032200100b02d01a040e130803001200c040401031220000d140858403503038070308803141e1f680c44074109660780c01142d051100c5405110024402245460003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 257743812 1250 257742562 257742601
    0x603010e0c0909010b180102030a020304030201030f1104060903150b0d020d1a010b04091a0307450c0201050108120715020c0d1b02010e09130b07050c07060215 70
    0x810742014000302c002121401c0a0f0f00c40e422003a0007207509000614064503002000d182400210305d4002e440001944a01541c231000e1f040c1a0ba44c50002d6902115800040710090f2003005a40e07551b0310341c04080c298418a010584810002280312030300d45810784500080350000811061501c4d250b075080103244105a14211140758024106007007e1076030740ca100d400b80c103221180a458906001d0910121841c2d5191100390140000d1129815240403983c1070a840b0f01081e04910526140003508060490241c5400001d8184104030a00c0180c12400307a4505945001407080300703502107040b800c3e21000e01500d591034022801501d21080106c0040107160300c0303400384051425041044208a03040382d40d8880181c0c00542a0002d00c50b4407a40404400c80c16208401c0e450b01c0d00e40000742055540700002d40650341600204210744010030403100742da9801381c0b42c802e151030300d0700c002805600401c1e030703494592040c00c00110341c590020400200c0607402000e40002a66549101b41d0b000d1503895 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 257745062 1250 257743812 257743831
    0xe04080703180608150d0c0b07081909031104050402031c1b0503040806160c0312020f030709090623091005060c0a03230d0c020325050105090a020603010e 68
    0x501901102c2d0703042c1001e1008158684440300589003c84400500b001c00c5602c00c0c0c45024000c0b080f00000d200b201101c4d003038804905040e0f4a5001034981071100348152848140c214040c4407541600e80c0e408103145050b01d1090040340918189c1c2800d00058400650f002503154210000c1c5d0407035103040041074810740e2414138000a5014603e982002801c40c010342c15240f0f60400a000d20030341c00100180b60700f00405010034103d025403040c0003844560034003c010104854006e03044290582d40d016070301d642e00e900b078101ea07a03801c0440d00a02032134200d2213008200d90400f40c00195402410a04601002c5c9159003e1520140d96041110b40e190080800c00e4031000c03041c0102e00350303c601000c0c0200360b00c0b4000070032000d034140c180a4110903c0b460505c0b06584101c2120726041d116105551507100d20075400305042c0149a42a41580550002a40a50103074856460040100389a68840700d0243c0000c00140d04c61020403500d44a50001c00394002030100010008062320720b200300d51091000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 257746312 1250 257745062 257745077
    0xd0e01061403150c0d1a0f1020100e0303100807140405060411031f15050702120f030a2102130509090f03070c0e060f0a140103020702060d0c090603060e04080703 71
    0xe00c1030350121041b14030b450f04101c4000c0344c091450b080c1165a01080c1c9401c564a4a071120300c1d40d4010030522428001c4103174401d0178501107503845000c100b90071a00701c3d115000c1c4000018114095500e4000302d0f101031021922001c0060040c901140c0c281c02c0e12082c02d40c01007250907240600001c3e00c005048c842d041680c3e450840c00e680a108081c600a00114440700c01c1c000d61055100c603402080c1e0003450044441081a8000d00d8000d0100c50341c0c00c0d4165101044615204106424420902c3d005100e50200050007c40646d0041000f0100034006110400c41503813040b2980480c0981c1c0710341001c6645501d0b050002c0d191000540c0d500400090894480c120314110341130a641100c001241c01c056201018070094011680c820780c04842902c000600d814401c0008462400700e22519911400380c0340e00458a1741b1940450b05c2a82d006001544d0303c1510740340e25030040440224840000b412880042035552080c0245421501c981e4072040c1326480369102c1c00c1d015031084504a052080e035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 257747562 1250 257746312 257746327
    0xd05042303160c05190e09030f090103090f02041b11070b0901140f04030f0b090c0315070917070801050f010803120c0702090a05070801120507030f02150d0e01061403150c 75
    0x492600c085c6510310a40031481c100d01e03040c2c1e042c540780d00140c4180b09542040c00413007147d52641098031080142480c0c046544041c50402134040c40c84d031080a9089414104140a03080407582a900c0440099462107420694890300c251110028001c0e8030f218a070401c030b04006503128100001f1448451414580303050189008002d89030310540c401c42c0c50b00c1042581009101c0594a0b02e54450a20000341801e11040302c00291603001000d0106a4204901c02241c11940701d080180064a0500d00168803140280c46550380c80b140c521590700300d90b00b4440000d8072030000008586c12500c3c02d0f4002c5090404103d0104000503000b007118860007400d000080159803250300290080c4840440010305003403d40e4010000b4605070400b41c1c4040c041c8a103800050350006550702104c0d00b22603a002c010030903100140c04a0000443d2500102020a5221b070040d00c651010b410b41c6507040003004980e959400340c1628a43c07a0746210347c50341080d002d8030480e11200303800c194800340030710005281060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 257748812 1250 257747562 257747569
    0x4116050c060901090302010f02090d06090c1d040204051302130c17070e090a0c050d110d09150507020c011d0d02031e070b030103020d14120d05042303160c05 69
    0x8031035010007a13440e240020189074082c440c126400d4011a001e40c80d110003100031948403170100d031005160f1962015901e00303225074002c500300902680d4441c9040c01d10302e41068040400c054509a109600e408003140342542a0141542d4455010f40100e214854101902c001480100110707818071680030307500229580c01c00d40c03291250310140c507100a101802e00c1400314940c0021f012481d140d1400c084041200d13042000c0c0c0d00c041c1c11400c4041403d0303805032504c501038010750702003d402d00d040c00d032a0001c0089441d0003c01c0180006403c220135520301104907038811b01f5003a254045001c00c4a107400d40e0310442d02000408030050041e4248101c10f501185c030303000e00100034600070491039118140000051201c00d00a1200c011810b0655046400150f41c0558800d00184400c0e9003205283c4041e5003400002054203500c4c0c6196100d0705500e0845018100c120750888400001007092100054200c07140203510500c84003d608013004980c4001042c240c5220940360200000c10020b119074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 257750062 1250 257748812 257748823
    0x1505070302071a1b2b030221042112090f0f0c0f050109080c09060102100908040501030501060f080402041805030d02040f08030a0c060b134116050c 65
    0x142042c0300360341d4485565000101c10001c0007050201c0f5082410017410a03c6416403079810343c61080754841440030500c2c0c00754005e00c21450042007000300c3c105c0105204070000c2a5600c11405002c81c4005214890b0300300854081303c2400902099180d004201d10010503884803010500c01c200e1204031080c01c0e141d181115080d060100da00d031404200c1442003452003220f0b54000d041c01e003010b00e461801c1c2100c568032003031119811801804032200260940c0c2c400c04c01081140d0301040100505403080c101143c0e00c1d4018014240400d0509000182d0300703210340c1020301e00c0103540ea20820a921984d0800c8081c0c020f1130030740c05011450b5104c1d80c000c0381040c80181203c0c00d002000583d12803500d0f40030800081a9801400b9941050100e100b40c603070006104c510142d400f49001410200690005460442503500b07241100d1402003ca111103083c50081001d21140c045480d2402605002000e8000354050803612420040700c0881c1006ca5185020400d501441c05d00300d05003414082072a2801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 257751312 1250 257750062 257750099
    0x220914010e06060a050103090f0b041a07050711151605010b1207030606060c0b07050f0f0f0306010216081504050f2407030c0e0f0103060b030a24150507030207 70
    0xa42000c4140701d0f007460841c030801d00520081c24140311922194440e0700c444510190041d01410285000804228541d4034908650750070845d100c1050a204c03a00600940040300212201c04c000d4075107101d03900c3d050110054000340110428078003032510090309204c40c59444115215900c5030071154482e9036481c2440c1005a01304001c2c288140b035424a07030140c440c26030041050041355107104000c03c640c64501c070303842402820590780d0b42c003880038180341a1140440c28201301e840412001c071901c0170800110f004507404d0303089032186590f044800351041191300c031380f00c459441400c010107080e2654000d90740c007501a00a41c2c403246070404846040c10705044c0803c66115150b120301840d12800c04845800588601e810042d01440503000b40c000526505031910070000c602e044646a88aa081301024003450340c0700b5500c83c01c01c503940d034010702000005032196001160844010086040c40d80f000c0325490308070324486a01c01c0006582a0344001310980450040c60300c0400d0301e034406803030344140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 257752562 1250 257751312 257751341
    0xf0111010c180e0c0a0503070c080403081c0527030909010e010e01080d0e0405041b14040b03031303030507230303010509060108070807050d09050618010b22091401 72
    0x3038486103030300c480c0400b040c0c0c0050020264060600c00703000d131800300380c509085840c240251303a9154041d040c2da0014010200a1284100180c04020030031000058104075842a6052081c040030780c0441702660000c541c440c01c1785000c0c209901c2402003c1e0030703465800600d0030a803894098505e002c9888406c0981150715824005001040740103c003500d00790041c1001c4010b842c20000e5444020310000400611502c03d603203440218081c84038542085092030030040180b90059900d01240305040c041e144454891403501e1440001800e0100448582c40c000c1d000d44440356045503800d80361900308031805c1d01c10404000322110080d2100c5240c6034645e100304025502d0358540004c011815000401142c10080001d05110a6540010360a80c01c03209a0404a40720790681c03081030300a12841102130024032666042c4030499040080d01550400110001d00c009242c07035007481011050205050454001c08102c10040c540c641e115107545485030031380364028070342601000e0035100f036007034100320 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 257753812 1250 257752562 257752577
    0x106030507060f02031602061312060b0a0b040317030a02070f08070510090206090d140a0b15010306180c0203040f09020a090f06050f13030b011805010b090603060f0111010c 76
    0x502c1c0c0c21105107010020240b004600c0c004c203a000e01a040e00e0700c040d0090040078045103101d8050b40e5141004003a10100040d0f4407100c0d001e0804902a01c5101c403510300841801c0408a400300d086000c03201903d4011042c00030a586c00046a5001e40c0028140701ea4554240100c400041c6120080c0c0c075018005e12001da01d881880c10282e04040c40c8101203035203180350041107001600c1d0803081d50f00140b4100c402c5010316080381022228034036040f116202900448107017008211002c00101c0c054181d4420500c40340407420019000c48905005c0c511543d0080c451200c6e98075869040807003004120300c1601d0030309a403071500d141102c4079031304201200d6801051130340109034000300510040992402d8148890300c0d0560180c607600c11500d502c48030b15000107600c500902e902040030000e65029080302c0e4190f0b03480f481450320140d64407002400e24144800010a80148003d070380000600400c65407841d11800c0c200042c004880404030b05010020800c019044428071480e1000911b40d01e4411 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 257755062 1250 257753812 257753819
    0x170301140603040c03020405270325052a1509130c080601120207020901030f1b0303090b0d0e01050f010501020c030f07140a090504061a0904052a030106030507 70
    0x14a45440380d0550090106004000c045210010518103c81e010303a0006080d0700c1e0071901a00e4081680a258943c40c060300074010880400801060420015002d4801a0306d180c0740f003007034071861018080c06a45c850a1510701c1c0d401034604041e00c103404070400541b4100c000d40415010a81d2140c4409030103008100d0035181d05100d802c0700f00849800c08200716003a040e44001e4990000078100c54100300d8280c208c0310000c0e0680d411a03581c10b030006c03e0540b00d50307503d01e02411642031080d42112002e03e003080d4003124200d001c500d10192941500c0e02e1a46030304001d4081040d400080024202a40715881c0c0d450481081c400c00d8050000304050403415030408001902d061280c2c4610f5020398450581100400d50200741d810660700340c40e25030040038105030000340591403142c00c241d04040c909011b000412860340c2c07015002d444084036594143e10304404000402c901142d000c0c0c8160081701c0c0c0302e0754007100c2c92a11403c60100803c0e00d004103a8620200303085484640007141e09500207074051 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 257756312 1250 257755062 257755079
    0x80f15070503060a03030305060103090512130618050436120906201204090c17060918070f030f1403030603071401030f0903180b0406021513170301 65
    0x40c0c0d219016080003851802c281002c40d4a900c0c00d448043c0030165030f9008520180e2081d080307810750340e81120455485150400d03200501750301540b0001e040c2e44003c00700003940307409400b4071019212410611299946813806100c05410300200740c0408040d030401a2201340c80b20300c03120110580c502e00c80b40007030b43c43e80781c20522001550101360500c0b0280d0420048a50b010a028101600c00c00c40a0300030400302e240c1034a816905903030f070300e48080c0208012681098a07400b1100f4201d0035902c2a2000d034a080303803681a01d40a4030030540182585001500c0c2002c400c01420040040d0310440c0c600c4da070740d21078501944200350801c485201100c0303220030500806582d81c410f5442e041c0d016500d542440b0300081d58030030940c07046c11604600010500e00300d038080c0d0f04c0015a1802440280500e0340303d4540200f400c000e10300491400403c80801142c0c0640c1c020540702a540207400234a404c1c00c6020001c00401c80c0281450060b04c011204240020f800e13226110117000076081d0705440e54100a40e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 257757562 1250 257756312 257756353
    0x3090c090604110d0908070501020c160603090c0302060304030905040c0e0102010b0603090c09040c03060510031202120307050f040803070f050f0a0803070c05010e0601180b06090a03110604080f 85
    0x184260f040c18848603940401504454500d1400c10700021111100e05c1d00e00c815010783c1b40094040e501c0482c03503085005011030202807610300207103041030780c0d9207030301c019006c41d401060080e04d5020002014001410300300003c5070854003c0c184115604c2d0b54030001015076614180704000a0140081c58a555070240204401602c0c100c80c1c2e0781c21403400350071859441c0c81d1802e01d030340301d031000030042402c3c0400038070300a010b580c000800348035600d007020b070400a40303a55100031911104030f0b160801c0c11901c0400e580c494464940032051a607114460102c3c0c06401404c014000001300b08000a6401010801804c0b4284140c080e08000807032414034504080f00112051000c1c0c01c82c1c0031a04c0000c410104490b4415840e05040d032400c0f82d20708046004180b00e1409090030301c240400414a14008440c00b02c0d880140142170003e42e803070b1030510449004082d855a000401100b051001800042d4003240e14000a400242021350303c5407414508612035504050940107a50150101075100f440b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 257758812 1250 257757562 257757571
    0x609080d0c02031b0d0c0e01030b0604050f011401090b0705070915030f020103180b0f0414010b03070b0c010b190e010b0c0a020f032d0d090f06030c0e0603090c09 71
    0xe002601e1600c0c0e401080e02c40d58000c05042c0e103118034844044069580d0706078410040c0e00680c00250f96078651201480b207550030301083d1101042c240c0001c185241074050207105882c000707042c22244c0d19080c110084407010048071410305c4400b1002160243c4108080d00100e4040c2d402081824a8020f00c4402c48610b0540e41903102104541071020521071204441c1c0244e0a1030009000040c40c0c1151107a0000e208005000344407190900021410440300f9500039401400180c0840b03c2c2c402d14a030888003d40e081a4140d0044c55003002016078a00113803c14000090001c1485484540001c0c7c0b07400101c0c3c69040c146055010a01c40a001c141109000d408819201441e02884800040c0c0c0ca281c0214003e2052941d4000084907880910403a1001c000d841c0800382d102107110310013035a0700d4400449160074850740c003038404807912540180c400c44541d80e0b00040ea184c14502c0c200d011780b0440d80c19006002104005040c3e60311250000c500c504100406011a80900000c1181c1e4400150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 257760062 1250 257758812 257758817
    0x20d0c05090102071e090c081608060a030201080405030d0e030a090e040213090f0602160201030b030613030c06020f04090902010320041205071206060519081002220609080d 76
    0x40800c140ba43c0000d4000c0650f0701059803d10561884058036100c11402e8000710203881c10320303007c1043d03d9005001325002d03558019020140f0030325030350211a43e5034229481540040c14120810240d40503410042d001401802913900d0880000300c08030948030342c00c1801a55600000d1204691b5901040c100064040c92a1075035090603d50001440946400340c1481d90541d01c00d000c80410185601809505910040a40d111003182e140e11640c806031041c1680071a040005006040c40c000c62000e00c42c120740c43c1004c05150854030122801c10301000f0454141e50308120303003400402c001000e800213054140001c603038138011707100050a036007440400034000c206880684100302400d8080d00c05641c6182003020040b00380c2c1c200a880c026182d8000021440ca0040c0c0009101e02a040700041d201c040c1c40d81c1000c001c041c3d0481142c0007591003080007a8100c400c3d40101c0031041c0d002000203041c0d600300403001944544c100820701030a640402d020600c42801081880014001005041441d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 257761312 1250 257760062 257760067
    0x11030d090b030a020c01150e060a0e06031207030225061e08010303050c1614041808030a150503100e0705030c011407031b15050c070f030e030c0d06020d0c05 69
    0x1c8600d009030201500c11400d498000c5040156030b4400d502070607a0171140c1d420030b840d207a9204007a02c26460305844460084044a40100c0d02084074008603003e80d2000c0d000308501d00c0c80500c07481107034101210440450040344603148001c6901084441e241440601a1034160320b0300700054181c20301e0900f010007007922240c6012503590000354050449806040c460341c1c41481040309400e010410800c0800c04103552400301d0107002083e08220007400966041011340c4804411807109411100c00808605041000880a00d001d8010b0300111102c411b0940c2c015859100080c00d009a4841140203203540b05000c0040001c104203c0f402850b05801508601e11480f000a2142c0600084004650f0000841c0001c06200742c454030b61150217a040c0880e2803140b40391048440084400415001d82000701060f0600c41d41c070120f5840990144e107c0601e20041d40d810341390000302d045201d90501405684414075103460541481c0c45200c0c910044e581d05101c05802c0894500000306410003609 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 257762562 1250 257761312 257761319
    0x10e06041a010c020102030d060905090c0303030415020904020f07050607180b0d0207110613030c0608190c0c021210110a09061b020613050906220209010c0605010311030d09 76
    0x100c0307008540711042841e00b200f40090f0390006070300d103110348180c45900d180f4109000a0102d4a0f922981c0600700c0101031b6442114007804060f5280401d030350280c50b501c2520703651180406947d008020814014002508113100052103004e035130821a01617030300b50015010400ca5a83c0801440803805481d108024124213000d03c03030845005030600003500550000300d040911480c0040c22100b14002031640795900003850780c1c014503004a2004031a5080401c0b0b002c9400d03030050505510882034840c030b0344802c070700548044010b0710300e10118005003d0400b00180140e2100c203046552a60508000e00846500340c00d04411540c0146a4034840354050182c4242250301c0040101282c9030344c035100c0c0034041c005442c41c580850020009511800c0002d000d00800100c040e0101200d41c100d603c02030130f5682e5030901c500b01103c51600054003032803002c41a00441342d640a06459032040c50199050b078075660b2440100c1d0f01c00c0c2c00642d145943f4925074181454100000d07000d45203645850f407219483d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 257763812 1250 257762562 257762591
    0x204050f04031b02060c010e0703031205150d020d0203011113050405251704030f0306050607050705010809011104030c09050105031207062a0905010905180a0b010e09010e010e0604 79
    0x280e0f020442c5454500701203002c15503075000700f6104219401c1000300228810040e0040da240c1e528031045010610440e440c541c680d0044c411a84513400413901c8041c03044000e82003103140c068a501c200e9204aa1010107005030302c092240514055040c83c150b070366501c5030310f0803180d81c00309580864400d509040401000c1d2100700103040034421081240f280e6580b005000313803001d14007450640701020b0510204400d03d940032248840c03400a580341040215107402c140032880c400c0a02c0905954481c61080101e035109041144d0710a101da80000f5403401c94880501c4181c1c8940c0c400c4d50341d141910343c02c0c041d154035846640c0c0180300440003064815101211541940103642c005840f0702d548089003040c50741c004484031102024032102091805c900e0070098250043c90180e10700007032610501040c81c0c1461f0b91080164040d60780000003541d100d01d5040042d00c2d041411504020711024041a16100d03451601d01a14044445802035030401050a40c83c0c00b0082038544610300f050040710b81000b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 257765062 1250 257763812 257763827
    0xe0f0106060905060f040e04060506090f011d0c04090c020106050a090b0a230409030503072a1b0503010c080405010c03060515071119050a0803070b0c0d060e01030b040204050f0403 79
    0x24404c0d5401611046600d118034a203019980c40043d80b080c1e4841003004202c02907214600c075407400c5031010700c251100802c0290380c010900480c0d100110365001aa006185903100d075900446442c50704d8a026150285030069489203680c1d203016070b4403444c00340036514084541750050310168030100032401d8004000b54031444c0c140719100d0240b002d0300c00750120150011100d44c2c4c4c50b00181040c00b90180c18078008001c0d91044803000f0016030074182244a105c0f1440f002c040820800058500641e115180d410140903004229407031a40300d02e82c00103403500c013802012444400368a90f2070f0585481d0a1013429142241d01250406151074402d111946d074640343c0e121001c2c40460140c0e112111803604030403c815590100b98882c2c0c00702246941600c1e500b03004c00940d082503078060090360b82c4030215540e9005104008201540d89000960080100c2010745075000d01042e0125409944502c1000c1da06804c0e00140c89418141c81003105500b41805000d40081c46201e9040c1d0502e011b4500810a8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 257766312 1250 257765062 257765069
    0x8010c02070302060a0e0d150b03120a03020c01060e0703061a09010c1103030904050a0c02010f02031005040903090b0a02010c0305180c04240806070f0c1a040c180e0f01060609 77
    0x901c80405c01c0b20308548a00380800800c04041d001144c550560706058400418080c030401440e400c04c100840107040204105460104c0c2c110b07420700700f0b4074480080d4040d40100c9028440c0b59611940014200c01d410940380c02070000f920006441c504050600806503005400dc482c0c000080000400741e99101c00822035168000054030000d90b64800000e0030341c440d04520b290700070300384414803a41010f246e01803c8456510340003006264460503c0c0c00580c00126401180c48a010004002504298101e001e80500c28a080d0100907207845c0b070b60301c0e60303000200b039030006139500c01c455940c0c181c251080d01c3d0403000160040300307007070000c44400b95100c07aa50b1181c1d00554550b0295143d10040717043c04060b90002541c8601c04c29217501c18a56514800c5030044000703011841e5580c0307a035016420f002802904107519020500034012525011040904201e400c4880407000003810301c0030a40c4c0001080b214400841c000d260385100381d04d40300d0342602000c5540d1400000f00105a0042c2011048 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 257767562 1250 257766312 257766319
    0x5030604150e150a060201060303080a09050a051212130807120e1003020d0b0414180a150504051006081f02040e0705130834080d02150108010c02070302 67
    0x14000c0703800d08801c1a81c0c190301c01501101600c0501c1140c0d04124814a00d600e4203590f0035403c0b0b9503c6400700c0c243da1080c03001502007070030300010440d508003a1b000643d1090240c812120500c200d5034402d031070011808115a02e045011548140d0b5007031030000c40c0d801c06a43e08681010050646400415100e2120002e10031b43d1090310001070b640c004c600d203003041c01c001044142001520300028000e54840c507100c022061400c550651b1501d0244035807203000240d030003061400d540d0034558440f0003448204044940c4038200300315000a0741004000c40c100525000841c80d400c061800a00d8000c88070ba42400f02e600f0f2420510141100048c240c40d03820302c55251000c000100c088140c028441c0e60402410b107202d4000b044640d640000017012006080d22030510126950440706803a170784002085281070008140061052010303508400089808000f02881107a95914440c50185d05040007000368110010340000b40400d00c00131401081207800031310104850320402510350b003d80c007000f4407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 257768812 1250 257767562 257767571
    0xe07080402062712010608010e070609150203040b0313030809060403050901350f15010f030506011107030501060501030e0715181503270201080c031503030d051008070605030604 78
    0x10070f402a254044080140640f001080304205800c07140601241c5c09074400307641c208820307940b500600040e00d000311840c941c0c07500d2131f407810031201041c10300141d6529001c42c402800007240e01078a0342c00840c012417408441e211b0804040ca40508004e10040500f80c0d190030140030400400d8020089a52070708091034040075519212901105058200400c800203000c2c88045a130303c01c1541d40928003507110f101c01820035540d0340d600480c464120407502400580070308002c1c0c0642e8081d0f000300d908550141088202101c60740e000501c1c14030594000e440e02d81d1285401c010a58151040003e11143c020161802609003806110040a00600b41e000c000c0f80340341002c4c0002500c18990098691448105c801400d1450f00401030044020b020000922105668a02c1e400d81201c04044c254181c480c001e0359550501c22507000c0e00010300401c04104200c096618a9805000401002c58103550011700c1c1d081850000040310382c55080038844d076200000600842e078001055035800700c0d040749c0c0031070b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 257770062 1250 257768812 257768857
    0xa03060b040e0f0a0c080607020d031104080d09061202090f270f060f06030910050403030e010207030203040e060a03031205090307061e0f06060e0f030c03070f0e0708040206 76
    0x800034060b045031403009006443c0ba412040c04042400584980100b40b0b01c80d0590325a48a540c40b4242a01e16034050790108103003081d55802600f00800801560b525581000c3e0b94007041170824002c2c00c410f40020703511802c140145a0018012410150020021820030707a00c600480d4000d0654580c02d44110002000550f001d00d440141a0021198100d41d07091810300c01e900804681064030780b1481171080c0c0c2c944105605018041c0c0340300d03c130007900810a440c1d0346011080203040181050301019241d02555401e2030090005140302c5200b54001d40d600c03032520340e1601848001512042c8035850314402000880e40c000000014496007400c002003d0701c070805a10314503c5080070003018242020003040c5500303002800c40e15808000c0c401400781d0061054014100d91460040c60003203206146146143c0c200318003200d20000d0040c0c00c4481001c415400280781c600710350b201992032008403e06005c0e20b134404004542040d0700382031000590501303600069450084100d10b80005410000c010b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 257771312 1250 257770062 257770069
    0x20a02070902161e0f050a031101090206030105120a0c06050a0306052e0c060f0b12010e1209010311030a020301081e0a030c02310b0a050f060307091e030201030b0303090a03060b 78
    0x1442d6032131780080b0701d501c40710072442d051740c41c0c10000106070081201c046601502c24418092000810b50003000300780307540c2c200820811040d44072400c680d2140700d017070001000074900140c1c800180c0060784450380c0750514484000c3c00d688080d007100b805070f60905403048803249150024051001514110100a102c1c26030032558126800d01c041d024030b00b0544d4200d420849640070a01c003010540e18420310081c100d100381c0c01da030f811101c07441c95a801140390f005007006500c05841c80c0700f8140740c0882d02d01500080e5001c1e81e0000e540e418042a400401002062010002d0500618030b140344111811844c010b060b413a020b0499000d014000041e000504650b5012101d182001107000c4081400004213211922b0b1002c580400c103803185041081a010300d13010a00400b00c030360007040d44009003001341c14400d007070700082c000405003c03504a000c5940405d280d0050800142404410302d100d01c0d40c00010300391a10031075000e0007078008020140d041d868404a03041541c1e0041d6000c0f41d50751280010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 257772562 1250 257771312 257771363
    0x90102030d0c0305150609030d0e210d09080d05030601030b120307060507081806010b09030102091507020a0b16200a1403160b07110d0206070303020a0207090216 71
    0xa501c16180c144214a015059403026004404082c1d0f20042040c01509000042c4a91825181d00d540402d0380f0100300c501c65a00709241482c054011403000c403561105c1c1c075021071010381c0c2c880c0d1a0040400d0042c056480342c094002000c210009002e482d2409101802d284005480320741015100c044070300c7d09845820b071741d07101c544075034007102c0c2c0e58041030401400038041134600000151409001c14003000040c03100348115210a00908035a901c0c007582241103a0162440c2030b0555020301040205580d1080c10b4030200c643d0a054a503074501620400055464171782000090325410b10025520000c00200c040380c0301d922480c00c80310120302100c44040009502e8074103921181d04078002c66401d050102604801d0ba0503021140c08240c40900999030500900501c03002001c184502c901089a4401c0444003c0e4044d1650904c640c40b50046003056000072030980200f500007034010942c42c0d04104000080000349811030910442d2250030500d12440c140140507254a00203841826a01000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 257773812 1250 257772562 257772577
    0x61003060b0a050916030b10050a0507020406030b13050105070302070c060509030a1e06060f050609060304080d0f0e060609060f0103111201030c0f0e0f01030f0305070f0b100b0c030403060209010203 87
    0x1003400303071505d482e050040310103006050f80040e003000304804560a1410404503045255154182082250304048078140c000301c9090342d01c10344500b0004041594180c049000351040d602c0603086540604056094400c0984603c04140c0f04001b20b4001c1007240200f001603503100e282240c0e6504000000924107901c641c0060094032000350038180c0000c50718903c107009480750802340310640c1e4a008a03000c0104900c1116080b90041280070b0891504000550340140708401090a141000704c9160840d60040042007102d0350302c1700b14850001d82006100d902000071a82c0b181c0b285000c030080360b0224650314400d414940c40360004006c07141c540050341c0062441450a0748250780d41e040a0103404014401ea40c000480002c0102c0d5081c00483c28038810100282034812607441c40d5140345d20805034800590400034140200c0000601200300b2002e654000c6000032050b0401d00102b58915480d40e004507481e0703c00f08405500a1f0b008002c0d82c088941152005849484900050b07095118014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 257775062 1250 257773812 257773819
    0x21807020115080c0a0b030c0d0c0507140d09080d120f0f090c0e101208070314030a05010504050115140a180f0e060d0809130209061614061003060b0a05 67
    0xc2120000001ea01c0700000b405c44054080035a40c050721456840142c0303d00280a000700032401c0d5001781078021089401042c07408600e044c0b02900d8002256180c0c28030f182c2290004030943c1d08155000e0613880280080300040c2039840f040040c0685000354000c01c130081c042c0c40d40601d0942c00b0141e8060400021041c0f8240010b0400c0e1030091007150b00c074040c551500c2d01c4240418095001720b021030080d80c8040c900125501c0b4541c60350300e190b4101c407200720200800c0c8144100c080110f00c02940c0280881403002c5242d50405081200f9241c05070888154070402450103000300703521400c184200442d0070100390352900848002c84400c1c404031680c4c19410b08020b030009480d04144a10f908131001c010843c0b0190700c4050400508050399074001d411380006210809161512902c1003403c1d00220785c0c01032070b00c6c1c4c1140c041451500111042d0740b4a11310300d4a00c4050090703002c64070f81c803460394202421a80c606070500707180d00c01c1da5000c080d005950301c04420031a619480d0042c0c01415004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 257776312 1250 257775062 257775101
    0xc271b04030503030609090a0309120213110306030c06090117061804030c030e01030903052218020417010903140d180c0302030d09030305041809060c020114130218070201 75
    0x2d0400603070701d80c8251201c5000d40401e500003000800d021401c90b040c41c1e450796035179900c0e62a10000440004458005070390260042080b2030300041d062243c0c00c803601d00780034002d0702c91800074105410301c003144100e075020301c4041207041c00320b80e40001c403102d0207030413000c00f54901e481d82c2001c1103219844d0303000840c40901c80d0003480141500300f44d41c5c80e111ba00c690740301010202524011070a454400d00c00a0200d102400342e98001d01000141305c00000703010b84000c203206e035121480581d8a100c00c1e4903000283d80041c00340842e0b94440018450440c0a400034001c01c55142e030020420311000000c03210390a00411100440310f140e4100d008080c00d03040800704c0b05081c60421200750301c07180c81b040b4480d216070700304007410b14014104001125050340302c481c180791900800301504a403144034040980d40d104c1e00ba000203400340c07240094801c0e290340002104402190340595255024003e042c5401d000c00030900142c1c4d60b01c031050080610b1620100f41c07a100d05000f03901404002041e440e405884 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 257777562 1250 257776312 257776319
    0xf0303040b0619080601120302010905061602010c02030915130f03060605040507030903080a0509010908130602150c04030f0c0e1303021207030909090206120411030c271b04 76
    0x450070410b002d900201d5501c41d008942420032105110a48240441c40e0080001040000041005110701c640a0b0002080c60580c55407a1401d0400c12038404615a59081c1d00c04030040c0e0901c61902c1039481400152318206900000603605107070910340003a44000020001c66100100a244000b81821000403010310b071207203090350107040302c2d0080c00c1c0110714007000200700c1c901c640a00404103030592078541d51034440100303200240c04004c003864503641d201c080700c100082ca8140142040700306800c0344c486440c10410000d003000d00760460f42030480140c0080c0262804200110f40c100c0ba846481003100e50136a29046034400003590195038200c3c46042000600c4081d142c0602025110754255500c088018241c03014a000354040600040e035112820b0121340e4240d4409500c03280018281030422894495070046064121811900602c0d40c040c080c140e800e0401844445001c215484c69084620001c040da0316042c0a00320310004a040002c5001d40121401c241c54401c500d0014541d03a589 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 257778812 1250 257777562 257777573
    0x3040311150108190305161b030b15120601120303110f13060f170c04030209070c120e1e04090804080102041a090907050f0d020409061e0e0a09050f030304 68
    0x7481024141e0044c0107a846040d083d03401500c140030f03410b449050410450030b000341c60200c9550000c81c2c0106c04881e600310035000403440e0400542c0300c3c1c540b0303000314a01049030ba44038650b140709890058203400120a44004007140d102d06540900e4000601c1184c5414110003408040b0070031242c4200c000341501902607110002c001414045030100f0303101c2e82d070f2002140c0224408032403400007003c9100c09001511500b044540102c10004140c0c18203031660006a4280000c0d2000004140203661030410400c0780a100c200d042c240d400c004079520144408542002a00758251040702e2082030002000d5686c0d5100b6141d02d41c01500d0305440381c2e11100307600c0c000d41c0300d030280a00c41034880b21445030b80c010345000c5070740c01e03013000e006c0345c10a448401d42a5410b070803d80302c0140401050180500441191002d800108007603000400c21030300d000e031110981c2c04031403c0c03030b00314824040d800e20041c40024091904031301820000243d010b91410580d05090034003102c03101c28040002440203221 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 257780062 1250 257778812 257778853
    0x308310801051b0315010306210506071d0d050f1e120403080403020103090203031c090606060e2b0501050916080a0b07140714060a15030f0803040311 66
    0x346408020042c42d158a107119542980d0002d000741d04050801c000b44641804806204110360b040c107004c40c170103444031b07502c4000300320000b208042641d5041c228070030b0101c10020b290f084111820303e0b030a10180710032803082480c824941c040c0580103042d49541041410403543c011640c200040e83c0703013000c210940c4a84480200c6d0003003141c0c4580c100a88601c0c20600484080301d601c0f0303c43c2c0389098078545c01903014208051080e13034540800c0c070242d500045035080003607554528000015140d8060700c0c2c40030032254550442c80402c00740103007400305601e44406240c2c00f815894103000c104c410405203d040b120078003500810550801090203d0701d9030000301c1030118074a100d41c110580f51101001503640d52504800340464803110701050059004a07000c2800c098000361580c0b50000644035851070485c040100c60482c1e000e071040022007002880750014244044242140403443c50700d5404006400880c05405204004085000c05000380b01e00003281c40701106036041c20b80c20011400c034a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 257781312 1250 257780062 257780069
    0x604090e0f072c0702070503031b060f042003031603110715120e12071202060604021620030a1a16140a11030309010902210601030831 59
    0x207104091012449600142401e5504281000828200b11043c1c5018180c1e00018210340298020a1804038030783d1800e2004011030048280b160354030311103514600780f030200c006214184c400c100304140b03c00100c04c2c44050a000c4043d81c0321950301e20402000a080d80f00310360780d01c0040aa8101c1403010103401c19000d4514003600c409a170092591054400b413643d055604082c0003c0c82c6500034446034200da1b0100b42c01d808200110b44080d02c00040d17140b202e034040071080e920780c07031100e0003400c4a541c104041c50b40b02600747c40650030700210241404158400b0000105462840d0310200110805262024a01c010050403200340f0846070503c520058410500340c030381c03c11024001010580c00d088a11410242c0f0340c4c0d891601c524004071180181c005440c40801c0107a14003a424512008002542c01244d400d0b00004c1d50705038502c1040400081036800303129024840c1c7e040d01c221800880c05034112234200040aa440e0343e941c440d02da524400c4640580c0140e01c2c80c4600d8101c1c1519020941078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 257782562 1250 257781312 257781343
    0x9090c0c0c0e0c03070815030304030309150906050a120908030f1e04020102030d1a040608010f0c170106052104080301030201030e0303091b0a09050f070f05190e0604090e 75
    0x10715100c611a8942c840c04441040260f40e04201261003070703204800056028811090095642000f10000303420743d442a0f105500103215501d06001e5501c0120800c003210203a03040c2300f20035615129010b4540d0140f0b4600c0402d01c8992829680d260405070071482078294003501c6030383c0e24a040ca03081c44400e0400d560f83d4030b51840c3c400514240bd4a04581c0c40e0103260160011424070007880040300c06000260850441c0050040081c00a0b454a00a403006000c02c040082411181541007100f00d40e800500d04007041080038a15965036400e00b4441d040d1407161800e2581c070840c2d00c00d072240c04018840306c1750591078000b0400c000d1060850246069a00c02d0742c0610804400220340340e0f4a0005032140a4a500300c2d002442d01840310703440040f00c0c05405803110803040d9807400c1c508100e4208560303505d0140b11440800101c2c0e640480091002c00460900d2810480202041e54040c0d000750204c1084c40f8072071101c004656a42d4007620010220103801f84102100c10030714a44860300403070445003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 257783812 1250 257782562 257782583
    0x609100b061206060f09030102070f02010e0613030b060a030203070305070503060a230414103c0908040312030c03050a0b0d03050325080103120306060e01030207020109090c0c 77
    0x40e9140c003504450040e04440129142c0f41c0326034080081d1036119109401c40c0c080308102819083d102800a40599801002d9070700341d0a0541c000500543e0500c540c80c0c1c4105810400740c624004c60145401c02d803a084980c5603145e030ba404010070307014038990300060f516100b55240001003050024004041d14000d9090301c14545a13210150705503040c02010315621404414a411a03040110516902600030076a081e00400c00301402e42c20040001040940c0e2900e5501329440d44603a09214161004507007504000d87c1140c02c1410b1511141c0d800350381c41c2c25140e1003454140b2588000742c070051074014403e00001d0990600c064010501c0c400f007040800d04103000038812002512698459185c0509908928051a6011255540010400b81d0b07940c000c811249120b03082c0e2100d0403024412078560000e00d50460a10350000003c21003081c00701402c140d0188023007a40400c03c14a030340c4081c280903868900f90310050300c4088081c0c100441c19450182c0302120035920103030348804075019030403498 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 257785062 1250 257783812 257783831
    0x80d090602010c09031203060b030a0204030311030903061303021f020306010e03010b06160309091a130b100503061f02060610020a020603060118030605330a0b0a02030c060910 77
    0xd0a03200f44a41c40000f048401c5000c1003c03500700e40040101c2d0b0a18a400660345da201c3c1d1a00f20650400e40c2d0b640202d980c0400c0038000c1541012840c0c1a030748000c8020350901031290006640c1c2c0360014104071100701018030110402d4020007900c0d80c2900f05070300110303031310080c10341d000003d400484105000510303e01501900e810188221034003a100034014a2030040300c00515108881270103070440070008200b800003150101480b444003240040140005000d1007603080182d40f603100b91030301d4841444c0580c5900565902c01080b143c11540e410516103035038032030f40003600120302c1d40003070541e084100c0c01c00490154081005803054100719000440741030941c40490356035504240007500b2240c1000840c1c5598054900c00003040f029040c400b0005859130f4895003540c0f800d8801c511001040c245401ca90043d10346540b848000c002c81d034440c0d48040100145c580c02103480b034845498400244220628400e000304c404400a00c4111001402c00100c0a5a5494003000840701540381400780c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 257786312 1250 257785062 257785067
    0x8030115091517220311030702040609061406040803030105010f0c020d0b0f0709082a060a2d080a0b0f12030306040c050301270f06031a01050102060613090219080d0906 74
    0x8018000071032000342004d10a580c0d096441e000d820300f41c058984428880d02c40103179514002e2030b010b03019085000c1100c600d86031203803081c01843c0c2d541c2845218140401c1c8500e500010982e41112000d10f00b030440e03000e14607020303a1074407a615000b07500310b00360701180414001715013031003030041c03a04500c000201c0d43c40c2c1d21700303c80c0f0803514003800c071aa401080100c5203e4031610002140400c01100c3d0a039040104800940310342e1041d04841c005c80d9a180490100c81c00c0f0b0106004034194040c45078010200c4003078010107000700280041c960f10307a92002d60005031034440054042c14000707481c84044940421f1455903e40085070141d110740e090008074000343e072244003501c0c1280c0c04c042205104010705008160f01c100400c90700d180c4280e9403900800300e08502c0c0180c034025800740b59026004507005189084030b00050708140c0c1550311000034000d09072100404425290300940f13002895041d82c0c4000b03680c065007000c02c8110707103500000104a0000100304c180600007035403503206a459a56209 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 257787562 1250 257786312 257786341
    0x2181e0a0302090c0405060712030e0307030c0b070c0b0a0207020f0a03030806061b10020403060c03050103110409050307050105270a08070f0519210c08030115091517 73
    0x18503800a0500c14100014203244001e55040400050300505040e180c1010503a10b402c2014240d80340e01201c1c0420300300580610501c1d62281700d80d4081c40c0b910b2540d40780038040075844503000301010340882c002040c451180d91011a40340e4001a280c403a401d100003458042d4120340801d900c91a140301a641003440d050161600701e90703054031080e40a94a4034108509500441000e8041c0c903040c442c04943c0680030310a075000107804c5000180c0316070031400d04000722512064010245445d010050001c42c0c00094894001ca9044401007004030341c1e881c0075400c600138041c0040180d800c2000b4400060410f07282c0340c103280d4010a441250501842c00c85569416046010b8101d0104224100200b2801c5143d607074030340d00450071580f00102c601c03d0981182c04e0305a083d100002d0364111242c101c0d142060b000d440c1200ae02e84074002e0025512442014032040c851007031071018800d80c90307442c540912a0800101880c0317091807900c0d50710751000342c000d244240220707942405000004031118103000c0f0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 257788812 1250 257787562 257787619
    0x20304050a06090302030c06040507060e2d0103150e070806060f12060d140f01051008100c0e06031311041407031a0d050a060b1c03050d0f0218 63
    0x1808081c001c0c2d15000d00511080710300340c0840c002000780408003402007010a019600c680020810f0034a050381c002c01100714104003a11804401c1c0e010b164004540c0e24850800c1040440e0034152300720000160300800349840325000400080400241c1441003400c5144031f02a2501c440d0007a1b0790b07100c10840607220306000d44850100601071a140c400c604a0850350004024020104217500c5d51102c5a24a900c08052100b035480300000a0110400f8000d164000100c541c10005070303030425000940380e5407900b00d0b18a1082d51198002401445000c00c00390f920b40240c403c954078181440207158070141c0700025110702503980c40c1c0806905151268001c80c014a0112204035141c0031400c13006000380210303041940b1100c50460410303544201c0e24526052040009202d114a41e15203101a030f680c40152a1042440207001c0503505403180c1c0e21802e00fa81441e180355544030006600e002450a80221280700784040f590701e0f100b804980307038004030340012030b410743c845d554a00c40805040300821 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 257790062 1250 257788812 257788823
    0x60503010f0e031c0f020c03270f0d02060d0e06040c1a03010306050912030a0c0914062212140105135f0f150703020d110d0c03020304 59
    0x12000381d1134244503c446103150401c0310701140311651340300144280d0701301284110b501e400015045003d00241070701524105280c46c07080d51201a900c00055002c055000307014014001031450004654820044a29041c61072900f08100384414402c80c0c1d0703d5100300d50840c0c04ad610f003500461061600302c41e0802c0070b40320360b94141c80c582c21540d130030703000d810040c1032480c080c0f0a01b00345155072600c2c08091803040c0c900200014103c010088000d040720300603409418141c04850740a440c0f901d95030200c0d4003405003140899100100c4020690b55004560b00c0100030054100b0510300704400d118803000b110513800000e20840d114400203000c103000920004151059081c0520741c200e2110410413401d800092507200302d100340360840c1590803030341000d000e42c404109402c00c400402500601894402c48002031003203d03140f00d01c4030340e01d2084540503036003640c4000000301e40d00d100c0d07011100140b10949082c89a4100e8101d504899000021031a981e18104980c140800c4c1c03180c07003500d209a4112 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 257791312 1250 257790062 257790067
    0x7050a09020c10090807020a030b07090504020405030a0303091b0e0a0e03030603060411030c0a09020c06010e0f0a0b0d0f1b06021204120201050909040f02031e0a020127030501060503010f0e03 84
    0x42e54034030001c15911320121480d8006102d9100565075a40c00c0000541c064403102040d4542854001c1c000c82c16074000d9842a0310510040c0050703240055841416545401c0009041c2c00906007011180610020906030580800001c1030241c5001c41e00ca00514540310144101d40e9200c0c007440e02c03804100e44050309603001100041c04181c80204c100a0018090306942c01045001c0104000708200c0d003200c81a01d400084032082441d007008814014614800c2484483c2803440e04034001c0358001c1d10107902c003a00c0342d60a4603a503590703030543c07800103078400710841a2140b149003801d40075603440c0a124a081810a000410600205e00078030302000152099103880c0c1400f45410b01100c0070700b0240e040000610024405494102006024a00078654181c0800440c81014917100c1c0b41c103c0c03000e103c0c5401c490074511440c0000c0c1d103c0b0850342400d004000c0000b40d400b400c4001200502003803101048100041403100c19032080d0b05844043d4000d0001c103580d0308114080d9a244a000322059104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 257792562 1250 257791312 257791333
    0xb09011d030606010f09081204050312070302033901050402090708010b0d091b1d061009180b03061302180c04030b15060a05040617060a061d030601060207050a09020c 73
    0x60300041c8540303e001d0030111b9085131501c40051410712000e00c1a548010005028010380ca800c00c40c5031401040000260314006066a0094603400380b9444024103402c03c4c4141c0070107142e455441c52030681d0880e14081c406000040c0c10340a040b0540d01039004114000104000920521405043e42c000711401d62803c41108800802450f0001c0242c50208100464100f00f40044031107400420b0050640700fa001200b04128019490240c10284610350001001d940310750010030385401c480c201c540d0300762503a5218819601501250324415414002d0200b0420345040c40414903604a000741ca59034003104000c00d400303559007001d60b06294201414031003007000858814560b5400b184030b9020362900518500810f90f242c00408000012407008035090100035404480702c109800f0b022042c500300c1c200100410030003401401402c0820a00524404301644a00020440048090219625034de540e840007926000c9900546104401f0180700042c42d00c3e044c0251400c3c65440b0780034050f49441c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 257793812 1250 257792562 257792567
    0xa030801120804050d080a1206050a0b09040e2a040b0310200301061e05091e04091a0601030606020610050108130204020712080105240304020f09010b09011d03060601 73
    0x1c1510449596108200c0401e0b41d441c1d100d0741080c03540c401e40d0015110180000c0c042c209405903816544290b103084810840c594440501200b110003801c8030b00e98698108002c500509807084205100c0c5c403070060914090b4200803040074950a0886544151004070010801503401c43c2034820b601d64849511380b44440016400b07104540c00717001ca20070102c001d982c480d1000e0b8100364003107070204402c3c00400121802c0060120503909491401c2031910700911b00140a03030410b6800340901c9d00703000011043c80e80301e0303511080420b60880020502c280385c041c0380045480c400c640725400681400c40000300c45000041d9a0301400b811480728100c94180001100d405100400710000d20291206020160320390344000c01c0f449000d800010110084100042c1c00b101060b44028011012000a80500c00c0c28190054900f40b54031003466980d1104d00002e06022080030507aa80200000300014013030b00140f00070074100c0401e88030b1018103107040800c11800d00d80000750a07016044100010b50030361 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 257795062 1250 257793812 257793839
    0x51005120c01120f0e06010909020907030b130e101e2d0903031409010b090105010f210b0415030b060901030c090209030a0606150809060903040b0f09031507110a030801 74
    0x2511400041e00703110754185141b410b442039100786078003039070b5006510071360401441040d401011b60409200c1c0c500d080300407c15080110307031000c901e9556004d9442d217000081c000176240a600034400e100f04552081800708891502d401800d20343e24000030450742500300300d241e1705c0e2a00302d0f00710030076544010100c507400790045080840805035a03640500214000b24001070180c0141c0000280301b0b0640c0050014a20301a00203a05000100000d1f40d04039034041000c98050200f03c20170280c1c02c00e04a590340151011141c8507030710070b0034030080074500c6411201ca802224080c0e0b076401b030161116424031030300910a01010303007489141242407102134101d400405400c0b20140482d01243d106448132000c965598000d4002881d2030020603500304d50069100f030700510400013901c40780c145200301e136640c4d21070b43c8141040c240000c110000c51200e8401581c0c00b00304090203480501410110a600c3c4100c1180c003580030542614005505020010750b61503400e03455201c2581ca80d00780b040160085 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 257796312 1250 257795062 257795081
    0x100f1205071b080904090b0105130902030c1002070f08030703080c070510271104060503011b03090203120c280309030b0c04080102130503060f1003020f060d051005120c0112 76
    0x1035030801c555005a1614412021047e004080710b8085504000401c40c1078090765070308044041c00d02c01c41002680e008904850001005c5500410140c462030042e420701e01c259019450b0301000402c00a000340002c0700800304a8130035900c3c107003180d030740c2013049409002d80d2401070003c3d44807003028400580e195001c80845403c0401c41c00d15000005401c95100d08103441c101c68604e010200c00c81c10382018002c12001c0d0204400903c44044103442943d164002c044601041517102c900b05410f54805102120315903500c003442643984d841046041785e0b20408003000c0d0001c024002954142c01268003a0241d00d180e146c1d4441448500d152906a56800d002c0d00462180c6410400010301c01d000b48001c05241141410640c4c41d80e140c0400c141c24084010801d010a11035241040b4a8032200d2405109990b412207503884603851500100710b090158022212a03989840140a8082203c41026007100c0381218504950304000044684540c0c80b807a8450208011541001c0d090075950400100c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 257797562 1250 257796312 257796323
    0x2060403080403210606021006030215250b0105010206010f050303030a050601090f0f05031b09220f14121e03090c0301050408030709080a03050412020f100f1205071b 73
    0x340d54680c4c20744150b520100704d036041c3e5a54505080101136014003400d41c850803608401c0081c545190041103244280c44000000b00c20001441c40001480d181205030044080f1002650b041c92848d05e00d910140c03c2c055540544502030002035001d500c0800e0900b40c0d000900610308544454007000003074031000e80528144042e540d400310300e40d103c501910000340078011048120ba8a08420700d4103102544540103000302030349250403802e44a91074000e07005620703108114106440504410802c0c000c9460003426200030401020a0240b040d42100091020360b090b1141c1c0036400380041000c1c0300c0c0b600081241c0000b4a447c00c120712080300616400501102500d8080e0280c41c00a4212142180c0031110801e0200500444903070024491010340414002400c4182c0c00d51006040c50040d0700c02c4c40502c00d08250400215184d01600c084c1c102805442520804911310000c0e10a02951320114005980c920340c3c4d03181c0580c1800303114020385480c1c82d101001c030f04c1002240084444010143c1d00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 257798812 1250 257797562 257797577
    0x206070b131403072006070b0c040b16060c020109050615190b03010e0106020c0612180106030501051e010e13020102031c060f29030a15081b0a0602060403080403 71
    0x2150540c2070000b2804001c50103169107400615040040040514108070608411a2030905a4603504100d0303001c203400900c0c6207050365440301c40ba0070a2041e90010b0340c1080022450585140d039400310f00c412603100d00d6060040c00c8090504a0032a6410303400502168480004141215280062220a000050031510313101d4124004a04419000e074465400c0203000001080079440c0801c205000d0300d224409040b0350041c0d10006030a601801d0303c3c16140d080d022022900c0098414074800f80c47c0c4503200240900da559040c814020a000c0b180c0c0000180212790b048040c0c40441da81d00d040c0c0304050240e26403521059801e02c01d048500b44200d05501c010010301d520707040b4545080d81e90204003038020035443d00340100065a250280c2c040f08003c600032106440d1015a407503400f10556001098544075544e00300703101c0127031403045482d0300f101c2400040820660070200d0480c804e0000c5c11031542c0704500090600105e80746510452005070060400300f00001d204514481d0407e0082c0b90604 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 257800062 1250 257798812 257798851
    0x2011503120903050303091516120b041b0e0a050f090f0c0903070f031a01030b0612030418021b03040e0412020c0406061214010b0d150e070c0510090206070b 69
    0x51850340140c504040307551181408417008d11044110681c000200e1076048030317540070403401401101c8400c0c1126107903601e030080c100700e64481d0780c0314050078680420124090031916002400b500390b040035550084031030100102c0c150610502c070b6224014017510048182d81c5134000316504500c0500469083c05042020091940d800c122036000b03042c1800155010500e940760000c4140902c503504040c0200380c00040011845c4000d0f80d551000e8141e42171140030840510039030440c440c17504401c2813200036a04001c120b0500e41d016000d1021080403002c6090440800c07265a8040d9100c0d8081c1e42c00070000140008000d4186a20702110380d0040b9402d1007082170004055808079080040010490028a00c80401c580500303e80c039102028181007030f5060020052142c41001081e441a54481e6611145440c00f806440010164860741e07800c036040c20f48000700000400f8400303a03024801c031000e0300440005032050080c256801411a860945941d9a403460701ca40107011040510300c01a120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 257801312 1250 257800062 257800073
    0xe0c06041d060301061a0309071505070605070903020301060602030d0506040204031e060b060304120e04151a0712021e01050106080601030e010e0708160909170f0c0a0c090c02011503120903 83
    0x80c3d2425280000c47d00c0e8546869814604015039001818501102c20440800e681243c220b448294002c1c401003080e564242d010b4624016541c0300a4040d0700c0d080b0b0000b8000d90100181074850b4040310180956101c2004000690103140000340594900005000204498035101c2d600340d44600c601040040f6030b5000071b400c03604100c60984080c0600d4003038418240d0312007812690b44504503410030440300046c0c0b0702400800a4060b244910031150900d1820460f910180c96015034031124858484811000003500c440282e00302104184c6c81520440034031a06000300d0741a51074550741c84071981d1700d003001100900900303641c06c45035550710320140e61000030601803c0041c00e07c40b0b006201d80c03d00c500b503074450400242d2002c1c000d2807811042e10000303100c0704560050003085c6030a00e40c40e02e00451101c4524490802c84a030144207992528080280c030101040c12603d40d82c404002900754164244e081e16503849042c0e0110459120602c0025100740310f404040c0142c0c03400c8405242c8a5959 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 257802562 1250 257801312 257801339
    0x70609150e1f03150b031005060d0f050a0b030f060c0a1b0f05070e090a0f020904020a080d0f1d0102030a0c0804080a030e030d0e1518060a030e0c06041d06030106 71
    0x28100004e460366900b0b185541c040081100501c00008210702e9441c200e040200c030480d05001e203601c10749000840e880300f0605c6410160000b407141108201038100700c481c0784020f00070752500500074000d450f40181000300c04100a41b0582caa10945441c181d50100d00f22a007000360090340034080f1011007000c000c55402211700444900c540d000740041c9050014135101003100a1038010a64002c2000d0390000f01c500422002d403a0b81640e14032240e403198400038001c440703280c0105c0080c1c400d4103501000303d5841a808a81460540c0b60032140c0300f100d0294000f544411158280583d03c108640890239100301050f101d4a0f0081d400d040c00e0a46603945941000307503c200c01d03030008858039004ac0c201d2405000c81c62892020303050042c114a504000300300150070141c4418690000410f00c09003424549107041d40c0c049005008503561206150060010071107a00000c030140b060a220380400d0404000f2101075540d0000d00701400d41460052071042840200550b800d95203400c00000c0441030101b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 257803812 1250 257802562 257802619
    0x350106080906150a030803271c0504060e0616050d090f080102120601080a0e010908031807180e03090303040b1e0403020603010302100e180702070609150e 68
    0xa44150904080707011a19003000903205029940e12030000240300c0ea18000710004683d80700d0700c000d80b01d40e201924806101c403600c00030000b83d842c203c0c842d44c2c103000100d04069030141ca80203900c1d900031070050407140da000d28000c00d00401c0c100030225070507140080141c130100e043c0e22540d4982c0b41c0199546070401d00d1610201c00410300f150010700480650030803440c041c1c02d40c0b00c000c43c24507040320543c181c41030000c0d1184d03040c0000705022807100b0740d581d003040c400c08880e0320081c0111046481e2000342540304944090424880c00360510700902c0100c2d075402120310491100000d00e0640751130700d009140701003420000d48401c02008a00391410b1000e0001482690300c00c03915920001052070128040440050740354004010500040e0366040580e810340360140d9215400c00e203040c5081d02c0803100c04032500c0d0701c118240055500c000841d202240b148401d5070a892a65075111016982001c61740961311300030002d014180c581c94800c000703d0020703640040c111441040b04180422091a1154 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 257805062 1250 257803812 257803817
    0xd020105010f0806041a04030c062c030313060b060d050c04030201080907180b150d06030c09020708030402040b0117010f08060f0601020c04090201050d0204090501050301060b0a350106 81
    0x100402c0300140c50b02000e0000e201c804043c04441c5440e654141c94a03d40c0940e12a580043d01d0200707003410710a04000130b585900ca03500300310b140e00780b04020610f10303480190b101103d454a007581c0d401c0800071043d80d0049040801c040300301740c125601c1001030480c00400b150417100c02d0000d0f0014170350a0055500550b500c1c0385081e680c60942c000105030103002489214284d00002d0700704030509030310714014540c50315200d00064a000000014002900b82e8a0b086001d24001c61403500a46c0e042e882407084900c01d80041d5000e556035038451069000c0c41300d01402d40c410500000e405420141c200c8039041d6414540b004081c1a69842a2011074085c0c0010001c13070a008002e0012560401003c2c1d00a001000c110005160404c0001e554625520602d030242e81c40d036411a0441e4040c1d0f050326000181010155191030f11500072100a02d02441924400e41c2003045c001060701a240407140e0154290b81c6114142c2c51445003082030700440720003103a004410714050b9040d40640c400c013034081e01155 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 257806312 1250 257805062 257805071
    0x11106070e040b10031b111f020403080a0e0102101505040f02040b0703020d0e090c0f0a0e130f0b060f040302060a1101091101080f01180f060f0806040209010b03090a0b0a0902030d0201 81
    0x303601012814500c495504144064036051f81300c100c0c000101020300050038201001c20b80e604a07240d102a000d5548010041310010071007204a5401c12101107800b0340c2039080301d855400c200000070075581c10180c007504513840541c3c103205a00b4150030200741d070b091103100580380580d10314044420b03501032041a00160003460340340c0401c69020f0344494100c2c1c0c2c111070500a43c02d0101190009101c0c4c100072100000c03002440c11602c50045501175140c80c0028401c410400c0c404503d180500008007400303608610301044040c40b45030400607a134003c001d00000d142468110341c02d000f220742c440140201448040a1600540c031003d0181c8a031083c0324108900510516070005070050001504407050035030050010301030502e40d042001c3e80456001e01c041400c1030104c400700d004010302c2d001045802020340d0089100034001038003d004610a40c1d450581d60790b5448820b0082c002079901ca01203410010003000450501c54010307820407810200006d41e80440da0000b440c04140e0310106004d40d465 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 257807562 1250 257806312 257806331
    0x20603072705010509130e0a0507090c0207080303151201061d0604091a0a0e070b0a111c0c03090509090615030c0105160f0b0f0a0506011106070e040b1003 68
    0x829407500e19425802408550181c100070010308140100071415000c0d07034600c00d014810388850b401920000c64074805591102c40f460408580742c115500075018414106450400c41c0b0707100292107000c03a14503201450540d10b4961762848101040c41c00e075036201c6019140031010043c2803003044014140e0545802e0b007500d10701a000514280204145c0c45580b5080c008008215a45080701003800c1c2a4282c50f0303d03694041c00b80d40140070045089200d4800d4490104444420000804e00380b07185803180458103d464a13025501d00b8281180c01c0d00e54000b60801c904940a2014240504c1c4a403c00d640b40b241c031040400c1c5904c40445d848460360b8040c0d01800f100c8203684100d41a103500c2580907200c501a8000041c00e24031a180150702ca01109240700814020994003041015030f008002e5401402c18550350207e518094509030861403030140402c156600031002140c9410b42d0710040c2095030707075001c0c050300c0340c840030300840b50021749134000036020381d880b000c40d520045050344000078500b42 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 257808812 1250 257807562 257807597
    0xe1005010302030c0f031914010612020a0e0106090b07081e120901020310030219210b090c01120216150c020709020c071703070c090b03061003080f0c030702060307 72
    0x40c080c3c04c0134080c0c03502c80010440c1d0b88010600c0074620a0050220181d40742c0c1c2d20b0305440c3d8501d0421340d0071103540b13880340211b2520001102184014000c488091310a91140c01d00c00c4141005e12950b008920b0601041248082d1413025003140b600a036062401d040c1001303501c1c5103001c172042d8607607840c0302c00241c18003804802481c07054010111000031801c6241c4070b40010701d04c59047c000644100d6200030760325070b900315401454024140401d600410340341d503482110300f4200d826130100ca4014040000603c642000144801c2c08074050799900071464094908100079804500c50300844070800c400b800101e00504a08000c40410300d078000b0f0300c0380c1a50f070002d0400c0c25a0308402c40c40d80c010040300070036082c002616002d0301e04071048241903480d41d10481d891885070305030081654224060010341c000003a400030004c2c4400340c007030b10080d543d400800b56816949000042000c202480a43c2c511450a0058684560781e101201e1800250b5000500b00b80c1040341c0c1000000c0f20f080304e00340c0246 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 257810062 1250 257808812 257808823
    0x30c1c06090c03020925051c0c08010314061501030e0f1204080d020f0c061c1a130209030a11010c1407062003031303090b0703200a03021e010e100501030203 69
    0x7642c04546c1e820b08070094103400e016a26141c4540100035020405c210349040c0e61020010000309444104990300c0001e5015081c0c040900c401d40e8a202d10000c194044040421458841c580d05c00704407949258420040d0010301102c40c0792115481420076801107480104000580c0b82070b0f0f5010551982c0c07410305804d1030840c1544241086400c0800e08405413400010f035081c0220080703c0d041d0700c0d03c080780260080114044414400182030000d0301c1030641000140d890344280555803202c6150b1803040d440164460315075100e4243c0d1150f82e0310000b103007101034584283d240500d80f00c103001099443e404881840321406100c1508682402c0240c603800c81102400c11007607415240c8800c070b054030510388a010007017805d114543e00300b818408140c4258080001b074101a4000c54442d074860900070300101008562142f8001914074414404800203080c0c02c2c03040d40769000f0700c440c0801c0a01d00d001c030259950703a10115034071100c1c1d00d1400c2c1d5080c40f28030a0f480103070000107140c3d85103004052900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 257811312 1250 257810062 257810071
    0xd18060e0609070506030a0908091306051903030c061109060c01020316080f1602010b18090d11030706020d0b3304060801150e060f130e0105030c1c06090c030209 71
    0x10303840000d04200300c0d05c5900c1502d50003002010002401d00d41c41c20600d42911a0740d0700640c2c4000200708195002589030f12210a40b10103498400030105002800003500301e0a000c00340100b403004680c02d0024810350060300344a0003980c00603040841e088007050705900000030711004c0342d40100c104200000610b45c801e910710214580030809050820120030300da000984101c02c50310020701008500c0e4004d400404c24600060b00070a0300c41000000b08a80030410345110f203850095072105041e081c032641c1080c050f600c0c1e0034003862800e00c999131170ac8000d6000388a411042610341c00c0742040d6030341c0c95440100150700c0c01061071011203100d4903003603031042c08030446a50300c00600c02880706940c0100400c0c1540c04d1420300c0e10f481c05501c181901d0300460001441e030b0140c0002110001c0501c800c0c00b502c540c1c0207401c4601d0103503450300f100c3d400c403040902401c0d40550001d0311110091400c4c186945070091210191416900310703445100680e83e06a03425941802800e1b420421424402e45d80c5510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 257812562 1250 257811312 257811331
    0xc01050a0c05090607050c0a030309150e030705040f20030108061f0909030c240b01031e020306010c0b0901090308060f150d0609150317040e0c0d18060e06 68
    0x103409440740180507400768000c07041c05010302041110802c0300070468100c86240c01441c01061660702d00d4010040c440d28010152a680c1544102c00001d00500e103031a60701e0030040c00781c245242004203000042440d0014524510740716510020390543c40d507544040a8042480b45641c0c0d130501d64544c0c5010740151290701001003406004583c451511613400641e01010004120001315080845480d10040f401412900d44802c3c51800192104080c1011030a401c20078880c40f216800158100c2d0300c402c03840d803146034000b9808040c00003d035000f564801014100070203a46642d84819a903150200ca000308a60340d68140c1c001416000203059034007a200310b50403100110a007010450702e0840a0780c020030803401094a660800294001e503001d03207600a130401603840881ca104540c607025200580c4c1114030030b114809a08100421241a18050f0810341026296082072403540e0b0702c504a40140aa51140b0a200716110680ca142406005420204190b040000907a0505c1d1020380441c14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 257813812 1250 257812562 257812571
    0x3010303050d0b0105040b120a0c020c0a0b0a02012d110301080d080c1b0705090604050903040e09010216050d1701120807140a1208092815050703020c01050a 69
    0x2a602500302c40541c100c0c4000460f522200d0001a11140603d0308020342d40781c00030800a014205011220344289014442445500c50029060340c131070340804080c0f07801034014038090104842c694010416140c0360703c00006c110030164144500e18099034011590700c80303a03900c40b032004400c1d0f0003054004241c5540c81031843d4503207201ba50342c440072242200c092048038400200180009415104003410072051112a5100002c01c0ea44a0703000340070780c9100c0d881150103d11182018403a20307108080f07a10086207400c2c200b40c0c9500c0e800400900f110490764007044580c034148140e400c0f100070244998010036100c0c1551070050034600c0d403d0460f5180f034910400402c104500d0851314200a90042130481e5034841314201002a4502c0601100701d80c030440c3c481404101d84803000482c555580d6980301804d0300c0d00ea05603900c2d494004041d003410610842907442003030341011718444891081d401e40e50300e10f01c0050000241d850440e00c14011a0313011410300d0f62400203001e926804007010500b0030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 257815062 1250 257813812 257813819
    0x10e01090b0406180c14030c0903190c0501110f011a040f09030f0e041d0606010215040b0c0c0a06050a020306180408070b060d061a01030b040903020c090703020f0415140301 76
    0x4a043c00c11444008605e8807141c8442c03503140201039400200644882469507850650264030556200da03a1031806846034070790001c0c400d52107407412030f6583da000040814a901e840300460701c40c0003110f00744040e4000c9880d440b0700c2c40824400c0d03481c1da4500d15070310701c081d0100314100b004803100c0be140700a9907030500c6150000264000c40c149100b040b05e0400801807551840403c00030000c00540034032500203185407111106000070180d215110907401c440040a011141d441c8070310003500e0040504c0f2950021070051103059016114000c115130480e44182c601d41c464009a84055540081c8554008207014281c14800d10544560900c80382034001d03420155030341e15641c4603000001d4043c000e03203808102c00b9603030390740006e404e5604140700380410141060071402c1000003100e1540820718042071664141414040c010505800d40c010300182481401880341480000303007040205a07080100c2c250300071041d0041d01c0500300f6482c41d9000602d00c00e202400e807600300740c22560403060600041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 257816312 1250 257815062 257815079
    0xa06080610060503150d0f0506100f060e040e19030e010504060e060702040e0a11240d0b060904060303090302030d050c101104050405011205064b010e01090b0406 71
    0x2a00700c502a143c0643e4942d5008034000b5520000c0107041e0380b0041024030780702440280075030450814068016204584c031489903403d06400ca91040c43c9222900440c1003200901901d40882c00d203401420103c0c1d0304d540f101c0070341d0800803050480040b8407000544a0103056016150746c800032400c2c2046460903040c40c034042d02c01004a8030f03082c801c0c51300061200c01c5407201d400c0307440c60b40b41550841e0754050f090302d0700400c00c40085504a00454501c41e0040d948030001d0f0109140000d81c0054924002c181030b8440041d02c421200c4c1a0002010010164151210310a0000440c000c0d40d44201c82820b41c8100b50510a100284404104090100c0c03007180d0004540e8803c3d4045252000801d0b04c0c1d03181c14501e00d4044c3d40d021543c442e00e01400000da100c070050f5208180d44c460015160195103501e200a002100e640381401c001d8035000c40b90480c1910a5030b4034945940ca408a1b000380e841c1c45d40e0403600d80d807090700100300800c034810040100c001c060241d01c00c0d6071401c036828451682045440d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 257817562 1250 257816312 257816341
    0x605031b0d0f06020a09091b0c0f0201090e01230301050601080c070c0315060602010f0e060105041509180519020d03030504031b0303020405030f030f0f1308060f0a060806 75
    0x405106040c1c0488032030410036408600319089921110541d261000220064481c00e107600c075030303103441c7e0601c28800042243c1c3c00004d0b404800540b2641c5110b082d640b250100d10361040412418003624a00203d0320b424811481030080c01c201d00c0240926011040d640040289101c0e000e000303a040c64140142a82c02441050b40900c00811a41c1c44030710074101080b010200f5032014200d0443d0803041c942c2d0030980e40180055429a8000f405481074072107009045480e484800070780d0b500104018815444c00d80c1015149441c2c0c030ba440e40400d500c548014044800380c0300c518a01c8008060305101700b000038044a071141c070710083c0002c2c05003031540200d82c035849210002010141c0e1100000c1c1010301410700111a04204440340c0701c15a00c51401030000d500501905d842403240c010440030080c0700000f1180741c8420300107000d0410020f0030102c0036503003101000040ca40c1d81c85102062100c400c001e128803801c4903c2035486203040c406035100489129070442d0f0030b5500600100408070404a81c6c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 257818812 1250 257817562 257817613
    0x120c1b060a0c09080309090c190306170a11010807210209011b080403080918070c0203011104050a0b0d0905030a09050415060503070f14070b040605011203091a091206040303060503 79
    0x810b41c440d540d0b000041c400c81c9c494400b8807144461001065601070745d0546c4200d0507110340c0094503206401240213140c0e034a201c40d2004000000c01150398009510891101d034000c5018181a606905c106a03a001503000c0e1b8864098050342c040f07803129803503921105c0c4421362040314204440d50885070b01d44450074412400b02429072600000c5040f0b454807041380340031700003071032080b0f10055040c4190014110b020884080e4400d41c20700001c11514000c02003150221980208102c200601e0200d0b40d0f0016003142e0740b01d242c1c01303603038600718030118a084c0300030884000f242d80c444020b0389c00d100402080b1201a210150304040010040c009a80c02008403604807205052110040e41c51110403244440c00d61240c0d8240440494100200845150401e0080d84a40400c0c0300507070b01c030145181c9404001c0c00240000e003c200d0204422024065401c11005840c00998a400c5045020500d00d64031004041030b158004820003051551500c9204080c1900b10040c1241e5101020301c0c00c0040304004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 257820062 1250 257818812 257818819
    0x227130504030c020a0305060f0601020c030c09090a06060e07020706020102040303090e0a1514120c0306060909010f060b04050112090201050d0c030905010e01060509070c0305120c1b060a0c09080309 87
    0x4107080c54001c0800035000c513801040308401903100e1500daa10340c0302c26144000c000d100310b0701098140d80003080002102074050010308200c160701003084424040600310010b1805205104404114940910f04c041e01040075102d00604101000a150100560001003164810301061000941c00074a0b0707000c031043c8107840300590b118482c0f07100042896201c034001d5200f18000019161988440007022008201c0c4c51044071084011a60b48458012107002d41c540c000138005021460032110707454010b10a00c000050801140d45200d007164401d030000001d40001090400c413070349e80015855401c68003050144107000c00c950028045001c1c00210909130b6440381513180c44148a54845011590403a000780104c1200300c594600a00e01d9008141c0079403a66030028000900501050034540e60590f12640390401c617031180b01000345e020b800325400341810400140c10800484501c5644110311020f13000d1814074081000480d50485060424000018001c000340030020050355890394080c1c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 257821312 1250 257820062 257820071
    0x10909081c1419140114061617030a0c030b030a0204020f0c060f06100215040f2102010f15180c090e1e0105010806131d10022713 57
    0x4003803410140c4035440b240034000c4007400421601d6100d2428400318203003803000410409100c0e082e402c100303131400d000b45001c0c000a603400004500301000144020b80b1112480d00b001c0c02c15036a07014402491030860303170120380e01005002a082c5184175581d0004800d0a04111500e1a81d001ca5110400703040068802e55010454400100415086841e210503003000da48041c900340000440c820b90070b6900c180a11558007400b00081d0002035803a000700b01000304841e1555540d43c1c1c040c000080e06404658003e56200c003110130f8140303003840d0a100902c5030004601c1d07060f1020300c00211858034590740c10b1107094000402454a000c07181c08050b2030080c1c0086184207002d142035404095980c051641601c1c41c504001c3c0383c403c010202c2c508100300c0d02400700540da031400112800c4006445c4594082e05180c09520581c1c0381e139020010101142c0c021028005003445c20a0078104e518024418080e000078242c41241d450382610902d5822030010011824014804600b0140b8502000b5400c0742c0d4030b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 257822562 1250 257821312 257821357
    0xe0a0b1c14100e0109120504030c1202030102090603070210050601091505030c040b03240103090201090504091401020a0504091d030301030312020c0d050c1b030309130e0d020f0601090908 82
    0xd024110303009070b0414040c880303040203011450080c03203e50b405541c0f443d41403441104c0d15204408071001c0b2500100091f84007400c0c90060000c0c41501501240e02d07650810076031006450f0000903610456094014010816030900c0e0728041c0c0300024880d9042101940e0140020382503a40280c01c0d01c4a13a14109449a0301c03001c079101c041c0b00346c0c0c008030301014011040100c140342d00201d10401c030b4490070700000c0000510005409a43c0030b0760b0000c0c045025010240030904065200c003002c0c500602c3e02c03c2920801624460880c1d00502c03004000500000303062103180b00c1341c0035400d190101d181c01c0500720f80d17040d8461a100c0c001808002e0400240106805800190340c040d100110780c1e9500765041c046182c00040e00581c040010358103240651300300041c0540000d1080a00d11602901070751908003038a08211203102d55031422907486503203c000445400c2d04000d49011841a60001d08144006072225407401b01d05074030815542d4101030300e0400050710403017038a016031860005c0740d448040d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 257823812 1250 257822562 257822603
    0x1c02030415060b1911060103051c0516110303070f061d0a02030a0609380703020a0c11011209050321040c0302011d03150109050108160e06190e0a0b1c 66
    0x100d170156929a48500d9002100384000410060b1403088a40c42444000a55040075521401032240842065140064a601160f01c2c1e1a0601a0309070044c183c92a02206644000c200c483c12601a260150303100032500d823030080c00148a410000c481c00600706c0e015558000380e5184040d0100400c4c940d1514035a10410020f100c03d0f0380303c501c10320350014045080219000740c0d01600c0c0310700c1c1000c030b0795240482c1c1d0b228041c1c400c84001510b40e03506d440b004116034803010000c5202c680c0040c100f050348540030030010f0003403140c010141d10840146981c1e9044600104050211011b00c00e0483c0703840c8240400942d02c880520101ca90a091040c0a41404890200000001002d8581500480e0341c150300700b10703c00707940b2416500d40f100208150b0743c17900c0045a41c4c1e1030020040e4010001c085003031200712044030009030301c0000140220501001d0311031012070b40180703500041c43d116280d01800b103030341c4407801a9449030304140e500e036400c1075200c0b900f401c001070b8500e000f4050b007a0301003e030103501a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 257825062 1250 257823812 257823827
    0x503031504090507060302094b0a090b100503190c0e100e03060108390d080301090b0105070f06090213153311031c02030415060b19 58
    0x1d8010f019284450b594400180180d40078001d45482000c9506404006010101ca0804e07800080c201b1400b2038951380804004802d032040c00d081c0003508803510940c0c3c603a120424200605249400800d086080e1b10500004c20b15000b05881440b4045c01000300550b00f0152120440c8520031011075400c540d0318080d02c0d8104a8000c1c40d4004220490240009410080020128006400312102d903030742c414449482e6000c007404064841100d0241440c80d003080e882151101070801c40000302c1c1407144000a00190740304d07804076600b031808801000280304510a0b079030000420300f0b06902c0d01d00140e882d41c2030320540c0c1e800100002c2e5900224404c1d5145e00752075284100383d0003001c100c1d402000c446120400c840b40b20760280d40c0c20f0521811f02c1c0003600c000e0074501c0d11043c2c0c074259084e90807080c1640c0e04002071100414911050042c140c46a00081080760950141880144d503410709040c10074003803e42c588400406e9007040c9080008602c0e203011250355041028071050007044018088480c070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 257826312 1250 257825062 257825081
    0x120608030d02030402030607030c0509011805090103050a050609010b01120e0c090f1008030f090f030f010204030605100503010b090705030a0b0d060501090b011d010503130b1008190503031504 84
    0x40c800400d50710029580da6000354021070084040341c4041da0b80c550102c06841c1c0c42c98440c00090703414460610310354007503030a01082d140300f203003034100c0300da10313400855501c1e9000d0b40107540d00c0e44405011408d0120a00901d03030000c0c1d141d0000d02252082d0400a0301818480d050252090fa58900c80100c10344144583c030058800142400214240315405445c080000d03205a003120403103560014503140008126948200d1502c0014200901c0c101004040f40f442060103400d8000d00c00a110740390401c0c070042014510900e030005042c180110b500305005a40c3c0c100c00e000b80c2c902026000b0b295556405a80c1c0600140350241e50f03a0f5039240804040d043c1401ca054200c1030f9900c6100800130345401480c10b0314501402080101d15680044445010b00300000401c0b2008107000d201030b511540c01507a1269a000c45050209859601d81091034030858200140e0314042c881800301206c140110290b0b4403114092200050227500e800d0744034072000e407000c81007050784a603210044d2a650402c0000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 257827562 1250 257826312 257826329
    0x1707030e0d0903050c190902030a110a030608010c0906020a150e10091a06060d020a1b060c020601060201020f0901080a11040f1e030f0326010816080303161206 70
    0x4032407040301074000041e50104803102c0c040c4c2c200b0307100181400d4140e500c1c3c0c10b01154404124030300e4101d003c1c000358006041d0595850329881100e08143c011002000f00c00c109aa0024103039181a00e1182140c14010000040020603a410132915600051030340002c2d410021648008003040000340060921410a084900682c1c0030700e10182800e510110040b17000d0000c12501e81e61940008540b50341c111026984518144100403482059501900c10b20341d5a040040c05075400715442c0e002100e000c1e01c1101d4180d01e410070760030403d034184955401041c0350700003503007440e0301c94128008034007030101d9860400603282c2c001144500d05800041070b21600034012a40d4546030070480074034085500402000d55104001c0300e041030b1451800c1c0c0708803074100c01241040c4c400c0b5a4111746100c540790b04080c0d0035038081841c41f0305030040c0b590702c0d00806001c4000c20100144500b81d801c1c1100650044140e50420310410003050541d18100d90086168034100303410600c010f070711400030410342d00000300303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 257828812 1250 257827562 257827573
    0xc0c060f09080109020d140c040515030c0d020a1406270a06050a020705010f050c01051005180609072601120201030f0e0d110c091e010e0103031707030e 67
    0x24000c0e000039088084420340d580c0e00c40d040e42c440040d00d0076901c0000000b50405145a443c40100b03003006444003c030303121401942c8402e10302c6c0b000103041c0c0750161010440d508100480c404035140070491485184e0702a503407020081800e40000707035011001d124000c081c061a4082c1c080a5440c503080b1501c03140070340081c0713030b00106e291441000e02e81e2000c0340c240603603400900407461900542c00e40e0750001c4658010700da21420100111404882d4403000c070144501406410a242c1e03083c000d052013198a465001c074103916000410091586204101074181c001c1410321005455600000d503204500e03040c001519003500c10003114440d1076514007004810003034008104140904540c5403894000d0f85c00f07002c62682e0880c0c401c21501100e11220081e4044080c0c9010030f07000b4206a0101c0c0800700550300c24035091170108102c50400c503204544c41c89601304803200340c48030500682c050300c40764210800c250704554002e003100c00d401e80000f00310580c040006410601c0b94214000140180081d5503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 257830062 1250 257828812 257828819
    0x10c02151210030314072109120b0f100b030402090411030f072405030a0f1d0c0a14010503070305060a170307051513110303040801020417070b0909060108070c0c 71
    0x1120042d15003c00c40000340c004030005080b44090054420580c0c000f200c00702400038400d81000c240d0180a0380d10300707011002c0d400123001c03100c030542004018091001c8440718a07203140c0741f588103080200481085040c080045c42074030800350a50760700c031b0b90546030990700e6226403c101c510310700c400c000290300d031084003800c41003840c0100f9000110b84d40701c80d01440d06c01c0f8000c8600061890041d044002a5003840060101c128a410100041480c20000111250b668503844140780758001c3d01c0e00550720200c4030703054600703001f4806001001c0800d18013000c8902c4200080c03682c403010301420f04140d12040400c01c140c4e80e0000040041c001d580c00c54401140c0d0030401516034104070000c0d6481c1c0100b080c103224045a1405907823007076504e818004e03107401c059500c410301000c110080343d81500c814072000c9440482403000388098080041d4503459240c0d40e40515180172900e4000140c0007000f840990f000b500d6152180e034105100342070480090f0b643c034070100d8040301610805002c0301c00902000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 257831312 1250 257830062 257830081
    0x204030b0112050706021203040b040f1b06120b030712170316110c10050f19030b120c031902030a02040504030305070e0405010317071a150901050f010c021512 70
    0x502c815071240041d141c6441d501c41060380c03500030002e0125800c0714200005000075103100e9207507034807500c20b001c031000f03603007850b107669030205958102901ea0800c140c10070720000750081c0b07544400c075503114400d02c0f040042002080e181d001178410f125102007064504800c11506e0102c11400c8030520304480e499181c0060280342100e00006094080380600942d00300300c02010610300c2c400e60014000050402c0c000b80125034540c00600d502c0b003944418050002100303128000380721950348030395001c182010108104011003132941000d40c402c0e4410503017250144c8000c1464003905080000040700d002290000ca41001002d42d0000d42c4245030108208c20035805920850040d00aa03440035103c2e0602c1c0e0611041710300038007003d007040d04030390994004820721400508099106902c42c040f84824068081c2d80c00e8400c1d103107035001381603a034500307003050a01849641c01042e089a01e9020481d0400029140c01e40610000c0d0003205c45640c0090f44100c03d42c200c8001c107002c24000307040c624041c5c0300d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 257832562 1250 257831312 257831339
    0xd0e031605060a05060402070b0412020309040219090b0a0212031008030307200c011202030408070f150c050f03161b081201060207050616020a030c0e0403080a050c0a050705010204030b01 82
    0x445444c98039020441500b443e2083e10000780e0712542418440e00c46469901a14001403040021032108122241e0661518006001e282e01c909040d19031051543c100500045107a402c0180010814005002d00e643d0018404015281e6420300c0c0d03a4940382c000c8640c1c100040303500001460312002080c041d01d1503000280010f900100c00752900c0d8801c82c01d01e915111302c0921380baa40090100d01300715a410b14554000c40d003081c4030b402880c0c039101e000d5450398004a007000050b51142054103120780e005400b4013404060340000d181c807500c0c04e2500d801c54a06804054140464003883e000045102801800c100c82a94601107041e1441d6072640392038200c40d4841210343c032204419100000c1c41c28000180c110a8981c010134090030401d50b40860746004680d20026a88a4400c00d03000000c0751100f00c250700606205042c94055141504020709022070103002620740314a0f200800191031000000d40e04002c0e42450100d80d14001820001d0290246403c0507005103091800010070b03030b000d20038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 257833812 1250 257832562 257832571
    0x309031101020c1206090d02070f030213020706050c0d0e06060a261006090b04022110031a04020f0f030c0607050c1905010906031a100c061a030c090105060d0e03160506 74
    0x21262560047c00003262240410310a410344402c0304d030070034001407820f10019a40c540d02c01c4801030802d00e542c0c486005566003030b03503240c505020010f40d44225075468010395601d4006140141042e04241000ca1001c0ea010310a082000c22920305074801c60090401c001d2051640c5001c6415082184910302c000b411240b107401041864008441c2c828100360003500c1c0c01908081c440030304840e4003403410100d0300008005880c000e103c0740000c00042d90304010340801d50350704054110946480e2040c028810f40d0b0000e1540310f00c0700200301d088242e600065241c420281620483c7d2603001524000e032031b106010102c00c1e403099111014080c018081030100c2d0845509036212107045560385003d0f0120f424900072040619171340241940a07003800c58481107054410716140b2440149a144c0030120f40b05108a11400125410000c14518040001ca460403034111100006d5500d03040000d0441e204030b803507500c0c6141c1c540113000c40480c4188251041c1408001d040301c0482c2c9245080f6440324021103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 257835062 1250 257833812 257833831
    0x303090a270911280e010f0509160f03060306050c09030d170a02090f0603040311060603070e1302010c1209030b0a0c020a06050c22030b06030102070309031101020c1206 74
    0x14040e50380c4109078081d0021658210018554421620052004e8000080010300d940c02c1034281156410000606403030042011041d000c007194140122075010019a5015502c00d1584005200104110104440c0c0f5010304e410315448080c5c0a07603058020b42481c3d8405440c8914000400840f100c085008002c0718000300c0903a115814a07800a84581e0303c2500713000b02244a0000050001440340d005001c1440700402d1840642e0b07100001a116a0044804500207004485590f803410810030201e43c0000084000d05042402c0410703031000120010a48080c80703841d02000410f59000d40d02104886d034010107440100307001608040d00c000301521003280c19001600000382c088220348141120485250302408007410103403a15405001c000d0000d90486c541000071600504c03d01c140440c0d620600148440141e00e50f040942500360011320481c003a900411940e070000354820040810360368805060005110f400e0f004078501000c0d0781d1410b4101800304403468590100141c00c922611224 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 257836312 1250 257835062 257835119
    0xf1d030325020a0f060618020c120405010e010509040609051e15060a050c0f010c0c030305091204031b03060203040602071b0308040b0f0d02040f0806010b03240303090a 74
    0x70301a0000009601241c00c00507040501020002404001039500e00b6025081c007103074803911014640701902400000e008116400556011102010700c462041e1031400c1c3c1c6090300302403030140083c044d000344103071407410044001018010f60b582c03948810043d000100041100e45052003504000e00c40d1640102c4084020384001051074a10180c1c0c10201803011f00200d0600d80814000e5402d90000307103242c0298000e0b4120742d54428000d204030001510940e46040f814469800c015045410161900507941c02044800e46490511401c0700c086980c00010060ba40c641f84445005541d105d82006040030300000030301003031200c0b0340c001d400401d004404004158403d80c17103101c040c07241480000d00c00d0405000030002010208003909903442c4125421746800441c09419080768066081003155500e403031000e0048100400410b4050140e4003042d82c5141400c036034050709c3e41950800308140c02d080305111001070300d00b0302c240c0c0c1c505600540002c07145a00c40710b040b0303080c01c0600354481180b100c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 257837562 1250 257836312 257836351
    0x60e010c0504051f09090c030b030f0303011d06090402062107052812150302031005090f060106122d0b040f0c051803030f070b01090506120d030f1d0303 67
    0x2880c2100b0008280d07245d80294900e4500d4220282c0280e0046200341541c1e58209082900d0600c000c829404462020f1503136076052014500030a0704000404602c2000705040080e6602e139090b0f03858100c0d0301203034425100c211094100150030741424240d85125503202c2841001ea80050140c5221020a40d000079000aa403410300704001401c00e8140000303080c4601d00712581002e0b4000200c25102d082421a0591a900400d01d0700340a514800f50740c6d07a41d50100111404240426016400b521019014a5140410091803a103802c075022030b030744d96603c42c4960f811009114071903004014480084660322090181d400030209110102c1c095030608030003040309200c80c4150041c8140b00e40355141800800c07a443c000300620503882c90b8051100b003084d000b00135034020180002c584201501a803540c10004280c084e02d070058401401200b03400340d89043e049000c00c03114a041014a0002004120712410501034201c10394282c80d00100408140e0900b0400300c02103200780c803102d0031803408081 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 257838812 1250 257837562 257837599
    0x6090706140909090304210606050103062405130b07120201150e090a0203150103120c0f030e01020c0418030311040503120703020307080a031a01020d02060a09060e010c050405 77
    0x3007010902058001044000218503021405941005106040324141a15101091015080340d02c880d0520f00030201c9a00403c02c680c0510006400d0a10703051002c0d528110b15900d136548003a100d0080d0300f044a61b611802442a000d40300c0e0140c5c81740261740c41c45c0d90f414001c1c1c200c1d80803040503940110b0810104d000580140103100c440074000c6007514182389404081100890040c02017035803030142000500240c0d03002c0204400d045a80b41c18400d0b19451803502c83d6a032030300440c100702481828414003000c5490000709613503464040c20b020846000c1f0300c00407410b0540c85541e0591140c036182c042d40380e01da040007281d1055403294500308081785a03c25443d105000f14420750345e0540c8010a10000b513510301003d0041240300e401240d04121b09950b17451450b4102c0f40224001950f00c03154006d00701c010071406400c0c04000e0014102c1c850f12030f000252901e00091002e8401130b1900305c4a42042103541c4000004c401201c020880c4540361a4001c02d550700078400c40d8411040b0032043e0400c1803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 257840062 1250 257838812 257838827
    0x60f051906050301050f040906060e060a080d02060c030a090210030f0b06160620030c030f0a09020a03021e1f03060605040803090906010509030607031e06060905060d02130806090706 80
    0x7021501c4490031030b0318080c100481040342d2988243c0081c0c440d160000040c0d8140070b850090300200090700d00b28640384041c000e01c03004036444550b040d80013030002d581170b03900410501d81008110214554903502d00c079500c8003400003840002d4100900c030303118550059042e4094001e05580150a12000012008200190144010306600768601d40d5501707000a50507800b00b4602d02064101c5040d13940042840085608122007128007c0400020008401b50250306190f20a01452081140303249a8011078501507aa000c000d01034020700b0381c14041311504220940710010700414610745034420b1407a00c48420300240d070420109060800c082815801401a582500d4440008601700b0703080d001046030511000e409030f81405810085805552401e0280304d104a0480d20040303966101240700d20382c0c00001034001c101d11441e0010030b0010130740c000400c100700c4000f11551502c0b030000315001c80c001d2040082c010f074100d04810002420080124031948076414523803e451685940741e80a48120 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 257841312 1250 257840062 257840069
    0x90c020303010504091a010308040312080c09130b06070503091903050d0f1b080306010e0910030303270c1d250909060f0317070206030103020d080706060f0519 70
    0x140c000340014400e0f4206139001d504124081c3c034075208034204a0500c80180034080c2c005079504030000170203205001d02c1e5140b02d81062a18900a081407a03d074000b94503d0040600c442d10482c0741c3c00100214402d6500b04210854006040c035a441c0510301d0003070364a5200748c4915019402008410b00704104c000130f01000c80350004040d10507440c1d4032400f1500511031400540078400b001c503401c4200241a5014104a4422580e036a66820010005040ba101403003a00784a6034001c0c0c108a00410004400e504403030341070502050610744c0d0040003141044e0506141c0c0d090500f201184140480c10880104a520170700e003400045104081480640008854400c0d41c0c520a180e031503862900d664803507060104a1421041154507842c0751b00580300c1641c031160f4000f03804403041c0140312151800b0b800b19580e1030b4145281c40ca40d503020580c640070501c4040e2250308010903070800d1080d41011100b201d60700c038400b008896225442c0060000e024001c442c001c2d1503203400305c165450241c100c04140c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 257842562 1250 257841312 257841317
    0x1309090506061c080304030804061d0c010c02180a020301170a0f14031c0501090f0e0d0f1101050702031b03030609011415040b04031713030b060409140115090c 70
    0x19546482c2440044000c040e0750900b82c5a40c480c012003c107003600095402035110342e41e038400a040c02d040407021f4541440c0400c800c100700162110010200040031070b0502c030207007001300300700c842c0d8000a110b241c80402d5000004130960200401c0d28466802141616000f05e04942c4059426175425661842000014060480c808498010034502d40c40e0083d480c0041c402c4901d402e810388004001a00000d0a621a503a02c4900500c20301c00103005861524015420070040b003800a94015644c4988000c9401884007104030b81041600c50801c0450048481c4001c1c80b041c03c240303100a590354480c9280300d9940a0b04602c94802420110849014440c000c1c00c81805900380194451500740b02c6001a038020109003103011009801030180c0020329118041503151491402d00d00d10380c4400100341c0d45051400c0000c400c0308642d1000c0074081c4d0340c00500d010b8169490300e000c94001c00004001409001064016400e410b030150044d2200316030703005810762107070b54072007182c41560340a0003158003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 257843812 1250 257842562 257842573
    0x30206090d05040b13031e02010e010f0c081612020c03070501030902060d0509030c2e0c0503071d060f1b0706020c0108040618050d0801060206131b150513090905 71
    0x444c4000e6000e080e00c80030007040d0f0314209680b695200c00c8600f0500043d1118448440c90000b03540c1c024203882036945007820040703072442c440400200743c0304420b10001d01705180413483c084045110313922960200c1d800104040c0c840202100a566002000c40240c8248181580840c0f0795210780107101c18035501070000342c01c01e4135480d4810045d14004004030718501c402d100e0b2403401102082007203509048181d40d003640340c4c6c0c6069110555000486108052400c11122210640e401000c03290300460602e0300001070742200d000313020903052040034180c1c06100890100040c0b0354140007840c03030059425884051402e55000f807603c0303946500c1403c025811003d2928a694012480c0e26445031207440c00150301c61080e5614900485443c2007500c00d6400441c50940040c0c2107a4070501400f15800140034a291a000040130070081b840300030b1926103080d03152101c11400c184400054032100c42c42c8102c585800c0e07030082440d040614003002c503103401c5070000368184aa120b43e00740145c01c03902070704 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 257845062 1250 257843812 257843819
    0x9060f03040303150f140f0306071d040501060e010e0a030302121c05090309090c040e0601201c0909020906030718090606180e070221120a09030206090d0504 69
    0x44080e080100150185500d50108680c0b03d2410060003003d00b07800440b8981c00c505010002114818040b2800c0c0180745c1d081c0e44601594000400302ea0000d202c1c900490b48070381050a03464154001114036400c1401e020000c55500e800004a0104500c280d1b03a13174072504010001c0106c20222444082e000d81c00110304d9861082926000700303006042a0010b00f449580d50705c104084860840d00742c01d4542000c40c40c0480c51803d40392031900601c046014505050030a44904103591015000318180407075403521008040d0551203c03c8400781503420750380f05111103400701c07114080502c0b07058000303840400d01117203001c914426a00d1042018104509641d603c40d402c4e55050119042e0590201e248030002500c44540d00414014260503541d884100210f2054156644c007030380c000190504001c0c0401890f50390001e0a039291854100300d1090320308138038045514500c03889071032040b8203400d4410064101c070070380c200c0002d40c1d1181c1e00f111029a40e142d0794a4540c0305040ca44400a2020403042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 257846312 1250 257845062 257845087
    0x5070c0b19020906040306090215040f210501050403020d020c041a062109010f1503080a0f091707081203010f06030b01020709090303050402030106302307090c02030906 74
    0x4195101d503081c00516002600300007400c141c00039402155400c0e16600c0c1c0404505200c910b050242c240c102c0c6c039074101805d000501181c04000d000d0141d50005458480100e070011140100700581c019008012505260900035142c01c40002a40094070071b24040f81d41c80d01b02032181a200124046404000301840805c0242590004800204420000c0380b0804011189801140101c0d0711000001d487c00c42e0f5030101c41074030012085004540b54511007000407428160456800d00c02514099000b1600300d5001e40f8548016081502c3c10320398212203803200c48000412030f0540d8a00130490f02103884400c1039200510017405106441628440d00304010740c069041060161300500544103d40d40326204401141c016410035400641c40e078040c04190b09081c403540d00a00410010004034010449502c1d20f50320350400c4001408660240ca10184545d8020b48503c403c058588260010070340c030241c03599011140204031982d841d11300740c10901400001141c08074940600402e00340707961006032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 257847562 1250 257846312 257846341
    0x7150e0708160e13060501080607110c0105030f280608011a010f140705100c0e0405011a18030601060206090712020a1502010b100519020111160201020a1e0605070c0b 73
    0x22004007084c00000d0000070000d0085501a00c80c150040600740760158000384401d20030700c2d8140045c1c0001000c0b03071999030700404803a84500c2c81c1c02e40340101e4a03490080b2030100d01a078205405440030848035030302e4001c1e540040c800c6030032210092100e0140c9542090520500764900303808036032240c00645400b03008030318113035041c4240302080341050100d8880c103003440139004140520341d0361407004000e040d40051100c1141c1c08140c1d0100f2445d03051600401e0301050403810740040041c00718951036400740f04114001543c1019007a40c10790350b580c07640696944000d640a0207140160b020201c1d211904601581209030000c02c3c40c4052458a0b5420460040340802c5001315525007078544501e4071001e404c3c9030902481c0c0d442c43d5a40000080c45000c81114650f00700443e41040144021640003500b517903400d0440100e0600d940101d4801070345003008000004005e05810340801a58014440b035a440e01c03400348005100a6545a0080fa00091042c0c0002d00d92244d0501054055006c1c120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 257848812 1250 257847562 257847571
    0x60203010f170d0c05031210060f02060f1812070506070e06030702030307050f12041b0603020f04030809010504120c03061a0d0f11060408060a060503030405010f0f02010207150e0708160e 82
    0x50b0791030000701080c47d040d0b030003045601c1076210419002c100007466000c4a007941350101440a85200c0c141254039420b8110042e00320402140c002240d054040c2c01840241034403030700200415514000e074070304603413114011184d44020035900da00c80d0f400d46c00c0800c201c038461802607024510f103a4400300300351020740005001d01d4200034103000a00e0403451101100c0e01803401902001d019031070741d000c0800040d0041c4c00000070940103001c078402014141d0240c0f01900da100c03012585680c20136004807000d00950340301d0300b0b50388101170550342441900344581c002d49001c0c1c50140003007003240d0748941c80e1b07840c11030b08560040581d080b0b12021072220800c2c040d04911900c1031700d0045111100181e06504a504010344a820182c20705c81e500f0003c0c03003008000c0000b5070155041502d00000038202c90309000c04001841301080140407014400e41c121109070f84d00105486c04c040694001c00010300486500c0402440342d8100440d054000040400a800f1028010b800303240c1414604001d0000103803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 257850062 1250 257848812 257848823
    0xc011401080616020a0b130b072706021908070602042309100b0c0715021014010e04030503042409030e09040c0512011d0a0b010608010506041406090d060203010f170d0c 74
    0x121100b000404414055015100e5507071070a0501c0c810010b68402000008190405440180c4ac2000b005802041303c09824841d542407803d0400c480c14403212500c9000c9005066510010340440d21404041d0003032001c00d00d94842241d662800002e214400d5030582c1c503e090107154031420040d0032445002440c20b5009401034031203041d40d0300d16501542d081039072844096006807100502400b05d522440070300746845903002c2031951520208840110000d00003030100640040003a0901c041650178044103c80103160340c000e070003800f00d03080c010710400d02c0407400940c01206400e07661034221045401640c004030300c0c0480a1421040100d5810b120101704400c4d521002080403200c20700140b02150f12141010f816011224a07040500890581001c0180240e03200140a241c5450080d101510800382440b8040c84480c00012603c3c000c0c01c1c1e0282c0d00a0007060400204940354010794103d41e850f02c0e11208060312140c5424041e100e08500c50f0b555030000394481611449114154401800380 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 257851312 1250 257850062 257850091
    0xf1a100e2a0712120b03071415130e04060c05090f13090c03110f03030415030f0908190f03060803120402011403040503090f090f0412050c011401080616020a0b 70
    0x3559241014035070201d10f40b02280e20201300c6414510280a0b841603003400711b01501a0508240300c0c80c01c44d086c0384462a02585510100d0310601c681001112403524140d403800e90116030f50134964030b942c107040b6030440f216410102d0b100180d0f40500140d84040303a008044102d0780c00c1001c20310041d80240300035505040c0e15440761102103040040c1c030402440c001d0b04118004a814020300150072426960b060295008000421070084e00c0859402d00c001c4514010031207501040b0b041c005801142806448820002400d460040b0600c01c030f540c030300d50503444c1d200c8500780012081e03003102d07090f20900702140c00c104111320800405000643d4840d2050425807400c00042d000450290000c0701e046a8990001900c0311091a00304010030703e2541c12a4149403518007268541c04407103010744010a901481040018100e001e0300a9070b080c0c24450000300700c44002042c041f5440c1034284190b500900908000c030341d030480924001144644c5523001080c5206103030341d40d03600ca500024120b000c040c010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 257852562 1250 257851312 257851327
    0x103060b0f040305010c1e320c01060e06030a030c1109150f030d020a03050f04081e060a0203060a03020f010909230105240c010e0106090506090708041106070f1a100e2a 74
    0x20103111103110b091180c0c2340e8541108205003800c443c103c0e00040700c003000c04400c201d1295000100b059881d07605141021b0446020326080910301511b0100507031103126202009045034801c41d42d4459020100e4041d02c0c148a444107260301d840420941c1170041c2c201082100120303025200030040b0303600c0410000d141503910030b001c50a00c454540c45658041c0441552101c80320100304803500501880350852135401c4c1800001c0c075040542c44003d0080c014249080c9980c0e014410800040548803401c2c8003c0420401552242c84540c0a4006000850002081a040050554140b1408040201c1070411040c4400c0415049910422000e41d2550315594582100b030040c580244081e003400315090420304104403a84200604110130800c0034010040458030411030008104015030300a80d41c1c59040c10710a158001003080946100f0107000003610901c9400301c401d105110860b41d0050254072903500c1d01414101b911381d1401400e990740c0200c590b504c4070f22402da054581030070440c0340009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 257853812 1250 257852562 257852627
    0x40908090406031202120f04060f020c13050907080304080307230a03020304090f090c1806120506010f060503190c0917070e10030b150103060b0f040305010c1e 70
    0x15081204d42000740c0b0000c07aa099010040310f109003264440743c9061401d140310b1140c042c0074601c01d240400202c00740c0c08481d40d001b44501c0554038405000300740301d07c601c041c08402602041c0c90180440c410614002520300000c02a6401da401500141d0324020f281d07203440c0083ca24858000010046150011001300010803003d80710390701c280c018540780c030b207000303a0314040b1003070506640c0106007040c5451000407590000076083d141e000003040040c030404141c1d04010041d0b03070084205204803481004c2400b40001d0014100d4000e0b03800342c800d003500e0307410458041c081540c00c044a4819112070b03c0c0115040d4001d52201c810782d150103580c4030398030410100c10f50080190081d80741c000314002e01440606840d20750340038005036400f0b11039901c0c0d03030303115400300344000d24064002d502e1070b41810040e07100750003110003002500801070f05d6810f0640d152509600910044481390b2800c00180116030080421610300c80c0044440d04401d0080c8509841002e45400989112400c0c00070814400f078 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 257855062 1250 257853812 257853821
    0x50f0f0907031514010818010213030602040f0b070b180a021c02011e12020f130b0307090f0b0a0f120e07030209090105041127010e15040b01020303060409080904 71
    0x41d115038003c122502c0c83c00821068100703d4204c085010301250482c0a9660048803207500002c3d030320b003840d82000c0400300150082c011400c0c2143c200a07808000400d122054024005980070b070b022606c0d2403540c0f078070391101c0c030f00c14418001c0c007141b0f96100103031210440c18a6038014514940030b90b80765031903139400135134840c0c05414042d00ca010501c22901c15541d0080c040100c05d0240e840c0700211010111010741261701c007201c040c0e4102d4001a48058040029083e03c10021075180307510f08058982c9107000039170300101c91030000a0407060740000d51910454402c0d01f1501c44409907442c111688500b19803407045580000240008148102543c600c0c0384200305400044c10040c1000074254410000b06040240c80003000340c1c1868240300c04990000d1102038044070486140b10101140d6284064071032005014020182d18000000750400c00b900b402c503c50904406903d800d4419070040004440e00751100c94010791003880001c8007420a41d00424000d4040c2000d2400d000d65100020103a9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 257856312 1250 257855062 257855071
    0x714061b10020309011d030904090606030b04050a050f03040b09060a0203070b090f0c0301020c033412080108011404030f110a060b0f010206091f02040b0313050c0a0f050f0f09 77
    0x4076400404c0100600080c45100110024400c2182202144400f015600d010341c1c08083d116070307070703441c4070038200882603100700c0003107038801100303072003071600c0e051442d01c6210080c0191038500658108121814000c4100c5040c0c42c40030312b01c241000c20040c01e1200540208040384258403040102c00007041c084101e0701e105612000c0103020f1150100141da0a00303410f4111140284c3c018001c1800d0610040251140102c81180403000181c220030414803c1615030302515800396111550004c1c0148250212080041070b152541180d9075150243c1c2241d0000400802e810a45004200040c0c8180901d106043e01860060188034042c407950703003062105042100c00700e54440000c000d41c1004450788e41c0d440700074009001c09107040e8518a840d2a01c00c0000d4490780040c0020181c1040320754180e074050f00002e00c4483e140d02e4443c408a0150b1002101aa55032060315a070710001d14040301c408080d10f02442100c1c03203091800050018401000400c1907006800c43c401000d41e4031402c1c1c0700d901c035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 257857562 1250 257856312 257856343
    0x90317040c05030d0504050901050609030c090403020d170601021b04110a0518040608030319180320010c0e060c03120f071e050712020a061a01110714061b 68
    0x22075203020200352030714142884480501000340000c01096a410a099044030b8040d22080e035a09001c10001e41032503404242c03113078840c41c50014041450350001d21020051170b42d48a01103003010703102003001401070882d43e6078016440b4942d0044103071a0b05058422103007015001081c21140190301e20003036004400f00c0c03000128007140d00091185c0000074803010003410764042010030f040c0f5081544921004040d03280a0007018852700d0b00c1907907540090a14410354240d41e4442000340350003042c4007404c0d42c4140c0001c06100c4c1d054599107042c4911032111078030740c40d1010f40b19900814080140c21100c41c61a45010501c54100c00b23140711805941304450181d074900e95440c161601402d0200341384030f80d41130700541009618880341c0003012a41519000302400111031441c01e0101d00d07003d40201d00034942824481016040400494400d0342151300740ca0783d81080050340d01c82c65890102d4414240e000751441c41c0f011881c103100004000c2c8200c014400964040b202c030240303181204018500b01d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 257858812 1250 257857562 257857583
    0x30c092d0b0408070506030c07080f030106020c040b0f040b03030d02130e0c0c1203040f0606061e03150b1303060203090d030b18010303080a0f050406020a0207080d02070909031704 79
    0xd40151030400d0151040300303500d074109824802503590f28541c50050074041c00000001c141000032420640b0000da610440c1580e4030780d80b09a83c02215002881203502500c20305941e03100b103140c18010342c2d00201c4042d00000042c1440020040908896250103406000070060510740082d280001d01d10600140c40840d14545400c6c1e2041e99000c008001c00107409040c402020304100105140b19000c0c0120600c0d6260745482c1014010b203061400014286494040d000403c0741e0400460b41030b94103228034516000007060419010782e02e43c09404076000066078401c0c0201918a0064801c682c60090455183c58981d038810040303a10a941ea002c06501140700040029494029400c0c0f0b07290503111080071400300d4540f001c10755810b000041c2400340c11000503203414529404101109203550341844075007003c3c00c100c2e000b54002601880140921000840e09102c005030b41c0854400c15802000d01c1c615040407800204030080f01101080000705800d080404029003407402240100101e90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 257860062 1250 257858812 257858879
    0xc0e0607060605100212030403030f02370504050906120c120105040215070b0f04110303070c03020a05090708150301090c03141b01050d0f09020a261c030c09 69
    0x100a084c06400c03d000c66020070400802d07407803604150303a049035050901140700c86031200c000f0040d0040d90742240a521400c0d030240140c40b03036001c1220300145100340c003651444c400d100854192180d8080c5940205039800424800d0414002e4121000d0703801c0d040c0d511004141c80010348144845140b41c00a80d1540103200642c5012040048446c402040c0d15191620503500d19080010051640043c5843d8400141c18004185466100c0321002400c0e02d03503884c59460a440202e680d4001039004591164020826043c84d0910303500600050311200042d80c1ca06192211107115280155019500c0b401c4a000040010307100718051031041e4103289240c45501041d030300c0c110711041190100400b4401201a913600442100e02240c2c101c203020410307200300040000a0a082c000081d00100e081d4400036000d00340c07007031001400314843c00203a2090105500b85690b415503403680f180846140400729a9980a58010720324141c45d0300304400b20f150340d01c205100344654400104111000c034101c12 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 257861312 1250 257860062 257860069
    0x903100504080a0e0108070909180804061101050c0703021f020c0106030309050102010e1614030a1e1e02060f091309050325080405040c0912050c040b01080402130c0e0607060605 78
    0x1030740d103104d081c41c0c0700c03000340303081c440080250740a441520891503a0b08a103054003403c504503606d4290b045001c0c15074130380d0340b101c00801c104a001c102e10050b510300408904810070300300480e102c0c50380682c0108881c4004164044001c4005802c01c4112a401c00400600394030071b000308c030300a6009880d1140b205140c000007a00b074030142c134030080f10b0780c00801c4014031007030303d010306c1805940340c68000401c01843c0001007480d054050001414a40b03110040b91203c0544214a0301c034184075001c801030b00d41407400d110701e1100111000030361000062003005d140030f101c04060320309034074001c10110307034210b80310321400c2100c92a2074103541da508001384011841d13039000e02c030440c0c038001a00c41618255081e16641a42d006d503024480c4602d071075186450701984034640000c05092019881d14413444645041c0d5540c9021940c020b000d1410b106146d40d0342e60141c0091486903401130500080b000d860316081d4010241202848184201c401d540070080d15000d01601c540b40c865000051a54144801c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 257862562 1250 257861312 257861327
    0x303040f09050118180b1506030112030e030304030308010b0717031e090c01210902180403080a0e1c18031505160507030e1c030815041a060903100504080a 68
    0x41341060412500408081c107481840c600d45420808111540c0c560081503256800c07400c0705030394004000300020072030080c110600012948282c80701100014510240351710b86c000c5210250118225100410a8801c0e45000f080303802d1203000f0303200c4c1e44819050011810341040d40c4500300080380384100714a1100381100345402c20080c0001349602c0740d80c200001e0004540d004282d0300d40429000d09a0080352982103403221a5008141d8882c2155440c3c0c1c40700d1406c011a41540091032600c04552aa48288a40310720680700c4400380400b00118091038028072541500c04041003007031300107030240160320184180031b50b2007011022401c0b03800d410208290740c0090032003a940f81130b205240304001e40100444850a07850300300740d60071420510008403007462002e05c040c00c4070b40c4012031008142d4403120440c85400b5000c0858640000d4100b070100303c2d5500d0220250080e0444408501c910b8000054100040020101d074205085160391406460090390300700c400c0300000c500c604005410417031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 257863812 1250 257862562 257862599
    0x30f0a0605150f07240b010c120c02030f010204231c02150409050a090615050924060a0f0f020105071e03020c1510061701140303040f090501 62
    0x40a1203103a0901c00041c0c88002150b2035401510742c0056104640c94040b0295120903400c4003600000c2c1c0d50030703100820800407400c030f00e98005240c40041c0046601035465001a03580003e01a034421451440680c0c0320000e550701030342e042c82603009c83e022400382400107002032314070451340303840c030287c503070f5410301d10074142c5502031302c1844ea20301e03000350f1415180b07581c4403500d404544844026508030450a114401e90300410040f90802c4108581d03100680c10024a0070b1003200c040000b08401036159451000714007482d42e000002001040300b0701d80341c858248030003001c1e040a809804030300740020402c0e40b15100c0c0e400440c0038107804220075a04540746041036841400203110350301e0a8a0b00400d00301084960340d00138001116840c1d860b0340710f541a40d82c1001148116590010405c40c0744021000407151158005c801d1140491128030580d441115032000910700207460342445006100c403502d0795407450300f500c414400000c1c0c080036810b000000306048080001c035941844245030400840c0034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 257865062 1250 257863812 257863831
    0x509041503142e052e050901170a02040c03020c06180706050301080d030917030a0e01110403080304080705010e070e04031407020303071101200f0f010509031209150c030f 75
    0x40080168080100b901441500e503042e0001d01980c40502180a06000803950040c03120842070745c600144502d1880c00541d40704a916114585e610360f540110641e51201b81c0c200740e00306540c0c2200504081d04a000054814180541072511001580d46048030494003000000c4007681c04540007001480344502030801464013038038660508032480e03611000045284101552820200140241c03a80506410b030460211595682001d080b0303040a0141d9000428641d460f082c28140c2030100541202d080740d901494090550390385e91500445500060420307100365482c2c1191148034441441240050143d82c0e40d80e1201b03007024200206102d83e0003640f030b0145181004401c0141e90004155003140d94801d240d01820144000129041b0f11940302d103000144a0900c00700705402e001c1001c0801c0c0d602582114900e01e40030594a00340c41c021703190100f054100304000704070300700300044580d840b10201040383e4040026682e0503100e50401c0314081005a004001e00c450b00b628481c4071900b004114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 257866312 1250 257865062 257865103
    0x2521021201020a021c050706050109020306040b0102010204120308060f0409050a030e09010311061c0f0c140403080f07080c1516020d1e0207090e0303011d09060403050904150314 78
    0x80f40c0070f580d4210b41090520105040c140c918491071041c03040314001a4440303000d103c00d503510740503080650003c0e2071303c52107107007446840c0b0410352051007500e040399030905441c2600f030156281a0380303d80303000e094160400c0e01c1c1050070031291190700502480130310072700040c40c0d04101c9090050407416108040c0d4481e2030018010000f1640340f401c000842042200d00c10303520f0f04040c82198030140909544d41071981000014021b007206d40d4840001d803000f07502d03030000061021950354500e1149000c0100b900341706124507800401814050300e403240c0310301c1e403080c44c05a203800d140e0720380352001001664212800c8c00f00141500070101c0e40b1059402d50004004244541802030015075081122440e01505440d04101c900e00c01c00c1100c00800c0c01050800c600041d80d86055220351007400340306410036034104408a1044081d02c440e110385200e801030a03003503c6903607040f58076600150401d940192101c109406804400b80c0440065215540f0b03160102e01241240e420801044c1c1e03501008160b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 257867562 1250 257866312 257866327
    0x1503060109061101020702030703080a1106011809020a030503030a0204030c1401020a030e1512010603060e040c03030804030e0913020906120304050f0111030c010e06010f0503252102120102 83
    0x1107824601a00e04a051041440c5580c0030b03618024040d91078080e6151080580020a0140e188010114007e00d0368802c002e952103d00e1030b9580b03d1080c81159500000301d90842c01ca209242d00c88040c05d4401891310301c07116541d4441d02e15640058448840700c59000070300300100000481008000c005240078660044842c10003c0c2d110605021302405002480780311005c65621a1903403c0c102d900085000d07158480c54000100d08142406440003291402d440491780340a01550548a01c1c0c2c00040d041451f401e59504580300d50000e8011000c0c00368180111000741e41d0307042810300c6400d611440e804462020300402c0000302f005410a40130b81c8075125030a2101e400441228140c070780549142c0c0d18080401c1c0100c500448121200f0014040420196407000301034000031100012441140c1840e604d40840503408450740c0300742607041e4009001c1d61040c0405508004c90080c0740d41a20840c01d5645005842d00002c41507598480c2d03510002c034104514100100c00000c2600300001c5040950303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 257868812 1250 257867562 257867567
    0x3350c10060303120f18030e100e0306070320270a120f0203031e03090706050a1d13110c100b0d020d0f02180f13050303060d03050412050c15030601 65
    0x4c901501081058032054101901801030300310385000c252001c1e03520125517184c20300400c0f0302011100340780306401d403c608803803640c4a0700340d507403400000a01a06882c0c84608042e40201016030b130308251840f290304203441045c20390020300450020101950b1404808058050500c0c00b006000d900c0745480440600030345409440c54511030780e002c2100f038042d440d280000b81c91409140c81c209000c0340700544242a07400201d0140d8080d80b41902150220303603da2406555500840d5a080c00181c0c0500040070240340b8a010311a5030507001d001501a4100500400141d403104070308032540840020300841c0002040103004100701d0344107001c2003a2181400005c80d4450b1204010b40300d00d030602c842005000350594506061a4003d00c035124100102c1403190b4000741c120383c0241071146200004142003129554441c2041e848005146156203a1080100c08541154140c041200c24480821000c64105044d908640204000e16856905008000c0c2c407411501d800c41c5142014020301440c1c1c0d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 257870062 1250 257868812 257868827
    0x130b0a08071508040c0302090114132903030702030a030908150609060d1a1f05120a1101140310051f0f23310f06031d03120402040e03070c03350c10060303 68
    0x2147d504019072000e000380002880d40c0033f2280060b6140c02290604010582c1146800d002c84060406803204805140e0b645400da0700300321145900000b40200040c40ca107440c02e10092900d210b5a40510710a4604026843d402d40840c1c1d0b0007810703180c0803149031000554582102c0104802c996030104028512400381e211400042c0081c01c007845050f804406a014080c0d1003604c007465803c55860707152a00030190840d8141c81058002c60340f00504081083c20003101c402c808250391100031902032170300000c4905000b00c40fa280b04021901d1007210060040170000c001a000400c0000079588042d08811401c120203880c04c00c40b0301c120241082442c040340884001c460480c10001107641d041d1001c00300f46420743c0c2d5405541c0c000001c0b03c40311985003111640c0154000c2d2810072238851403080c100c1d507038850001c1c040d140381c0c08103a0410004401c91189105411080388030303841942d0b05418510188044451a0b0781c448020a1214184d50100700c00000619440c01c1480318600d181c41c0985000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 257871312 1250 257870062 257870111
    0x60406120b07120b300a05071a03010303530606191803022701060806060d02090f0907020a03020607030c05091905130b0a08071508040c030209011413 66
    0x1965045d203519945014105004039402c451010340341d5411591500301d0b2920703950700841c0340144440c0b0076213220300c4a00041d6416607a040d280d108103401078442c6901c0ea40c6010384000e440c00409161406000e1441a4007003517081400301e84511075003809102d40c0e06c00e40c0100858059a0305016440364242910001da00c540b455007445480310f612002801020b180982010b504400c0380d00e0700d0704890194550f191208060846020b04030303601e0310030403541084152403242e408082404403011114141d070052001e0310340100081e8440d01d0103004940944000c13071300840580c1240d034400c4281a014050680c0c0080d0380c1c40c04129295440401401c030740159070256014800352844160084100d4000b0009450020403411041e03c0c0000e08034050b00074080710500600136000001030b6174000081d01d0044d5140b0864580c42175800641c12100c540004000b42e8098009120000250319000c0c0014041c1c084d0241242410b2101004d100e030f480400e44140010710318100c45400074114009c2d0944c0d05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 257872562 1250 257871312 257871349
    0x170c0d0503091c0801140d03050901030b1315030b0c0a05030406052e050a06020a15150f030b0a1a1e0102010617010b010f050301060e09060406120b07120b 68
    0x100d440b4100a0340c0b41c91114511039254010710070303040803000d411070304090494500402100c5610182400d2100d1010901e0700140854001c1c0001c030744a40c025003050b00c00c500040c215034149041c0035200303010365034181e00400c00490741510500c1030041400c0d119500065a0440501d80701d07401400030018032004001070440c0da50385022410440e03810720500c0e1002020300e45185a040180c00040c03881c0c0182c814244945d403007460004446002103550360940c0d4021310314030200c1b14a0846a4007038401e00044030f82e1040c104602003007004c1e5541410000d58000c0080c54510700e400f41d8100101c031400240000d608146809403241da036203002c800200116001601c64026000a0050713000d0a01900f0601070903010792220050050154040c010000090741d4001c3c0c0740b00d090314141e401e0f10081c060400024580c14202031a410200520f40d00148003a0002404d5565140542100888002c048405d50084820709c80c006a001000c0c00d000900208100402040900081c8406090340c0039441e030f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 257873812 1250 257872562 257872567
    0x6011407020609010c14100501051210050c040503030c06011415160203010b04020d0e0c01030504050316020310021204020103050f071205061f0807080a060f03020f1f0507170c0d05 79
    0x90503481005417203a229400b0720301d0840700c08103c0e80c90f9101d050209188102c1403070f250000a451134841c250316030035040800501b074404600e1240e500a0b1100800301c0f0b040c13040410000900b030300e00b040103005100c50480038200303550606a80001011008100c03a12614109000c5c40351103039054104e501048006501d9100c1003440c1c400300c0d01401240c001c941d403240c40802c103030f0750217102034005120021141058950188801e401074003102d100355000340c91540140020704048200786420700381140000c040b50f24020011030700b001a079020015061045040d841807004558041c01100d801200d07402041015184c580b0004010210900d00c40224030f03181c8001c07071155256400d84000403441c0844c00c00d5010100710026200700f03030036660440001c401c2400100ca01c1e072140f003600700b911142c103002302d070480c034540800000c6005441013940c440003484500d0400213941c0c404054040694540715160780c1c041c2001042441c40050000c0d20084c10483c80341c8500001c0b1710b03910070000380c1c1042d64 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 257875062 1250 257873812 257873827
    0x30c050d03020a0618020901051503061e03060103030519030e03161407060e010f0e18060102010f050906010603150f0302060f0c03031e091b120c0303071505060114070206 75
    0x7450620fa501c03003c1c020514010003031000e0942c580e8501078103802520f00a0310342e6a240180300b007d6106a0281c1c0110405001103a400c0c0340c041c1145010071184540e46c6107401c5140d0000381021000e03402280850700004003440a030350040e000510804090404004030700f9036181e940c2d01c7c2d00c50101920001080200042c007001641c442d4002c64120010403940c0603500c41e10040c02a61008030014003040c03004d40055046803240070b95030900300e005002003c43c2e0741e18410707040c1c0d030301d10103030610303055540701c80344d500e2041098440c1610a90515001b44a80d52600e42e012701211030380ca51083c0720032800ca500b40b10310074108130060100da80c15500c143da03a4500b1850000d00d8007440005c12414000001072100c40b940d02080c0450a04c21080c4010940e15400b40304c0c1e5480090030003081e01454001c001200d00d141100035500d000007048c00340d880550321f450020b07045070700c291380c00c840545000c1c4400d110201039110782584401d00382418148081da8506008050180c024001d105610014000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 257876312 1250 257875062 257875067
    0x30309011d01140d02040905250309020d06052e03051f020f0d09020a09020a200708010c020f070801060b030c0f0706020d1b0801050616060b09040327030c050d03 71
    0x8020003d80c98540b10460288408041d600c00d02ca54003400e4140b5012a15158420445118480c10201000246d49002c501a4041d04204801fa0ba00070b000407038150124030640a001d1040b1700d075003054508075402c84441c40c542c21000034180011780e1846402d20020b000011040b00e0b0070407070b01500030000250a0400060321400404602c10000030841c82150a201c1d040703e444203200710b0f0440a401c3d103e1361180124002d034006140003504403101840b42c01d40d6100071012400087c8107075001d594450b900c060a44480c09038841c0141d00042484080d100140b02007006010709200030300c400c07450400d40d441070f0b00015082d10b5944a00188440c035100c8483c04480303030594414410364454000c00b01c00c000810603540007070514081810704244207441020424141c40009007040d0929941040c0808000c1441c2170441d11207a0b190649c50107a9034285681b1b214034882d075904e80e84040150103020704003802070b0281d0042c4840c81c1060000a4000442209540040d51041c40081d05030a08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 257877562 1250 257876312 257876327
    0x30c1209120a020303010609050415090b12030f0721020d08091507080a0b030622080f180a060801050d020d1a1602011103060d0f02120d03020a0806030309011d01 71
    0x80070003900c00541e0800e01600800991304a80355500e074000b10a960b401840292000072205044050090700d050019800c65400b90b200300324040c2082030f5800c3c00c1c40001345035900400402e0039280d03022542c002007000340704802460100480007980250042600a591904941000005d01c0408000102d03c50390400016407204100b42455106041c81e40c0042d050040594400c0c01b0700341000380f868428100000d106006989207810f01d50381109415803c00c1442600740c003128414010040c0e80141c446240140440f40d10024140030701c101108100404168160300c08000e201c039400040106a440d41035840d002c58043e54a8006040d003032503c9038840004540d4056900c001c042400300c4201d05040840d00021103800800400c105640f03404d080340070490712913078003100100500e4000b480c1001c401c0500d42c400390000ea076000c1c42e0b00010f802c0980360012480084d5011a840c0d4405a01545444d0081c41c1540918645102400001d2000100104114200c00200d8001100b41d100c0d900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 257878812 1250 257877562 257877583
    0x7020307051c08090624010212030108150108061e131407080d0203040f050d03020a050d2a0317100503101e020a090909060b040204120c0605030c1209 66
    0xc0c2c0b403071080e5011250041c01090094000001c9880300028410701c4000703a01402580580500c200f54410580301203000e040d42c5200a046001d402c0c0310100002220020398060a003800260401550307003200508800c40503800444594016000e000100d440c3c100ea0054501400d8145089991940804500d1000740301c40101406031220030320b4890701003c25110b0a0310750030416501c800c408440b040b6568042c038090b06d00c50a850440400803850180c84d071599042c4a8010765262040c107883d0076003044003054021022680c0b504042402440384036540070070030091003008054191640f801001400142c0300ca0507000501d8020520100d00865410010035004080390103404802a020004c0c10014003c1c05400c56900b05404809040c2e0081d111021700542c0c0e1304035090702d0140c40710044c0c003002c1010346409a40c3e200a01203604c80380001c00203859030241c1d0103568401440c05003140c40c86039000c481000020f00038007280100c00d0b412118090b48401c03191406440b0402c80c03900f03144001c1c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 257880062 1250 257878812 257878823
    0x3020909010305060a0e06010632040b0406030608010603113f011803050f1c020d0b010807020c150c01060b0d060e10050108010303030f090f0c23061207020307 70
    0x40c000010040c0018855200c0d0306903070400c0c8640e2112424543d990700d428005c04000c2407505404000e544a0440a83d80285030400072085541000c112008aa80150402c665070780c400a001e003c45500340c0100070062540800030888585143c075046203006455040c0c502c0b51020054040034082c04946101e0700848100320a24041d50aa42d04070044001044103041942003d000da05840048810500c58540603101c0c0d0303240c40c0455184042030390004180000e40c0000901c40441d04a140c409055075644d610000518104200f0014010003002800c480441d8481034440d8001c0c4c441d515520003883c20480129140d03500380e003156000d00f07415004a4516a404110307a040071400f40c01c00c0f0211a0004c400c002c0b03549420f1192642c0755428090a03010419480041001078443d91081700e01c1000c81000040c40d10761907895a0300a2403007002519101030210091001000b4242c0e23a02c80788240088503d01d204c219800309225005100d035800c01c800110000610090080c001c81703059aa01c40c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 257881312 1250 257880062 257880079
    0xa0c0303201309020715090c15050306091f03110102120f0d0509031603050a0905060a030606023304082a060a0203090c0d050709020706020405040b0105131203030209 73
    0x40180350869005600b00c2e50707040300b80709000203180c6418400c54581c20b80001c459522070760280110005000b840354101d0300c0494000c1d00140b001d00440c401800300406a850320b40c0c80c140312040007030f4440040d01c42d81d0f9440440035101c0c140382403440048100c0e94059190301c0d80b01c1100700140e081901110300401401c200054590582c0c0d40a401441d554080600810250311245041c5649000e100300d03000841da20b200c1c0301c20101c1c0c011800b4140101d281c1c03500c0040280c80e0404142e0a401550440012070f40f90740042c80000d4041c041190101c0020304480d45102d88031041101445240181042411280001c54184802001103c10058003816500402c0c0e42c0083c0010102040200340840c44c001c03030010406044490080364000c40d0140006c0c9107900d00d0b4410480380441c01c1c24101c8003071142c1d010014024050340044d040d1a40078040058030b4500d080140420f44820803105c504000c4208010444014507104031419030760a100484880d20461030160000e00c2103960603035100002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 257882562 1250 257881312 257881361
    0x11b0b06061e0403050d080403020a030c0c0306021911210304150c1805030606010e040b0d0b100512070312050a0216030b0702010b090411010e01030908160201090b03010b0a0c0303 79
    0xba070010300482e4421022200034403520790b030844940600340e82c01030058000c20320030750101c0d120f40ca00030389040c02104a0b070b10ba9540ca40c0d50340d040360720030312403000c05405818015030b6a07504000700e00c25042002d03002d000d840c8420f84900c06101c40301208280c0680010022506005c5090f030308400f4101c44d11030130442926a91f1020b02184c4045c0500655010180b101040d141004120140207000607120006041c0701882004040e00300c4000550300300c4a0030700c8203404150040b510354012103901c45981c9840b030134101445440c0c0c50103030a0007207550001c0004c2000031105d00307203103ca2850700d1803c1341d250155003a0480c141a03100c1a94510a1599103010088c0020780307842c18054125500200400c1c100e10782841010b030404c071400350611041031010f41d82c55000f42080003030b4160514002511510742d070b680e500181c2000c036408048040e120140030465800c501c0305405082c8140c00b55045601d0194028058890807550104005d0007541e5002094000c1e0400000491058844240390744e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 257883812 1250 257882562 257882617
    0x406030905071a030603071706060f040902030d050310050303180105130305070b121f0303030e070e0a0e0d0503160c022d01030f0c08010308160503030c0a0e011b0b0606 74
    0x6441146c80780c0146a0002020900745022102c0110594080c1100b039442d10100480520240c00e6282c000d5150414a00165000d02600d82050126150705490b403d00313208209101d42c1c280c1001c1d00907841000300c3e41ca940d04207250080150003d10b00030369145050085020402c1e210740c00182584100c4070f0219030112410054031152018002d41d460680e80d03802408401d115880e504031400303032002c1f81030012900c2608161002060f4808403086681d603040300c040d48200c21200c1c9000d9a42d25440104210742c103000780004000035140003401e608101c4941c802c00100c28548909204000402c00c4c00c540b22251512004201649000d1441c0541c51580021900d840c1c0c400740040d01d0b100499605540318420000c11030603030f40c0c640c0034587c211f40d10081140d0001344501a26000c48403d000001c00800040d44240140e000c601d8451141200190036a44089001d031b0510200345170304c0b500035000540a1641c5a00040711512a4482031301041051080782d41400d84154001102a4042d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 257885062 1250 257883812 257883817
    0x807050c09060109060507470606040e0a0506180408090a0503211803070305030a021b060313031403011203110109030e1e060310091505060406030905071a 68
    0x182601e28015642c0d44200465032803046001d11000300381d090124101240e603820000c05441301001c100014040d070610024200206c0300340fa80401e0310b20280d55035078150201c80450b00110b060310103a081a0414065411180005148215a0366200e0000b030003940e071a00441c0c1800706110f200d110505190818441c683c0c001d990b4140a1604040d00168a003400112100e40c4100e5101c140754059220019000591100f4049d8080100c00c00304191180d9050240e81c0040d40729400440d17031101501006803c180392800c1240c40c08000880c0f40c2c040b5100c16048030340c80482e011040c070600c4034500d02a6601d03800301c5605520300f44080000300310640d80003001c0c0170290086c3c40d203404c084605030381d041c281e070300501d00140010f0600300014441d0401d1403001426500446580ea003900845012034040d81088800e00340301d2441c7e00080041403a02e01c00c45044008440b0b06002c003906020208003076210750b00c1004101551820080280103081c00b241c006010400010321200311848004106034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 257886312 1250 257885062 257885083
    0x151b19030923031605010917040807060801030309061215030b061e0607110d150f060b070201080c031803070c03050d02030a020d05070312020c060a0c0c0b0c0313080705 74
    0x15070040c03415035030104544982e010090080320046141c801441811002142c411204803040e41d01d8100010029849441303400c0302000340e04c80d89440d586041c070314516110032603008200344054140184082980701600e0703c1614030b01d0030048030b0020b41280724001004c80c29011000402c840e1030100411481124050040c80308480040120700d400742c1c600386a415521801394484001c0000b400007a90034414035002c0d02d4002c1c00408101126120000162121104446001c2d9203041147e0001801e10404001c1d00001c00300340d04058050380003800306000074020548107100800051480032410211300e8101011109a0707403102003916100d0100c0c10301c0c0c00f003203896009640c10705443c64400000e0744e8210516900800401030800340c1515268000102542006800c801e00c0b4940c1906000400340703981c816004041c0b6140c918070f40710882d40034501010410403242051004104000d6449410613501c42642c0d40c1ca13200c400250000c0d08003100d00420160004c20b5660500c0030129000414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 257887562 1250 257886312 257886323
    0xd0507030e0111160b18060403020c0a06210b0609030a03020109051b09011205100207030806010f0f05040506031f0b070b10030f0b0618010b0714151b190309 69
    0x42c0c8002d08040915400f070b10720724010100340c88402501060305c4c00c500603084075148456050300041c1350003803424118200d5051340541d20440c206100750401c1e0300c6100007440e040ca06810350402c082d03c9200c61462045070b03c0082a1074969110860341d5600403114950030080858903002828500603000c0c180007003094030369008072040d4049049481a0030380e026000180752150750317030030441e000501b400440010390b000c0c8180550b2600b03c41051004003c00b0740a910340c512036203040c07000102280c2503e040203040201d0364001c1c0c844107410005550640c0c800b101e240b03480e581c800d000c2807000c0e81d03d01c45c06031503140c0160002840f4254000204030060281d40300bd18a5500c2800c103041c00c1e0720310312008156040005a000100e54036028464010100400b0341c03c8000c11043d40080c007240a800000300035070300040110400204100710402540c05502614038881040040f6070030200c01411640380382ca8040c0000d244180c41300c2150f11703504106582070003002e00003600800614054104444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 257888812 1250 257887562 257887571
    0x7080601050603011d0a02130e01240801090b060f03010b03180111040303030f140a0e100b0a050d030507120302070c0602030c0607120b0a170120030106140d0507030e01 74
    0x4180c02c01c1000c0307034141d4204040319580340e0040c0459105003c07006040e442059400d000c0358400340c031150f60403c0242032080301d0411550504c011940e00d14070407500c110042852140944c171254020940c28111044c070b000001e0710341110380214131544200040070604006c00000400e00c3e0a403603002e50f000c4c07501e62403410862801505580c5c2220070b411746425005100740020000240320740c1011600e0b4000e0040451640a101007800003094155640c5c2400c4c0d031280d8003e25414020000c95080041050062004250782400f04d0002001801280c1c0148410021141810700a0007191b5103240e000781c1c126101001003000500a41006000b00d54401403500000786152000040d510300718070002c081d00454a8504094400420340c01c41d1920403034490404600c00e03034500c0351810003401004184044210301c904071908490240c0c0c047c10740215043c403246106207144007502d040d5000f5003010842042c00680910b1907008940382e1504440c145800c1000e840d034190040714102e02c0303a100922 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 257890062 1250 257888812 257888819
    0x180209190f081207060f0f02190e01030b06070809030c0604080601030b01120b0f04020102010e0d0302031008070b0a0c030c020411070b01061103090d0c031221020405060d02181207080601 82
    0x82c0c603810006140580380d00f06003e2035000c02d400e40e01640c507229404600044040e01c910300b480c00d9801908008190954400c1d074800d5080d01700000c0d084000b002d1808204224032040020440d002d0560043c1c40c038000031503035282d2502c003081340e1910701d0b000411058561b0307517501e1036035a103003024001100c0017501980001800001043c107070308002d60290010280350340340b01c0c94000d8990b000b841a0304540d00c0d42484400130005020005642800b0340d00075950b40340070485080c1800701948011041c0e4440c6800700701840300c28040d01c609510500c0d1810b942130050170212500c0001c144003a42c89450642100b03910981080100741880c4580e40c080c413140e9071741c103090751160200c001c00070050300b0800000c1b2035464030307804021a0318801d000700065151690bc5180c98517481000d40c0c0046202d071160002d1085041084110b5484030b4041549464100404586c0600501d0940e030142c58020450410380700c81e6422120803010050b01180c2c8441100d00d860b541d543e481e200340c0015004000020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 257891312 1250 257890062 257890079
    0x2404022508040f0e07142109070b0a09050306060d021f050c030409060905070e030d0f02011401060309050f03090f010e060c1c030605010215040321050103030c0b070c0b01180209190f 80
    0x8560b8038408000a0000030b4038807c80b0301040c0703001007120015016582d000f103104131503c0c01401c84111540d440101d043d00744414186056001f030440d511031220b04141c44010707584c13008100145030229186540c1129041f500b03540c41c0c0a5440080610f020106001c00d0308540c5600900413640440800c2c8030f41d4560311400d031030768802c41c0e102c1070b01a0020f520001601b0b01036000342c2c1081c1c62600c000189811100c030303594403440081e0000c00029450301d40300000e1250411141a40c1407064002e940ba2403c00c00002d0108070303004800c40e061010f00c0440425175a100310564110005200580320726110204035400c6584402c800d0001283c904032020425500c0014403003416a421030b1042c001d40c90b1502c00340d800c80c12901d0f074802e9450040100103500d018601560340294030a4941486404882c6054106400000c005104100f414403005002c2071224404a0442d20f81e0401610032034180850180a480b902c0b002d40d41207400d2a106c42c1c0714050034040601281c4815030030f0940e090720743c03081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 257892562 1250 257891312 257891317
    0x70314060a090e0a0209090c01020f030a020c0d031103030a140a0b030709020d020403050706090f21020f0604051c02040c02010207021f0c0b2404022508040f0e0714 72
    0x20650030401c041414085408280d01c100c140c11405000c0b1280b520840c0e002030f00002d0b08450214070780e0040e102d41c0d0f030030f940c042000b41c0c0d4000c444c4d0007440c10b01000700c2d80296181001541c461281e424a03841c1814035000d650840d43c1d643d4a102030f41c9d500d103085200b40020300314040e0400c50b001110000180c1d4058188a04052244002c001d40351141c60444550040d42281c02e040c0354081d400c100000014504000c288000d2804c0c0d1184503c15240140020b03820000d6401091540d00400c0780b1114205a032051009595040301d400c081c0c0764161003c03d00d180a19040030381c010048020b80c800303062448501e4450309200b100e05104548000038101e00b03074010b250000f900010460062030900b2002a18824a10311614241c0a12180d6456266502206503140e2882603c014085070400d9a01c0c100a41c210000747d80640c9000388061007140a410420102c05070600d0006560b01045043c2c0106c40040400d2012018000e4a804860b900d50700d0580b20075000c02e690540080c034100c03e42d401d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 257893812 1250 257892562 257892571
    0x2010b010e030d0c0b060f040203071d011d01081f121407050307031e0501020d02030604150f0b07030909060b0901120b0a050f0111010c08070906020c030a110607050a0803070314 78
    0x12444d09400f056561500a040054491030b0700c002401c0001c00540c6503880514402d4000c4e0b51051154111031080d0403444284120f11810080c0140800c0202c28200307001c482044002e00e003404c1d1a955104640300450066072200060078000071780000d40c0000000b079005100e0040704680b03548500d200d0201e60318000740c8a07854241e04005020000300784803445061041d0a0b14044003070071900b607074403c4c1c220b074848034035805215808000c0c080d050410344100480070041c141f04203249410090740081c510302901c14492803880001d080d00406110700054801410549018044581c40302c0c407c03a40ca800c010111800500640a02660f0741003a0103005040100980f404050900f86002e000c00343c103403805241d051101802e03a00010903400d00c00d243c0b07609520b0381c40e0511070424000c010681d15895200c50210350014014081c1ca41c0d001c6070408166501011100032090080c000c542e82c3e0045000190850003440c1100050100c0c181c0114412015a5020040c000d00c00190040c0b00d03c042e80c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 257895062 1250 257893812 257893817
    0x5060309070e040201021203270105060a0302040e01180b0f09060115030b0f1314010f1d09210a020105010902070809010e03031b010b1329010909090302010b010e030d 73
    0x107041011550000040750403600610540703041080e80c0b800c0240551060303428035291403c1032441c6080c5c0420328864100128100024031242c24003000203400b00901d404040d00c100da80e900807031408002503000f99460b4145076218a8041c010f800c0c0382c80070b41d008484100f0503001c0710002541400c004500d15050701c0f01000c403e05481400b1008900404510b04031580220f00b407160054241d82e24007181c0c16030291140007061105141000d03801c0068103a021480c1c806090340140b2450003850310340d25010765410420500c0e07035075101e4500d16182e80d40c1d481106000486030040000c0010100070004000a07400038070907070740d86c1c501c400201c0c8265800581665404c0c08a003034a0f40c0f00c2e4007041c5c1600340090480381050a000660107540c000e40209941c2e6a544850918440c14035080010b49031440b01c0c07003040b1104080c11840143c98243c1c0800251508984802001d41e00560351715000e000b4030101000880c07850f00d0080c2c000d08146419501090f50109a00c0a91800080300100402e481c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 257896312 1250 257895062 257895073
    0x702030f06040b0103172a07060e1309260307020105071e0302031801180309080a03050910210518121905070821010902040803030105060c1e07060905060309 69
    0x140c86100075140c0c5c406204016140070010300c107454158440000d0001c08911040c0740a0b800d42c42410314240d504d612100c1131003020240c3c102c45a4440340346401196410314088cc51180924001c0043d1ba104070090f90100d002c5c9080b1088542c07208055840751101d80c008003c243c5400206031100302801039800f18544003042c248004601c607030003440c1c00042c4400d200e601c03070203c04403007425901d00414107213450341443c24500901d030b80400300d00000e0440b44041c101c184c02d2920700602511a403440d1034098601c1414004119214850303102e43c010001c24440c560080300c0c2000b4000e04818ad5a04044035841d42071284071100214214010500816100c1c0c80d00601c603100109a0414501c44024040c0900406d00454100c3d00100b210141207510700c030045c0c50000c10b0410700300041c1c0000700710910500050000b03000004c00c90b41503030703811202151514192146146461501c030359100200c40c810f0740b8058400000940304080d40d4081c0c071041c144544070414007010340401c07101484c007507000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 257897562 1250 257896312 257896319
    0xa0c0603180f080d0f020c06070c0c03062306010e031b01141603091703090f040f140a05060111100b0307051503010609090603050322050301090302030702030f06040b01 74
    0x280e00a0301401c22901c1c0d00109480e00d921000c4002e140d204050710a07a20004040150001c10303c0b0b0005e8180c81c140c41141804205000c1a9882d0b03030050082041c0101070b070340501403000c204140802503a101034180700762511700f644070482c050180e015200f40080c04001c0754496010b00e000c86016a0090020100211054601c0010b80c024181180c140300300c00403180303aa081c010380104803070050010500142e1802d8600108134840079800544203804030740d0080c9006e0404002c40c0c42c068000c03602100301080c480002002000700350104641d4038039028038101e800c0c1090985c00d1140c040550b0801c15551018019101401e902002c003884d0b400070003c0700034110895124248090380034041f1a00240c48001060100944203100040980c02000401507294044103943c050071820109002c60f0380340d035852645da80500300910f4810980046444c44900c1c42103082c10007048000c0090208142c3c0e800c010b501c80e806036100b41e0107806090700705100e550300004c101e400b40b5440003401f1056842c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 257898812 1250 257897562 257897567
    0x717070b040f060219031b0201050108071a1b0d02010c020105060f06310305010c090614090114040b090f06070c030b0a0b0415051801180f02041a1201080a0c06 70
    0x211812180f49500f03008801640c11425a207441424075030b1000070f0070b5805030104011070031100c50403c085a04001c014056110f0205448080321010403070b440324140c44d102c0c0ca6460303015044415105142c42520218000c40010b1158111003054000300b006111945080b4242d4604176801504184506130030746150411100600781080f02c004040e071001004100920341030007090500b2490180c3c0300f003e001303010b4284107a500d00a1203040443e400c0786401c00190044454103582460100c001c02d800c00103074001d8400c403040950100e2402d903110b440b40c4c402c4c130081d0403142c4200c1c064100202c0181160801c00200c890041c1c001e0310050800c2d00d595640c1060680041082c0c5c0003a8464004c5403145c5c4450081450501140f500424094100707024059100f81c0448048070309007041004002d0040c0c045030109589164007400701c0d4450307162524502a12460303205414011910019125503640403015200005004000180690785c941c4155564046400b01400c2b650500c0000c211250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 257900062 1250 257898812 257898833
    0xf0c0f111605010f031e1d0102040e0411010c150509010f0608150712050c0a0e0102030306010c1205040f0308090a050607050705012609010f0506030a050703020913080307050717070b04 81
    0x100519012408507051b650b83e0305105440d4030320b65078450711080c1215580e03d010701c50b80741ca0340071140218145454503c4450201001401c06041d65104203d01c40b0a039100f240741103641c1e900807004180c80c080c500005001004110b5504009502e00900402000c1040c01903104451a850040100201c0c04401c1207403000080c250200b0700c000702881c9900303014540140c3e4440c81003100c00c180c4401410309c0103003900342c8482009046410420030071156a80000100b010140c11080c003002e040315a03d410344051085420406095009140000c1045601c800500605105a81c4180081d0f0b031030052001034000c0080081c0315400030f40061045501c83c440c039900c103019121109000c000110a008040c075025a08050140d454a9000c00c140710301d8019070b90841c00980051103030200c1921015107601003400020f01c11040c00d030100d18a00c405030840400a5000225541d0f2800c2000c405442d07a0700080c001c03200c031082e04402080c2d080403841038481042e0008609503c80d0754a940b0714502c0b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 257901312 1250 257900062 257900087
    0x1c0c0f06140d1d010e010606090612110c0a11040c02150a0506060d06030501020c1615030f0e06010e19090803070c1401020a020309040f0504081605010f0c0f11160501 73
    0x9a9181d180862102d034940702c21845914243c00042c40340c014200007800d4680d01c2e000781c814000500c02c2007000380d41c40403800780f200700e003510f00095a8124400c030240b280b0030003022030090710482c5481c205100400d41440c100c2c0c40c007207030200002488031800360780300c0b0260610819a81c41c07910006080510030313000554070000041c2411725017461441082c00b00c61441e0000e45d560b0b9400302d9440c42c0400f040011040008141130b03850a440c0ca40400c00c080701440760758182c101512030001c15003007140ba40000315404500c40035901103684514400303a5100c412515004e200841021000110382070b4461a00c17001c0d00100340318550f58620105a50304030020004030f410284a2030743d4a00480c003840a0b100d1090aa03000e0b540c0d407005101040281c510f20144540a0391800e400c3c440050f4415044640c04c824400407002d80401c00d00304140102201e01034034030404d00340542004019400019100c2c01055a01e4111090b90203082841d03482c1c1c5100103010b5070503120981407001d036009901c03d409a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 257902562 1250 257901312 257901337
    0xe13140a0206120f0906010b0a03020a0c2013050702060f0619060207050301062103030b0604080102070620090f130e011e0e0a1e020607021c0c0f0614 66
    0x100c040d80480e10950042c01d10f203e45000c0340083c0010805520010ba802c01181401028107504040c0c1886140c0700c1c1d001d80c0c4091641c0002e101c0c0c0d11901805c8141500340e004a151180044880e943c0340d840c40d40000307101d100c0e44103c815210316805503c1180d0003400c403a40145031580d5403400b901c00c2090054151940034142ca105000024a80c2c0c8590018010b142c1c00740c60564900414075003500d8a07600400c58460304c110240f0300c24501c140a80024a070180307400b2400b01c15100100d0000c0c402d0760480c9105500000f14501440001d4026421240010400700d0044000d40c1d4101e40a00850840c284d00c5444501179003201c1c686000300c0003003824500b800054000810b110642110803512010000419039643d0791044503080c4148555000001d001d0914041c4950303951940782c9505403030030803c2d0050850b090654540b01c2c2a12151607000c5e042c024004030b044048602000d210408940920000801045428032460090f0880c0d2040e200d45070242e5180b05101215000061170140303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 257903812 1250 257902562 257902573
    0xb0f031f030f0c0e07050901140a09080d02030705060c180409061104030c1a040602100e0109020418060b0301020426010b04110d0501060203030f0601030c0201060806011d010e1314 79
    0x202e03999a000e0080c0511a454142c0e0191070304000c843c181000805400500c101030200c41e031142d800002003c821140f68100302d503550980170060b81c2c2090b8036005030b8103600c2160f03221401142c0020003409400e000d00111206999802c0505c28a407080c80c0c140c000c40751a000072200181001c0d00b00045c0b0030302c640300219685030f03c0c81512186801a501c16114030181610800401440e1140c059010020400c0a40351500b4444c02a41d5104103c181801e074581d511050001154213611800c2c03401d41c02002800038202c40c003104040040c3c0c00c90b040d01c16929003819601c1601e01442210101c500000821000d00d160b1114807150385510110421195200c10072031245a4680c4104503a00d098488000d8480841c44121021207030147c22050655204105200ca003400984003a40d121009280c00f2440084d1710100320301411180e8000c070b200784502070000c10749040c184102c401c405010040e18040da031381e61610010036082601c2e14000c03200c4140d01900802d5914229941550001d0100ca1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 257905062 1250 257903812 257903819
    0x61516060203100e0a02090a15120c110616020c010c0c03020d0c0e0a06121707060608070501110115060e12060406020711040e0601090f0e0f0c0a0b0f031f 68
    0x6007070307910860741410310841100051000000060034503821101900003141015069004142541c1d03540c040c603c0d8865014030030703440051046102d0641d0803032001c4240407242000a014290030a00841c66805000c0c4200140c5a42d030310030284d503003c0c4140d600600780012100010340e0305d294030301000c6c1c904c1c3c07441c4a40400541c8890707640c500c4240c0316a5000000900c2c1544918840b040a4139000d105030605c10304201c91100156a14945600031321a0490000c840000a00c42e11420300700501d500d003400350018454030040b4507841100e20a807101c1c000c89210720780081c00c8482d070078001c80c840b440390350060100701d03c18103c1d29000d090141141100001c415281468800c08540c02c851a640010752281006590352443c0840c0380d050710144401d07104100c0c060b45031001400b640c0402651142e1048000400750016840250b00006850200303003083ca6140d1602980701044d40584582800042c03101344520440d520030307800c0c800d01c5d81907488840c1c1e00303091540c032074480140c04030000c0b0020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 257906312 1250 257905062 257905073
    0x150d02072f010804050303070f12180b0601260604090f0c0311060306060d050403020c0a030309030c06050c030304080901050702060d021c020408300c03031e061516 72
    0xd4444000c002240c600e104100e1078295040303075400c01080c10419820140000030304000266904010349007847c50740708a1045e41150301032901c460200c0c8482c00d00022003100720b0030581a085050041c0441d100d079549440c019500e081203d28041c100d0025094481c803c4016000c0150700801c00900c082180100703521100c22005401c2016500d000d801181041045403904210290329400d42d005429868860300164070780c06031448410700c0544400014003014400d0000503100c2c031000303001c900d03060340f01c1c02c0050000300903000854481c110303da0007144036801402030340c114003501c5004514581d650307902c0c60942c2c1c1252400906020090000b9001070790b900c000b03003244038085400140c03504041c100c0e0a0038500c0044920940038410403007440440c0022a0200c84440c090020904019140c0a0307000c030014a2180701010b120003103004c02d03001d00084004d5001f0503a40f20440140040040c40081341401500e040750700038030105110307144c80c0406002e031101c10580c61440c0c0c007141351511740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 257907562 1250 257906312 257906333
    0x1110d200a05060a0c090f06030f0e0102030703020903060a09050a03050c010908031602010f05090318210319020c01050a120b0a03030203090a141809120c150601020a02150d0207 78
    0xc40ba0342c1c01090400c40c4421542c4602042240b5501d0602102e0b80360040b21524100d46004450816455004404040c90107801541000702d82c2c5001b15900d20304554024000d412034480f803842800b541c0041261690315010700c01c490390300310b80500034030405684d040d6550f81c0701064003407855403180c4402d00801c500d08060361064450314144102e64285000003400c5405086094442c40d1401e42844060200003061740d004400d078900240b003400104000030100d04c01c00341220341d2008402c080741c0d25200f021020b4050807c80c5001c5d512000240e640a0340c50b4042003d00d140094012700218001ea441522082c070012800d5400144104440d80802e0564100340c006070090307407000a14000b1030800d203071800000d051070b203040c11880801340b0025041030039003c80d80c0362000c941008590131803014015894010102007004c2e94075002403003c0c0707456401084d4811500c503503240c001034441d400801c800494072381c010001c400341c015070031070000b4a42208180401d0aa800d010b200c0028240d00c40c0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 257908812 1250 257907562 257907583
    0x20f0703030201060e070c1101080601020f12040527071b1a060901090e0303011205030c0a030306230607151b030617070303021507020a0c0b120601110d20 68
    0x444c1d9036050680c00000114054011020000c421403104003103090a60740ca15108424a0000a26120080102e14000281d1440c82c2a8000c0480300c1c00d04044003001031040340c0d405d80b40a2001e030703c2c6010320030500c03c42a1154250010550020790b8452290310f0040d030072009000c2c40c40e04e0035415101c1c410400f130300c40000307200785131039806000700ca00c0c090650700e004200300740080c020001074029951b100d000622440c40440c2d9003142c0041045020300588045079002c504445a541503410300402503d114070506050300c140f4000d40f10b5441140091503401071014214902c2d0841d6681d0700e04408040f5000f40f01c5c1036680d01300c0c40b4016607a105105802e01d40075500428070a041c40c003000c0313061018126220b213542c1b0024081001940205603101040040480c0c1034207584e03240c0080e814000300c210000c00500d4200c902142100143c405044d0440c0da0781540c0d800f075915a0010366a520181c003010300594081852110070718814000040906403540c0d071446d1840008100070300e8000c101a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 257910062 1250 257908812 257908817
    0x602040b0d11090f060904091b24050403110d0203100f0608060609040f030504050603040f052103160314091c0806100f180608090d0302030114060a020f070303 70
    0x54148071200960141900101010325010300e028541d40c0041c070b1040d540700c40d040c054a0003107682c0e030880da5a6409120b41607081190040700d011102c1400400e070046000700341240c0c0d42c01c100c25505014506500d4030f00c14164440c0c07413410b811070b242c2182000d00301c090184d00443c55009900107803801c1c001d04400081e010fa01044201c3e8800181050b03550316008495294881c00170449156115001c043e00b2070b0b00704800704007195290800b01c8440c0310f15000160408400028801008188009a54040c1c001c1c41501c1400c0c40b0f0240e14a41d040d54882440c0c1c41d10001d101064004011900c03c02ca040cbe4241400996110075031155034080d03108a40210041d00202e01001c410b1071805401f00b1030072114581940c1d01d24103d000100506056141c02080100314141d6001040c0610200314001501c41c0d2001c00e05951100000c16002040f1444500e50050b402840c0106000c0d0003502c0c160b88110445146103007001c030910a10341c0010406c0710442c0b00702680454840014004500558001d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 257911312 1250 257910062 257910067
    0x50603031b031b060402060a0c020607050601031a070509011e0203070605040c09050c0a0225030203030304051c020106050d110f0a080a03020705220903140f18060c0d05160602040b 79
    0x7400300b900d0307521080c0b64540c85501304008210040c0c2d20078080300d842600381e0501441d501d5850001c038220b4000d0200041ca648942400401400140080c0c00030424070714098501d40d56609a0840e454010b03562000d000c602c0d0314011100d0304100701501c0c402c01c0454411241481c4407603c850003074410a9400340e030003009042060107201000c0c003071941d2244950407078501d8030f084054000d5039075a00b4214250b80034420030710794440086c21a695402590020200c90712810642421a264000a1070000000303528407005950035006008007011070300c00910790040c2c06099210400c0c2502c10b0803031a680070b02000843c5100e41d0b41e0814010242842c0710080980b0412490064544806504018850344c1c00710b030038500703003100801000c448440c01c503030110b4842c4043c50240d4840c20306144c802c074050070108008045100c20f030b01608141c0030540400c030101400d82c1c00e01100703124100000d4082d0f080302c03080254050042c4001c01c0040d10341440c000d003001c0c5d2611030301c0c12600b09400031600040700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 257912562 1250 257911312 257911327
    0x62004051302070f060506060405090901020c0106150c030c1b031a09010525030b060a0224270c03070306092604051215090a0b0702011401050103050603031b03 70
    0x1d000d6401c11990100210b20b0f046250f143da4001c400110310040105d0744a100040305501c0d6102624010000034180b40341605000d100c0314040e401c0302403c202035601c2c01c08005102800d01161112358506a11096800401a1070840c1d500000c000c0aa820481030507807a25907903200342c442130080d80039102c41c0c0c1e8802040200703070110b050040c0619007580c3c1030400f80507045408103804c500104181d05012820b0400c904240d01174004241d48c03d40c0320350003140300c03500c0707580126030741000c03400ca24860700103401d05421410400c00251a641c83d242c103841c0c80018200000348140204510030012100c414070b05600103031504040f500212005074541c60502d08006e007100c850718609240c1b911580b600040b541c112142401948280c0344101405030000c1c4103000180400c00c40907040b0001c0d1052450100c101c03541c0d80210901c1110b410310404002410144184180c041083d83e0300c03800307000c6902e0301004502030403019261581c5404200103201800f60507500c038a138071400c4000a180c13296136 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 257913669 1107 257912562 257912569
    0xd02070f0f0606090b0904050a120c2a0501030e0c09060f09160e01050304080706050711061501090b210a090f030e150901021906200405 60
    0x240000000305002c8240c11000954400210511400d6800301c1800761b6078108440290441e003080200e00002980c68040b005452214071300041111515160058440401d4400305401c0380f109415580780030b03407419824004d0009080802823403414540c00703a125030041c0302403407180c2040030000380255941ca0410a010b08060018800380c58141070808441f014008600301140301c50841500380d41c410b03c2240e11a40c3e108041350f0900da520f5a41b0009010041d0608003406054030140c20150802c004252013003072908070341084c02c9003280003d014040e0b1b98003d00c080e0301c001c10034603071109280042080a41c05560072005030350fa400317074510020101008010000c3c106844500d0905901c1401442c1c5c9940885500f5409144034180c00c0d103d22070302d480c00e401b50304944d101205084511446640c0a4000c036404511450203410760340040d101d01303044d042248000704040c4481e08 = true := by decide +kernel

theorem cover : BRFrame.Cov 257733812 257913669 := by
  have h0 := BRFrame.cov_init 257733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 257733812 ≤ n) (h2 : n < 257913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
