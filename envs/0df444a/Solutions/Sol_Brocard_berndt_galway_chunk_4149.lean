-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4149
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:42:58.618989+00:00
-- url     : https://prove2.me/submissions/0e76ff45-45b7-4ada-aa67-ba53da723571

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 746043165 ≤ n < 746223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 746044415 1250 746043165 746043167
    0x130b07020f0601030606140604050a0e0402010909110a171b03070c0203100b010806010507050a0b0a020702041b020f07030b0a0f02071a0604180201230c0a08070b0a0b030715 76
    0x1c148500c1212080c000c075030002c804c201c03807900118103c6183c10500342c5c4200d201301c00c102c094442c510804c4d61003c51000200105404c81e000190701600505102c07040581e08c007800c80566140f40d200e841d9031400080c0c00d0070425004041c18001c010301e020020103a2500540c0304050031050002c07031124490102c00600d0142c032554640805581c003405844020b690a90400060203103121035902180703070f0000042655124070103482d1100d03088001400d031031030345450700ca10030003002d00304018442d020404940035845070b0140386803020000a148000110b0b105000b41800002190008075420628040020501c0c0403032140c0c100c065203400007500450f86220200034410644014602c0c003514044882c0b03601000c00c054880c100c2560184000b625060b0010401285508000c0c0490305207415030a4081e440b4841d030003100380c40f80411345810381c041c10350391030301d40c0d08038080398403680001e0080108115050065000f01c0c41d504c051007148120000251529100c1c080d030315502d26500d11450b903072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 746045665 1250 746044415 746044423
    0x12030901110403030c0b1b070c080c0306070c080a120905100605030303100302010810150f02060c16030503070c0b0109020705011a090601051c152102010212130e0c1b06130b0702 78
    0x101c08041f1055602c0103585008510906203100b00d10143c0035514403c00e0074240480c46c07504c2950540d40d6014074544941d5420882d80007052824104550119000107908039403140240707450042e8001d000282080b0380000640d650340c0c0085000350018420701c8040c50f445a00301d0240e85c0e09080a44403a507510049001e1001c560748402d080300ec080710a180d40a800280442100c44151b0130340d50169115586180c45100d5050100c10f2078001e50400301c0030034030a03006560049100d20341840c0d440700644580c90080006c1e080755600daa8009491020004244154061070002020001407500c00e400069400000144158140640050aa05403810701410b0b03003280340c01420100301014003c01d036481b18240030700070720307601003460303414141c10a000342c0001d94010f030305a00420b00751000c948407501c2130300046041000450320344c4e40031503076840c500740c1280300300d00300f01c6050744a00d8180301e0040019030340c60445002d50404400e1144078809040c402000980101e040221074403501e20803454 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 746046915 1250 746045665 746045701
    0x5070c020f040f02071a04021002030703020a110103021c0e10050907091e0f05010e0c070b07110102120a360f0c27060602030a020c0d03030e12030901110403030c0b 72
    0x75401c0400035580300c480840c0c42050040d40240c8803142d03a2781c080802a42d50f4885d4042c0640035901c009480400100d48807030005074040c2c185800350601844050119034200c4c5141c10081c1d00b600c4000f84c0c4808801007100070341032043c00380184400d00744008696100c02d1907000f40c00d219a29500303168802c6c0e080c1d103504440b4215652040003000b41182078400104003e0090500c00c0303c5081c04039a0b40035080040d03074811074006040d0303a4a0f888d10704059420b442c208580e003ca954003031180900c4c1400041b5a140b080030249008542c5c0801d0f0080300200351945507070b200c0c140081854003074801c5440720003a40000e40c0040c00c1c5403441600c2c1002031215146601c00050401003c0107968a110810000c055440394030f1428040c040d00d0b55400c0c4e84034003907040f5150060740455814a040d240c88078802000c2741c02400d00180035240c00c40060700380021030740049400c14001050214056092049240091000c0940c9003080e0540d40d005001182c08440600020460408111200407000d070700a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 746048165 1250 746046915 746046923
    0x13020307091a071104050415050415020c06011806060503070305060402090a060e0102012a0e12011410080307030e0603040c0f080c010e04060f060503070e06040b070605070c020f040f0207 82
    0x300e2039a00e200d28101d20f900c610021607210100034602c1d513050a081c05654000c540c07106019005184501d0302000400c0000c1c4240c884000c04520313804024094801420321100d010003030b08866042007014040c00030400010650f8902e00082000b00590040c1a0707600422986400310300f603121100050042d0050708440d9510a5688100007051070300407e00f030311141c40c282c001b4400381d00e6000ca66414072039141c0020180704409244030314014428002c201403074200034905600d03800c103031010032b0844540c191103049050010040c04210b0140c100b0b94001040d000008516000300c40e03400800d0401c416400d503010f8a008804942001181e03400070380a41200404044841e03511604070b5521076100810078080343d8041c81039000c6040501600041e110340c1ca000c03140c1c40d450140121040d03030004241d0810840100c10502c25a954840140028421000e245841e0300140c105a0201c070000b402001c140f2500da20b06c41d0050700c0b48210102440340803500000e23460010550a8081d22840d00028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 746049415 1250 746048165 746048189
    0xa090b040b0c010f06050a0510030e03030a0b1903050706030b0607050d1d0603060f0d03050c011113170a02040b0d0203070b040806090303011d100e0a06060f020c1302030709 76
    0x100e2081920409000c0c0142c40308000e00c50a489480740404070380b601c0c06030b69045180f81c10140700d07904220214400c81d440342c0c54006100f0140246803410760b00107a4000030480c0e12002e40b08841d04e803203130a4088040a0000c00d0000030f186984190b55980c1e140b281d0740c145503c1d00c11030610f42c3d40f83d0003601c08103904202966200c8003507031001010068111100424494510742c0c00c1ea29050210940344518400b62518180c1108a000c0001052f41d020003103007007210400082c18603450a000e408007511150060544401010b17203103005103540c0d90888903080380c0c1c25030000c0044500140340075450b43c050340d000440b0b86407000400e20244c10102c002e5054031a0200c00104021040000c1003150009026241c0c20340b10300c69015128442885840f2040e500d60201c054000d0407860807540005003036184001ea01d98850402c0c48541c000c880315091740e903840d1800c110558004e4480c04485d1071901c0502a0100c40e003001862001c6a000030041c442c0d804800541c480b801038050780c0144ca003019002c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 746050665 1250 746049415 746049419
    0x23011505160309180204050d08030c090a0f14100c14030c0129010507080403060e010212090a1109010f1814090d0e01140d0203042d030215100b0a090b04 67
    0x3d00400864822881e65015035200010308110728825102a10f000410800d402c0180340c80e40f620b5608003505045201c40c04208014141e0386502c64000100030208608142a1900700300b00b19201c1c0c81c1c041540181320380010074008540c4800c0300424941d10034260b80300e9950240d4058038601504180c540b01e50b01c1c2c41c100140c0b00c00ca180800714090052400c3c29026081080112028000c212000707188240c01d100c1400001c502d90802054000520300050030b080310100f02500c46482560392a141d41c10440d44101404200344454042e070784140c940300d000754580900b24500a0403032044100c921141c810f811202c3c10f65411020084085015106450420341006ca4036045c41686010106429014442e02c5500401e518440e00c10b06130350340750400e84080c0b041c0c400b075480100308441844142d02d000c00c64240100751070b00b4001d80c0c5900c822075400756190103450300c01c1d454110110804440100708615450140709820360b156002d041b138031100e9804042d14101170980010710300450100300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 746051915 1250 746050665 746050667
    0xc06151d01090207051f090f0f1406091b041b081f060207090e0c031b1002060105030318030a05070902210403021510031407030204230115051603 64
    0x10045a00015032566030b03030281c00089110b07844000340160080031106207400c111180d02c007217200c10004046a0030101ea0345c0d0310416420560103c550901c0c655a00080c08242448040c482811400500140c105402c48a5640040c031941c00b100d0030104150070300d0707500c6541091202042c840080000b80725031b84805042140d04490800002c180d5000007681d135402c2c602604100c0706150013512451b41441c01e08000f51460100100043c0300303610409aa64500b00601c0d0a41c0c12420000010300040208110b01381242d15440b004550000c4014446a038003c011226648506400c40003c5002000401c0c280810560043d016000c0c15000045801d406e800400783c580b41d5090345030001a074149150401c200a45018005070b00800820b1640c0c0440c960b4945c0110180098023241c0da507940d90034502e48401b404650381c80d0030a020030411814140104e0b822642c0880185409501d019040b02d030382e000500c04c180e1083c0c41d001040400328001d0003100c07443c1c01600c01c0f54480040900b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 746053165 1250 746051915 746051939
    0x30304060c0e0105070b0c1b100c02122502030c100507021c030c02130b03190212030f070809010507140105100602120f0f04080106061211030c0405010c0615 69
    0x200c020082840c03002c0c080d00d1503204404641081d684850103c1d034540b12220170105030b821181078241507030340a05148485800130080e5040d24542d4a03400f044c1081070304c20013420643d0b81c03480a140386a06002280a00c400c032841c05120743c1140b44c07141081c07541ca00002c0e26100e1f00d01455a04000440700760410180d1103001040901d00988180059002000c0c41c01380e60020550040c00040498094500600d03142d20291581680c030440800c80000031400a070501c0030028040c13903503201c059400c50446c100603503052003540e2884040c40c2490300c5020502c8451191003001040ca400002c3d0212090780500103540449420642148098052000d1a802803c0070f4070000714000749400300080445c400590600050341e80103400c0c0c2000d644d02910900c83e00420b003a1811000c05200c04602e41d00e0901c20b52000301569074441424826800240342221801c84428140c0c1008204200340c0c00f07100f1040360308940080c60044228603d60520034000d0000f1151405940307110038000441184500d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 746054415 1250 746053165 746053181
    0x4020d02040321032904021803060c0409050f090a021908030d1e0507020309120a02280909050c010e0102100524030604020918070b0c070e011409151203030406 70
    0x380b0104840400d04d1a400d544000400c1740c003444074440c800000103403c168014003020001c804050903901000b04c0000c0c24031000301e48499412102080400144146004507034010417040702421160a1035401203031140290400603016a401d580300042030000b0861000003400c0080980341c030368804403d0700f4040d000c0c8903ca0041a0741540d40c1c800e44540501c5064050030aa80085180512036828030100714004424000e060054010f0000540c40c0c401c3d403041c10004071204090750341d00b07070401210b50304030603040480441c2ca41040240040c500040c0301d10342c2c420900745515090300110040780341441c803032403080106090a00b400402c078201029541c881c240d0300450068804010145a514582110080d5103c4414404202806c021040e545100300d600000c1d03408603515403609580701c0e0700031401c003441d0f544010b000708018100d03020030501402591005180880c075001c002401c60002a000b4003505589004d84c455035503802030301d90780001d00281a42d0316480e142c18441c00902c155 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 746055665 1250 746054415 746054417
    0x4090f06090c0f09061101090218040b010f08060109110f1809150904020904020105042d0f230103021605060906100e01062109060b030d0f090504020d02040321 70
    0x400c02180c0c000e0343c103094030301e540781e881071407152420303000300d510342c000b500f41c3d0b900b0303558a441d9200584c0301e444110085202082c01e60724182000c3c80c0100904505901001070601a40740500940ea404101e41c0e0441300402000b045a8030401840c01c1a40302d09403841c010742c100003540c228100075001114002d400111051181a501c050748510340c0c2c6c081c0200b040c0c0c032081040004006140c22000035411078010724200e820582c440310041e414030004000300141459a6054508054003c02e541c0c002d000c6000121426900d4911a80390340000480f0b100e4090310960304103001a403090303050b6000c42d0820100340704044018141541c6a800a0317030446410301400f800541740c0590003c15100b00d4400203e004020703840c0040c21140ca1030030001d060f40c041b00e503c0014800c1c03112409070042650040e900083d041ca110410189440321000554050002182095082c6ca03040001c0c40122141602c0261b81ca00380c0381142c2d0001d21550b04010150340c0d02c42864509841c858420206204203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 746056915 1250 746055665 746055671
    0x10e120f070f0501050a120e03070b011a09010f03020d0921020708010204030f02090408090d0c052d010c03020a060914061308040b07020409020a03030201022a06060108040804090f0609 81
    0xc1e15645400460302c1c0c0909800b1a408002e0400300602c04c3c00043c0103107000d04000141a06403a81090441d4405c00c410740d0901c650a006019454003242c40302c1400141c001c2d15850142c926001a080c02c24002280091541c00300f0107050b4024613030231410006904c1802440307030102e003c640d000020040110000144204000800c1040051080b102070b0303a000031b40206005010707820080b03540360040080750481000d02035404c89441742c01030b48050904c5502c1c0780c50b040d4141790370301c4040b01d40c007008080300754402128a0076200041d00b0082c0f1000084c68090801040c50905038034002164400804062800c51001c06021905650301000505101951550345455441c1b40080060344406046100c0802040085070710070741c0102044d40c800307080400c0008881e00020005400c41c0d109501503500000c20f00204034510160000405c0640009095203c00800b070f1907807800c0040240b8140030580c408141804050825100180b0352041c043c002045051144000b1340800d1080090f10742c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 746058165 1250 746056915 746056919
    0xf11130c0e01020a0f060c210c0f020c090c03090f0312011d011805070909021201090b0d0b0a020a03090c081b10021b010509310203010b0a0806010e120f07 68
    0x203c0442c0120f0200c0d04000140c10784006a103035840100482ca452900340318196441c800311011b040013000300f50014020002e600b139107421010300340b8101d029059045412032040c072242da9941d42502a0031030350880f441c584a540d841540e0b072600c1d058044400d00d500c404100c6a200b280c40c0c10129042e00c44034012003144000c103800e00d15200e102030140e4040048286900e000460940e032100e94028000e00d00b0040c40b0342e5500011080740d0003c1d500d0000e2002d150014031a15400c0d0050b68001c3e4000d075000d911401168491000181014080c006000d400160782030307804bc4680c00090706240c11440302c00b40c05a80e001401ea071075409088409400b6070002c500665031070308004003d00180280c01400d944405407000c0c05060003c0050719040c0036060040040b640c9903210f5019241c110100c996141d60310740004201d1085064132041c030807500400c018400c0e00f483c8001e540a0200c2c6060204407900c500340141d402402243e00c50b0f80006401081544400c40041c5c20607a489444007500d02d003603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 746059415 1250 746058165 746058167
    0x9190f090908030f07020c181b13090b06070204110d0c140306010f140d0c0905040e070312030609020a0c1b03110118090510170304030c030f11130c0e01 67
    0x50702040c028180c0001403001034034083c00c80907102c1c0d202c40c041c4141c0e0460725030180000c0d20b03440c0441840c03d02a5a640411549608100d000c0000241d503c2100741490240344014030030030007a025080e211034480c1d4003410b682c4c54038400e964819a0040043c0255019440850400e0300403400e0135005a0410003682c007402e0090101c85982d04941d652913140d0303500d031001901d014416809030010492032040000303540902e000604844221003002042a060030f0100900d140502d40043c1c1c403c1c0c5c0342048100089c0b0340000e0020850b50b0103555021380f4582e40320141e000700f99603803042d50814000a000d59503142e2007020410b425102d07480c0503810744c1449030001000030103400010040b601c90440c50501d580a440c00c044000d03e4426018000b0742c94849050aa91060b21038041c8440910414421914502103101fa908071480096040c1807441d118110200c03081c0c4000740c040d09080301000d050080150007004040009420f4640304401c0240c1c180040840701389100c001044510400c180c1c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 746060665 1250 746059415 746059421
    0x2739030d03091401050c0c102906070b04030201020a180e36060403140c12091309060e06010b0a1e05090904030f1d030604140c03060c0c060a02160f0809190f09 70
    0x1581c56102a400701c0d00d50031146c80c04800d27440345076a02800c10f020840009030f070507941c1392155201c1d0340050b8680303010802c06040a840000510310b1411340000600250700500c3c881907000008000c43c070074450882400342071144480854030410540b02807905000c1d98005042d0b80100d10035521001d0303a50030140c58128038003500542402d1900940904040320311000041e040040005049c0e40034610400507180495840351011500700b82c807014032100c91030b41403003030b540141124500c83e494031682c135000030403019005a6100b021180b00b040b6004186c4244152003170a00701802010044c1090b0130082c00c980c841d0030480e40000d6620b101444950400ba00d1807042810150080107075440e0740c0d81e860120000f00660350068440d100c100022a030b0100416409508842d450301e5540c03820680060500d00024400c2c040180108845030314402c41042081d030480e04047c8040304c02115290500c000c1c4034000465501295a0038070200c16034040b0076940c200c60741141b420400c2644c0c2d40c1f001e026 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 746061915 1250 746060665 746060681
    0x190602011b030204052805120c0901090b060415120c08060f040c0228060603080309010b010503070c020613030611250206032739030d03091401050c0c10 67
    0x46156000d81031048941c1000c006541086d007910f1600e4240c803180860304030722040c0640d84469100881d81c0600341054552180548504038081c007140c60f03108003046951185219041c40d040000840e001d402d841140000028101503038184140110901300030030120081c0d424522034000b00300f8100d80f51916128540c5a00510303005056010210b09000903112100b00200c20418807203c50f11001920910940700910b01c101e0032261a401c1418040382140e440b520b849042c44410001c1c4031840b40c000e151459079aa04031140d41e81d0f401c8400c05240c50240300e1348000c2c1074074142101d00030000b0008001d40b44209112100c0d001030754000d0110805000c0918010790449810070100e95001c07510144101c40100080384a0704642d0003000503450080305503241000405035038018803510312420b440d50702244e40c200104400513406c000281d2119403a005003c02e1594503850201000000040d0364020a07505d0000c10481c88c01c4809065590b014450020345030148854a50b04030307502e4460005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 746063165 1250 746061915 746061919
    0x6020405191503020f1903050118060311102001061404020f0a050f0f030c1804020703020d030b030109051912080f070c02061213120e011409190602011b03020405 71
    0x710302402e4200540007907001114401e50103d0422401c041c01550034404820042540e40c0010198903201c455034110004818083c0e042e03040c4501003002c0758540400c444541400c0300c84001c5120703480015101403180c50017015200e103119128042c400c0041d480b00044504825046007410214800c00c0100d1083d20001c2e12015014003110394140d10036000780c4804400381c3e03038083c900540d6981001440d001220601c802001c0003a4614040e5241c64588200603401d6a040d41800c8190b5006500c80410f90b40500c20541d0b00c481d0040f4940d070075007002804039000070a4944c2c01e68410f0845024045000d000c0da4000d0400b04000665407041524521802a6076640d850030b40300e543c0115040c116160b4160b80c400b40c140080c0d280e0031051400c40e40903c40c607281c03055a0950030310b45010400842000306050000402c5030219590f040071003508002501407841d0368501c400000242070b0341441c42c031107190481f40000454030580540c400e84403a2880322202d42d802c404107100300e00b42d1282d8000c441d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 746064415 1250 746063165 746063189
    0x30b09030a021c020c120106050102070b1c090c0f0803090f01020303010f030f0609120309030f0206070e090604020408031c05130f2004020c0d14040609030f05030c0a0602040519 78
    0x4080e203201c4583c01084064410382d000c8042040c001580d4115441c5a0100e076551030300200445e40c0c04000340d5000f40810404542001c2410a4003114800c01011000d0020f8842400c4400c01894609c900064186065020310907612aa5000c1d17990304800340446c000d440003003a241056000000341d0303049410300281d540106085541d4644018000c0700100c2c1c1c0b894480803698001604044505210340a982d000110300246083c000c0032110f002400d44252740140c01804a038990041903c60406010f561400164845001081c028030569000c0541408040340380b05003a00795100c0c9412080c200602400140c66040c100000d042000d0030080c80700c4802010500000e4900005080c0d4031140810700d01111a90b00204050b6489810030307085035045100080040d03a004480e01d2007126000031a41c0c2014186070000e0b08d44d00e114040980000306a001150400c2410800c50328040e070350343e040c1e0f0700c81245803800700c02035040307070085038445c01a9410803200d10000481c00c00841c0d400740e1000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 746065665 1250 746064415 746064433
    0xb031902040f020426030706061409070305090717070510021e070501020c040b1c03080108070b03010e1f08070e061f08040201030c030e0313030c0b0703050d0b0424030b09030a02 78
    0x5420004003405e1401c0c2c06002c1449441d0105403144282001041d43e1118450703d010b44000b04290104020940c00a05150009001b08243c0001d510401d40f84585889200101e0700c0c0005844c203201580007030b9204820500c42540036a0206040c1400308c0c8001742c4115408100400d20b484103003030b00400e40103030302040c0f41c654646455040f2254030319010385986020041341c2c00741004148008802d07800300d44210010000f005007041180c1c020404a0340b040d0941d41068002c0d281c1e00c0c0003421070348415110030701140a00c1301401c2024014091401115503540d501d690080a501040303c0440c400c0160070510071070740307003941d500c5140c0714501c0d510210385a0352680150000c050000c80e0004143c2e6400c1c100f80d80b450100002d00c0018465424020003901c0c6160040340364540350803000c0c0800c024018080040d030404252400985040b034042460b0504d080030070010310415429102c59403908241011144900e0010005d680c094004604c1903034603892416034034401e18151000590042c2c0708 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 746066915 1250 746065665 746065709
    0xe0115120b1506030403080702100606091203020f03040e15040501032a080f060f1e04060203041505010603020a0f0203041811160302070f21030e03010b031902040f0204 74
    0x1055002a01590b40c41088405101041c9550800c803012008914110103002020b601040301c0c003200120204140038590400c00c00030500800381c800c0100b01c231841c0c88030348200350003030210715203041c10001101e0b00c40740e07900c1c02d000d5403e4007554081d0640c11140481c1d0903e040034084c45050701c1e040f002808070201410120780046c000c2514103048a80008800f107040d041c203025110200101340010046ca0400701c01c8080c200e50040d00b50301400c0091180203011003000500c141d03101c8e070025001a125aa07a05000c050756450041200515140000200f000b03034040e03001d80354504e05c645c0c5d001141c04030407005a0743e030301c5280941030300000f0502103510007080d9a01b1050b02c0e64609464582092504010302c54620080c1070100c3c0580c000c2c000c140041c005e20b4900038020890240c070802d82010010440d880b95403050405410041800c01d840d00301c0d2000d400200320301c00d0250440704502e10382c42c400060b82061000c100d12641c101012031204035514021b45040da1840200d0407141702218103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 746068165 1250 746066915 746066933
    0xf09040e061b042d180c1103071e1a0408030108100b090a090507080604030c021e0913030e090103030f11030f1b160902030406050108061e06010513090e011512 70
    0x40700d003141001e052002c43c00b07075900c0300c4580105c44c00020108100c81025800380041c2001e0440d4a0740da0f200f809054040340f0803030340e03088041514400c154071786d4002e402d007411000210442044100c1c002002d120400c2242c0d00114102c917007030b40c291803243c05486490025109a082c05a40c00030200300802c8001803d0750165032080d109600f04c03403003030b0394400503d030805800b11006c1e8041002c0f148030100350300b440c40e1101002c4140c2d0100c62291001640010341400d0f0261038400240440510f1508060062003030090307042000b04610071035a0340346402013240d003003504c2c100006640142035403144507001054600d01410141502d0402c40510340c522020252500030700010310503000d24000d8403101e0401072026041c0b020015a8178a8a8181a01902c0c81a80318810b02c1d4480e6040000541c8541e5803a884005a9043c21146031a10340048801d4082ca05401040355491400060240c100307500050040640000a0001e40718a0312400380d000714521a131401001c55403404c0002601c0c2d06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 746069415 1250 746068165 746068229
    0x9090d080609091e010204151107120206070209040b090f01060e0f1e040303021201051813152a020a081e2809090e030f0f09040e061b04 60
    0x942114800040002104101d04690004c003030507950000d410f020881c004806003204ca040340c2406c006e4213051200503070703903030700307680700b0980000503040c680030441d80c0385001c95503016002071950706107051504040c04125000ea88071000c52140c0034520003103e0040c003440302110701404a41c4c025030b03290004420000ca0081c21000407910714548081ca1803450b6011900482c0a83c3e00103840c0c100204068600d0719068229078800c17090205190b100c0c0c070350a014560300c030035111303800c450b485818502441000c225202807660181040100313903841903680c1110901080d01c40c1440e1104060600590711104801405030800e04104500c00b8615025402d0612410507403611910f0300703104420752981c0c00803085020710b415119038090402c2c07d0348622400b0103040c1d4200100300041414650607600c1c4240840040042d00c04104491080100e60540d07202e202c025106100d00d5841c400c03459100c6000303c5a2103140f0703000c2001d0b001007900f07031707025035055a20303c00119440f01d9540c45a1034040070701c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 746070665 1250 746069415 746069431
    0x91f0b090613030f2d0210030f051503010b04020909060613120803041a0106200a0c03050c1e09013005010506100c0c030201050307170c04030209090d080609 69
    0x4200c250300052000b011603005502401e94210310f4420391800100e8050014030380200107107406080e110401c195070000070354640c11208550b2480480b0800c0e40a4040142039814a5103028100524031094100d8194061000c030000c000c1c1880c4082008102d01070010119003241c00400001c04a0030090001c04084034043c0b46411340540c2e0703010114010841d07110840344104080180400c10116034140a404c00301d01418080c0766040000c01041c0c041c0e0184050b03c901051107a50300803c1c014030402d444240c100801010031510307400c1042e900c016441e02140a03440701c40c8000941092005a003001480007407404016034130701042050485601202150003002968800c0d680404c488190b00c076862003040007040e50700e828400c100400c00740d186d800d418480445c2ea07440004044002040036280d0900300b0750303182e803615141100c0121914001380514680309007405213401d0342c0c0707000c3c0c4120b270703c01c8521040a40e0349140040d2120b8006081102060b640c80220783d1514100a0300780d442104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 746071915 1250 746070665 746070667
    0xf0a0b0a09050103050c210c04150e011205211c0f0203090703030905010203090303041509031e06050606090d06200a09030506060904030203191803080306091f0b0906 73
    0x554115070100d4800380d004803207580c4200110070050906418141c404e005070b030000007034a0b00810280d51186104042180b2450780e070b4403c003901c1c103000651407015091400040447d50784908880d00c1c0c00060310803c0e1910322440b4501010903140c4011804a6000442060f040c0341640c0200324000200d1040540c0842d00c2c0c0c01c03c1c100a450310320265101d0110940105141131131410080c0030603955400a90441d0000c01445406490000c122811903420030080c240c46104250210ac1c000c0d8680c000a0804074503140152255080da040d541019004450070030407904ca6004111491092094642d00100641e05030700c04200311343d22907441461070070076060241070308480142155100050b884c0111b0b030741805c18414445c007040f105a21490640c1c1e03c014908003030300c1c06541c90069008901c1c0b0146031041624506109008012485c0070040c10380d50015128640186540c204032000c5d809102c3d12000240e805040144000380f82c0c2c1c0c00010103881d541461520003c81e8402100340d030304188 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 746073165 1250 746071915 746071919
    0xe0109060515130506100e030f030c210702010e130b04050a2c07051e030a2a05010e060f0c060f0912071a070c050105011514030f0a0b0a 60
    0x8040c0101c51141e2164040342d052208000b040180401801d903c510b0b20625190030400c854454400c5102c0c0c5844a040c00c0c058601c02d0f6002a00d00035000352101d5007070101040e440c5000d0000a01c900360f010200c100111442e65410320300b15a80113210001e80050310302254041981449201480c240d82c2c1c00340d000c0f403124101d001140682e00140c840d07003030183d56500b5241004082d03c00d03003e200c0400814140141810041c1c06503a024103000302031103044060360321628004483c9002c00c0084002d02511407514060800720720100c4001c0f104890848481620540010328421f44410f841c016154030524071240400c0c00002d821900e0b001659070301c1001551403640041104d6031240395958440c0325070b0700c1c0540f6564100408074030240901e142c00d008840c00900c03494080c0114003813408103c0d0641d0340d03010f41201c0010710309001411039440c1000100705c403111009024103402440d1904200d000e40810703603800383d11040703403024802074030000030400703503483d0350000140c1c00002000d00768095 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 746074415 1250 746073165 746073173
    0xb090c0a0311030c15040e060315070909240603050c0d060806010302040b0603011505030615221502150403020a050d0806090a0605060d092604050901140a03060e0109 73
    0x56039800c181c0b900c0d4a00203145280f840c00304203880401070b040c0d80c4501640c06841d0b03000f101d4040d41c01001c0340484e455000034090f40b0202321359242419009012080350501c01400781c000006406510482d0741000c0100165080e43c00e4903075280c4100c00c0059420f50f181c00d800304e005042c01b0384100c010a000300a40c00380e1072854080c1001420603440502103652452041108481e2103110241c050f03a8240700400000c41101c1e181e1182c02501c3c1005641c9580312000142140000000c490b5510004500740d05140c42030452581400800b50104020b1034a8182000071090241d507450b00507400307940030800070501c1c00003043c0c010344640101c2d200040150384541c00c01003040c20340000112a07508200052410011882e0806050001080540d04200202e0106e100c2c5017144000b49850300324580402800c82402070ba00c8100300048204a0b0a14641d202664098883c4034801c4280c000085155a414074801e001e4080085c19080c13010700d1a603c40c0060a01030290a10555951400d18042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 746075665 1250 746074415 746074429
    0x1103131403040611060603061612020f0c0109030e0105030c2505070e07090b070f0b1302030f07031103191401020403080307120e0105010803040b090406210c0e070c0b090c 75
    0xe00441d441300b0070400414201030f840d100340280100d20039030083c8103020344141d03600343d110400817544c6410704a481c202c1c41071a02a101d520306080c90060300140c0d1009109066102780710240c842c1d40c0d0083c0415080d801103079540030a50700c4400340c002c20001c1c80d5907100906800c5111108088483c070541070140c0f1000e003001d80aa101c200001702c103104028005502c4294078004d403251810b4141090b80907110340c0440da03502c0300700030611110700300459100f0f0340040702ca03040140d0007401c4401035020f00314456215400c5200403914684050b40080742031a02007480c04021489145080180700c094448a07426400036a040d40b065508100c00f00100b134941000358412030b030a46600035080041c0c60b03400200c0d00d000150540c01d92410b801406808130101c00c9074100d46d11260500d803110001000603000b00420383c003051445408005500d01c0da0200300302404003900031190307400c903d0f41c2e0740e0000c0380c0f00302d00f22044400a2800d100d02030005100c501e442e5000042841180c85201c501c10100e03500c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 746076915 1250 746075665 746075669
    0xa0b0405070303020f070b0703300c1b08070f150c0201050609071d150d1b1107061704030306030209040b0603061e04080f070c06031509110313140304 66
    0xc00d03080010240107050301040103400380214a03004152044c900343e44030040d405250740003010405400c10040140b48104091805905c0c0c0a42000942804150b540010004400040046200c80c40c403440081000004001c1058101007450300d045015510355021070348981c4110f1344594070014207125101d40c0e10030b00d00c0e29080c940000400c0d041c90000c104002c9001451501042010614a6001420704070350890200054500804c03020150034500f1441c09000b1001440f9460942205001c06103007206078210115078072082003002d110840903881d80858050403000c550b00440d50704001c0100c03060583e0042c0245000243d403070f2aa030015030b000d1000d80f0156a440d000100703204403450300340400e0740c000803040f1046000040254040000b400000c2020b8440b0001080148842030101e08580c4100d501c040510340700341c1c0300d02e40a8010071281803c1f4001145d41103001c99840c80ca807140c8419800c04114190540d6034115031a082132104887c11124544000da601c40074400030400303000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 746078165 1250 746076915 746076923
    0x20a05040b37020d031e0227030106060c0b0411040507050306040b090106020c0609040e010606080a060f03020906120a0c06030b090901141605120709090f0903200a0b04 74
    0x35610410140c01c840d4140c0345542401103682c0b44042c040140c001851610342e0310a810003145542841040084680b910903201e42900c0c0000307040c01580001ca0001010180101c00b4510310840c510141401c039290740c026500442c6003150080046450911a140d2183c40348881100525048002c076090b0781044c1d03441c00c0820000300a01550b46130034041c0184046003a9565080e42d03152203002580c03140c0d40c1c0c0090b40a5000080d03442c82c81c0d103d039040300141441d000b00a000403507544100070718101007150032030019454814007003005007584407840107c2cad030018811b81a60f195034040004400e220000d0414030311820b414100041d80011002c401004280c90015807410074105120b41c980000340040c01a914240703950710780505009546030405035589441d40c04074829207041da21446010042c0c001d0b27180447c108084aa0b0020010069425040d014033031800804c04507415070b290220300902064001729444404550070f25000d845400400071a1000505a203600c0e12920090382d00391 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 746079415 1250 746078165 746078197
    0x302281703041e11210303040c0e0f090d03230f012918011214010f08010c02070510020102090d080909090f0a1b170706030c031e020a05040b 62
    0x44180400c0402e92483c02c607410b0b480205529841e9101c108205891303500511a0000070b840c03403100d544502e40b41401c1c680f0401141c1c0e0700c1c14107040ca02a9521680704840d8100c072103a0000c1d80815001c0c00a0f40503101c00c0004040c9100406015005042d00800c94003403029035480040d0840c080342c0b031080c040e070f840007020070345941002e10760031080c9690681440000f40301c84240a03900d8100c0126240a0385c1e400d000c031074505d030b848012240f80340364450ba42e0016041c0806808050440e1481c00d0484038950581c000e500d45c5ca1886500b039420715800900982c005582c1040b0600b0030ba080c2280c0781c5914800145048003000000d22180d024142c181c6400c071020401a10606161849a81050b62900200100c0c1310400e0325541c0d40b4505903000788014500d40c0d22210070601d80c1e41e260007404507201245108442e0f0741a0303031755a86081c400d55000030309200001c41c60300d0082c80307042c13070700702c140e6079461401c00c045c60202d40a903103d40c4c3d51030308000c41000300241c018240300c0948000d2145d6a00c103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 746080665 1250 746079415 746079421
    0x24030a110310090309030b060a0b123c07140c010209031e10090501020d06060c0507090605060702010302070507091d06011d01170f0f2103040302281703 67
    0x325103002e4480b0b004442c481d01e0f21002c04040b80e046192102100d40c4000c40002941d07030400410b0300c1d00041e40c03059240d50300120303a4084141c0100c200c00e125a042d5030007024502c0c0003240d203056a800110300100c00d0442c014556200c0c4081e4001c090f44084e035800c201909a00180b40d958444e4002c55150200da540800d0041c1d6270b207014411340c4400012034a5214407280b070310010342e031035038107090070421850b60f203030303010b01c1041030a405440392512510030030032650f661000b02500b12203000c2c80807141030003011030102e103186072403052a05440b0050314150502d174042c1d0040d8000e44c00050195200e10407907100142d0f9032a42e00540d200b440790340241001c80e801d00042c48e441e1a80c183c11408100180020300c201040c4d035900b40c03c1c11a030444410070400c0c1d6012200034144450b44141d0b00060189556a825525000070804080310036032b4074241440820042c0e4802c140800e0f54002d00682004c010540303242e03c010015601410510302c40760203c001d9a41e207203038440117100c4440c0301407404020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 746081915 1250 746080665 746080669
    0xa0b0112050708122703060f0103061404030806010e030f19050f01020405060d1a030d0513050306090a030305040311060708040303060b070c06030e070b0f0903010b0d03050324030a11 80
    0x104400400081c1c0041266191400118049001701d440c0c4176202d031040281c03802072080040101e00d0402c0090700b40d80a504211030032205041d030900055031854208081b20300d41030411085d8a1240d5010390f1800e1740c54642500440304441d07640a42541846007107180b80c4900814810b446a07a442d07000280c0b14802185040303030428041d098401082d91052008010755114070007200c1c0700101c0b0342070014604100011040200400380d0803550103114082d1111110b6405c88001c0180910b0a00d21111080e519001c06070b58440c2101d0840302c80e000b00e40d40c080000e019402aa40084c032a040145c0705400022603946400021680070001031a007106210038982c042c4103003005804018001442e00205445188280307180d84180c508040d45e0700c89004e100e02e4140f1040000d00f828284a694601c03000f01a545160003c986413413203546000013400360307880e111011340c000a03030584460382503a84501000d0304118500300c01e170f1030750b03207080002148581e028020444064030803030b6100c0c05030307400f101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 746083165 1250 746081915 746081923
    0x1e0408010f05062d060403050d02010507020c0d110402160b090c04050709150815060403051c020601050a14060f0a020d0201050919150f0c0504090b011e0f020a0b011205 74
    0x401030f0b009250340390511545020b0442c135640c00410385805480d00355a00804501c46206503030018002c1d02408032000740c51076040d0817042c0101500ea0031209800c070103a0030007601800700c1c0380c014400301a0036046c4c0000e0400b900540b6000c059003c0503011000140c8401d004440100d5000d880351b0030030040c1451a15152080c10741000d898580220f916090046c0b50081200840029050200a1000130010400800694803203080581b000b61140c2d80c91402903682e26a0303644252009081d4890f1080561000503494100c600c000d1040c0c000f240340228100000b011400801d40281003048889448400752008180840c1340b41e00908401d40d945030000d08442c03000c4c1c0340720310399003008607002d424116000c010b00b030036038001d202500d11050201722071000b81980b086040005041c68984014990040042c1c01160491071090001515000c01185c40c0040b0001010060034104140c50146105285140078604540101e500c0b80d4440e0300d41c12544070b000d9001103a401141001070b410441c00740 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 746084415 1250 746083165 746083171
    0xf0207062d1512140f0c130b01050a0c1b0605280819090c031a0f0106020304090b130603050115090203040b041106070b070306051f0804081e0408010f05 67
    0xc2040140d240180300c41c0e0b082c41801c0c070030546203640700381c400ba0501c125080354403100003159040b910000038201409890b80004c1c207003d80b1940d124400c255210210340201c035085001651a146402c1160009841e00c03034054100b5070710300700791903c40002100c407408420080d20b41031720b4064a404401c0c0e0404040704ca003201c0d8003c1c0d008042071246079550481e80e015040302014504408030381c038030598a40140311042d40500007007600706000084c050307003042441e008804c001000f0301e15910f00740d407070714040401e205583c0140d00410003001f00c850303294040c58240348004d24141d603205c0c4480503041918480d40060f41c0c0b076503480030b041003500035120180d401055484c80030b5046103055210b00345000001440600001002d00c01041c0c1613454030704880360f90358040421030300e500b80184000d004241a0165a00640c400300305090341c00814852140e000110341d0b204e42d215170740e035500c04503c0e0b0001701040d8501004110005540f80c02940600301400d2014000a08110210500d8058440103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 746085665 1250 746084415 746084501
    0x40503060732030402040f1b08130c03080901080f0702060c0708190f0306051c020d0f021909050c0708070620071514040b0106050705030f0c1b03120d0f020706 70
    0x2032182101ca6014103c00440b000c2c1c1c109415190b481c6411182b81c01202d03c0300415145c1440c5010080040d4a40a40030340e010a90700c44c201969020b8803501030410540710075016900c0800001c04880f80513005014481c496086182400081c01c9144503038490010070700081030b80d1505018038141c0c10302c1020020642101c0d561083d0441c483c501d0520858860040e010380340060030304060201100402c0e541950140c4080026040c8001d5a4040380d6140104440d050500300480c072a24030f000160340c81141c10508103440e044230b568a400040050180b1410004007103001c201c007503614000600070290041d10f40c0c0c0c2019039407604400c00c0301c2d20a100210001c24400501c0b001c06c00c00807a940c155480c80c103140d950303511107092140c558003d440700304089140010320f0448040c004905132100b60480c1440e07203d122850f03c03c03d43c84003800c0c000005450000d03c21015001125004502c1a10101000510704038082d00c3e02001c0c1e0348900640049050710b0130a6000c0e0042c0242504010303040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 746086915 1250 746085665 746085671
    0x15040e010515130b18040c050301062103090305070f0807080604030f0f02100501233a020306010807060807090b07060b041e0c110102040503060732030402040f 70
    0x28802440c0608000d08005025040220481a03400f0040c4d201c050039441c001c0405d00164180c0083d4000d5020481c1c007201c1030703003160f0350018907420705000703510a542c042d1401403404d0035407954140e00940288826000c1103104580000480d17007d1203004003415190003103040c03141c10041c800d0304c1d0490540c80840c0c558440c80810003c242d004003941303500c40c0c0d04e2400558802900c81c00b20b140150744070700054068541000024519000d01e0034455001e811200442001714500400180548851080d8603502281c001000000034007240101c0c0c000c8030766003100810300c1e25004a494440c2c260840c40003540f014400b888203c0e0404060343d406000780c900110600c0c108216000c0501031510000c00c150b4580c90255013a66460b0002404403100c600a507910b03c041d580c4076006083c503003c5030310108a1010300340d1a442c0e0107000300c0b0300790345002d8014501c90b1076070300045540c5030b4441c0d0300c03460040c141120701485034078850f03400e500d030190303600026228101801007204507541c09c0c6507500c141d45 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 746088165 1250 746086915 746086921
    0x24060b09280501050307050409062318010324050c030906180a150222060e0402040815060105160c0609153207030c060501090504050307110307090515040e0105 70
    0x1010701c1e030100941c0c2082c82c105440c0d864100c01683c42c1d00403074002001e56402c042c40070400200301205c1482f02c0c1c002210140b03407101207805004140c034603a90301d20a960301c10001400458451029044a15003860500b62210b89120100c01101c03000c0e1451040918000203000480c071080001540103801c0c4401c4421400010411595400314988014180c505020141d840c00010b6030641d4a460024826443c0c0d0203e171052141600c440c501445004c5803800d40d09180d40d0409100765410b650207900204031000c0200d00d41003042600800450400104205403c403100084594180c1644140381c400032260400e900540768000d0b1350425820002a0100d0300e400719400484203403d2052150398521441904601e0b5180c030800c08072128426000080d81070030158444c5040039010f02500c01048243d03280c40c5014252070003074401a041707500502030100804c2144030304541050009003119500b507641c68404007600ca084400c03d035000640d0b20301200e2130405000d108004040310303000b040589 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 746089415 1250 746088165 746088229
    0x1060b09090a1814030d05090c0f0f0f0d0c030b0c130e0402030f030c0f100b0102030403170c010c0302040e150a060e13020f0712090f0324060b09 64
    0x250700825182c41c0320786665000b40e82c40e0b0040d40b10410280c0183d940b10100800480c290f961342e021076000320005140000282e405079000c01e684802074001040f4910511803d0104007204a00020065114031503000d0b001c1d580d62440c0319130300201d11602c000002c4614508011440003401054034002c41402c1002103210f642010246c4103a070021003030500c2c40d0b11a0300220707180c980e5020007101e0500c00000d94040c0b1080c0081d00c203240e0076418003280c49041e00850309000380e980301d00255004d40d00601090000902c50300c44e0b01c144805801c04d003401c02c101d84030120f007921201c00c802c0011030750000b0f003801000d01c441402c076441408422920110843c41010456800d00b0307115440070000e181502020941d20030038042c400c403080c180e045d5298407082d1024620382d403100c3d10403071f41414008030040d441802088131001715140e01c03104910712485d42d02c80e0743c410340c001c0900d002898041742030400000641c0c480c02014202c8000c00d203440b0f00c196401d014015030b130104510201c50b40c9600740c6840e5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 746090665 1250 746089415 746089429
    0x6090b130804030f051c030203060a1a0a0e030a241805060a020904020906070c060f090602060109051e10030204060906080319230d050f0f04030e15040f0801060b09 72
    0x984e41300490040030f05190406608180350f0ba80310079400184000702c1c0c901c056058000d1170190108a42034800e407a911000c5c1514034410b00e5880d00420802d005801c0024014154840c41701000382c191035150009584011504014805041461b007654060341c0380d00344d29120b080b00c49a002071304000e110500d600d07032079075450004090341c0186030009a585465225a0161071355090090172403503c45e003891030a04c00340c1d1180d0180e6800206080b00314411648a011890100c910a4007e000c050b4240b04044020f050f00070819103074602800e1502a1001c020000345200d5a100440204884d0841c41000161500c6034420302c21942003540601202001100b21901d449035500e1945280ca465542036911101075821301949001ea030b0300b0000045030480081609024840042210b41d03602408030741c51810565042c0311609240740050006402481003240b00d07070f002042046140d0f20007903e110079034855000f07140d0054050904024024090140401800c00d1400031420b001210000c1440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 746091915 1250 746090665 746090669
    0x3160b25031e0e1201090b0a18060926120601110705041d0a0323040f0509041b08031b071203120e0d0804020108060103062d05060706090b130804 64
    0xd070040d0381d0500c600c02c078040c005000d50f164000e4807840581c02d1240c1000d00902c482141a2000e01600c000500b90b24014460900d0a102c3c0b407032240d10b0080070f40c40b07000040c000008102e8406801410310664003d210b04040000c1d07912400c0c651369260b1600945c10300301c0d005080315061003001c2450700030740c0401041e040d06856040c0c4000902040002100038800c3c0450340001d8235009174042c000625a1040b409140c0514291000343e060003602c070010580d125078494292907517403c200030300261400250094005000d010100f100c454103181013458541c06500c40a450f5100060510020701c1080034070710f1400790031010302941d81c034080d01c01c0600c00301404000c04100d8001c44c05689441c00781e001c3c024000110040f250104485c1d200608400c00a40b004d0b070201e0b6009000625540c030a004000c2650b41d1103050744000781c00d04070010180034204144810b810a0184045102c2c1c0f14840038082c10f030b00415010a5540d440e050500b00c0800140826091441861442010510080403101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 746093165 1250 746091915 746091947
    0x1e020414070e22321e06060a080603030702120d02070906031e020310150f08030c1209012a0c0618060f03020f03040b040210051c020903160b2503 64
    0x65007041102c2650903100d04c08019480b00c5a0302e5141003d040840c4103500e10a070a0860207100c0340082001d8003142d12800c40349a5405003042101248231882411002d4000b10050101c0f0309140041d8005000743c0e81d81c0c4140c86083d03000d5101c1d51080c07581005030800402c5400300410440b4116180e0001404250310b03803003c1d01e0400200d190440d10308201003d0340326250641000324080c0038005a140f00c0c01c0740b00c2ca44115100c1200481c14980100859107054461001040f0303442c2d58112407441d5400482c074131418030604188c003206d42511031141d107812a40d030074810079a030040c07842e107102003501581100302045140c16868004400051030f01307041c0c840d90300385a0703110080c598040700039105050340580e1808001c000c1c003040080703030341c2c00d240240d00c2207a80014001c01206c04803000e00840d4a001f03c08450484010300c0003c2c42c1c3d0013488010000b505940c01e20100405446c00b0303080d140e0203558507080004d07220a0f49509460240341070004402c44081254181e28024800c01d5412a65a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 746094415 1250 746093165 746093171
    0x1050f01020312100f060806040b06040806061e060417250e0a1506020609100c090905060f030f030d0c0c110103021b0106080d030b06070803041e020414070e22 70
    0x7600064113203c07400007440104101d1040c1519010010314000c419a00341d03005504100d010b2700c0070314041003602d059070280300090000d1b6032044200510600410403840f02c070074a0340416600c941302c42004101500b9803402e4203001c060702414251906440403003110407058042591000e5a0304c070245207084544002001007651648807030140204039103240c4c80704442c1224000183c258003c0b6180d0321900c101c405480301100300b90601c1050f05c00060018001912449081c0804030307071030b407182d600041c0c00361840c0c0d500e207440f00210340f4200400c01d24107501e51000c108041d030440345014103140000180b50401e042e02d283c0e070b9140c04902107441c9640c149500414000780e106d2128a982c0c01c0c2845100091017165640c9400b1510340e880c644051380060b041124000d46418807508030b03110180d1003101207142d5501e03900c650402000b100c5001d8002010b010b010300c0583e0300e50007140400c0c42c00040052403402d2011000d0080a08151603a004814032545204e141d00925082c140b87d25aa41001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 746095665 1250 746094415 746094421
    0x301080307080d020f0a031b090e060409080903150609010815010e1f0605030105030d0513051908070f170a02031b03120d02041a040b191b1a01050f01020312 69
    0x80c3c020b40030301c800700805000b000c0f0301c00941c1e5074103070064610380800c0c200304620010360020031680d0001030f010b4141c40e0341504006c100c0c942050707132140d94254000c007511401c0c01070403800a410701d145400741103201c2035a041803100c80e261008800340104403000c000d000d061703545422500303003601c14828249007184010000d040007114460440100000c6500c1c3c0c6125500c41c1300141c841d070400c0c050b06000f44685142c3ca94428052030840b00c0b804805004688071510700b60403c8103030720002084040e0612081c8001038600b2080220360302070000a1102c0d00400d080400c461103160014401c0103041e80181115800f41e180803071060340003031030080301920421205000c00e02d0720f5600381070384100c5000000d0044e450348041d0f000c4e00c2503a00e940000c0d0007111907802088403a0061b801411050381c2d0402c40d5110b00b21032020307601e150341d6403030402d0a1b400806034061a1042c2541d14181d40305410104913048443d4074407001405403000321031030007198021500003982c0b03010350741101040528100c08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 746096915 1250 746095665 746095687
    0xa0e0a03141305030f071809020a1a0f04080615010f0f0e0406080312160c080d1a0a03080901181802090f0d03020d020114041a071413031106030108030708 68
    0x1501010340310207130490381c0c48040c07408101e035114041e00c01d400c0705804080d41d464040f03126025050b51260000d040a1081d4209007020f44002580c07070308082c45000c00c2140c82060303110000600010310350f4074040e1a45241004249480101c1860070904004020422860254100d440001407400600e8044030701c0b1708150100740101a560040d18091201040b00c01c1551860300055200d102c4501e020003015949003800e4580c2010301b14020503c1d2010301c4160b10b2448aa440440c61a800b404d0008400d02c100004c9011400c140d041aa00e030b000c0010b00071142d5800070008000e078450703074a401c01d05600d0f02544421040d081032080480540015071911641d0b156019400501001414210641c042d850080c0d903c0ca400f003450005542804a006030308400e0440081c4900d4120310642000100f002043c40e05100040c0418240804d48108421801307a03400940400c141d401455200c05040d0706201da28490410222071082400b00b006000d00c4502206903454154040002911401c5002ea = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 746098165 1250 746096915 746096947
    0x212180301150915080a1a09030d1a1806131d01021308060708011d1e04120e0604180b01120218100c0c0510020a020301140a0e0a0314 59
    0x12615050603100101e43d028260703000381c070318070082001d1259035179554561540752480d10b00041c01c03a08a561076002550041a41d140c0e2140041c0c06582c03500601324240001c80b69850043c01c0010b80d00307445043d003800c1c6450142c2c1e8101e100c1c9140b40d6107251040c00103000d41d140610480d45d160b19412500311504844003010150401c1b01d000355200c0d2400c1e03c01d07000728122403088881601c01c00c008500100e0091794890305981e4044507100b003480703400d5000400c0e6903028040c01c0b00c00d4115030070714007400040d400d000d000303d03c111030b51105a940702100501c1200300c0403250340700703440c2004208020094201304210b42a010400800d440c150b0300300584980c2038504007658960300015002e50000550810205d8413030007141e0a00b50880e000700304561444400c0c2000b03200b00d2003110180103d103440503200800000e03030710480b450140940c1c00300c0e00707607420152000e04401d084410b120a4802500131005105000c200400c28110f198400801558403180808034851000a0340c042d9442400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 746099415 1250 746098165 746098181
    0x1003171201091a060a020703030305041e200f031e0f030c030405030106090b061c1b0801030c05030303091b0604031a0402040c11070b0c0a0c060215070212180301 71
    0x4200c00815030751061001c0c05010a000e22045003074010701c40445a10b001010313036202014941c010180581180d400ba0000d090261064130f051102200034603050840c0d1802c506a180700f0020000c2910008100500140b02d07642c0c810700c10305958504600035200000c40912040c01446108086218042142d007003a44045a0440a000c0068903601c061000001002251005d80080000965034051881201c0050b10107a0b40000100050021511207020041c9650100c10000a07400d441020390000708840d424041d01094914004000340711491400100420b0b09a002d180b540c03074442e280d107032183c61468402a0001071004d40e4403850b107c1c1002e4402031680700a08031240d00402c0c5100030b04681c2120308034815404c281c19420018840c0d81c045140d100444002c01d901410005002590380009035848100e200340236041d00851000b0f6a1100100000e8019141700030a85a84102600d4000c0c0740c0b001b558031950380a11051054011101100180c4294100c1e117140740002a014200034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 746100665 1250 746099415 746099437
    0xa200f0a1d030d050301080601081903050901033e030105010c030f0c1e060f090c0501030e0c1c030914090f18010501030302011a010908030703030221240405100317 72
    0x21210f00070030b401000030350503501143d007201c01176a65101403d69a054070203005003126100d0a8950029004002500303214005040105498221a1140301020601941016041601e148050840c0d001d003c03100d0b1004084013100d0714560504c800a48001c04a681c01010000601420071a0034400c1b001c140840e9884120085103da0321100d54071541049002580c500303240200d078140c40c134250321502000d540d0006044480034900320042d0000c0a13000c4102100d40103e00740012117645021149108000035114400d00d820b15041c0100701d244241c2140161401070010120240d5425a07115403100000340b103001940d030340c00881913112400c1a0b10415660826001100700764040d000890f04207600d81e240c0c5c1811540c400116800d400764800c82c4443c1e0400c014480c0405c2c880c2d00105403c440c150245141d0082800c1c41803022642100d07140881c0940001080e00085218180060346404070303801c0c80a4240366442d0000103542d8440240b103c001035420805071858503059651034030705 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 746101915 1250 746100665 746100673
    0xc08070605041212150b130b1908100303080a02090414040c1401140301090f0216123509010e0a1b08070f09050c0d02030a200f0a1d03 59
    0x10340303000b0802214400101001c280301c6034032050f440c004e40c07007000396442d580314020b10190315004c11030b505980b10b5441c03000c60b003504000204040082c0b20040802c10f0340c62018100d5441440401404480c028240084d8400b21541c04c04c0440c0d03000e200983c0040c0c10110040c0e58802003c001401030020000c034120f4980020b08102c140000361400d102200c0902550400d031001c40c07801117600c0c015052012814400a10050205440c3d1358040c0a4290900d400145402000d0020004112048000320b51911508000140107135010000c2e0700b082e410705142100f28050940304840300942d0701d04a00100b0504000107220a2094104c0780114003460203a920760809810404031440c040c0790b003c20311024007240081c040c040082c42804075045101d14200032400c00306064003411000d840303401007e4060004044130829840251f0048a0407000090a00d02c5218011004105005952202102400b00c0c0d1700184408040312401e080d50b00d00540e400514801d5510081c41c003808168261003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 746103165 1250 746101915 746101921
    0x20f04180510060e03190c05060316030b0d030c0f051f0e0f0d020601170c0402031e0a0b0a150c0507080601030b090106120201260c030714090f010c08070605 69
    0x400d0350155000d040c0303106442c00c84a407500029180000c4403080b19805510106a24608184080b80740007424402c1e001c0d620a2581c0b5000105660401c1d0781d04c2000d008030415110714039400d4403810802400903a0070400d0034800e91000340c1039825680380034101054078000581000001e200c0229802c2c441c00d482c0803042d03070422101d0020b21a0600103901441409039501811400240da0188900f8590090206070700f0440358036545010641482042e2180b10800030703140c0d80d280059841000c04001c21a0700c0b01765036203191510740b000345c20108010b15203402c03c40c01d03440711180d03102581e0307440c00c1c0070f0001d4508030006c5588151544015000c3d0007800004a00780c903010850604a034040c01c442d4100343c03541d40c3c54900722080e40c49241025038a940565005500500d01070f44603000c00c01700c1c080c0c403e814100701031941c20101c1f04908400310000c10001c4440e0010b1003904c150320801c6600e8245203541000c11030907504010300301d0512410130341c2001081401c00495601580c41402804241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 746104415 1250 746103165 746103209
    0x9030a06020408070b030f221a2502060a11071e0c1e12020d02030321090708070504050a18080d0b0f0303030403030e100c05040510080118020f04 64
    0x14002d070050711254000d5030740c001290060300b0180ca000f10252440c001c990340314103141c0c0c10441e150b0300c2000880000100c1c0c141c04a00511a0040340440e42d45490702035140c0000302c0324550420000c0803d4903504400845045a03000a265500c18480380c070004d08000411540b0105000708113004004584400c8c4c280080345901e01f00300b04061042aa1403581c039201c004088003080d4214500c04510040182080080c07400e0310520102800508030032a04481038001c642141e00c0001c00e000d0f84200d0488030940c40200307400c0d41343d01c62144006006a2420192019258445481120302c03407a142c0002c120030841d5584a08842c4a00000c0ba1003100000e10306a40580c03c008008200d0910382040c81d40a4103119541c1c1c40d00f03c1000300654590358545e6016001400660031146151050a105901d0211305103e0481e8180d400e4465913207a0f4a40020011b410185031003400412a400c40104810180011541e007079041c8450056110350039010002800e008030351120118850f040703101c002003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 746105665 1250 746104415 746104417
    0x30f07021c090e0703020301030312020f120f040201301d0a0302060709060c0c09020315060d020408010b0a150f05071b05040f0506061b0c060c011b030e07030807030509030a0602 78
    0x302c01031021203c060380e42031015001c0380003d11000d004191009510758151a031640144040aa840b080300d0030080c54258401e681d440450703000300d4985d402410301040d9a04954204015900340d814400c0c0801c02c2c01070100404020414241c00310384400c10a0b8024a02004084024071207104682294009080081d50303030000b5100803000c2900103101241040c42900200d09054204c01c0c4542000d1510300d000c0000c0d0320080c41c2220040051003102c034141d5450b00140a4001c0c4002d01580f90390414814600f110703a9058030610514010f4820006a52030703101685020740c81d42055031088046c410155014030030b00320b00a1901c0941c0700c1d54001013091a5800703060f500151002c00010f01c0e5004644102c8205551681d07102105103c540a40c00e203d8844041c0040c24406a641c5190040f011988039000f0500c042d043c1e0751114841c1c070560a0900d00032201120030710b010300002c600c0070140e5071034004030f0001810034a000914801414002c90032140711071400381c200c4003148a07a0401c4402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 746106915 1250 746105665 746105669
    0xb0a0201090b010f3c060810120c05010c020d0c030308180303070e090c090604030b01170601060815010302070203061306051501080606090d1b030203070605030705030f07021c09 78
    0x5250080e001281e0080c603c0c26010985511200320915000304680c01002e20450b801d105c03101e10010003e40384410080d01100c4001c00c4981c8a25103282016a010343c00e95416400c00d1b4103104220100780c1c045a00048041e088800078201401d41388028004035001c4e841c038600250400000300000820075900c40015481482800303050f414190520885a0310303440b0640314500010300c42182c100c030380c1c9000d103001038001010940691404035a44c000c500300d9006644152251780d01c0000400c04070914004203075000c8140d8028084560600801604090010708100c088000d407000710825a4065030445800b40c1d00101243d40c03515145001c01c003940602081120543d0408011403900504495000045641610741d81c074280d0303a00041c000e40341c00c00107400e82d010003451780300310100d440c0c04a104003a04000181c0c011840c05c40c01454504030441c0d000e002001001c008119241d517212003030325001340b8400c51b04c80a40d1a008004c03803504071401c8403990801c0407495078801c030b640c0204250f42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 746108165 1250 746106915 746106923
    0x809040603140a17120a0b01120e030309100204050a15030b1806010e010203161401090b09100605150a201002180315010302190e100602150415020a0302040b0a020109 73
    0x411400c0340c6807102000c0c05015069184c0228003000b00e00710b41b01903007040a0108042c50300e01c50144da1071415006543d80b41c00800d50315040003062002d90071051041503500da40540c0300350b15080c900b00c0800e000301c1082c86000790030001101c2c140043c42c400c0d040513a18100007041011041c4000e1003111240406680f520f01184040410028550010040e40c2a040c03101541c203e01d02540e03150100c1400c51120720017500c2d507039042c0c07060014156945136805011918005c00c801013a8007182400c030340840d0005881150300d240082c2000d1000000c64846a002d031030700c2001100c1e000070780380d001102c42408070103c0c01090150940d40006d0342c050808000065640d02c1c0000c41081890741722110484840580d01101006002504152403095984260002510355040e915812054844000d550301e5140703c9210700304000043c0d04200110842c141c01ca102d14443c00c0c1a81c03400c0350342d1204c0000c101c41f15004900c1b09551802981030701d001b041864940366032101003c000900820075402c08031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 746109415 1250 746108165 746108183
    0x1b09020711010e0a0b041403190b06030f0a1e08070209191107080703080c13080a0201081608011806080a110907080702100b0a032901060507030207030809040603140a 73
    0x440b62804c080c5540c01c0318034002c8044d180c507041440c0303c00c00359118a02181c03d8400c9002c0c2c007100e6149100c2c01d282060203240400710724103020381010b081607006c118440c041d0707101440200c0403030020000039400841b0b81461243d582040c1c5400c2d401802603000107540501e50a04100f0100f50200d001b581c10700c030207507040101c1404880c1e0310220380116480079107d8041441420000f03802001e00365000805201c65504100145444200303144581d040320425030824515001103581003000140c001d80000855400c0035071850005002410510580c000d82480e01040424016a41d1182c2c0181400d0b405881c4280b081c0d040c4420304070b10900c0000d01820303150002a40d524400d900e01c81c0a10048d03030117400d1071160201404041c2100c44042644020355401c0000044e440107020781054040c01d210940402290404c21107440059102505202e0100710707010019038040340c041c081d280d200250545071400000403400426048d000100000c0150844100ca418000b4000090920980c091 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 746110665 1250 746109415 746109437
    0xc170c0106080c0303070b01030206070807020306100312030209030a0312151712160303050402190e0405150108030714030f0f040305010c050a080a020913050a02210c04031b0902071101 81
    0x419503a00c0f03032900c06860b41085031f00600061070880c0080035524003d0f0440703414004a13800081c01c1c00425501d0201080c1c1030a0b080003003040c10118240030b5101d9007001c40c104000e41c00420388441514600030100300c40b82c0d400959030b01c03060780080b2800c0e40c23590200c0c5900c0d0300c2d00c11901108020001103185442034a00e541d09200c20b1100702d4030215821101040c1111090760113070041c0001a2040368419003400304521003a100391908401030090304d0804403d8181801d009060100d940360309950341c0d146100600840c4c100104a511607039000d0511141c0d41110440346042d40144103006c081c01d58006400c5c50005451005801500c0c01040200582810640c00b550349110f210154004a00c0700c0700054601701d0144c0c00381108031000390a11821004800458081790000c440710320724a0343c003162076800c0c4000c085a40440b580d207203004413141d040501c1122100c1c0140d01c0010500d5a42c400811115803801030350300001d0184403400c0d5250704241c689000070440510880e80000c1d0402d6103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 746111915 1250 746110665 746110669
    0x9050124090c0905090709080a0f030e03010509030f130302030109030e130b210c0904080418060e040b13080f07030f0c020a05122404060501240c170c0106080c 70
    0x40c00112040716103032204804d00d020180001803000030224010700441407000100124140481c242092141110f2051510315140181003036a81d0001103001c1c1c3e00d02410054071501c008100c0e215044082c0c00c50780c0b148480031a50b0920350203900029055428240381c0402c040e00304400c22040341d030885500d2a0484a43c000c2012944500b40869100f6280001035868840c544d036099074042400c0251404604180b01140340210255170031079250000140c1000204200280501201c5d10320205112161070b00c100d1100c01e0002030000307000d006030200410f842580003146502a25070100d0314a4482001c0c5417011600e800c10682034021a00f240000c02c182c13480f0300380100649600514140003941401c06200280248a02da4501441540790384c1c11807c90081a040c844520503100d00014506442c0c0b0505461069008404101c803803024054a002031640c07482190b941850048081071280c1840c3c3c450401100030121702002c0010219000201908403805031142c61049594558615007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 746113165 1250 746111915 746111921
    0xf0e0a0f030806060c0102161202010207150510030c090b090f0115110c1302040f051009180906050a0b03061006090303030f0e07080601140402090604090f0905012409 73
    0x240051480c00006100c0000034000c01440e0b41220001d889541054101048a030880c0d1106550220714601105800d08000b034082c00c011010284d407000f03500f416159515000400125150070001c40e84550000d0300086005409400030741d000803480c1d103030725950000240107050340705c00140115400c000194580b03d050500c28103c1d8650311340300e044040a490111079100e801445113041c1c1c043d0005100b49581c410114103041010901c2c010307170b51480c0040c00a4501e4450740702c07038022070300e80781107084c0d01e90002e1032070b42140c084500e00c449540a20354100000c007441c02d0020325062400c0c0c1270000e03461641c0e020030400103007581210401d0710381d03101040f403800c8584910000503004604c14400248240c011148403402000c001c510540340324005800c028135900a0249030780301c2d8004220304100f40c0101c0c0800001503d0461030308000320b0106034544120301400d0310280c2c0383c45044199032200d40c0f0100c0d5172900080200100c0c0401c201b07160380104001613041c1e0b058003038100072410b415148 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 746114415 1250 746113165 746113183
    0x100504180b13151e290405060f070b011d06150f0c010b03030a020a031e0f0807020a060f0506010f0810260d02060f07232b0f0e 56
    0x4080d4150204040c2124010f042d01211951844001e07400008403640e40905403000c1600c3c024a0f039500714201404043c640e0070f4a2015554850210100d100c1c010b0320340110303000d0310000d6520590b100142d950783c00c0c1d80e202d10080140200c04e104d0000450114400b50002c45040c007100c1000c49880f14401c00140e0140408400403a0604000240d00e40c501c40005020020700c4200105000069000003802c2d0381180c6c1402016030845083c5804040d404090303039801d01d0161100e0101201d240000810f030120045141e07045c4031b40c00010602d100e0003000b07802c023501d81c00b005c2031194401d0003a680003d04030940d111070104121200c2e28044601403040c0078851103c209802010529000101c1032038140105500002042440390401000c0c05020380405c1800340e400034149030802045003800b20354010022001c200b5014809150399003001d07007070120020303a03102c0d05884024062a804210b020213860080100d4040d0f0325540d518516005000a5800f04000308040701e00110516198a070704 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 746115665 1250 746114415 746114419
    0x40807080a020f0f032a061801080f01060219060e010504110a06090506070f0303180c06170603060708091e06090115080607050304060902061614010c02030f18100504180b 75
    0x4200086a151b0203a07004a800342c40c600020326200d0a450204241d81e10264880c818103250000415055030068460f540248000008622961510314000d403511214259500d00401d040d0910b42448803507003004900403150402000030341030a2600040060722580000e000f82c0f18400c00107403a60040d00318004446000d080b0518043d40c56460704200040c85000309c00340741d61162000b403c5000c50141c071002d103108000d151001410084081c001110b80c01c540031280d00e126003000155140400c82a400a04a062a0180c6d4442d811268109200d203105a4110f104203a60908880720009000c4e00480f03940008103c588807080400382101e110740a40b030650303800301000c02c103000c0c81400115481801010b000480c0080b075130000e002584403100d01c1c1101012400044180150400e04444c4034031490001c2240d01240030340603440740540c0a00b68503503c004600a9409000c40220065601006000327103400c846a02c0080d000d0f070006e020f59015245030089a03d80f840d6148a03a20602c040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 746116915 1250 746115665 746115673
    0x50a0e0f0705160f020d0b0408040305010605090408070f060e030c0307140a1205130e010e0a0e010c0801051905091e07091d190f0519050103020a1a040807080a020f0f03 74
    0xca03449905030310310803200480e0445c01901c01940447c0e801d01c981070043d4450155143e5651442c106182541c0040e0032542c45610118103102c00103400004803610203a003c1440885050345043c540014400b4030301003402d0f404009808010700c0300100003895940e00ca003090f210144600e04400380c0e50200703000002c2240640284071541d4a0142e0060005281e010010001c40d58650194181d80a0300b0b034022034400f0000d80c1440064052802020f240f440100c00030404500d12960040000c0018840e003800750421744090210000c4001104000d040041c0c880dc080307040c841500741c3c9080a0307101a40850206002080860384500020000c0f100e9180454000310903140289032108800b60020b0f0a0f0340c00251400b20b0200e50b0b01601c0b00d9a9a000000192850068842c98003080114040441700b45071a00500040c0d03500300456040d17814509649052408880c4c0c0728406215641042110788a100e42c00a00c19600188400403940b09036020301c1d07504c0c5444203120008208030071155050700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 746118165 1250 746116915 746116957
    0x9031812010f05190905070909080c010c021c08101a0d0509030406020d02030c03040e151314150303030f0c0705070f050a06050a052209020f130506030402100f0306050a0e0f0705 78
    0x9034032740200c019035018000c114a80000301142d20b08450541800c0800758100c00301000d12015620700d68a9910b20340c0c10300d66040c1c9022511308050907240e00512800355030341044500c00005000a80b080c40502c14070801580c2028540ca503542e8115202d2309006204803021494450720100954401e655550000c0d801c0605000c5a603002040c020080c602c88103803d2400160343d81d42b82c0c5808401c0003c0d8500041d030000d011000e0040c07400c01006413249a201c48082c0c0110b0318000200c0358480c07090041c50007180c441e070900500500c100c41002c1c0003485121400300304408007074806011150112489000c072690f51406603118055500102c0200d0f00602602d82d6a6800100c45d1254107007180440811589603100b0b0f038100d030800c0c603014607241004205642c072110742503007000241c0b10840d00c050452819a00140c002c81d40b035503981c000c0000381d082419215010750000707406041d0051460410b65100d600710b8000c1e0300708540c401107100d01e110200700200e000700e040307850011100110f000c10752 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 746119415 1250 746118165 746118179
    0x50f010c0f0303140f0a05010b040f0e090c060f0d05010e0606040303080709090c020f1e0309221d1501150f09090228020609031812010f0519090507 65
    0x500c0d400240c00f8142c07100910104d4002440301984031794603004241446040109400d0201c1d18160081440c100007040203110180c424003441084812240c0e44003031550340ca01d074423820408501103094101e0b03c003140b540004480c2001520114009000c1045541c0e0782d10b101d28020703130059171520741140d806c20050020134440c400d107660002d80703401c00f00c6440383c0e07174520b40301180c0811000a0040c3c01075021035003500d5082c0720f00c46407031000e56007031032a00341d00300c0109481e0310405400300d200c0c0a0109401c1d01f02c180c61040d15210700c180c05070401141503001419941c0d02600b01c43c5038118010000000c1940d00101049816100c034526070a5001c02c1064041e5003125000100406100d04001c00090760320060000f80603d2480c1b01e448601e16001d0303403046006000d00e00241065422038400c110440030000250303650782041c002407101441c00301e0b0104541c080000c0404449501f05030303003543c9540341ea80259015480004494046041307510402d0100c07510008020015004040100040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 746120665 1250 746119415 746119433
    0x4230f0f01110d091502060f0f1b040305030a1205040c0b0901030b03190308060307030b0708061206090d080c04030b0f060303040f06090501080121060f110403030c0c050f010c 77
    0x38880c1030405100d19650400b04510f0b280c00080c552001400d9070301c1c1406129040000050a60010300050916003400c540b82907124400a101180d00c901401c0007841d080c03540711039200380f04c440c1d201d050307511a1070781005c54981c2d020310681c00c003140d0036070740d0304040354000d04c030f22481a900501d4019900b8180301c854442540507612142c1007644503040441150740c1032151440c1c10300c2d24281c18a9401c81440c001e40500c0b801031080b8480e42203031200b040031502404040b80c1c48800391814183c6580d41c40c0c00120304980d100030840341441003900300f208a000000e040981a201616040040c2c0d2f149203401c03060341300e540001010f10100e400400e0008241950140d040b903001000e503400e25071501003252075900e803540944001480c4080c04c102c52f503000002c1e81e02402001d40c2968104596501c0004102940b840051030741e43c1d10a510f4481e424245d006d05030310a80010308907a1386a0f2420014801402c04c0016903811410210004043c50112440c01c240074040c0c40e0b00071a0002600c9038105 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 746121915 1250 746120665 746120689
    0x100b04081e030f04120c060201020c0601121a0a050f0c0a17040c03060c0906030f06030f02060313170d0e160608130b0703050702010e06040203030d0e03090301060b04230f 75
    0x4940300500000e43e141110802034070180118544059241a4608240c1ca406142d40c0c01a070a40e4030402103c1c51103035000c0360340c03819940c07844540e02e81d0000381d1034036007000390405500c3c291200c80441401048001504507034003d901d045105091601c4803514210b46124004d0f111011030700e5243da009000c0617401c40d0507330140c0515138030580560389440340c50070b036101e04e50481c2c0041c09511060181035094403a00e80b882c50440d404101c0340342540e0300c02d15041502c41010b8071a80b80880000c080c04400c080c04001c0543c070030402003c0025150b041049900301541280040f41070034900b00341102c0004011400f94000b10740302e01130038980310090f900d10f50050108800c1c102c1d408001008100e00700b0704940100341c5a580001c41c1c1c81d0500d8001d003112400d0380043c189401000902c40035a60010a60341070840006000580d8080d104106107940b0602174030a41550030940e00140c41d1400c1c8018104440c0054103804a088040154001754807a6030052039000c0300a150403200c0f41440454012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 746123165 1250 746121915 746121973
    0xd1a070c02100e1f0c08040602070e0f0405030304030503090307061d070e0408030c031f0305071d1b2a0a020a080706090b09060906161502070203121e03040308100b0408 74
    0x3818120030f4a400718030354056004230000d64446d03c1c00304001e1f6051a0710580c00540c0346040c0c0000e0805a0b11180c41c0c0c40080c01c06801c0100210218407020410301c11200020740c0040204400030356510711500301042c0341410500e60041c0a000034200503404071240c80f03694010440d51459440c00316584140d040501400c500410148016480c02c07c04c05008014501540051040030300e0040c2134030188441509100310150035070300340228242c0414000c040b10059810042d00c44a0442d40404800803007020020b10850113034554580d0b81c0d000c21581c1c0c4850081d40c0350a0701c04e440715070380b0359940b10718410f030700005a48050801807142407002518031076500070f20b441d20380703142c800020f4080e41190103681031000c0c9602c0d07400100030118103c6008040c50080c2035040154503000207441d4041c1c41c440034045440041c0030444c1c01c0b4400380c2840802298a0308a4490070941402825800221a1201c06a11410010038060700b0304042d50100e1b10318000a04034a50300c003124800c00040f01003804 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 746124415 1250 746123165 746123177
    0x1c090606093e0310050a090605010c23070f05091602072d06030b0102013c06120321060b0703270b0a0311040e04020d1a070c02100e1f 59
    0x8500300c0080c2d0011402400f030210204c11140c1003408103c8002c0e40f90780721030a014030704041000540d800c04103900105401106032072000342e1800c1002c0420224082c2001d00b0300a0201c04580c2c45031640582040d10029106034550b075039000710000c40c80340c000042d8030159001200030444440000c1176411516182c1e040429280c0d103c0f2642d88921419420030030109440e408816544d50f8248100680c0e00c0710514000c076582e071107490124000051100c00140781c4c04c124084140350600d034210400130004075081241150140c1802466824204254510400e84a0714008000c1e0140903680c2990303c07940d010303890310031203a0742520215404100c4042006412040c01e200100c035004000081000800d040c1da2030401001c01000c659000100c102d04400a2200380a01c108528070107520031382c1941c3d83c1c61100d48e142802c4030101d100c801d5020600c0d11020400c80d080f540300c90b43d41ca10501c00d690700d40544150346015107460719100600d0342c200c002d200030074207000940403c088004103141415 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 746125665 1250 746124415 746124521
    0x11d0403020c0619080a05150d020a031a040212030a2f0106080d021e0618030f130906141003020a1701150207050604080d0c081c09060609 61
    0x3199090300f00113807540103245805410309100780c12008284d440510403504005600d402400c01ea90024940840d9004550300b100620454032140340e40c2c0c014540040064984040804010240704002c0303400324000e14101036010b02c8924000251250109540c844181e02c0c50b40038a02e201d0b0f06420020210492201c034154034038800c0a200311400307080040058154205800d00291a041124400c651443c0206e440d0f2030520302c01055054025000382d1480400c11180d4564600d14000c89400d0307284500c000407500d0032105c003e0a81d9088421190b018000f480d582c2030b02c6803103410600c03001c5030450020402c43d422076100340d0061444010b9420304175003001d4050403e59018800760060703038a216504036060360b540e40411081c0002c000446507140b03450704182c80142c036001c84400b000140300c0614000070400400d0410707102d1b08210781701c95850168080c9040c0f4042c210034102590390529044022614108074002d0380a0402f001c00361038661b101c3c0344031000002c144001e901040c22011122 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 746126915 1250 746125665 746125669
    0x607020a0b0309011415090c0d1e020304021008010620070f030305070506010e0105181b0a02011b02060105210712031d180424020a050408011103011d0403020c 70
    0x742d8040d0100d207000140617100301c13440f61400d00003e829160100c0d084088810b5030350342c054000c4e40c80b1121031021500c4011490b040000790134580320094000140c0c5046218004503503001c1c61180340201c810304c800003e48a01075804820038040e6000161aa60074581003c0d209250506541003500031580425600c0c00c200c80d080504e600101c000410010f8508180001000080c2c00740195850643c02c84d4504000981c0340b09001440800480c1130301700040007020b021402d00c4580000c2d0281c2c40e62003d520350020300900c049250350062000440040c022184000741c0d95040c1c9002034408460002c3d54a0001d06400d1038070f810481d40d101b01c880100e54504411184038030644030380c9a10049504516800042c1d11002a02030b015191b1070f42d0880311102c000f03102c10f403c40c1c0c00914041e03112902d1102a0301703418070320b610f40c507003940002541220154040010412616800e0003000315121311050b40940303200a120310000e2507080301c1c0110064840003e440e810034401d0045400e90b03a03034680 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 746128165 1250 746126915 746126917
    0x71b0c0f0302041113150302040812030906090705010f030914030a0302090913050d08090c09070906020705091005012a150b060c0a030305180f0105070f1d0607020a0b 73
    0x11008031464818108214207182c003c0d80710020400c90300c1e40c14241d00480d42c501411280c81080344d50b8401c040d4210805010b64100e078050507904081d103c01c403445254603d42c9500c151203002c040d202d200006100781602140310b00a441059681d03550305001c0d00821805002402c8082d603009031001c2c000080d00c0e10400040c00c1c800800d480250300d0311880810840308260040013902690155080c1600241c40070072030542d03c02240c18982429241c010406151003101074a5a400c603400405105005030000d426404440d896400c5442c0300b41c6039001c0c040140400c1d00d000c3c010322080c0000340302540c0503d1014100c840807c08249248408074215500001040c1041c1c410307a04c0c05201c80c2c0f0000540c09280101d40040d181240b0344118584082d03543e00e50300d030b406410503a071100468507241d003243c00d444601429a00710381c1e4442c0c88806840c000c03d015a00340005c50245001c03c00030600405000380c2840d020865801c80009200034000203a00c8104100e038801d4403d1004102058018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 746129415 1250 746128165 746128169
    0x11011412071e0203030c0d02090d110f0a1212050f180109090902060318030c1221070801090b0420121b070f110603011707091103071b0c 60
    0x20140c41080e092202000d0086041c01c20070050030011075010b44403258001080301d4002d00c200c07520507a11000c9009040003030050101c05a400ad8108144030300b030050f1040c0081c1c00107411144070707804010345800c10003294018450945c2214082c0b50250204220b0100782e0b48102c06400c10b10b00d0140307440c01e0b01850754022064064103600c846664600e81d64400c01c8503000d441c0c003500801c4091610b40002e000c6c4d02008011040d10407401d83c0320008520103006450300b2200b02000c88466141e0b0070a000c01981003080590f00c0a940303155401501101c42030002d00562203070311140b40c980d003000940380c00f505ca10041907401a1711501000d003410805000c22150000d6403100c25164030030000d500c181b411003d48820300b21107090800c10b4241823604201d88403c1d40c0041d100121040c0c515108411024103607620341e002402100015034000c03601c040d610445541c0c826644d0132519504000112800d0980c000d10000c428030001d40264080d18020304141c0420544e940c030040c00d99285a50202c0036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 746130665 1250 746129415 746129437
    0x9050403050c120f1803120315030f070302010f0503090a050a2904020f0d0c09050f0f011d06010f05160507080106080c0618011211030f07030e0703110114 68
    0x140b401d4224105000181c607030f149124405140c04025028046107029010f0643c5403049018804075082d42c081080901c0d0034405050f00e0b84138a40300c007410b43d4401030040503600a0096a4a152140c5004202070066039416110030000c6100c010302160241c00080c840c0055200c4c0301301f0300e03011030000c2010049030352180030161241500000b901c0454103401504448440b03090081c0001030792601081d040c041400e07103000750302c4142d600f8a84207010407a4400320381146850f09001100090b4036555106400341c2104890590740e400041d00d00002c803000444e505580c14011654075842801041c14400b51072902c1c608250b01504466204501c0e410304079569400010304208145080c000d103801450218007400d81100104089405031103003d085070b00058410f016203031160f001d00904a042180403208002d80702e08200d001c1001d500681d8010712081590700080c5a1a100c0d02a0341c56440350500a003224a00d1a07540501c1c4a00484c074180c180419070040c224078882c0d0f500907007482004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 746131915 1250 746130665 746130667
    0x32307030b06160f031205070804060e0114040c0302010801120b06040207020d021c14030703050d1d15070314090a02010804140d02010b130228020c0423060a080a08090a0905040305 79
    0x4c5180280101c0c24812082007040c0c10942004056070b0441d0b41d03258000d80000001c916217040c2d107080da004003401691008613240c9401400284450010b02030140c2e0302c01c0e203d142060b42c8039a02c6003124a4500c030000c00160701e600000c1c80605054000d0314641d4030191951184a20550025491407020340303a0a4403403590b071004400380100326450307840c2e4a030400c01951829205450081c034a115007000c10f0a120f86078034402c00d00704c0c1d5072942c0100e01001c500c01d8454002c1d40f01074041140c0d100740d43d03840000741040804100300003e005030b80c0c0568070a00045c8050b01c400d0b80190783c441001841901c901030100440c031030034001442401c18654050780005981c901a400308080004081f520040440c810300c5181c0b14039038040c4240f000800312014509040340301c904224500f6031080c0c021a01f10b400c0c620040c7c015586118060351140c0d8207442003040d903032003c0038032071650f4483c850b01c08103500c03144005002c111044001d01c003005016258519542d01d032010002520700c240c50440008070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 746133165 1250 746131915 746131943
    0x120203010b2d06090319020d120c060f02340206030c04081c080615090a0b0a030b1008070302160501060803041a0307200a14060106032307030b0616 65
    0x30401809410b000d0886001e4185070003030011130b5554041c1c9422440d800e04411001040d55107050012030843d07440303041101d0f14204024000e150742e081c0c8204943c001d08010300c2e03590f0380c5602e00a446100780031407200e000c6001c480310321781c02109071a841040002108410140503854490086218100141206907130354982801030349081c810640b50f10303140d2004564407281940c0008101d0b0400012600c840b586650109410100e204440c1102d40c0508032440010700c6001d0480900f9001026450410074403208806200c00c02c014610321000086855001921039400780c0d0140a41c100401c076400d44080c460390f111401c4881c4c8e9003100d04168004501006601504200701455120400103203040d0f0070145000382c801001c141c901c1c0b03003401e0030b0890400406402c0117001d20107500413060000c1105804410346d2a0142800360500003070401c0d680041c038aa1400403403440950380c01d02c41143d599283d0046008042d42d5040c030380d2100e01003045d006003c0600c0d0040842c81e008080042c40d1134 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 746134415 1250 746133165 746133229
    0x140105030c0d090c18090f080a05120403080114091e0907030804080627030301050108250e100f050409150302030a0501060504060e15010f033c05010b04120203010b 72
    0x201e0f00d854410101707820105100c1c00100880c10500905030b20012164440c2c40c520015a070a0080002101040310900100000d0651140f000c03030480340104282080c45034400c007441050041224216a0500440b03a551242c1022051503540001c45d0420b98048503100e82d00c001740c540c00f82d844a90241d000c078060110100d200207011000941820104007104001461580c590005100b40c9040c00300380700010b016400301981e0001d01c901d84112440d02d100f4210341c0500084843c0030b4050040c140e01a04000320340c062280f4861109498a034142400d141c041c2202c083c08400103a04100c140740800000140c50401c181e4411030301c50300003c28201d00302401c0c4030860701650720202d4180151400e0005410207912a00c0c5004030a10789003111a460510640242c81442120510589001380b4500002104410703070503900070800c585849041441108130075100280108e002140341000104500d919001441c01c0700f51015001046074400741001641c4103910300c1c3c1e0003000c0c9503d20303008110300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 746135665 1250 746134415 746134439
    0x6190510243b1903150204050409200616060504170415140703140d090206040611010b03010603020a05010c061e2408060a020c1906020c060907140105030c0d090c 71
    0x246900f039908410000121200c00340991441c4400b80c0051280303081892003240540450b405860003510038030002c2c40b146080311110314580c40228235444d414400751b2032450b014040700d00c00ea090070748000111002c0d8480300014000a04101c0344840215440c40f26420707884003420040c82586501d802c180c07034048014081c0c171503450001c1c031011410400301c00040c2d0409951210200041c41c41500e5a616079004c40040c180154007a6000001090000700a90303c00419030214002e94002e2160914031700070306091725491301000b94802c3d41224284841c1d44180a43c0c0e000b02c0c001ca1020a5000c6001070814030108140380503225541c540c030502a81c800c00e000b0100e00360510b2000002a1464124083d03100c0340041d18051043d600080d211880c404100f1190040101030090754100080c40e1420200a506c0908410128041c810000e8041080405c0d04030883d00741350b02d140001025180110303141e500080c0700c0c50155206100c03072070b041300c40780c4640862544034030748044000341040714030f00301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 746136915 1250 746135665 746135777
    0x3210405190501050f2b02091513030f081b06010303090501020f071a090619030623010e18041211010c0e040c030207050619051024 58
    0x1907084242000c006070b9078410100c840c030380c05d03200090340c031a8408401400020600308480e022002240b044041200450340101050b45080300c50400c0610354140e503140d18007844c03464850b1440d05010400c0414141e040594509120b110740c1840c02030804980340b031006034585001c4190384440014420107820201c84800b0304801d0000748100d107a8014240e0b511070350342c01829021408880d20050b03544000054400b84080206613645075000401010420754810300502e00203400e1290008041c00c2c0100c070201c2c0b11210440d403403038041d900320065440e40421007034260044404050914125000c54616004500c60300c1c201c3e42c1c0f80c050700c0000708000c070050504041c1ea4540310b5807c104c00e80000305903074481c805440c0410022000f81e41075009001d00003014040340184010455910b0b0713070a0f11401b80c56040f02080059849036058000070131aa1f0151540c4500c5290701e601210480f8003042a222405140c40516402c001c07454041041991070083d0480c0c00c249217401080d9100040508 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 746138165 1250 746136915 746136949
    0xe06070b090c09130303090c0503030705060a0b1f031104120308090c030106120b060312030907030303150b0a080a061511060f040209061e04090c09140f1503210405 72
    0x1c8141882804c00045410880b001800d0668940301c0c10100310040b5810401041e005054030b4070342c10542070103902e0b8001114151302c0545406001c0c41e09241420407802c43c0041012900106980030005400401c158401c40a0700f181c24131000a10340b0f10720240f0018141700307544004150801524461074200c1500340791344a6414031005010404078a4200d0140c1c0b90420019a11030716480e0201c0e01f0084841ba080391050000010025038000c00210001103074480d075000c0200c041440c4140d0341d50b529501030804856070400c00b90003018460120305400c1180ca80d400120241d841c0a903825a04072103d15001007602c260290350f046009010041e441001c2481e000124589540010144c0900802103803041440c00050003008200300140d03481010050000c200b90652804d00302848a4079104007181d460401050901c3c058405c0c00032070080c144c0001d11582a161445000d1765206074517045074061080e0813071300039407000c0c2c8100c6c00b040d045240e1060b5500c81c08c00c424840c031064042d8600e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 746139415 1250 746138165 746138179
    0x60d050a0818220f090b0a18080a0309030f02120a0c1a041209080c03030f07050307050f0619140a020d090b01410904030311130e06010903020a03080306010e06070b090c 74
    0x1c020036800102d160348800c0c00600003481500c04011050000340000c0d025012721400320706808207075016400700c42020f0003500da80046c1c07101d40d4001c91303450200424400250b10140200e01c40d16011354082c408851140802c000f1004043c0c10140c6504804c13a01580c0c500d0700d220381c0e5040c00b50824000700c094020000a48a80d90764400480d94a02c076040d03681d844d56400040c4c078001e208040c0255000301d0780c8103050b9502003134000b800580c1d924090701c58200708200004405d00d00040c80c800c00710420844040034004c0d49d01c1c050890000d400c12072034001003a4494a80c0c60001e149d0980450180c030b103038215030b01920800c00c2c860141609548102040d01c00302c6c8031007200c40310302c1e80e03a8207180b601c00c40d6643c040703030760b0741c5001c402038500c0b0b6005000302180403610141c0380301040c0140c01520111280059a03a591100450f104840b40c440603410488a00044c000b06144200a650015060404003402e0700e5645c00b2900076400520305441d10031680c0c05000403140c00b4040c0740016031f0211451 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 746140665 1250 746139415 746139431
    0xe0111100b0a05040e031608040e011710020c06040b1008011d16030209130c09110304062a0305090f071212030b1f02070e0915060d050a0818220f 64
    0x11a030f4074841c506407d084400c0b00d000c030318100424441128060705565203148000d50b07640c00c4254140c00d000e528054640180b00c01031429486510984201038082c40040070b4903181d43c0c6070900e24500c06494800c007003c00c2030012440c00024020111040984045c441403000b04c072910341e041c06890008100020060b50040025036070310359400b504020504030f00c0a44004130300d000e21b103698940d40481841810840c0440c5840499409148143d018403002e20907480d40c20480c1d4070b4028407922070405480215003040060740b03c2e610060f80401030388101d407000342c140b1610601e003104551004090010940200c402c124010010760001042414184040c0e503841c0005502040001408c50000303d440b0480c1c80d1052081143c44001d000c601004a440d0400c940b2854440f400305082175072003900c000c00b08140e802c21080b410b21341c58105000c2c1c001284aa80d8441e51a07011100580c1041840c0c60480e03c07566072103484070303c3c019070001003186184401002c00d0658080c0c1ca112010241341c0000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 746141915 1250 746140665 746140691
    0x901030c1a0d06180b03060705040b070c0812280f0c1e0c08190206090906030a08040602070e06040912080a0603081206120a050d0e0111100b0a0504 65
    0x40d090a65454028014801201d088940c100307008091101651074102070000075580441440c2d854042c84085050205080308014140c0d1100145c03210340001b00308020030013030140c6200180c00014414500100116a00d40302c0500c3c1071020080070009240c000b404c011800030f2414030340c50020b809001800d001507000d002420b0190300413201800d20104905840030450140d000e070140449145114110304150300300703900f080c3d89a000742c500e207100308100c8068907003450700601400e5a00600d941d14107044e80c030910000d00ca01601807138051140d441c1400000301584c0207400a4102c580c01085407074545404210040005400076024074a4111020003040702800b446801c0d00d07080c10980255100c28403c00e00510050340098039010001c03500c05204190303560709901406085074080343d54a04d2150150300d48134680c00003015075010b20300e00701d07429020380e00030f07548203105040101541601d001000d0408203245046180c10b036580160785c9907481c01e80b0412000d001d0650b020031103c641182 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 746143165 1250 746141915 746141933
    0xb041b080712090b1303030606020a0809040b0a0305030f07020f01080c0706090809040612120302030c0324121027060e420c0f090f100c050705090103 66
    0x8802410030240b020209a0b9800d80d03008240420780c003103892140c501d0712005440c100200140100d0010b410103100084031803000034400c070816048030711a81f030070b03000b101008000c02d0003014854124440120000c04240300b4409001894500960319686449601c10048203e4803001014140842076082c4000c0c0f002c1e9500780c03555107600903000150190641803a110034004c012902d41c0c03090038141c0101e40444034a80d1021003034460701a2800390301c0c440780d043c0c080c0c1c04112080b114414090000503020301d400018000b02c0b081451400501000300800305031032494850707200000e80e00803039a0580c010700905ca000707524202c1507000d0b10359455408140b1510b0040500203003146485001300d0016200074001341c805030301e524200c0034420707500030049004148444e80c41420400e80c010000400c1d200b01d03118510a0900c3d4107814036004001d940f1801da03401200e95584c00039440702d005040ca883d8061010400401501c442c6000740c01803034410710f031401a8003c0c0d0b0040d80d03034000410000e58550 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 746144415 1250 746143165 746143171
    0xd110a030c12030b09190f05070f052d04151706010c03021e0a140604030c060515090c040f0909050c090c1201030c06030b060705150c07060f0b041b08 66
    0x180b892030b650300030800100c000d001c1c41c1c14482d0303118100d0018402088103a07940265038000d07102d82482141403d4103207804548046440402044600c0c6901155510440c000c1c0300313681801b0a094040c00f441c0240000514000601d101452800201130100382d50b1200340324007846081c94400f0340300101c11241081084090a0076050112290b0340030308150090101e414580310300007200d10b0a10325406102d9454441901c1030740c0d481030310440751400ca40045511881b84d42c1549543c68070b448a5a180c0c1c0052a000704158003003401c002d03403c111a40c91507081c078054240444d10319100c0d800c1c210141c0c280100e0303a005000c050f01d0040b0440001d80c0110b072460315514111000822542d03403041807185485903d4001d03a144840c1c0b00040700f048903a201107030990382542d0b003c0080d051600140a06071064000143c015449180c42c45800c5582c1840707698002806002c0508010b10f550350103069610050b180c6661648034406200305e0f09003841240320088118503004c1400c0c0704200041c116440107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 746145665 1250 746144415 746144423
    0x714160c0e0621010b030f01050a0b1806090a0e011518150b070314070b15180a0e0304090903050306131e0504111216092c010f0e0d110a030c 62
    0x21101c10f01c000c200b0741c406840032002a090307803401d03c85000d806009110480d40026001d1034154030914505046620380303540c40800710440b2051302c41c40104010f45200401404401c1d84452090010300303c28011150344525103600c0e200c0d1542403600c000c0e5240314054000000c00d240030369480d0400303183c0c0350f02c0c01115a840d00c42c83d998296070800722504882c0c40381080b00354000203220301c00c20510241c910320418084031041025454002049840b05d9410490848443c506010a401d098517601c08100544008210b038070303060b038403002141a280d00d64001d40118001104004030350074082503511240820900800208455032030224148080080074200d007a9a0000202008902c004480c40d90000030518024544c0a41d00d059030f13014460040c81c4000f21050740007a02c40b40a01902e030440c68508400c1e00c3e02c0c91140c900c29000c0e1060103409200c2d41d260002412a43e41d60b10807940200c5079800070301018101194082c0c50b072104510403642c0350744842c51000103ea0311000d142d0916601c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 746146915 1250 746145665 746145709
    0xf0f080703120b031e1023090d0c03030c0e0a0807030512040305190507050607110f010309020a051903061b020f070602030d020306040212180c06031e0714160c0e06 72
    0x104004d050f1038500c04103100c140341c61038004644207080740703010380c280147e0f01c2c2c400c20403c903522001269220302c850b40ca080c021a05500c0781c0800280a500144080b45003841c0c00b40003085948006403040c07070558000b40854101500510500031b041c0b15030b8088040e00c03405580741c107142d40d450503a02d207000166070300c684da41124103d003005018000400103010080c19107484103000d04020964810580c40e05109041d00f07045400c2c1c55003e4003e00c00340c160001d01d4200c91301e15010a1140c0340c241d03220454200b2000c02404030000e01d0900c201c10041c0e01d4804800044181c40801900c0d00f50000c80c0d44181390b200304400c020b515400011030300106c1102c1e80140e2607032501d42c00b19010b809109440c030001c1050f0010000c4010744045404002958041110081010302007846001d01c0b0994061503452030f4103030403820381480e81130003c0d0021138502e0862050f001c1d0700142d0b82c0d03a420006042030a0f00c03048100c641440f00700c0382064041c00340841040c40e641045400035414500b1140700e2668003070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 746148165 1250 746146915 746146963
    0x5060a1106010906050f0d0c0b0c030c0f060603060c1c110405030d0206070912020307140f030304081c0f0230040e040c08010e0601120f0f080703120b03 67
    0x11080300d1030380d8100c8000381280e4042d40c44140040180405002d0719001c0d1500c44024400c0e450424800100c0e41c0c1c04c001040111030508510382c903a0b502c040304d60010351104109910100004110400240010790041c0a00b802c1180425007441d1020389589210780c5d0902074180044500440c062502c4912800001c10701079028001405005070390082e9490b0243e8210f88200f41c2d000300d440c030311540d00da90b10b0400703140d10f401224440c1985080003039007581c083c9406014549a051903410140e000426918400c060200041c0c0303103174000c0d04072103500e41260814005010070483c03000346d184501e051404003921040030082d0382e100314444421400d010400b4508620b004643c0000c6604c1b103101b400707656070345ca8004101c4401019641200c080840c0d010018a20806125155085902c400905256443e001c054800d00d61800410740300b050030684c20700e00050030207075840c0840d4450600184c84200f03d05028016030000440c1740c400c507041010740c400a590200382404d064031420482c00b01e9803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 746149415 1250 746148165 746148167
    0x3030a0c0309120507031e0203070b150604030c0f080a150c0c050106062a1a100503010c090303030f0501060905060721031b0e0f09040615060e03011508060105060a 72
    0x45a4040080c120380c80390000c0ca0f100551100051003001d002c0d4079036207000e01c0040034500c1000950700a400c0180c02c20300c41035002451a013503c0b904a03554525108515115000151315584550301c00c403820107001900b0000402c240c0b51001c0201200c00103008480380d0f9440d68250110302144052919546441910005000752030400146070064006c0100d0b41d2036510250018840d0144040d007031940b24010f20030584000349444d5903030341c00307150b615000c0b031034101001c40128007404541a61881c0c0da0003041c2910709220319454400d240d502c0032805072a42c2409011201c000c2c01800825051000521500e600002002c04a03401a200356680c2c10715410b24403221089055401c0200c4032032241004810313455000030305240d042500000200c680d9050560703000c00da4101c1150040d0880403d41c04500e0000031840d0701038010f500101c0c0403e00034030355000c0d41c0c0c000e801110200b44034122401c2242024071400303400a03141c618840066061004050740c8203814401c035445600000307440a582 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 746150665 1250 746149415 746149421
    0x7050d0207051c022401032a09090602030411040203090a0311010915060806160905040908070f0506040b0108030f0d0902030712050307060c0e1315050303070b01030b0f060303030a0c03 81
    0x40408141c0050f220040c00100030b441e05500c540301e1860700c0c01103401c441e40d0050f0034501c40c100d03944035504c807203c3c4010403a03140207102420303910681c0c51a5118001000f00030f900408401c43e02c16080140e61340f90610308202c5c80f40d22420003a0086205000f0030202c1000028420115901f40c01e00c03005140a07105c0c0705024048590006103200248002c4040c8140182c2094003503030300741405c1d10095a9007180c4c01c4100b05200305204001b81d00740404201c01d0400b070303016078081401189c0740e51800010b6291111124240c0780d048800350b22a03010803040c07007000c0d91940e0241003003801552424440c0c0c511000540100210483c00c15644e0720640c045580400c00310009084c00800b0110240e818142aa00e0f03406c084810707501681007000d0080d0702e501c02c40158001000080003038102001075407070b90700200b03040b203150142815600c40100c3c950354204003503c000740c400c105525413503041d07240600c041e10001d004c149200109205128540c0c0d070200035254001c9204500164a41d80c810040300a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 746151915 1250 746150665 746150683
    0x50d05190614090718031103030f030106050a0e04060b090114090a1d06010302040609170a0602030c040603060909030c03051e0703050901030b030c03062805070207060906030507050d020705 83
    0x3514503124000440440d6070380803222002040380c4180c0107aa52900c00d032554a0800095250001410b41c02d00002d04017a6a0340300b060006400c0341c3c00d191091004079095030003a000380b80403c0c400301e0a00c1c1ca144c0d100c0c005030b010790415601802800e01e00f06007401c0381d014814403035051010502101c8600b02c1c0718029505102c01c014500c1c40360700da80c3c243c0e51100c074004041780320581340c80c01c00182d46075008e4000c0340e003210314607902c59464a00c0c00e00145508140c9160400c2d06000b890b0401d40412401d0011794050040c14144135500c0e850070801408a070140e074031010020707003400314140200750030070851200503406081075959039013500d0b0400300301030010b01c0f04500030303d01140c0802410b61200c0985000a42a2801c01c4020640005c141d0b90301c4140036032640c144c5c0881c0026410704040304030045200394800104110701c0d80e6800140580d582140d01e2001684450010402c080d0300c40e00c000010b0100b400c04212504140000a1071441260003a5490940000e00c41c3c0030480c0030000155 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 746153165 1250 746151915 746151961
    0x120d0c0e03100b0a0b0c0a0602030702010b0306180c01020f0d030203061519080108031603050c030c010603110324130807051e0d17060d0311070803040612060501050d05 74
    0x3003500301c450700c00e004040e0f005070f05004200c480f0340400e18540b1441218590704c0502c008060f9500159a9007010b5407005100c00215504c5960152147d18100003050280d901d0742c0c020307030f04814010201d40c5804010f200840c11588441e4a0400d608008202c14442c40036034a005a5a070340c806e030114621004012501008a00c0016800381c084402030f00c4040d03100c02a035408281c2d0b6610601507030b49001c0c0b5882c0000041c41d8800540c0042e00820081007c0200d8130152420800888071450854041d54000d4801c42d4032110056403500d018407401c1c4060940e14501e40c00714406d500c2c0d030510010024100e01e5000c41d0464604244042c1c40d0968140c0c40d44001143d0241e82c600c803025401c911034400400e801e1041c07220058000c0d01400c10004107051002d4055a16954081041012185050140d090149204550a5603c1e0901c20f407005860307840002c5031759a1030001c004010a407e400143c108503c1c10314203018603a8084203c8880c404050008100c6407505040052031000f4044945 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 746154415 1250 746153165 746153173
    0x31707020d0602030a06090903170a0605032a030a120f0c08030c18010509060720040c0f0e1021061509060806090114060d020d05240102120d0c0e03 65
    0x7042007001d4001318810880c041c1d0a0004658031805401560345082c80200450540301640c450b0f40311198405500805508011580c48d681c5c4020a042404001c108003610f5030b2401c141410041d58190003410341015801002d5003441910b03100425611540c0326400c0203107a02c00d000e03019100e6404024a2500840e0035075990030142c0e0241320740d600c640e050306c0340c252842065488e01c2d8001d6094809100002e0481460090309030740c0d601d9041c041c0c0c3c0c003080c0005040802c5010607100c0344140c2100944507160300140a0b00400060100c085070300d1543d110b141000202c04025070b01c4402030800100c1c004120002c8001e00740e2810203411190000b50084c1400c00030786400c641e01488000494040f074640c070400352901818001c03001d0f0240a924140c3d030f0740c070b40c42ca00241090001030400219920b8010300f0b1184601406d01a220b0944038060100380001d8694810980640c815100043c00d00061047d807410880070340d00c5004004040070f4160f502c4001c40c003814010025606c4401c070080503a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 746155665 1250 746154415 746154439
    0xa15210c1a0702092e03020f03010c0e120307140718020a020a02121015051908071703071e0204050c1c051b1b0d0c030c120c02060316020c1903170702 66
    0x62002c170919100c180c1c41450314452006c0d040c101032040c60150319550350b0703c03494030008009000211300e00b40102c01981c8010441100440c0104000c5840c084104001e029410716000340c6620445051040381602d0b4030400c003a0400c240c000580030301d6580d0544481d890407007403100c114107000d40341046180716810f04200141c0203040c128046e00307035102210103d01e000c000c2003d808459445014103170955122900c18012010242014000302540c04201c03131400ca0250307200c580c991481c10140110440403029282140f40900a5950043c03204c4032590801840019202c80071490090700303240725a0b40c0b800300c2c1e002609420807044288101d42403555941e00c01d08140c0d100000c0703408005c1940180368a41946c1c0780300d6250106003681540c0e03410110440ca44a48903075224180c07498052016500c0749000503210900998031030f400300286003100c20089040a400c048090010621407840c00301e01c4501d164404001d50706698108840320582c4141e0420260345202d107200103503001c00200f0380 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 746156915 1250 746155665 746155741
    0x15180f150607110907050c12090a1701060315020a0806040b040f0204060c0218090319120c020c10021603110d02030f030408120a05030a15210c1a070209 67
    0x9a610041e004d50302103005a4a44504407400c0c0240800c2e5a940d40003071507803011511420020b080201401003041302017566075000b030081004000c80f140d4690751210f400b0810300003c0c1c51081c5a80a0641040d443c1039100440101140d00c001c004621460f680c107443c011540316030384601c0b41100000811503031030351a40009400201c08540c124855550002500822040712034000c2c010301e20340009609020b0700780c10f64580c0200d10807103207003080b0b0301801410007824280243e152640d956009010045650410f0064422181c00d908055520801150010311460414002225008104840c9900e4100002154802c0200002c0d5043c89800510b00c0e81c2030000c0020404c450003e011640c17480d401418240003805281c3c0c4140102c1d105000240c200405038203c0c0c064401c103c0f0049407066110368801121101c02525500140c400c50707100300030840756206040192814004c6040d6900f81e02c02e1302d045a104034071009004254010110301480ea07020284103141d00da6058040c1e0081c41c041d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 746158165 1250 746156915 746156933
    0x106090f05060a0f0e07050706060b03011706010506090d0f08070c15020d080402300d0905010e100302071703090a030f0c050604170f0f0315180f150607 67
    0x40d000c0252804001c10981e1034400c6441040b181c821000f440480c0c0762060301911084010441c400b884000c02c400b100080700c42c80789601900e1914501d903140e504004502000101401486d80240c0c07048005105550343e14041d640001c50464010100d40c1d1a450800c1c070b0300c600c003040142800b002050500030070810300741c0c2005961004041407080c105010b0226070f43d00070054800d01149010001c0340160601c4440c100440c0364042484502e6151900b401200c29920300e55a011604074a40c000881d5601191074002030100b4602108107128403000946400b0078030300741209243c1e00280c03500030002c0d0554254001080d0240c03a40d00e80c41d1031864152203d44c818022000607043c00390307028010b8000c1c170701c4561258104009180c00d6880b690340d10076030400224082c2070604c0c2401280032074440b0b003000740551410300540c5522418500c540a4110601011451140311a64401031229510030320300c550000d840c00341c0c00c8440d01ca0031b448000c64101c400545070888000940380c024030085007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 746159415 1250 746158165 746158181
    0x40206160818032103061c120e040f060302010210021e07030f02070b0403081209030c1b1906081b13060302030412030203010b1803031201170601080714061b010609 72
    0x94242c0c2c0341181c2c0e1040102100000d410044c00d1070b0b400340b002c581503040a10805a042c0c402d0b2007241055105030700c40c8500301420914400004406503a00d500c1c50600e401080a00802c41806011a40c11a0300203074868465000603400c55074045440ba031008074030748280b0b042c030bc02c0d42d491b2a0354a1103400d009280708503500510b400b5205007200000c460b00e8030401c076800c03071b9007000890341070050036010928010805048911907202c140310f440c072168001d200d030541d01e10000400384103220441040c40301c915510366656070185220f40e003c201468000c03510550001200d85900d0381d00c50324102ca05094040c3c00c000b069405803503500851800d406500460240e800f0303e110004808100c0000c80580c8424041c00e190000309020038958412400214220448020181e1f030601d203100c10f40b1803541409900005811034601407810311400244101c9015048810252100c54248500e0300802d48071800028010f250004011004031914100e8900c41c12040c1e000344500355a804e40c020150501c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 746160665 1250 746159415 746159419
    0x507030303050c091c030e0915130e03220e070906020f01052202010203120a0203010e09240612060411040c09030c0b0306011209030201090b090102070308040206160818 74
    0x42000f00700b1041200c019102220002031030b00b1002d2100348140310101c2103421085060040c00c542d4440c00765110440d062156190400b0594020000750411060071741ca0314200035464038000c4200103624001c000c42d500c0400348210b109803504280456031421049910500742c5108070000d0041c9030358400d0700441115242d46c06c45076410f07106034800d404c0322019541009100602e42414003d4000e0b140380e20145401401030324209101f041c10000b01403030449184d02101e50010041c400c000400362850b0b0004000b070000c20440f01160000c04402646114140b1800000c1c40042c8c000d40c1c034be680702c04130192410305a44031810f1501d004070303240c0301e00d0700ea4500c01c41c2002d5008000510490800d01140e400c000806d00042c9000c0140415130b202408035410007801c0d00700c04110030759a02404400910075400003c0b0b104860038a041080d4002c1c2000210340d004108003030100e40c2c03004002381c0198045502544c0d0303659405450300400060640249041d001080c03c0119050020440c8200401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 746161915 1250 746160665 746160671
    0x312040905101401080412140d0b0a0b03190b041803080103170c060109050901111305041109030c09180a06060f060201050f0a0e010b130903030e0c010c1118040507030303 75
    0x4941c01a04000f0300b00e69030a000810701c03030000300407410050741300d1041c06250901e283c09502e075210326205940700b940ea0984494136902003c8450820032991340042202150080c11342c241801160582d40c03c00e0803401141d40c40d5800c1d0850755459501900703d210780c1010349085481c0b94a0041c100d10024481915483d0840c4400ea803c0307a601001c95100d01d0510016203d1070303003400c0810008000262190000b9980c642150303821010b100b004205e4040c0c02819003101c24505800c00040c1c500386021803801103006d224201903901e00090480f6000d1040f42e014006941d80d4085107903125007030300304490a2040c1c01001050006940c4210251800d400ca8950380584a00003030b4260b45c02510066000900e05000501080d2586e000e21042c040240010960501d008005520480f0b1120358a54640d9140c03031307440c1016058410701e428100884058003607016100e0000e0440c0700d0524001e811410307c1c0300050310350740e00c0380c02d10184140e901080310300b1420f090419582d1408940812000300b0700d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 746163165 1250 746161915 746161919
    0x2030a080a0c1205241f1232010506040f0e06010216091d0a050c01082a1209120315060c01050109090b1302030d11010f05090c1504030206030601050306031204090510 73
    0xf0054011555103850051840d0340100d031003000c90b600381c1c851003c2001641d560081d400403824884117102c4c0030281c10100100c8d8060221095149101030788650310528003044108419800035482d941200c0d01a1054146d80e40d0701e400507400e00500c0400b0b8501c15584190109004c1d035030781c2c0158003902d074400940344801c92034010241d07a500d05440281055000b52465110340d845080401e50004070454090320700c81d804102d00001d03c01440501d60000004144103207a50201144158042c050300000c1052604840c00c1034070074072000d803401e0101070322205c007480241c450004540001725100d00030000382d07940c1d4000b8802040300700c40896440c03a2910110300000e091000d41c0141e10380003800703020081041c0400782d0b614a840214103c0743e549030304030382c0c8940c0b20500c1421f1203503d60310007030301e40084080c0412a28061030070f80300d00c0d00c11040c44240701607110041a603a20131002c0c00d1460b80e031786030540003a26000c16090080f13102140060085a00c1d0a5504558028035824a441e0310182e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 746164415 1250 746163165 746163169
    0x10801020a0e06090901031b0801020a0302040501030e21090102010b06071203060623030601030b030a0302161a160503040b0a0c0b01090b030d120f0e030403050d02030a080a0c120524 80
    0x40b243ca1659030344860585c0c01031011aa0724041a030b0251014059850b80d141d88581540c04da800c91024600400da000c901003190756054003c0c050080c03055401361016224106a060001022155403001c01001082020781039000354000c1caa600e100400c1c1d1900c0791180d280040d421031400d960100000e0401a0001c1c030076000d040c0584005110b184061407007146100b10308440e400040549041684880c007200d015201481121801d90007503025041c000c140002d403d00441280c1d00c0500014240745080b503500c15600c040d40c1828a814a01440054a0341449803840c025600722001c0943c001680700585504803003112081c51103841802400c3e80e850311700c0012600b010700d0564154001d0981424100c6c420140107801c0d2400c0d2000003920258404048204d94400203d80c6290380009018414040200300c20780d101c440300c0c4001c4d85007044081c0010140c48016204103086038407849101c0c4002d0180102d1031030100604410003007450b000d250310001c5811b46c030881d100c41090b01c0d104007480c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 746165665 1250 746164415 746164417
    0x7032409060f14010203070b070c0818041406100804050f011407030c0314010504090303060f080d0201151409040501020c12030123011409030304080118031107030b0408071a010801020a0e06 83
    0x5043c058020354207184650f111070112040c0148807000700042400c1c0301c000103604002138014080c2c074000104080c000081400304641010302200880000c1c0340402c100d030356440001c090011030616000303800d91200c0c074007580750140525490180703500b0400b0390309000c0000000140710303101c0740e5014402001400c0c3d0942c21a00c61200000c45140c0c01c40051040f401c00f904900c5a41d4824031b8009400d69460021401015060300304114542007000c1402440f9424000e1074001c4492442d21404c0b18070700701ca000d01c84642292002d010b0352401e0002030500070294140c5000242c01825075410900140154445a209001d8200d02e980c40d2001030150031800c1403650580c90040c0c41d14604188118a94103a5422052030140c0c9840104008180c2c104203004c0c035985c55881c50510a148489450b0103070540d01394090043c080c1c0e20041f0200041540c6101d100c0d00107400040c05640d58481d810002c0c407045100e000d500c0325040c6070000107004030707055005100101c2c2a44d241e4601c181414108211 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 746166915 1250 746165665 746165699
    0x1208091f0212090a0614090a09020a1805100e030307060c031d06090c1903051f3e0415020607020d0e0108010506090d170315010903050607032409060f 66
    0x400841c0e030013800010702404d46d00503480b0343c1e5010076083c0404000001e0300348103e40c1062441d1034012410340d041c03540190a00020081c00108842c550b424280803441c80003001046504010b801031111046407818030454068542280c0140000d440703100c40603001d410000860340200d2070205401940300004550540501c1d40c4101034884400e184003000464100880d01d140c2c616150403001001030b4040003500c540001c9c005503001080c0c864040c00781243c103240260080221418031541c2c69151104841c102c190500101c807483c124070240c03c80c0c0c0e60050b9042011600ca90f1407240080c03640001d10710b8820311941c2c0c01c4421109100c101181c4030310802d85814081901c500040c070081c9440005001109406000d00d00901005c0e00c0741d52844242588801d504000001800765100c183c0182028144c020309020948501e13560355107903a428003e01b13a1081558800e080e80044111440710000050240c0e682a44203807142c641c0301c000c2034503109005c0e65100c9140c2c00280795401c0d28204130 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 746168165 1250 746166915 746166919
    0xa09151512020f040c050f0d0f0c02030c1009110d05031c1a060c0f0106060504140102150f09010605030304170714060702010c08090a120b070c0c1208091f021209 71
    0xa0b52a020f84144009468500040741c103000c424020005403229903c05001c035a03c80500100c1c90f0b260300e042c2c26040300d540340c05c40741c1190020041c107240a08006003c400310b0b003061000141100a50420162880c00d03c01a281c0c014401004902485000405040b5001244503a43c6400c810a0788050440e218860f008550781c656818004480c038103080500808580c14050740c50844084000c242101c1c940c1d040f000c04103d000c10309101d14010a600b10084400030700050013000102c3ca040c4403080c81c010010150f0070280f100090508901707400490050002604690310b8035101c41d4120200a028503812003d4814100c001800c001d403401056810302001c3c20403403500096800449030b00307494103002c1e034030400100500b0003a51194007400b001004400f114020514492a02a24191010784518100021018880007044002c000c3c036080b80c09414101c58648810702e000e003881c1c01503041181d8040051403007080041e912041600e89031800c0c0d800e0b2524401c1c2d2150540c054028001525 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 746169415 1250 746168165 746168179
    0x40209070c06110c0a0b07050c060604090303090c060806040f0203040b0115020a1e0303240b1b160504060812030723030412030f020a05070b0a0915151202 68
    0x1030089029a2100408070300608001c140d01400032507800300b5501040d0003d0503588050304540c14401c008280e950010303007500d03055103000c09500519640d02000b510031403255035140009d808041c02a03025841e010392101f289100da40ea90304024001410860342c0d9030042d030500e03d41401e0682c5520881e80726a070b0100745159182d081c02005078410242041d130005501c200101040802c0c80d82c1d520b41000035681c075102ca585e288031301c0c0003801d0380c001524440c2e150408400e0702403001c1030300401100703886544030304075107810390001003c41d4591542d044000c43e002d005490b40d5106a10304d405000c0c1e030810703141030041c0c0780c0d80c0184e82d6a5008107940302d403144c1c0c0c0030b101194080d480386900c0c0d03900d90204940748078021103001c080c405030b90042d42d04441d0040c820124032205c94060042c2c041002041e41c04506002c0090b0015055108034000200000d04030700000b108080075070710005680c0c1c0c00c080c1c254110354400c88081d000300726030340f146140da081c984e0300055070346480850100b50b40d80c090007207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 746170665 1250 746169415 746169421
    0x6090f0b1617030903040302010e0612070806010201020d0216060b100507060f020d141f06051b031213060b09040309031b09020f130510080c1e2106010305040209 71
    0x1c488a008a0004444074807040180200d5040603601960050408102a542e207a00d5440058414039124107001d010714810301c219a4551020482c40b90b0001440c2014465681d038900100d0082c801c4100d103011030351000c603504c088200719200805405101c1d410030005c004c0303408104820484038240c035038000350007001742c480015034070340214189600c190009810280c800c503506041c0c1e03140601c181d410448410401403204038050710100c0c981d51104030303ea102c0e03003040030007007541c899284080d1804621340700c8141002c0040086414985409000c0c20720303414242c6100200c10411002039541030f082801074103651a161608a001d540d060700e4000c50325195030b8651f03080c00204120405010b060140001d000007003800200340d400711070008145d07528005800c0024071810746c1c2240c3d00802c06140c0b5080c00542000c040303500801d1640c1001d07117607101345594050392441121000c041c0e102c0810a0740200c10501c400c442d10f56040d1442001715030300c1d440110101c0300104d8000c4e6000140e4408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 746171915 1250 746170665 746170687
    0x201110106031112150411091023131409070b0315150c010c091a0c060f040219030f1104021e0a090b041401020c0306161805040f0606090f0b 62
    0x140581020142c01e50b4049000e220348003102417802c44050312001c1c0c550503d50003034548980020343c00000e080d07807030b482d10303041800401c1014404003405160640c0205010044d44d00c00705445201c03002c14500f444080b0b8241c40c5810104070075900c5510510402c5004601c0c4030002017600d10683d287c41150510b01c0f818003c102c8446080e06008144800411008041d81401c4c0102c500f18404c68a401003040d28145440b1946054131032a512160703001e0100c0b082414000c03d140d500700e000001e5840043c0c89500000c0c80c0030040d00d001202c80090340c50000100104050080220350080c2c0c046290030b107000c800d000c1644070301c024408540c2d456070600c012968200016041185d002e01e0304180440d21041d08884aa0054000c1c10b10b0644a540d81136a039a1b0400c101c01c0000c1094018092a0900d005030419941da0380714440d05022210420f1a00340c615034001c00e00400300140207004120808031a0001803241e03008920010b1040d54001c104003110005d01030442e001c5690080c502100303660 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 746173165 1250 746171915 746171929
    0x203130b101415220f05041806020309150703090209070804030206070807021903030e061b07151e020702041d1018080415020d080610030e0a140a02011101060311 71
    0xd203031a0f03201800391944085000800c1c020b81950310412907107650405d001c00800f85065801303244034070b0400040281290a8050080406500c000007607125224107607400c1c201000d0b44401034a40c560182003010701d0f40c1c16088001d90078003d407032040c2151200d001c00c0341d002d0821107000e005a4400c01c0841d036100c2c03040b94555448801d51041d6201c9001c0500b00405405500d28242c0010b40c03902c1018425039014400c070b98000b048501d440d80c0f5441203400d0b80050f40070300080500f8881a00749280c070107201e00c0d000b0404d034504031400c586508421440700d074003e400820082c0d0140745020382c0300111008410b000c0c03420307440314001400c11514005181014001001f8141512565141c9142c0007a98a80140001d4000040b0b0704500c01c8448100a14017019a40540200443da0080c4021912510300754140d00d8002e26011840146c00d454251500711030480081c0510b0050110400480c404103030420b026100742d0b00c080703001001c4100d640c26900d0a0101038655542214000c14070f140c081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 746174415 1250 746173165 746173189
    0xa090b160c051e060a151e091d0d0801081f0e0f0d110a0210030b010c20030c01050c0705041e11031b0c07180f0203130b1014 55
    0x1c600703904809015620359040400391560f002940c120741d241d0b8040b450080c440030b50b110300090000c000f030700402040c030a10701c07203584600040715070015600d2609090307504c00240a00f016101c144140c1f4038011020080141b0550801483d0003440001e8490601c16001c960403074140c04001c0a40c428119680c02c2c01b0f04010001070130503942c80b4040040900140585016010b10038007a0601c405c14120180c11060307000f408109982002444900507a1640605c3d48241860320b000501043c0c0040180d840c580301520183c00b102e6000d003084112802c8074070054415100b54191403114510303100544d064000d646030004170350403030a410300050800b40e101d8010b2055542ea4030500310a800c61443c115140f2407441c0000010000410000c070341003442c80d004480030300414516150010300616150400f40c0622000b2541d43c00784d40d05550015001034030380c0c0d0034100c07003190303a07081250184100c0390008000300d40040640d00002e0744162290031140807614a190141001550302003001031a80480b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 746175665 1250 746174415 746174417
    0x30b090105150702030a0b041406040b1b1b010b0f040603021f03020f03070203040905150603071409060c01090b010b070f06020c010908180a0e1b0c070506120a050a090b16 75
    0x3e1040c000980e070700700203049600740210309840190900e0700703041441040c6240916240e03481407003440002507184003015401844404203850035030341950010002d22031403900407040b50240380040c09407a0103500030124010105c2d071890445420606110544803944800b940c82412010800c88010541e8801da19002e80c0e485c00520742140c503162103420790425600640141d00104051000620300e10400350000c1a80800065840c210301c000303001848010110800c00010341c16412100d8620419100c501c0170080c0901c0c3c072040141060b500070030b41e001d000d03102d1981c0c02c80002244400c0c41b0403201c500b50454600b045641d000c0d01d0b200060340c0072142c0702a541d0368500c1c2150104801da006003c0c2c2052003001407520401000401c40c085005410500b0084c401400f84886c0e5008402c1e2000c04448012445807036030020030409090883d26032245d03030030000c0003c00300303211105051a41d11554150604204984802202c00f040b00c0c40701800410742001135000c04d100712034012602e1090401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 746176915 1250 746175665 746175667
    0x20c040e1011031f0b07062a030227030d0f170a06030b06010e0a12080d0608030909011e1202240d0f02120c090d0b071e030b09010515 59
    0x8400500c10840b001c1122024a1600c044240115801842c14103d00d01c2003108002490604045140d81d41c1e20481000501055880038055140f091103400b8440780300798181000c600c0701c030030315010f40a9440034101d107005501c1f440381c66100d030f18080032002040c80003a00600301242c0e0682c0a07980445076035400424888202c0000500c03402c050b001c03610642141c5004600300e40f551812207065007003c0c3c07495040c041c03080300070121501d414808030121101084a419009080c0c00c00741c8591150130141d6000c0d03814400003041115001000b859030403400d5505410a80c1d864481006a4507200c1c019148404683ea04000100ba014070700180d07030f4001040001d15085000302c140d009580c070525085000404107803000f07036441c1032003038801011543e030081d032034044c002c0482c003c2c080b4018003100c0307052008540300c0c001d5183e004141040030f40c051941c1c50703e414180b0002e00021480d500be58400340c0056070320001d5a01c0f81c050018070200141039009542d01b1b003010010701800c074294417865154 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 746178165 1250 746176915 746176933
    0x32a02070e070c1707020904021c0503030f01030b090303011d0c27030c06120c0a020111030702010e0610061709100207030c0b0a021e0702033c010606020c040e 70
    0xd5255402d015942039262500d19568074940346802202c0c007800012411410f10140e805a1200389045602ca0b50440c1c00c1849403000c0c3c6504440b00326200e101603c248000300800480c41d00e0b040c035480c1070f0b0b4054201d480c0c642d5500011b282e41da110074000d09000700c0e15003410542580343c400d0313035a80100004800c1c82c1054000f803000ca00f4110710b000c100703040b0f42e00c85039400e1f01c6007414085014003500554840c0d242c900340c00d2500d1a105005040d12503006000108440468801c0d4480c1800030310340c0781e03030350b640f4103182000a01a22440646184601800300800e0b000e50200140e18212025525030341c40c0c030f881e0504911490b44c8020030045003405450f001800c003480600c020034020f8031035104d002d0300603482e0501c507410480042021000340c0c410032441083c50303040080d80020807410000344d503070340c4a40c0c0302082c2000c080307003203084102c04035110b0f40c3d184101c035081107107003408809144200c000079a0202401c2e07481500c00c20000d03811198040450341025008540e450351b0071130803500281 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 746179415 1250 746178165 746178179
    0x30f0706091203150501050406200109060608030301030b0c090d020423011d0c040305030405060706021e07050c09160c032f2104231e030706032a0207 66
    0x2c032840784000003075514400840131140344104100604404c3c40c220307003000c0c10200040c000440c014001e001056850000d040f202c42d00750000c0d43c03201e9002c00b082c4815a40c50340328507030b244c2081c04103e41c641a54800079070490f62910590340a01801000c20714200c248e502880003c004c0e00b0100c8080e07420080f0502901e400c8000118001c3c0301e40c0784270ba1100400e00303450040b5040c010309040d00c100002c010820215500006550540304110340c0c007561100c445c0b0304030009204941c603104854100030211003a120340200a44602d03800303941582d09581310442002001d640031144800e90442c6d01000003201403262801c051000e100b82480701a080010f07540d59808050107013582c04060300d007012114428400e102c0d0b04190322580c0c54180340c40d2402a140b070a1401107002d8140712003001541902010b20105112a880e480980138486d0000c0d86c0100b414994a4014400c0c081c0c818000b00140c031503c0b80c403840c038500908800c0a01c0300c00300f2030104a09101c2e4500040118462a50b001c0340c20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 746180665 1250 746179415 746179433
    0x1403190e1009080903011805030d0e160308120619090b01051b0703030f18060c0201090506030f0f100b0405040b030304080f0c10030203060f01230409090506100305030f070609 77
    0x6000b140d403a91541c1310b039020142514005c007201c1c100b900ca014051000240000f013500c1280000410200b506032000c10064602003100c41d5054a14100c07440020500801c0e10082500c00c0c40648a09450f60700c0c5000c1c0b000341c405031400d803001c0c014201001c01c007000c280d60202c80c07e4841494034910300150300c2290710f401540c0b20200c50702508034407410005c00d80c0060b403a600006c540d06080c0403c3c00784458480c0700100700d11441c400c0c406c4020141007160320506400c0007404000f480c490300c13402d001c8102c99449c041229040c03040c1146001181c560704403060350b41c2c00c0b5002d601078075203854100400d000140c1044c000c3c07540c0511003130001140340031003406110400981d01d4001c00807600c4141c208810380c1d41d14107029040c94410011301c01075440e18001151842400c1c03c00d0050580e0041015011144a400b81c0b8405480031402090f20001074010850460144080303450700d0f294041c0ca601505540d210003441a407003040320064070b02c1594007400d0001c1c0201030015510040b9121001e607 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 746181915 1250 746180665 746180681
    0x30c120c12010e0d02060c0a0c0812161d0a0501031d0d050a1b03170603100507090f14011b0f231b0907030f0f0609020a1403190e10 58
    0x280d9440b4120a40c0d4503c00700907807140841284001c0a9604040000110a02c600440582000400441081801011000c495030210004950800d074a005407465120f40f80c03824140c00044d400c805132044245200340e021242c060010240c200340e27454400150002c03c9001e00310b030024403140c0d4511507070450500c0304245021060b15802d59443c222400107224160307000c1c050300c1e000c01d07000400c000300c1c1c5c0c8024060206544464040ea4030b0b2240400030b480c094030094a00e40580c240030801c4521513110200004031120a480c030300019845610081c000c81c04ca00016000030341458502c1c55824041c0b469406071030003034001484c600e03078a440b1b40e9a6903501e210314500003200456001d058000400c100003c030483c1d21001c00c12001c1d070400041c50700300c0140c140000c040d181e003010401e0b10100d5000b0800e11803064004c114440c0e032000c0840203074020b03a646001003418811115406136580d4100e078800c1400c00400c0440c04400d000f03030001800f11070a80015840303030100c0c50329090ba1a00c55104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 746183165 1250 746181915 746181949
    0xc02190818130c08100e0f0103170c0601090e0c01091a1605030406172802030601020c0a080d0f05030106020c010c060905010203070804050105090106051e040b0303071a06060405030c120c 82
    0x851405d503500404113002ca40c00404c02c80ca001041000b131940c1d0024180c1983da200080100d154038005a2803420f0180000783c88060149070b00000360942954445040c005000e4166860000c1c66401500d1024a9110325842d0b003100e52618900407c05900800003460080d804400746403060711100e24640154000e50041194600700c0307582011100d0005510140c600d408030074500d0325a540c0740100075100004020f0503004800724800781c0c024040c54204010281411181c0384d0b45810459540211a411801089652903803440243c0300350216816164590010f000d1132130340e9001100c9804800303005072480c42d9155a1203000490a0000314050002966075040d05c0c04e080c00c141d07007141d0300501600e00342d0780f6245080000e901da108001c11515107001003000d010710340c000418050105082429418040011441c0400140b08210120640c08411000280d80c130b003400e2112034892401040e60591000d968520507140c120024054181c1c00400c2d501041d443d030001c104d100b010022401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 746184415 1250 746183165 746183177
    0xa080a030f12021603030c0e04150512190305070f0804090506030d0207063504050d0801060e0904060f060902030a021c0504020627060d0c02190818130c 67
    0x10442d41c032442c554002107041d00c0440c07a02d42c07015030b0712900c0403802c0030080030716850b00900c0d402e50340109011590707480041e001f440142103043d040301d2100c0701405014403524a14110520003c0c0020b5000900c80625000a255110a45090380c2c0d80c0c02036902201e2a484d01071081d0000341202019000400c00f242d4041200e040c080b08160911400d0001d0008543c0941000c201d1190301001340034107203648885042c28985284003088070b13800d030840004e07546160001417000f004800241090b108c241d80d03503101410390301c51f041169a800c114503080c0d4000e09200c04507000c90f156a1001105c201a160b0004074140c1d2600c0140c2660001c847c411000d07540072400134502d840045100d41c0c0b903252140300300590304d4164001611405a1440740b021585a901149401117024140100e0100c1c020803203516050704040f0340c80680b00785040300c00140155589412940384c005102c5200d030781d1042c403150500c00e520403e070400001c0e1100696005600d6100b04182120341c1c8144410030402e0f9541d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 746185665 1250 746184415 746184437
    0x17190c03111206070309060b060c03090a0b0336060f060a0e0c0711150d1a0f100806030c0d0b15030a0f38100504290a080a03 55
    0x7603006280c00c16080d0040d94200760103844048041440c0d9449649401c00007907a00305410503000501c00219079681040c00040c449000c07030310003c05011000b504a070b024141c1030b111001304120780000d84401004404407940c0c006034444107c80a5031030304115102520099040420354a040001e03110301c40c584000c41c0900c0031600b0b04441c2900944003031440d00c90641004040c4000c64414000003400380b10440d004c40c40b013a61100c001400503400c680f20503494102002c80d540c002d054460704100d414030b01c0f580c1c5c0b0005041c40b101c203075005140140007071206c034108001501c5c5000010200340d814012110090026510b40380f400d5602405040f030000280f40400d034184142c8120460544282d010781303004030010b0360340904015502c0d40f11034015400840050200200c0c110081e07010707044011b4040310800320700030f42203a074403680c81c0070728003403042d6075442c1031004494031144241540180350360900c0d00410348c5401d9065250014081d00d100a95a00e01c070b5017046004501180058131001503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 746186915 1250 746185665 746185673
    0x304060b0907020120030612060a0b010207051c0609020f0607080c07060201060e1b1e0c070f05011425050a2907030b040608030a0c0605010e09030417190c03 69
    0x41d856000d0301d0750008000c1410807294400c600040d540c00c0466040703000000400395203881c0583d1440403c560100c03883d600340302260344050418400580e0041c07040f20000261362900b0608810504a44840b0080c3c6210315150344000c0d1025200c03d980184208800c160951100c00c01021428082c0301d4254544548640560030a50b0711350002c5c0031a0704111080c000d40c00200c03491508106203241118824000101d1903045020700c40c40380243e8403100308100d60134143d06004240c10541003003a0307010b80b43c980c1c0100340c026015014890004031922010031465240e68000c0c100f0108205009188441c0100041d00201080100f150349070040c842c008200f00303400074134185130300e801e84802950400340b60200341066401032401c0105034075034005600035102c5034048009043d46109480c2e80300900c440c0645202d040300d6040710340030300d008000074200c2d00c4180e540340203020000187d460a454072000c8014091b2a80f20340d100344c001d0380b001d01c840d880184a42c00742940300b810420312003441c50030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 746188165 1250 746186915 746186929
    0xe0613090e0d0917070504090c03060c031109060c03070209040f0b0702191104150e0907140a0e0907170c100806010801150203090a0305060a0501050a0806010509070509060304060b 79
    0x1c1d155000d901c0403541c014140e8206003030000b55980804810212025910b403980382141a0303000581081c0340811007821720160303469550035280140001c0c82a000d001004900311000b000720180508010301c1115101c0c030705000180b00c80c410407c1142c0c2402060f1f000101081c02c00d0394120b070000c103000c000380100039600b180d442d03101e42c0500103082c00c503c140c0916103030820071507001000314690f8522900c10740d4450f401031951000155041425544502c001c07a00c0ea0002e4070080024800c03a0f40c000345840c01000381300030818000c3d1080c588c44e07182442c8100c1115004e4903541ca40d0055041c0807440090040c1c840d40c2c1100180002c3c00d0840000040c86030500c00680300c0002c000d41c100400c001c998000c0300300e60454901304c04c214140a00e45900306d08500403d041150700c0045540000107100c4002900c44c0140300031002041305981c0c2c4c01c00c11526000b68441c446d09500840010801482c180384440d40c0282242041441c00c640000018000c0d0300807502107600d1079541c45900c2071400c29038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 746189415 1250 746188165 746188181
    0x412020a2114130e060409050d020c010905031204091505060703050904060b210c160f06050c130b0f070c0e400206090901060206150907090e04030e061309 68
    0x8202c2d103241c00d00141e00501c0e40807050242130f800d01c070b00d2008120240c499520104200b0380000c2550300c20541131703000944030130390303810300341d00081030200c02041515020482440c010400b0020925052030503080b02c3c05407503030640c0384055034680c2e0000901a240d80005001d00b030311131358865550760310703070300c20001195000d4205034011b6030b00307100b00842e01c099104c1c1c1e800d66001811109040d55107403075a0400a100701c03440c42007140d18a86c039002c2004510750190a4407441404288440d0382e0b640403010840c040c0751030b0a01c0c0c00051287c100282401440200300031140014014501110740d01e41d2002000346a0021141400e00810020700410903030a010000020403081d00c0e540c2150f0300855130054030013690f1240c042c4180d41800855441c90200c07803414601034018201d540c4e5902d030103512000b040710039044000442c440000c19140c1a003515104e4811138541d00440c5083c105544001d4a0003042202440300f0990840c00c65960903010b070403205510b05100c0106420040e2000540d5511 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 746190665 1250 746189415 746189447
    0x807031a0c03042a0b13080109081c140c030a0e0705011e05090409230c0a0608090c0a0305030d1d030a210e03071a09060412020a21 58
    0x814040d80074100320803260015049418200300500300092800c40404100c101c1480c00c1c07020310f000403589510b4001c2c3c141c102c0c103903d036100401c1c1d8030a40c0c02d0a0310590040240101c00401c106c070b0500e030401d1105000b0092199001400d80c108414140401c08207441c0c04031120004020000c3c400c1803809481240b6145e00041c081051800c3c0028010b412005c00041114105070384e00d0304d410f4401d0313058505078000100140403172603c03424881070f420720700000c26034114115248800344540014540801c0c00003d081d0a915914001c0300b2a86110041c1c08031126004a160b00c043c0d03a564968518040c60095000d1560b80c28000c010350201c4020300300d0120b6240700c1443d89003034070501000380c0700c0404943c24001c204421f0f5070000b400f44440c001645c950b251402070701414840d400005480014440c0d40c49010b50110344601c3d00c1c0380d0500300c0d045d6840c1d502c010000703400201c0ea1050010404c5d040c1c01100c503150159599200e1410751030341b54803080b0505048201c0400e80c05030b0b07000490004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 746191915 1250 746190665 746190713
    0x100b0705010504060e0d09092d0c0905030d080f060d05010e070519060c08030c07141c080103020d1716030201150603020705100e070f03030503100806090c010e040f0501080703 77
    0x5020300a00303421f825102d5030f0b076803070f44e1a100080301c00080c030070040d0020360811f1480c42001c00e0008406c000c05005c1c1c1d041c000a06034400120329800d0018480140740007544412003140d0b100700450816000007442140c00c141c07900170041c000341c424029030f0102c1484102524404e81408140610189041c5c2103d05115131040c042012a030000c4064549641280f4042d6907991520560a0148610980241525900701c80c984030b00601040520a421045000c00d013080000e82080725810801c1c040650300200149002000408002c441070444801c20300040c140790154440c9000764030721980036030150b512a030605110b546000b26280241c03000d8141141400301544506654400311155204260360740c0064012030001045250000c0c00c6c9003000c42211500d03450300030a00d400559002e81c1c4010300078004520304501094403031054076410014070800300310400444a4130030488055410603603407900c6e5008441207003c2c0d075000e49513410003040c1701d518614100301601e42514000000710a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 746193165 1250 746191915 746191933
    0x1505010c0213090503040b0a0f02010204140103050426070c0504050408040e0c040312030e06100e0a330305062202010c060f05010609080d09030c030b100b0705010504060e 75
    0x3800c1054034440603010b036612180642c2c1c078590400245520240034055100c042400505000c0c100003c10401100d80e8841104181070f90b0142d0a0380241e000c1c0aa1a40481c04e91036204c0d4401d0303001c0f0f0380c0503004e5402c41303902700c0f000d503041500d07000014100a1800b100040050921034181700c010014a82580e00b0040c17031500c0e86412402d03010b11301410004405031004a04a114481d0980d0b01840c1c1051560400303c40410018004001e4610a5040350007403600140300e410107070f5404404c4034242500301020b9901c1910078402030088d2007501424450085c00000f038800c0c00a0584452180030800940390f03801d40c142070385440300c000e1030001401515141120603a201d000d044c00800d90a00748428110305c249040c0000d404070340c040c503015924202c000940d982c1e0106115044981944c1600c04015000604407807900140c00041c1481d08680c4042000495088045500102c5840803c2900c0e442c0c11714003003c1c0c0c2c014a01038401c2da44410074802800807500c40c48c1c5103071a101000b041004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 746194415 1250 746193165 746193167
    0xf1b11060f01030803060612090604020f060a1409121605090c030103050c06070f02101d030a030801141216060905060c0619061e030b0c0a02120c0a0c0b0d150501 71
    0x70005020003080c0c80b20100110342251540d070141c40c1c02c5034161a0700c000f6441c0546150359241c1040302c09900c152001c4070741c1100b0703041500c101e40d46564190354505640034042e14400d0681d114035800b136007102504c0c0b14501c0d24a41840b40942d0b0441c900d0280c0d200d64034142c100940c000000e4404a8840c1003080100000303040011101c4d5440b0701030781c00039154245403d006ca9690b81101c0f000e03400542c08455491300644c800e200c4090f0100c102070840c5030949020038165200700031003000b0701041c2c0000040c0030340b25244101c40010030005014400030101e10004034101810040d00180c50882980280803060304082d01401030081920340904000401410650f20b200c064162184802901d000014860490300300c580540248080318241d16221034075402c120756688425a440380e01c850100c1c040c3c0c440f0304112580840140d00800c440f40440722030008542c401070385040c60388240018000081c00c50380b900ea00400340c081c0c500b034848036512000720946500054034050400c2d1040b0901c416 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 746195665 1250 746194415 746194441
    0x5010c031b030e070512031b241b0703020f0601050d0308070c170f0d0b0901060e1002071503090614092e0203010b070302100603050a080d0f1b1106 65
    0x800305520740402c10186050f90715061403080d800064115407109041c51103900004014640c643d41c1e40b1144503c00d46ca0800c80380c80b0141001541c03000c0d0880c4081c48031002c0b05014094100710b481074012480f4445010803100c030360050303008801582104a0f400e001860a00c009801008262a02009240e1b103560013004080000c00d00f1080c0075841d0b00c00c005214000a0440503044980302d082d039250140808041c6603005040d521440314104000e40040d03080066109041340c0654840c0b5a2801c980c0e8100203030b080300d200c810821442101070000f1000b1545000e4280e081a87d200041d0640d03560900c10301303482c200e007942aa00d410340030030700c451410b00040019000c8003071612440c094464813020080030243e010b00305401400440003003400c0304003000078015640719800301c5001d62480700c540c40c01d07139600e488064042e811200504011540c80401482c001041c0c2d40c00160022402241c0811201c40d00140d07401440c00400510900d40c00014220340c115110004107540d103080e001018007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 746196915 1250 746195665 746195711
    0x2150c030702150a0b0a090b0a14090109020a12020307081008030711100302040e0a0b1809060c1308010c020706020d141602040b06181311090103150f030f05010c03 72
    0xd41c01110002c2c41d110015030283e049414006c0c03109010380e90324200b01029008001c1c2c0c0380d01c03d150000d00016000700c07a602d212081600035080f032020ba0305c0e003112070000703400a10720343e002d2040f556440c08940c6000d100641c0b01c0c08080d140c85559041003000c0d01d1080c98103400007941b65004100d0b00003c07810b402108011042e044400303100b00b10000a044019000c0e07540700c200c1c0248081d0502086c0320080c1c110f000c9024060341d40c0c003882514010b040c3c100c0c84042c0c40b090641e81122001c5031600d03660034001d149a107007070f0406651880e80c4445d0207003110702c60780d1240b0042e0001c0c0d00c28050140d040c0400c038000c00003860000d68011800140e103a0a100d0030501101c0c8076031454030403046485541280ca00d001005240644550ba8005002031070b905001286220f8044101041c480d05100e11816683e82c00362101e00d0b00b08401c00c00190700920346040c0c2e0b100310108900000443c110803420070f030040e40c4100c000d5021200245400c1d400d49002d130300302206050a05807a208110f0448004540d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 746198165 1250 746196915 746196943
    0x91815040c0518150703080f070c03050a0c02180a020705010b090702070b090315010e19061409040f15150f080309060d0e0607050c0f010b150a120c02150c030702 71
    0x8031003151400003003440480d0101607001030ba0101350170702130507000100144030341880f0001c400e940d566050212960aa150001400b0510900c698046240700e03401100e02144040c11030107110380900d01c200a80c0303100319140780d03a4540000704003003002828020503c1c0307017806880d04444c6082000020392102881c4c05454034002001c01d05018642d0f080086140d00801e2804008407940c41d60403c444500d412560001061505503d07500120013a101f8042103c2045214581c0c1d2080c3e0020002600000b80040d100841111005000300d1800007030100e003001c030aa400521040c080111104601c055448808a60200c2601300701984002c0100c3d00c0c0d20404030f503007560307424041c00440020100c20541910f588150401c2008103a0010001c1001c4480182260011162a0307405420384200342c43c0c580d0400c041845100740240f58030058032240a04e810803942e4500201d06090855a2070601800180d1201c038900103604405010103401c8818844543c0c42c600c1c041d41c02940e542504603050b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 746199415 1250 746198165 746198197
    0xa030209030c0d06061a0304080a1101150b180a120b040302030c06010315050f062803061103060a0f0b030705180918100c23091815040c05 61
    0x105640601003255442c5000b0302d0420400001d0030604000e08813030040f480d50404502e01c0748641075013882624441c581c094009854002a4601101d240c0d0900314451403075921000001c506101e80303500034001e80300303a03482940c441910039090400d00c0c511030741860042e070000e0000c1c0040050340c0c000255641d000b4112a08a03200e61900700d00d54451500e050040780602000032041088005a8803030441005e41c0070f00c5980c60380390400091580a80da0a503010150590440c41e041c511740e500c52030300c0402503075034a04507038035140d041c252105140340c800e09080c0041000640e182901000c0080c140c0c078104112100d0030f100d1199003e210203002e00e8144600414190f14244500781c2e201c0c0e0079070340507044e00e01e6424a0089518075500c001034020b40350103008861400305146100301000308426540c2c0c40e44894401e0781d5000c401c005240080c02100707042000303942d551150b040e1184070140007202d071301661626010203281a8151a44036125a00b0200c00c01c00c0360380d008080e48c440b451002121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 746200665 1250 746199415 746199427
    0xf11070e04080702030706020c0108060907022104270c05030708040f06021b031201090c020705010309060f1b0912020a0510030b100c0302070b030f01170a052a12030a0302 75
    0x102d61034000c11074001d60500c01d200001c288035a01054107004183c003030300d44000985a83c0c0820120761412207aa500582c00343c0c0800000c0d48a01040c8500d2440315801e840c5003945814110008050200c0d15400080d0040c2d011003c2480c907104503e010403580c40c2690440c201007400412600c800741000c8c01c0c07404000580403d201003541103881a55681d10680d01c4800520040b9890340c10a40c41a40040d8407a400055000c07600c0c085c60b00329121a0340501001c2d410200150010051004140d880b65500c2001410000e0a031084040c0001240121500e01c888080014124a05500495858101c60510200681702d4084903401d445045400c0364600e50340c0704040300106014000c03907602001c0c01180d494015000f40310898503500a45c00e542484c3e440b0814100c49100035149444a180d010b00108915844c40006680a0b8405c0c1e003503c0d03944400340c65291420300c80701d040c100303917682d001e0000e20082100c981a8262000c01d4441400034969804404d03246e00400e25484203140d00002d203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 746201915 1250 746200665 746200673
    0xf0c0c070b0307120b0d0302070911041230050405101106040c090b06030606070f1b0312080a0b01090512010612050d03050f101202120a120f11070e04 66
    0x164001e00304941c0016100d15040000070002c80e070440c3c0610f601c0380ba0010b015034604100c0d109610340780d0107400804000780f038989110020100f60f0034085103094203100200389900140040c0c1601c3d07000d04200c4110742d0f0040182c1031040c03c1030a5890341681946410b001441e0044256401c0711402c48200f260402c004100340c503841d40a901c40c2145014400800c8100800300d1096000c0c0c0b01558404c00030290b0700360074848144015200c0311790142083c00803800003402c2c000c101840d107104030b042d2000701000700c0290340ca100254000700e991150070f683d0b54600c146d0200049601002e0000284400d0b40c3e4400060000c0500707010b101d006141211a22060140c02d400c04001881e414401348400140c9050068481040701d10b560000790500d03020555030000c40c541d03980902195640728203542d1a00d41044464104120202d80045920345008503804040c444036010f51701035070050100c402240c00050003e81070f01181004d10004400a41a17000009000f406444611408a8094983d824 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 746203165 1250 746201915 746201923
    0x3050c030d090339090b030c09060402130503030307050a0305060a1d090708070b0405040501060c03080c0304050a1a0901202b021b12180603070c14010605030c03060f0c0c 75
    0x2041280d541000000c03132010041284021048030000041013100085e503404060321440d415841c2c1d82d1007005500450007500d8030f50300400e10280007d503040b41d500c0c1e81c1d0001c2400c541040381c1060101c1c07000301d00000c80b5030305402113513030091085031200f08042c203042070072501c09040140068800c6011002a0310038000308802c00180c00038208450a46943e034074042c900760303c1402a10b000e182081c00009000d0f0144540c102559403680707441c00940e40f0410198102d4000074019200362240c8810040403800c0031a520278001c220174000c01040ca46549411f01352010351032003444888c907070041c2514401c601c00c1036800c0d40c0d191514507811400500442c0f80241d2030400c0001106100041c150050011245501c00710702c0d0140c16114038419480d08205c1a0080854480145c40e0300726414015161060056034004000d0401d1003851341d46071143c0c1141d82c80800b0211280c2e641750018412441c0c1041840c044500c100d00500700c6240c1414004215034000e070070003100d80b0f0045151308850100740 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 746204415 1250 746203165 746203223
    0x30d1506050313022b02030f0d021c05090d030905031c050d0e0a020303030a0504030801171c051e034f060f1a010302070209040b0a0f0e0703050c030d0903 68
    0x2080429600c0143d030054861017200e542d040780710307114600b01b0b0800c0406c0800d201721440b056401800c1c0121819601409108403010f42e0170801c8820007444006039551074260070560300a0f610b4003003135801c0038145480e0940c81c000c4040615052014804e52507849411918450919000800d5420403c00d6091800c1200131000f541800701204000600209512941c4254041d0b0355000090341d8926020135803d1481141c0d800c82d810016070b9006126000030b084210800910b0100e181030981c1c4003001c82652040f4016a200f0700c00420300070104900c80b400c5502036094440d4213801c00d010340129000000c0200c003070252031080024030b218900c610b001140303481d070002001e008052010344080010500d030300e03d60841d023a03180e15820042d403191003501c2c4c03446c1d40548000070688840c1ca8201c11128000e01000c00c241d101e8104400c104518001d030144c0007000001807400c1d900311b1a03e40d0814a45140f40390090f8009284c000c0c2072580034000c00c049030303003040d0a01300a1894840700c2c91146021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 746205665 1250 746204415 746204449
    0x302030f0609010b0117010306021305090709081b01091a040e0705030f0f060303030f100f030308090106060c0506010909290618010b0a210905030d150605031302 71
    0x1100180c403244401164591181009400070801c03050442c1c01550222150041c01104002c400e00510021389264000e110540c448000f8401e00d6984400140c5600380407104a800100c80f00d01c1082000000c10100c1c0c401d810b45140f864007400c0c501300081a02007503224003a04a00e165894040e00f081b01412580030b004110b03950300803817130800006013060744242e5040c0c1e2462454400a1001c4401010031401440010083d5143da12145c00543c00e03014090420040e43e4401c0100040d24a450343c10f42c0000d5100740c0700ca9026180560010b800c480d01680714405122014180070001400440c0c0c00d030544007403000018043c051400c2100d0300381c201c0000440003010030399031307825002042151107118402c200c0e1141c07143c8000d20901c0c0180103007132042e01ca8030740e400d000900b502d0703004100c07404250b09219426400a0480c0e06a08240c41ca0ba03130054641d0342000910013214400c0d0300480c100704941c10f05107801c1d20700e041300c01002840001c2c0b4607031074202d107103040078210340d02c04070205188181 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 746206915 1250 746205665 746205673
    0x1006090b030c0d080c12041805060d0605070e1f08090d050a0804050111030f1602010c200312040c0e0c0405010f050a11010c08010627060c020607050712060b1e060f04030203 76
    0x4900c030580d840d031f11501404d0301c0c14220b064541c582c1007040c043d81e44200c90141080e111020b071959070704d0142c1710203881c0b4018030507407103440780050b01e506090164811981492800c82d82c03150303901414504d00030b800c60001d81c001041c012903458101041760042c168518010015580d1420400d0042c000f20017501881200001484048000c10204c1c902075a000041008990b01010f400d07800c0b5480018450081a454007504030031048005c1402601e282000599281150100380b400d4a840d040b201151070a8483c801800f20440543d50186e00c0071402c480f491a19051500107011f0000c14640081049400038071029110712500e00609080c200000a2001210084010704920401d00840c4002481080e5180301c1d140d04000616113225156800c01c040707802c00c0821141c1508225040c2c2e000340040104100142041080c04001c0001c518020212043d914019041d1a4083d600744e109000011078014503810392810041c0b44031040f188203603241000d0703240308020f00840d84080d5150007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 746208165 1250 746206915 746206933
    0x1219090b0c0c0405070215040b0c0405031905070f06020304230d0311061003020f100203070b040f030906140d0b0307440307150207060507021006090b030c0d080c 71
    0x540060000104001150f00f80080d0fa201c031000ca80d182048002c01c1c0001da50400841c1c003007942c4001142d0806045c82c6014602512480403034030309002107410030000080c101082043c40300521407100900703000110100d84504e0000025900d0149009900d01e035910914821b40070503025480050308800500101c030032768020308000e000445050204c0c0f600303015601c0010304009030030081034283c0754020300d2880c0011000c414001d00a00058048055100402c1340101050f2104d90151150b885510f03000788803841854020302c0e00382c0320f600c00401d0000b443e111020360001981076851121340300740001018941c03080001d140a185030700400000c00b014603010b6410080c040d081c0c190807d00601d0401170070622104c46a00c00d9441840d41d6180c00038001100000c140c0d01906600003444100542001d02c00e4660f90300b00e8030155448400b60b44800c280042c280154081d10000305900d035810049504510b010a403524074a03d5500e1089095602c00703401c002480c030940e06089015070072520310384 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 746209415 1250 746208165 746208187
    0x1f03020325050a03050610090e040812040c0602011413020d0f230f07120b0711070f050f040e1b010c0b07030e100c02070303030f0f090615081219090b 66
    0xc0d000d043e604000070708007000200769041c104a102d444c940540d0354000003078039005015001e8803024000700e80c1c24004103d0407034031424021500d4065801070101015452620070082e003150100091034182502d486c081046c00407400a00e80003050b0160f4481d00a42010f1400b02407903820a41e004103c464450328000350304243c4104504044060f02c12540b01d14440d414003551035400d4491525203410609240780050f01c00d040080c1c006807103080c5003c222a280044504000a07a08460000b406004042007a0710708920492a039400654003000304c103646070711543c0c9500749410a0201c2c8800801e0111160744602140241c2d590031088241950034100c500074043e1008030b820407443d200300e0540c66411000c81c41011020704c142c0d001031034980d103141d800790064041410182d0149a5441ca62400c04102d0b0140410340c5105010018101d6849840e03c4141c0046410500d15980240721140200c02e880c4200d803041c000050001c4104419075130200e440e040150002e054540004c2200300c511 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 746210665 1250 746209415 746209417
    0xe030901031d0d11030d0603030e0f04020316110c0303180a0b0c0c01211b1b08070f060b190306050c1603030b040f020f03151f0302032505 61
    0x1000d981c1800129500c400104410380442010280d58210300341c0300d000240902031407603a4003c1607054904046002a00ca403c403181c640c4290046820856040914a841d182e8010070a0040320118110300384040641c0300602c0100151041c021000040d140e00c080800110520b01c5005003100e03503480b080e86004508049140303a103801a14a080b0102c1c1c1c12850609460410380d400000b4200b140c0c19000443e90440d4080f8603005130a498202813410224a000d5009552610080d110003245140001441e9083c4140040d00702c120013094140010000c00880310145e420181e454482c00c0e86003403e500a00c05110380540c855621691900c201030461424001c417130007038204120303958032045041c03058407486034066101484c10551a00180c0030b54404028414042d000142c1410101c1c4d52208903409400c0c030302d00304200401081902140343c03201e4200240243c4c1d82140c40f50240120154140f01e5801a0060580120020380c01850000030a0149440909400801389003d40d020380a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 746211915 1250 746210665 746210677
    0x60c050a0212340b07021008042609030c060a0c08030c0f1611010503070f08090106090e10060b0f12090a02060f0a030506090403090510020c09012c10090c030b03010e03 74
    0x180f4030049900080c02d0a200055960007038001c0c00f03000007079a03a001c0480b40c0d1480180f0403070b062800d0030f00c025050b500b20045803424649c0c2c03003402e0b5991600701c400c140ca0001a01d10440c8100002c0045114940e81300c607410307852036400740c40c02e030f240e03102e00200c0c03041400f0b103821008140402140e8410141c801132079007800240107070baa81d11a52610001100d0900c011104003020900e440482c2c4000380c410b00c151503000c00803000000d80180c0342c841030780507280c11040d4070045501142d501d9040340081d200c0e01d0020185418101e00d0141c904003642c401d40105043c5e003071030024071000100e403009c0902102c9001d1341e00901041e6100882d10100d420717a0840000d640000f0706e03140000d0320f036082042c00720f4040c40d0940c665452062411003007180c0ca240100340b100443c0650400b090a50326000012400792624184503070b0b680c07011103109103045c40c01d40c1c1001e50f5092040c0901184030070401000c1e0680c2d088040104030b070644c0841c158007510050241e5900346d8a040c0182061100220241030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 746213165 1250 746211915 746212003
    0xa030222020c0a030504061202030f1b09130501081006030507261203040b1317031530030a090b0d060806242205060d0506010e040507060c050a0212 65
    0x23241070700a2035034801c90108079408440081c05402141480c10788440f030032030580303484400f545040d40000220325021020108404096202e4005104009080c01000000c5003102d000700300703842c590340b40c83d5540c50007849140c174580c030049042503107424003889421b500c05214040341d0080403035040c05103c580c0200c03001d8a0982c026404034906440483d5903c40940d00405015004520502c000400d540003a02464400c58984443e05041e101d62100541c3e1942c0c0300461150840c00c403a014034203014184071881203400410000b80307030940014505040c3ca924400305030b103401c40b40c0000002840283c219040a20074038003004110911580c114004980b400402e541d01020b40060000c9078040b68902845490b0b000360345245400c01c0d03440b240d48914003c004000058007603c03640d081117403e8001d42215061038003040140030041007118014003031407800700034030207040d21420346075980c1c00c20081c440d0101d507110051350982045201a1104000c21012140d503d221038060903c0030310800314 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 746214415 1250 746213165 746213177
    0x61b0d0f050c0a02101b060212070201090f1203020f0c0a0201030e0f0a0602031506160309060c0201050342040608030a0c0803040309120308090c0a030222020c0a03050406 75
    0xc2912810603544101c1e80c40d00140382c3d81010f5400c010724180e4601854040045014404002c0c01d1081e000d005030702d01070280180d4495901007a403904071001080001903a0600c1c580d20300250017a1100c00070140c001415407400780004800314081d1043c1c5590602048000c00c0c0c6402094020901d554098401d88003008400c1480d007001340c8803039920002d00825000944500045030740c41e001141d00030b40d0308844001858454000407101c4d044640c030082427103e803024070803c040d0042d80000240050342414000d00c44140c0c002090343c880108075414a8110185100d402102c100010305032185482d400708102800b02025584822007038181442107042441c00249002d010048500b0300201e42d41d040c03000000c58540504a07440078000f1810800c2c0c041000032208407040c42d00ca0500d00c00d90b60707446141018160545001c0208900c2c5d4464400700c01c040006035925246c201ca00d07091848a10150f60700f40072444000e000e00c80303101030140100302c042010140e00000030b00640304a61100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 746215665 1250 746214415 746214437
    0xf27090604050c0a0c0f020301151a04030b01030212010b03010627020c280507030b0406111912140f0a05010608010b070303090204291c0201020c040b061b0d 69
    0x8401d0702c03019216083d40c02802c11007a0a158800c240094410f402840e8203540d0030440d5001c01d00f10780b02420403280480071004280050444042c0a00c26004010655414907080d031b19070112145d410301c4001d2242c0034105040d01150030070340107646144001070003048280d40e14640741020400905541d10344910520020112040503c203680c00754001d1002402d42010f039050040c0203005810b001c5c624102e030b1040c89000500200110405540320b10300c60002c0742003074a4604141d6816403045100843d080c0485d03844003030100a020036900b01d030b14250103000746000152009022500b0541100c480708820480c2c0c0d0062444468000c4031400c00411840e0b9135050111001c00c028024404400400c110040220340301e80c0101c82030038002800014000c142c5a40c1514012100414412407032615403070003030a02d410180c0004482070b544450054403500d0380000c2d159104050303198403803540c030080e0407040d40390300d41918901f180c258183c140300240f07010030554815a00c03141d41c00143c0bd210007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 746216915 1250 746215665 746215669
    0x140f0c0f01051305120a1b03030215061305041b0306020c0f211812011e0b01051c060e04050303041202070b030c0c2d0c12030f0f270906 60
    0x403121001c24102260b8443d40c00d182c104039030742001080c038010034030440941c80082400e043c80354100d4070305154180d54091443c54040d0405207040c0c0c280c4d0030468100100080c680703a00c103850303070303e003550440002d83d50365280b8003080403a9183c49481d06c41c20010002100304101540104a0746041c2400c03100c4c50b10b1032082d0b05035034021481c4410300c54202c0c0390b11181c1100c40b0101030483c401c181d00c0c1c040403030012180801e403844071040700110345a4607645010a03044080f000d00b03668102c42c1e0408d12402d0720b40000a041d80c4a4000c54815010481140c5030880038036a00c4203000e003080d82d0030440c0c43e09041c1041560703600242c03000e81c1d126081940d08c20030b01e400010f211045403110508a8110350380c281c4501015082400e03052020b0040e4200d0b500d490a400c0071078181c0032062190108032560078a017581c0390828580300e950140302031200e03048000b000001601c2c200c181c1e50200c9540c401d000b0742103099034010b1071250991203209140c9022080f0540c407540311003140540710a0385a03079407081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 746218165 1250 746216915 746216917
    0x4051503070207030201051810200c0307170f060c19050309060a05091c020d0f0207050d08030717040609060506010e010f0e12120c0f030c0c0d140f0c0f0105 69
    0x25045002d648545020401940a0f17400380140000e924030782540c100307441012403051038480c40f0960010301d081282c21003207132500c8802c032441015140107014a00c1c108020079906c6038140103405920164600344014004200414240b00010304192241820304050610701c6030041e81c0c205c192845a40c074480c00b8540b047c0c2c2a04c4c400d000f8500281196124890324400504025140c10314a010f081d10300500c00031500d1000e01003082030b0f4001c20158442d080300038081031100302044115003220070108501e6840024401080e600034140c9a50390315102c1066442e480843c81604600c0c0c038400c2000148482c40e4407450318180140010701c03460761a000110303603141c8030a403002d011802c1400740106041c4901c500248841c3e002d4a00303040d040214980da850515030507100070b5001400107000321107180030b1108243c12510200114100002c0c056a161106502c011040c0034406100b00d200a002442e40c5981d0940d008206903482c04440300c04141d203074442859203034003d08030514041100d5218030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 746219415 1250 746218165 746218171
    0x1103060f09090c19150e0301061d01260d02030901030f090f120306080a05011b020609060a0b0604030c0603051f0b091203071211060606040b182404051503 68
    0xa003c2d00703501074880208901d14003003c40d0190b100040890105a0f2800461079061480454544003541c006040805080d54400c2d001405030204844224203888500308040341547c0002c41c150901e212004406102d11141c06d260104500c900d2003145c801a4000c0010800c0d03130802ea2781805101c00d00101700f0b00741c4500d00b0004220103070910f00700c00482c0e0820000c15411384580780118200c3d070b480000c3e6140210900c0700383c031207941d6145200c5080040c0b002c4804111500d001616092404072407540d1122002030038000c4107610b594201d03c00741d45200c1100c010b03550101c0010f0105480d064010b0080804171510f110300c2e40000351504a11b01000201003c40d900c06820903e402e014606001205c80e207682c40a84070310040c010100001d05090752414481e69076a66100c0d0048880d14062511101803c414050001003100f408490110000c9450985902514001e900480804140229000943e00350408a4584841e021015440040c000c991040b80c08a421168109040c40306200503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 746220665 1250 746219415 746219431
    0x130c060801050109060f0908060106091d1b070611030103200d11010c0303090f0506160507030912050a14030a0315050303030604050402241e070c05221103060f09 71
    0x741342c0801c0283c2c40f910b4042518007031440e1402003641d07180c00c81e6107401e03c01e0b0040000b1400981007804802c402c02124088400700c5500161239017081100380109100403401c0d98110310002844205204103038202c100f5180d17219504c190f5075a5282011244103d404240d50146c105a043d00d100c01c0c0303000f0252a89440d080079030401c0131105500150350b05203a01e10100c0a050b00c070754501c00442c4001b0581c84101d40a01c1c040c2c100e600d014501c2d107260004a405501c02d00ac020700000d004250f2054221081e02c001c1410105480280c0c10198a031500149005100b03481144484282c02d6021014104881007600d050041c0700c0c002402088418007400b90f1358142c0d005000084191400e030308074039003003030001c0c15051500c80d0300f40c2070081801c40d000c0c018005000000354810b44030605c8038070000c3c420003400100c0c14070865980303d540c13000e458402c0904c00c90b04040d6254140c0e0400d1500014001800307402c01508008024810703041e0811a00f06100342c0c0b01022001c0381d41048480030740308880b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 746221915 1250 746220665 746220677
    0x140d020607051803032205010203030c03040609020d2109060f080a2d0603020f0418060504020418032f03030a050403090308041d010b1804050903070209130c0608010501 74
    0x24488085405403c005038415814403c0b1000700440d840500050a035500c0c400b11608880380c001000881038001940014119802002007094400885040e250419840a404240d82100b0300004691031141800600403000503007030448081d0203d0781154a1a50300c5d140c0d0303140540c1ea40c13016281205807d0005000c103200c60f000511043c0c0b01d900a01110050110303e16100303030709070f1401d010b0640e8041c503074545566800d810f000b50701d07001d5114141076100f20b40620640e9001c2054010480905000a06240c0c0301c43c0480d0441d07071140c200096040c070350040040010020709009004480400a1108131580b184601c13240465114030640060b0000d001149103071141c0103000e004120040c4140d003002031908001c4001903425005200400750000045102da1950f60480c1412070180d0080e01c1c0800d040041c4018401c1091541301030b414102c0d0000780c1035855512890852007000802984203c021041014034003c515650300c0c000e0203600103001c0d1907100c00c0280ca540c0c4081c010240420300c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 746223021 1106 746221915 746221921
    0x1b08010e0a110406030515150d18020901060c11090a05070f02070e0c070c05040905031c0903021203040f0c06031b05041a1b0d0c140d0206 61
    0x148282042001d60b109001078640c0302e01d00c60002856260b0001848004111049500282c0c02410344850700e00c0381e41e4000b90aa11a002000445140c0f100b8a12000c01d01c0c7e00d0700e007109501400a4903a6420400c054420740c0c0d11f01390440d00007003642040070080c0c540680c014040c1014480105080c1044203024009450014800d42194030100040103081124503003240c1204440d0401595080c4a04040c449110650041900035003010101e40c1089030010040501c0a40012400c008010301c00380340080d00c1048502400580c0040d2513030b10301d884048000c0da00144644566400d520047c0e0b1810350422156010b0400301c0c0d6a03003d21100c603d0852000f00c1800d82600c3c1807481d00d030418145140010b0b000e20b0b6400d0740ba40114103c1e0b90301c02c200741142d0600c512a01190030347c00420a00802c00c0039401c804460305084c4c65034100e902400000c011302c1c6016941c0140c100341d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 746043165 746223021 := by
  have h0 := BRFrame.cov_init 746043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 746043165 ≤ n) (h2 : n < 746223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
