-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4197
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:51:06.59396+00:00
-- url     : https://prove2.me/submissions/978e6cd7-9ed9-418c-b6cd-c0cfc585cddf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 754676258 ≤ n < 754856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 754677508 1250 754676258 754676261
    0xb042c011217040605090f0d030203090d030e0d03090303080f240402040f0801050402150901020705040e1606020d320a020f0a0507090501050f13020a05090310050105100f0f08060103 80
    0x1180b05100741c1c1c0d200d82e581c0e8800b0f052a0b00c128801c61183c140406103410910305990601d4295070154010750601c1a001c0c1408404888100d05600303110417540b400ca00c1d661105000321340c49100341d544201151541c90058001c400140c503c011100c00c2d50f08208454030a03a0005040726545000002c2025103880400e0081c400c84d04150031807885034401040c40041508a1809180300b645c840700000042c1c0c0380a0010702480b1905401608451420810b603e1f01d900480c503c5c0311f0139820703201d100f4945040c449103c140e0760301500241e080f22608a4141da0880020103038039008000c59191404211800796180c00e81c80482c0843c80004984012524820400410030b241d83d24102c47c0d408500f802c0c2141c1e40c040740e201e47d8007283e0070300300003050034100410304140b1018007034000d00d0481c22912400001c4d4101030b83c0c64040000a00c400c08a5903010451401d0103250403500003001c2d41000280626400400500c400340580803018070b141d00d0b8081d044281c1045140380005031511403200403030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 754678758 1250 754677508 754677533
    0xd0c030e1b04330b0408061f050301050717010b0405150a05070c14030616050702041109060a1d01020c011e03140c0d0b030601080a031b020603010b042c0112 69
    0x280e80248084008108055079428000b103002d10030303d0321000399911007034032001d4455802820b10640045012500c405200c0155000d0302c90400101d8080946400c0031900319402160a000007801301d0806504c83e43ca40c002050140111003125840c01d81480040707540071105421480c42d44c88001b941c0408640b2600c140c2e285a42c2c4092803061107603075100305080c031b4110810032074424040c01c00400c492000e050180007044409450f03030350070f003803aa400b000010100c00e4a00300900c001088034412a540e40c900400d10003480d40ca4015000c44403108049050880f42c000c0d0341503500c141204007441e0f13005000f5940c1101c0440442c048141c40d12412409000d52009210701d4824020030301444c040301d40c001c0c001e003168007081007100c0078840c010141d80ea4402e120f0904036400000c4500d020910804402c001010f0100003954042c40302e84c0452130030b600c02d9025032091203004c6414060310f11100d13461000c840c00c000c8000240c102014820000300411f103e0410700d012042030b820300300300c090500403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 754680008 1250 754678758 754678781
    0x9010b19081f060803040312020115060c120309060f1a04090317040c0504020a0f0e030703020a060513170f0709020304080f1b0a050c2b030e060c0f01020d0c030e1b04 73
    0x51b52941d64920341a01c142e000040014090b50130a51844a5400b480350700500b142c0455446018420b060740b10f6516490070600350504041d1254103c1e40841d072640600010140001400680c107000300700200030a41d009001076105500307040c03070350020907440341d4a110f0002685a50069a40304d520f0942803601841c0d1020f50094004134441103c00d0b00f200304609023540702e488180d1511040c0040689030340c03550000070352060b8005420701410780300344081c01c41c0b9903000c1d05006500e40c0f80e031150410210000c0118650f80c0c00391504250035031060009800500c05182c095056040a949455040c012090034090324036001c030321040c0c441e00000602441100c8075080d10403490041c20215180c0013000c2100740149a0554070300e0b4000700c4400000541c00301c4000c00807074000c065404a0300e40c044e11103201d0b4003040c18444220b030702c1e80500c40f00861013008000107030f0b14400940100151020b500b0b054013490b24001c02800f00240101d0800c0103a00c0c80c42c800c1d66161205400100108880c1e14030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 754681258 1250 754680008 754680013
    0x91e22030f030b060a0906110102162603090a120519120b030a050a060f09020a08010c022107020f2427030706032309010b19081f0608 59
    0x41005240e002560740540c030796241d40c10f000d01c800a07010b0020074400d8400e0f2000080c002d0004000184c8205817098002610b100098600b440703030140c124610203d144159070a0940301e003a25621b07030706401021070f0032010100480c01d5143c458900e548840545034054401d0100c3d003d254142c1e885602180e18020b4520103500004065036801850343e10744100c1a40d00354600f01e407101107803800003844041203500600a24680880d40e0329000940220842a0b040780c0e102c100c0c000069580319583e1001c0c101c4000002080c0501e07100007443c1c100003039494461401b0302c0c204a99004014811a40d940b90140c071403d00c09805a00410106400110344220855107810380101c8801e24200504009460807000a51031150b034214040404190341125031541c03060340c080207c0d80c041c0d0410a07262001030501da0b01c01c0c00c0e80b1640c44088204441009050b5034031031050110f40b4141702c00c495003658502000300102c2c24081103945d44e2483c00160301708500b500004420716400ba40002d4003904840c800d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 754682508 1250 754681258 754681321
    0x30302120d1d06040510060513090602091005070b06010e0904200a060e09220f1a160f1e052b02030f071803080705101b020705091e 58
    0x640b00c0d220203007038030103c41a01414545003201030f030500a03501a21001030080d44009007007002400108000c032021217000e138080c007112880360344a52a2013650f8880340c40f0141e4a10301c030f117071075095000000e00c0581840070741e14490b861500c849020300d40c0140e105060781d038840d290300c661000c01d802034551540d105001401c046229988440805201030080e600d035030381c6840b0302c0340050f000c0d114484030540107108141041e01082180151980780f0f80903109801080d01004900743c46007108450b075241c01a41142c2041680c0e0740080082811021441c1480e0740160030b020b03441c1c8100d42c00c104501081004646018007450407075414501c025801c0c0005600192244828081c1d0812902019014103903c00102d001d40101c24021320449402c2003000080d0442e070390741d1081e8001c10419101486504201241c101003441240011220300070b0010b803241940380000c1c030302a100d41040380160317403407800d01034640e000d9195810409150f45d28041030340d0794581c040d03141104078074518409003881038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 754683758 1250 754682508 754682561
    0x90f030203040513060806070e060d02040905010f0905040b2403030c1617120a0e06030a05041202010c081b0721020d03110d050408040815010e10030302120d 69
    0x100070070490700d06444c104541000c038807144040b51402c4c030039803a05400150000f2041403084103402c0190f88010302030303420040e03141c13004001c9800540010401581d01c00040c0000540303198504020805c10409000b1440c05944000705c402c1e000e0403004051540345180f10025044107420301c01024040c0889484c1c89801d401280d0700e008044128194601081c001308950085030f0015400c4175080004101e0006003503d070620550201200c10104005400000c1a0340d5400004501424403020085164105802c0010981c0b41c007600c01010340e0715218082910a81181e0880d40c0084010301400c100c41010314146580d1141020040100f604e0b403144c000048404a2003401d1220030f0340c01c442c1c090380383c03d9040d0100c40c0800e06032071130701341e007445840080240b54020340d5000e0f10030821340741003030f80d20a031051500f2116021803161b6031010006005080030910b08607031046c0440511010a1700d103132406500d41c1800d18110030b103071000040c40d11042c180c83d0404441d68a002c5000c10074000f851 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 754685008 1250 754683758 754683763
    0x1606020d0c05241f060207270203090c0906040c0c02040506061603080a11030f040803060d060606030605041a0a0501050333100f0509040c031503030804020a0e04050a060902010201090f0302 83
    0x484d500310280d0400f602e034440000740ca0028000769031240c3c00401c0240e05158420107210f40301d0341c002000342c05000045200c1c1941e4005180a10450001040ca154a000c2080910000144564000e07880c1500f0710b82600e030f000a80345540d58058600042613200c520106402e8880e002081c00000320701d0280c5420150b100b80520702c6100d52460421440989842011061000352508440d10741d0100110b004600b0650007190004002050205458090740e609000c0d517546078021030200baa6500f0800c1142024060141901604403401124004041c005a8070b01c4041c0292410803002000094403041402c0c5240902005004109928001701d40c2d480d21040d086d8090500802c102c407800c0000500541d000c0180c00302c10380b074843c14104e8402c2408000e2007010306406c200360302c8244000820750200b40e0714020310302941d01c151403880c00c2c3c010b00503200b1065100d04041b000a60420001c02c0000c11a254260350128004c2680099030004030701421100d000600300503032000743e400405800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 754686258 1250 754685008 754685011
    0xf0a11030f030402190509040602180a0b040f0b03010302060d0c0c080d0603060f141f0b0d060806070513060e0a05120d02190f0212070b04171606020d0c0524 69
    0x326004031400141117058490308100d4030030150040d4101011a001170340b030780c02804240b40d0301000110ba6030001030005084501c00d80c0303c4148842c0005050141c91032040ca0000034207820941c0c5031855140d640455001d102d06072642050307507903c0049140f45c1d803050b81c1c602c090907000601d054441945000c524000e00c2c1511080740c0c4103141c040c084d04801e0050081e0071603401d45614070101e650703d440140064112890b15a848424044404604406036401900040340b044100080007070500e1002407030004050040810f001040c0800d059541d02d2041c41c1d0300392521864a035000501300008150b4111458100329803140e0210075640040f54006121100881b45a0031102540301500c5218503861020070050000c00d9628481800340c2416107d0b03c2d43c0040900440b50703599920894011a60410341114480d4408900380c441a50020858000500c0103000c200905a01d4503002956500c070396440c20782400481e912070024480d080c000c407024000c50701c86281e405443d201c1103a440e03c60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 754687508 1250 754686258 754686263
    0x2030f041401180b071103100218091003050a080c070b0406050915030c040608150405090607021c08060405041506180e0a080901110106030f14100b060f0a11030f0304 73
    0x3441e600c80c039203101945040d004032142e100f0f54618003181e1b9111b5600700d591200d015505441042501c14880002e44020300c400c0440d0408003101d84966802c0001521000c1d004190b44010144103002180e0040790b88410a980301d040241c0e070340240318411707081459aa100801301c0e1804140000e4642c0c109005014000048451000400544505207035a00065410602c440c10510062004600480c12070b81c020540c1c0d0111130034400c00900203015200c0858980d403040e0445402d0000250701013000000800e010110768018000c00880144107400042c084c5205a407203801050a00002090001e54129041805e007e0701c0d1322480e42400050302840b83c035074214548690310103510760108a00d070006901c200c22a281c42e1894004440c210b0402c103001503555a5070000000041242d48882045841040f0214402034100055800d225920010001040c145481d440c443d9071020100c51005054840c0c250715420002c03c1111080000d170014103082c8000a04407110541080c003440c422413 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 754688758 1250 754687508 754687517
    0x2090a050a0c0f020c01180b0d15061106150616051b06040506030f040309080a0c031a1003140a0501110301090c020d090b0702041806051f060903021002030f041401 72
    0xb8031161084624001000304030005070032442c0040c81da0341c8651460788800081078080d114198955200380c0d20b03640482c054a0f185a0390310300ca07650388841110700c3c9000702520308040e0380c42d44001c0101900c800e0000d1601a40c1c21074640003444aa441c1402e030350f28207500718012000d480c954070b4055500d0300d0078640380c50b103442031041c0000f861a254089400380c1c0d8006d0101410740c0c031591805000028050401ca043c00100c0c0c40102d202801004650f68990207181e80720004d03840c1d420200c642c0f43c40d082444900d40710780320401403004803c0204a0860354441103640000c40407081242c20044c81b000000c1141d424112400d2034441894061810307500440000c01404d800a002640d580c00760841d030402081c0c49400030050117180b1000780c01e9039400a8000b107136800885070481011142110104c9500c2c0c0c3c0c91050241c246444084400441c15040d0002d8090742400e0000c2c200440a200c002c0c030803006043c1d0414200c2c0300380180c50081960801d42d645840d19814080b0040030803810090000d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 754690008 1250 754688758 754688771
    0x50d0e0406080d170606070f0f110402070b060d080f161104060f090c02033906060f3708060901060e072006010f050307171e0a02090a050a 61
    0x4603808030b030041c096140f90300c0d200a0080800100c000c9018010000c2d50711020511404000ca480301840b9030b19103200b01d0046140300982d14110032108480343c002c0340610303c184600d00015046402094000e0320031035205d180a130b610300d4601e549100c6c0d80064000c003000807506101d0b45070303090351010031240310704001e074040c1e000102403004940c001e02c03400150008070303c1c082000126503880360080c07207030700c1c41501e140ca44081c1002929140980382c0380c410100c000d0014901c105d41d104601e03110f000343c60107003116041000000b034010003440c0411f032242c407000c140201001c04c0b02100c0503500188001000d410b080b1000c42c05d5285039144607441d210b001c0c80000031000070062080000f620142041c418240c0c90b541001c41c0c4550305a9001c1000c01300c40c442e04010408200704260081c01c2c20b0003480d580d40d05040505003010019442210030008415610b0f055a02c0410404410749201804405e185c42d1214032610300708a280340650015079050a000c07138004071b50401482000200001d200740c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 754691258 1250 754690008 754690019
    0xb040e0105040b060415050c0703140f01090b0610050c010501061e08010302010c0f0f0506010b1b03210405100903050a030b190b030a0b04020408070302010e22050a09050d0e0406 78
    0xe4811240003c0d500c2081000240405401510140041000c601e4040d043c91108000246803041540081d20301da0b04040c600100a801003025010451810b40203000a0341207070b44200f030a54010303003542d1080c4004503100e007042c0d201e0700942d00c208141c20004e0102d569a0301c005050b11000901e00b80b00c843c400a24000074902420182d4106c070707030603540c00510b50070503194085030211030340d4112401d01046484c0030102d101000081e0180041446103a0307203620703201c1088411500300d0810303e829001440295210300d00110b5022030043c10b00300d00719043da55850106e003000156103005680380c0c50aa9140c0506030300a02400815040c0e032010002082140d040000343c904821124280c60b80000040c4481017a01001c8e40c0c104c1001c000104081d03240c0340c0054141d03007080c0c12125059100400800c155a40710f1302e5900b14440a03a04840c1c0c0701c0840c504031018036105940380898540b42c4010541125490380142041a000420340d02001c0c1100d00c000c001e00c00810900d48203504000740440c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 754692508 1250 754691258 754691261
    0xc0515093a12170c07150b0301020304110a171009020a0509070305010519150f050c010c050304291f0f06120b011d092d04060507020109020a03200a0b040e010504 71
    0x83c2c075034401d1041c10481c5030382e502c5807240f8036181c1b410007454075164a1811510240040c50090b8480d20718841003c1c042001d0181c0d00c809980b05120414628070b135a42c0c00d54003c01c28500043c50a64007058404050001c0f030a5090b072030703000b5600212603204100078a589940510b041e904100c503103050740314010301d40c5020344856014071006420411004c2c009030340600c07010300c2401d0540c2889801e2050400d002802c403100d200c40800428800001c100800042d0004008000071201c980c0966002044000301e54210041c4000d40400746400720350310402d000501080100a00c0c800885201c1d10b1f05802400c09170500d400c541a9030900150103003543c011683e42040035030070360007440ca06444000300500e100700501046007065a588505c0c1e0b00b25161400c2c110b5541c0382a20115450a040c54060111034000f0458021640341004a80c016130350081a00212508100301d41100845000700c809803441c4c10a0580c4d21065040c000518041600064001c503244151410004d0780e80c0c0040c0030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 754693758 1250 754692508 754692511
    0xe0a0c030b0603070f09080f0304330807230406030b0f01020303070e0613170706020601080307020d03020102091207090b04150510020f0102070c0515093a1217 70
    0x2c0c2d1010080c0002581c03548210304400d10714010345441c50b40c0c2036413110954200100302e201a07840f50400501401540b0b0310170180c4070703a07400d00c03501a1201d0020b00b036000f4619000d0310450b02000003030400f04803054800c3c00d100565007070f004031001c55035140c3c20744070721154041c3c82404082400c18a9140091a00d160700d008402d4040c3c01840ca940e07030300300c402c88100404900082c0c1c0a6000d00114100c06044141000545080891943d462000001e52494040c10b0380c00301e0119800840180aa003001209039906640d0680700c200c0c0300d1160740f40c00c4c1d001e4068100742076000003c2c05d0284d80000800510f183c125220441c0401842c9590390603c801da4445a120b001d42840801d420810ba0030540100d210301e402d01d1055601c5100400d0459080e68401d00c1c00340c42c821f5000c03105000a21708100a4203814114080c13003803820b00554040341170790107605d80300001420b13041d05480c900040c0c0080d44903500015846259103c219252114561700c001d00c401000852418000b482800e0402085 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 754695008 1250 754693758 754693781
    0xc0f0a120c0c1406040b03040606030b1006020c22090c060f111b040612030e100c02130e1903230306010c08031017010c020111090f040b15040e0a0c03 66
    0x100c1c0943d0810b160342c100c0e050003100c0e9581003182007100242c003c100030080c5009074481ca1001c03172464610f0802c2000044090842d103122001c14030100100d41c0c0003e11503c05001c2516000000503041003a058164080340c0908034107802c001041c010484d03400014000d80e01951035141c5c840d042da00040f1840d1041e005054515440b0000000813094110000420007130014000b2940303a803034101003583c50840603811404110010681c0d916031a00600101485140d8a801c0804034041e4000400151405d000700701c100d0f9884500700210030042c0400109548440c100c5008a00a40340c0102907040340d8204c403180c940440c00020311042c84d001142c1c012003050303507030045030a107680700e54a040d40f025004503516101c8140c0001d00114003500d114000c01c080c400000e07030018550010f405d480c0c9599454005040400040106550755610307210152005d860000c0c1aa200c0c4022a0030008030a024203000480800d00180c0c00104002041c41010100303c18444021901000c0c4c05944121404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 754696258 1250 754695008 754695023
    0xc0c0807032006060a033f02100908160507030c06120b0307030201022e09060f0506180c070303020c10060f0b070f08220f080c0a0f0501030903050c0f0a120c 69
    0x20400704156071f5803003648140100b0031900c0b120440d0f82c01c6648106d07a009100c000443c0c00164080260180007400340da00b80d40c1c00500541e000c0390394510292081d461a901e10303910458400c414444108007103409564000400c450007615050040c2c908883e0000ca01d60a0f4209505040c07107040c08201d41d01101ea06800030298032440019003008100c004001d180704210302039840304151602d000702466180151000240384c440c86200805540b8010402070141143c62880242030645146082d4480803903490715884001c18941140a0310030451802031900c0b40c9000341d01c83c0301e119404a002c95001c02d1001c030605540744800b00082c010420050580c00c1c400e04000003152410000f0095103140d407000e05848281940030104684240d0004001b4001d030341d070f0a00c441c00c810041203044440403208400418506a1004400303200fa0158904264644200c0d5040501600030303510000d54001c181c41c0300c110344c103a100d9607800000700280c4403015101c2903444560b004101e038006664000c0032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 754697508 1250 754696258 754696279
    0x1020f030105040c120c0507020414060306060123030103210c03020a111216090b030102040503070b0a211e140a051909150c02120d0c0c080703200606 66
    0x2000020102500c010b4140504040304845c040f40d50301c0b039070f9450b42e4180c5455489016600500044414081715145a020381030140080c1c1e64001800c035510000900c2c1c903100070154080d45800900da6280145400603005c40084108003100c4807102c60180031002664500302c17030420484521204200150241e04061856804100110103481d1080c0c0060080c41809001d0003105240c40e010441e0040c3c44000f410051144001501464081c0c5004400960902e400c02c00000d07101e44291180507200000011482c10082c02003c0314030340780d10f070342c0c208001c0e40104550030b201605141074680d8a402d540026140045402d01c201c2e03484500060b012006681e030080304200034400980182941c50841c2c030354003494600d07070095070b4101d031261107501c03210707640c0095034800c0e940410800e0055402492114000104000039548103462480d004a51030107034000660b00001f04820142c00c1010004000d401d040e01320034490066940b001c1d0900400b0301d03141e103041e102e090a072481544803038070b8607 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 754698758 1250 754697508 754697519
    0x30b0103060b06120408270a0626011d010503030a0504090203060a0b0a02030909010f03082218020702030c09090709090302030d0e071503050705030c070f0b0405031b01020f0301 78
    0x388000c0c180311010f00110b182c00600c3c9444003020000f240c0032070303444200189180018503641180c140300c00f0440c1000c031292003034800041c0b0101660041900300f080ca40007528504441e03115443c02035464210700109540c588240446500c03090442401c891071800c0005400e0070f00000300e9a000c1c86a0361114200350808041c000130b54800b070039081e4070002c8041c001c01c104160500400748034200d6001190f8441300e0341f050180c44441648034803401078a000e410000300d0321403011101e008800ba40c1004071000441c0702c1d4bc803a100281c0002036440780750943d007840c00845170b0042502c40c1c021800c417010501c21b913040160360241294203a405412070302041109205da5044034120b507100b40180d0781072084d01500b0404481e014084d000803684681002c10a40b00e51072200188035a50349070038060707440e02c0c0b803026215100c040c296985a200008020b401d01000d0880c58081540c4690704e14043c0c1481e0810350f540741c100301440408980380c165010042c039814800c035800940101d03002401c41e032922 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 754700008 1250 754698758 754698761
    0x4120206070812010f0f1706040f02010c050a060c090e060d081305090f070e2b0201110a03020c0301110705060a1109060406020a20010c020f040f06180c050301030b010306 75
    0x9807401c0310448401c0c002000c40031101d1042e64040c18040910710809440c1c41d185106c6030000d68042c00c0d0240071580058910f60700812a0b661242d04582c805151040a00c0103c81e4500c00d21405012405250200c1d010040c070798111014243d59503a9001449488034072880101d0070640d0740715441616800340c600090003020140c1694051490222075580e6100d000c6006490101d82110400302c070b0104110b4240d4101003c01e0100005488540300e010700032007007040034002e042c10717901a120412a80821a80320b1212000c04241c3d503c2540c514074620700c0c020350f59888000d5030754400d500713001d000c103004012101500c03000c1d60080000c1100b61110320442c002407500c007070312104007801080b41c503016850f45401080144903540c010211004c1c1401c22045054140fa1010a0480015201310302aa400000c845500e43c0494448211224000005000b003020b4082030003541d00300100020382022803e903024020710000c2e0300b0300801d1070364041125288800d000040c0460000e100520100c2c050f0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 754701258 1250 754700008 754700017
    0x3060f0406150602100501090908030f1b0f0c0d02060c0d050c0712020f01050a020702150903010e010f0903080c13180e160311031c1101060915030201080c04120206 72
    0x2840000414140c8102c00d1404005250440d2001d039003c0c2c860011030340407031720665005001801c8100041b0440e6076071088584000307407840c2e402246907030200d84884440e044401070741c01200000ca0755260314243c01400b541101c0c0c0c8840c00c03800b84100450066001244d51803158001300b14a0385010300e2100108010310000d48041001e0005104100000e40319009242441c003241e0028403840407210394003401c2d600010445104107005100d8640141c0791400c1940c1c00d09074244010740c07946500700110303004110024039084507600700788000b01d072041154402000e86000e0f82e2502c88681e90000f28032560701c54034001c45546541e2800070410840305502e03d03900d028a0341404500d07010045025840c2050900c022410503000d000104104030308616003c400130002d9001d80640b18000751490000217502d00c0d800b00340301c604604c8102c142d80a40c030040140c0381e03101d81080304810b400703c030144641d002e00049011490040c04180c42c0700348c90303054800b240c883c1c9414141d1b6038100d500388410740d080b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 754702508 1250 754701258 754701263
    0xc041103061320030906090102070c0605070515010b09130908030a23010f05010f0309150f0212040b1609030512070c0e1801060911031f0503030a020c04050703060503060f04 76
    0x68a00c109610441c0c00e0314a449110b010f02c062a03101d0505c40c541e54100500613243c0c40d013580c41000840002240301c841c01088449a040198a507a02801c1c41030030031049841c1640454469030011401d44014005450f01203000e860f441404103012000c0e0086407401c64010f0403062040c00055004c1035240c00000ca13041039810030180440d80c000b880c00350329001b038100d424001d20030f51050020f540c2c4201140c9042c9500d00e010b0040302041c3e21120300c2c0344039080003101c0e00c907102d545414028445404480000f40ca1421034103031813826050030017070410103842c444240c8850002c160601445244a041520741100280540c020400442100d80d171045808070b03003040707540d000000c0348003140c40031902c10035880131249413075040885401c2c2100c41a810003417500d45000130420340d2a5040c8282d903440b05103904104000715101000c04482511980080ea16100c002209408203138049a1600010780965080c01b040d2074005040e81030310000d020700c41e010b6011500286420050f024100e030020f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 754703758 1250 754702508 754702511
    0x40f0204020f0a080109050f01050d03030c09050616060c0521130b04030e010210110f13050a061812020d020603041b1d1509010302060f0f040e090c0411030613 70
    0x5420a580a00b81c011400c2000401c800300d00412071190b941c00384540c095018548003001d981000c0002f8201c00006e80e0140405a403060384c0258680159490005820001c2402d51684040b81602103c11000c25003282d18030b0500080401980c00f0340c1c01d8405102990150310718016500c48580c50a160090182854a16103030117040407031382040501340513a0082d510452010078060001e481c14102c03103101241d5a1400341d00140741150b80042e030340c081603107155035540c0711607040203448000d0441d04803a900000030800002ca641d0002d8250018900c1d0411580c0500c0e600e078210a0400c400c100040c2d080b00e101c0450b100146445001164070502c0380c6059140783c68200580f00c68610103810041e02c501556151186030040d128155500110141d0f0510043e4000808902d00e864103110003409483c0226141c0710308180c42055543c1400c009140390344456440d000c440442c0000e5624111ba800740c078540203035505180c01003010140703038400003c1c07a40d01c400042c4005404e101d0010039245 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 754705008 1250 754703758 754703767
    0x50c12010b130b18040302071403100c02011b05090f0f04020c01060602010614122104081b0135090c04020f03040309060c050634111014040f020402 65
    0x2541c82c0802c2e400c9440300481c1c002510601c5205200d00c1d220301c03440c8528855503560410000a40c0083c1c0b02050355030a01c03042408070020800b192601c0e41013120310669a05102441c0b481982c1540080362102490700c14038007002071480c0580d402c1c80360409440d004150901c901c111818010f203560640e80028200600c0c100140c0415400c451035500a03e0051351a445c080004d90301da0503031401c1c00f850132128101c82c60451400c15503a6100e50103840d101c45c41d000b61070b03840381c0070302130644000b09a01000d6403800b442501c2e02d900c2e4078486032401340c04590500c4051141c07005a0700d0f00e03080e18455541d50100019003102c01c281c0c01000911154180c804c40c84800f24070344441c000740c21110034085409850742003034507001c0c1c855007058000e2020410351140000124600045440e00050801e1220800242e0500448045421010041720803030108000701d034402c1d030185180c202420003009541341c4401310b5078050700761000c400c00058001c0360000410085400c554040c00312a00c000d20040c0760 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 754706258 1250 754705008 754705031
    0x91103070e13121209060b011206120f02030309030a060b0108010b030c16021f090914060612041b0605091002070b091306090c05040311030111030a0f09080c010e010f0504050c1201 79
    0x84d075545440484045807900c0c7d2545607560080409102441c91070410b005090034000c030201c01109816000c1c2c08109031480e40f0302507486c20310032680184006400d60b02d0380030081c1460740103030600c2c0b208680005d09142c0000b0f02120540b00780d038002d0380a03102c681c0c40c003456542e280d590a00b00750416a4020030105029a1000d214403400410014903111844c0040c5050648400c5503004c64002c1100300040040103450703641c84003121040c403c90440e5241903100d60909001c50144101603c00074502e5075400301d03a154011001c0e1001c41710485010040116110003282c60740a41c0c8500703031004070b05100c444140d00d0304a00740d0840407031210380000c00d56602e41107001641c3c0c146078060082440003605005100103910b0500356041d00341c009100c0c0c44101500c2c0305003071100034002e042e525504c810303403e42200a80c116454168000100544919002d40e07203030b00900a41020703044c1d96186c660090b03140c610b18080c907482540c008015050b0300c4402c01c2071050700c0c040c42e950100315542c3c81ea040d406 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 754707508 1250 754706258 754706261
    0x201090e011518080a1b03051e101418100507030e0f010e0304180b0306010602010b101e03110f0d1a0d02131d01091103070e131212 58
    0xb4044100c424140e8407441c0000390000c6038500503c41880c00c071660a00403104c0c0010360380c41d4640d1001072807030410b6155402e8040d004040c0c02c010040d01138910000d180c2a081a440c01c249121541990310120300d1410080460f10b43c09202c0040c00340c0740340060781d0754204001142c0320b490740300c082c1c40107219821100802c8510440303501300072030361f20034074a058580100b200d0002d1006400081100c040c1d294a0305a99010f41d00c20000300e82203041400030206a55080040d00110140880b4290350f125400039028026050b02e450041044d0b02d00722003803c0c4507410303000380346501e00c4120310403080003201240541112034518925607000c124a1041410140c0100f01c440201580020701c8414a010401000d10502c0d040e88070382140c1c6c540c180507954050348094201c50039023001030100a01070034034008481900a4104035464200d0031006c0c0302e00c01d6128040003004405907000c10740c84505048403c0004c3e240c811071107074a0320000000900c20b00310300403c0562818200e91401400803040d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 754708758 1250 754707508 754707511
    0x9051f080601080c060307080105040906090f05010f201804090507080604020307090b0319020a050607060504020f0a0b030f040609080304050d0e010206010b1c0f02131715040f0201090e 81
    0x340c0d110a0040041c0002400101c003401c400311005841c6042541d0010000c01040c02140d03ca40da03500c48680c01c1045d1a0b04c0308a049500c200c0c2055a0229410054028071403865046505030a21005510141030107131045c55407081c0700c48440c28543c0307060300214a47c1c0680030003900150b540301c0d010041001040040014681d280c000c2c505840d01c0e206060801e0b40740c1d0300c001c07411814601d600790255004560010840d4040080001039001400024003c2480c0d07480745070401d00016542062102d16001544918004daa5404543e40303858103104095a45105600c4031080600120b40d0940d032070710180750094019500418201e980d41c440114075030080e24115403c0c2e02400203091120b8001104088940c824005001c0703a600d80b100015051040c0484180e0500b04121140140340c0e80e07610045620740081b00441d162102c1101c4035075800014001c4040300c990702c0e0011001c0e0300b400150500c910104803400341d01602c666981c2c60030700c5449241281480359102c1c010803039026800580c1d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 754710008 1250 754708758 754708769
    0x3060f011e180b13140603040f0b06010201142403060105060a05030c04030828081b0a090e130b130f0f05031204050106052103220801090605010e0601030e0709051f 72
    0x1e4900905e017146401045c2010030005009410510822021400800c042d400090308603400c8082c81c0c0d03418004038010700100f004980d0388142c4600b44400c000344051040702204529025003070000b501c01c01c042c3e0300e01c424401c05030b11080400640c80c0da18818070140d5007045c082c0340c855080c6074880d44c4002d031580011004481d03240300c940c20304c0103400716443c0d030a804040c01d00b4030201904004610009010203c4640746400310009200054688075225550082c40d03101e2180c015420109a500d426210311001a2699130313204001c50b0303031013142412071a003056107d10b1486141c281940d5441701d40c550440d05030ba40e0f00080c0402e00610001c2d0401b548180d110300000102581060104820240a25408200b80c001900d05c992150000021651800c1800c2948900c19904144038094442c1c1c54000d00c01550a003940c1c3e00c20030a0f50703000f8038140c918545058100740d4030140110308032042c0c51407101490380000d20030000f0450301d0380003d40014002c241e448100d001715184000c03009031503001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 754711258 1250 754710008 754710037
    0xa0203100509040c0b0901050912030a0201060b12070f090509100f09020c06150f0d060603050606060f0a030504020613080c030c0102010207030503070f0509100503060f011e180b 78
    0x1000010016004180040c081c102c034038501c10304203070b110710302007000074040d04207140300c0000d01c0c10440e030141003542da0420004150403400c03903c009980761603402072480700c0007540c00d040003c9000d401d10000c1e0303202000100c120000540d10345104590748100041c1c02001d1080d601e0001c00c141e205c0342d400e288100781008042c0089464008988050085039119045151041c4141e1458140c041002d90308105104042c0d1320380780c1e040c1c0c002204060003440f240d6101450440303c508004603a0041022a070141041c0c030300d04ea5404091005910421541c50600c034070402030104110702907400f0a4200c3d0000d40340c103060108051200200210300c0c2c01107551030b0701c0440d400380c083c6820031081d021120700784020350810030550340280a5000c05458403041c464503000b43d02c0d0740b503c40d8041e070b8100000200003101410141001038150382c0269040f901844028100003d01e5000380c030750380103901081e2209614514041011600c01400c5022490410b1000000281e2021b104d0301400b51803044064 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 754712508 1250 754711258 754711261
    0x7030510080c01090e060303160b0901060e070903030c03090b03070207081b0109050d0f1e05010b030a02010203040b0a091503021911150a1503031d01111e070e0a0203 73
    0x20100a08000c50340641401d070300c003240d4104581d034002d25450864003400c0c0300503030396160100083c1c00d600441108101e19031707007600554288120200c14500440414008005c44c0d5203520b5810725400b0200c13034040104503940c4c010000a48034158031a10305000b46080da9078139444900403139840d0300644402e070061348110300600c44100c0620200c2c50b01141ca070b40b00c1241000040002c0e00000041c03050368031501101b10214240840215a22405680314680d1546146503d0b18004e40c00b080f408191540d40c40d01d00c207481c8078100020840202a0144c0085041c6850503120242c242c1c0b060500e401000102680014030f0f0000400d130202c1d21070141c030050307220500351800e00032841f0040000401c10402c00002c070260140440c07011100c000003c40c001140e514031805c0e6000d8503003030b00b108103910b8030f61400101745a44444082c484907a4443c03140908a0b01c84c00454100d04080d0300c650300d6401c115003c0d600d819000e04000c0400c0d4664cc140e4110540d102c403c00c1d04201c0843c0d9000b9610340000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 754713758 1250 754712508 754712521
    0xa030f03060605031006050c030f1c0501050f0f0418081303050c09012103052b2019091505090405330f04090501061701020408060f0a0f05070305 64
    0x107030001621140c0703095030842c030b007120414030700c2c40c1640300d00c03c01d00c08002481808500c0500840e6a52040701009603030318609205c200c1401d118104442d4611131a0000105051510044084e26950001c04000c0d09111510820005015007106004222003c5408000264200e0003170b01886042102c500480d600e5814291306050340d03440428461032460005101c0c0c600781091041d41565100151951040a0720b415100340c480c08114107413080c1007502640425440203841024444c21110a010096582c0d0181c0501c200c460002c18528001f80074007e241c104030a0418103a803440d150005401b5651610700c0740c1280711841003800200b00103104512801c00e409041c4d000422440083d5800002c3c0e100351691604840c1c460101004400364100d8035522864042506203000f007003003050751402d103072003802044035208100d08a062100ca0a2101d1410320a450444141e503001c0c240075641e2619001c41d0841c020520380040e40d407501810b8045603644201c0e4400d140507100001e1508241 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 754715008 1250 754713758 754713761
    0x110702030f0609030d0903091802090a06020303012102030705120f19030504150c14011512021c03051c140622020702041e0605121b090411030a030f03 66
    0x2111407031036551220703060100d42a4000222003241407040b20020b2803d08a1404a076811f02591104c1c403c400b0317201d600e440d203610070381c000e1119020444400d05403075900d40040c2d840340024070848030a0207640144800015411003d8203038648010207450101d62904000758a64500280b019481c0e80007042703180f9502d204105040a1880700b54032800120352941d8018843d203d140502c0003401c12030ba000c040b801d40101c94204803542d101d001c0355558903645041d207000703048402820307c404c408014002214a18624010311683c3c000d0f08400c824140790901c41c4500e41015803c03000c100d401c0015103616031440908250b00301500e0b10124080410a001460394500601a1440f03150803140c2180102d22500300c2c6040d017201d5010150f1107600f54000039008042d0072105880078041e1040c8010301c844190700031016580c0c101d402e41c4100c0b86d6400301039519040c90290801240f5880401c003150714050503542d600602c29081c80002109a1000c00c0c2815449101140030031039081910301d456406 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 754716258 1250 754715008 754715023
    0x230a0204030215040e0601030c031b03150e060a0b03040206070c0b09040c050c0a0204050c07020a033207030f11030d0c1104090512130f060e0f040e0c0103110d11070203 74
    0x15500703d03d0802c2e08100c4130303075400440a04181d040c95038079a90245a140a40c02c1250500c40c0400d440140d081070384405809081e00b40c091080e4034400d240d010507002e01820080e800741d80c003d0007100c0e40c82d00780030340740003d171340b0103030041c1d0b44220103000e0800007450700c58800010301010101d03692680c101406220a88807118000b8041c0709007406903841c56040016088e0007150129404541515480da01c1410380c4552080a900840303402408014040c0d5079140700c1c6014900c4500c90038100c0c070354011000c0c0c0d508990740c00900342c01c03108041000c12070f40e00c0d128686600440d80d440104400900191401c06407a03504d1002c01c90344407500c0f0900140809a0b498460183d03401d03c207043c020b03030711152500031204034070103507100105a030015981c55044600191000070401510b00b030300c90001030000b07048408803c0c0318400c4401c0400c01400c040c02100c822500c04c40061048544800055000d060040601d506200040c061821400d0a500a02c0c18580c00c7d00881c41d40e448180c014141001c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 754717508 1250 754716258 754716289
    0xd030e070e0c030a0c23071e03020307080c1f0b0103060f1a070501090506011205060108010c0504091e02180f03070e01030b1f0e010e180c0103230a02040302 69
    0xe61400c00c07080b207803a0341c1201d500000420001425140030390007600c1401007a8148019000c4003560807109121004c01030281e9802000c0c038010b40000006407800c6048019001001a042070200400080008015040000c080402c3d00c0444041c00071072030840071105107100c801c90b116504c008855070588101c101070300d1100b001200075820186010808e448404800b010183d00158032400d103c000c0d8403d244c800d9014007030300d2855075102c80d028410f0100030425100c2e0b008901c000901150148224490305640b03031900303801d00c2d140059400040c03001d0074441105000144107a14030601d5403000b0142440070b0503044111505280600ca600c5c62010903442c0240d00100d4207010b5000411400341c1102d07803200004c44240c0e211814103000d800318000c4111031540100001c2080399039240e1a6058a6a0000280031a6581c11540d698890380b10324401803038000840a0229500c00c1c1c01201c401402c51458000d000c81f85148182d4104088076043d9415a020605108614211410003444603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 754718758 1250 754717508 754717529
    0x512030117070f170102070204060b0c1207200d02030109060f360c0e0f01060e0402070b0105131d011a010c0b07030f0e0d18051c0b090c030d030e07 65
    0x18100000f6422200c41401035a4410307030b01c1100070911503c00d40407103d0081d8003401c00e004241d55810b00304a660014600b004507402414400781c103000282c001d0f00c07403081d00b0040040004810003060954524407005150f0031081031a01c540c0503803402d0103003040d110702c101c40004505600411840803542d4444500000c500900c41440710080e804004070303100950481d10024000561501706025103540d0311004150507046e04000859503143c084604890441d26500100c0c00000308000881c400c1c00c0c001410504810018080743c24620300c000c003204020040010b411041403103143c0b44824109460100e80e450b00d500b020f40c4038003a51942c01c1400d0a00b0011101e241c4d541d1042d20108008002c0c0d001c160f03807100380805201d483d41100e51803806000684403001075401c1d0041c40c210401c400301c0180da0200400164506206009010710394082240750440807180d0f0398291099030290142c0035070b214000440f60143c1d403e0008025080311a00d00152024a070021181070a080d58040840c58 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 754720008 1250 754718758 754718773
    0x804030318020102030f2809051005070818060d0906050105120d090b090a0506070807020f091303030203060307091d10060e04081c1a0a090507051903090512030117 72
    0x507600003081e030341040d01903802e0f60b4447c18802d100d0b40c01003100703039420518106045828004036030803281c0c050941d0400d42e049101307030743c42d114141c03024403a2100041600000f0070411080c41c02e1200000204003005104901d400030300f0032040196800440107039101982d07140108200d00d03000c001035010180d800f014100180013840050400c207242e1052905c12031000518504d6071f0340f40c40c0128040c001c001c14460301c403426400e02d4421500012412800340842c0c803403a4100385408081584a0040a10040f00204082d81c2c21000ba4102409442d0180300311350010500303c80d1400364801c82d030501816502c3d102651031400745000080d2402d8072a4501c0e040040c04083c4a00c42e1240d407140d005664140d860026000b10060f041c2d54013071084089207800c0d00c60a11224024000c1d9038004219a80d400741612200f0300001c41c0d405880e0040454002c22000c5075028440f00f1144c040c4c01e803420000340241294072071a0818000e608105030300c031000001031202c0300100300309806a81c000380040c03524 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 754721258 1250 754720008 754720013
    0x110105060d0b0903040b0310060e0d0b011503090b04080304150239010606020609010c0206130605220f0b0f16080c04170109120f05030609040c0e070804030318 70
    0x5141c58440064002e802140c001401040c00700200ca00405400002c07543d2450b01107151310303a40007580a0440040d5486440c03001610b4050702038000e13142c0091400819910301402c2c2420302d014685c8030020700d52a0700d520404100c02a00b0a0300c21801280680d680c2c0c5041c4c504803c80f41c51000001c0303500ca1041c040c1201c8600f40405c071104084250030001d50240003048400d003440c03c1e4030034840e1190300b000d0000c2012640481d100e4014200c00000340240c00f19aa4141c0e140c8a04880c4403c0c1a00085501300c0840c10a410454210304400340b40c4500e29910201c411618030a1102a01c00b0302c03d22450804022a010000d0703480400c55038034550b94141130b1072200c885c076400c240c010104a54103022803035400c5850111002082c00795a00c0c60003c55160810f4040c00340c011081e41c0d802c44556400ca441c0c0d0080280310181191543e0703503451995070f407080148016000c0d00136501640040d00c040343c4050b9a03d001c0780140390a4491900754500752a0050986081407c0038481e0140758850900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 754722508 1250 754721258 754721269
    0x60c20030f0d0e100b0a050301060b092107032009043c0f0210050f0301060f050d02030f0a06051203090405040f0227010605190f21060611010506 64
    0x6140106081071079484140c9100400035001c48100041103010b030810000080d034455118400c070110648000000381e0f9510201400c8802c00d2152079071100c01001580c60301d107081d841c0c4000703150558852000000032071031051f2070415190001c692105549100780c15220384d00e0400300010304c040f152103402d4a01541c4451020100c100001c003070000792010000c070348480c64940e1409260b080c5034020b0407800c1e414074001d541308541b41a0301400d04824035080d410710030012510405d2510382e8262035030b444c0036401c480020040c0488020481c0c240441082440c09000541c0104810003466046040c520484c4040321100c1d03020074412100100340c0c10f0701100120650304000d00460740000c00e50b545050443c00e0601c2c403030000b0f50000202201c40303903c5005400c3d0000c90300d5084001c001680c0c0b50034041e507142c8969030100115240281101406501c2108401c4030840315140205541500c02d20f00c0040a00b42101d1020064030342e081804017560000c02c108003c0104402170299062400104e40e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 754723758 1250 754722508 754722517
    0xd020106050d03140a090510030b0f0604030b1305011e0603140106080706050f070c030503070507090603020306190209040507020705100e1f11060a020307090e09060115020703050307060c2003 84
    0x700e0701350110310070b03410900503c440f100811000c2d0a48180307404103100200200f401a0f941761003840c440c0d85d4021641007002c01d0b070f030036694044900e900329101c0e5020104080e60245007160190b481d607691481ca00c484400c010010105c07500086140c904500c1c005c0780484200e064610f41782c0c03500c0340070003000c0e000250050484545081165641c2c403040d200320401d1003000c001401c440100d440000c10020004000c00030107014a00381e039080340d01c0b440540306440440c403002e9030652050f40420051300b0003112111601d4007150005282640ca0b50100d000d48a0807602c0c24056041078100300f1403400c21070880d000c00001c51402151050389040010740004001c0b000001119020310390b983c40341d001e600b0b0005030780003640803a205850710904c0c80700698002c85105000030440d0714001000d0503100075090254144034042d025a031b0801e0202d03054180320180c20011441000400030104034288000c2003140c0c052400031452080e8104040c084941801c21108040350441360950a2400402a0b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 754725008 1250 754723758 754723787
    0x9031707050c061f09050405071d0c22170d0f181205120d0204080115080312090c0a0905090c0604080706120f110306011211070f0f060c020d020106050d03 68
    0x550104d80308500c071040f50f00d05508099102881c4c0000d01080c44000101c00080760320f400343c04120600c210031078409081094615600c0749005010a05c0c0c00c911002d186c00100c001058084020b0350340700c03c1064020360ba10034440c51a00b2050b038103602e06920403801c0f010761a0740c0c18442031604004a4103090b01c0f9a0f4440c0400914090700321808001c000c4c06100b2001070402006030b160801084168001d5010744100140f035803074140745c4805075480b2514101190100310195003000300711a10440c26800080010806018140441191380e032101c070400098021018009224500910850320f41a50a02054030540c01400708121107040018a04203495a03440c002e8501071a1a01d60000b40050710744d038880c1542010ba15203603154862024500c6070200b41c1e510013020318074804003402c80d9400280c190480c41e0400c850808611312420348170405118291140c2d0440075070301c0d0f03c400c40f140f0003040001608005021924564240a0200034200c00c40d190403850070b071a40e01403c0c43d04140c0c1e04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 754726258 1250 754725008 754725031
    0x6100503060a090608031305040c08010909021201020c01020904061e170c03010204060f171909031704050303060901060e0603010314010e0f16120f02121009031707050c06 75
    0xc41c140c5402c14641d0041100b00018030880c1d03194003c950700c03908800000c0c40c081609840015042c0307802c0c0103851149841da1500d041c240d0030b012004c005440c100e6400d0760003000b4550401c1c0128030920041038801301e00300c00107890f06815000c21098401c254440418080015014201516291418801c840403405409204090b0500050a2940311001c155241d44081000201142c0103400080d0056065480e80c2003c03030015580030030310034242c0e02c0390210428104200f500c0041e95029424650007030401404456801d807818248402c00c071000c6070660000b009204840c00e1200c2481e01404090034400c02c0d0000d6540820700d103000511020344410b508884501954a0a61004040703040c40c400303032900050300900c43c80d65480a21050200c0000340e040000c1c40c040c1203c0180c026984c420317046c030540551030302001584080c08591034224010101000740e0991548030780007803688242c40c1c000c1c0080c0b2082d0420f507a20790062412050107001c004074030040d00045941903000010804 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 754727508 1250 754726258 754726261
    0x1807032a0c0c090c0c02090109140a0209300f07120206070c120b15060a020a022b050d120c0f140d0603061a0103060308160206130e06090f06100503 65
    0x8000702226140d922001103d860000e58181556001049400290003510601d2280c0d90b10b044c004203c4510038903005d282c0703050101080c03241685030014104a41c0003040082d03c0c2c44018003101c8806071240440c03003000c14400140a10b884107200540d54105a903000d040030320710300003d100010000e850000c0c03041c1b100051003000c01036100d6114020b8000917421892401d203d00c0c00e00c5005800b40c48001301c2c04400590003500e840d00b0001c45010506903805404030440c29400c0c4400400c01e02215941003c405e003084032840840311074440c2050181d030003000140310224000c0c02c445101c99020007140c1c1010386104540d504445800b030010110310303184140c601d900d0441c0d00c0324060818048040c5d410540004280000c91304050840d6480002c80e8000e2002c83c4015030456580d0b20004040b00014424507000000501c1b000140720b0015011a00c0e00c0320700346044c1e101c41c1c0541c21002c00c40004405005d8181401346183e80d11880f0403e07205038070300300b0380d0010b40c007050f43c0d11100013000b40000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 754728758 1250 754727508 754727513
    0x30c060809010906050424060803070303020304080904020703050d0c020601051e0102011d010e0c100206010605031009020f071e020307091d0d02070501140a080c0702010e1807032a0c 80
    0x1401503010136040081008075080a141c1400d0900500741f0005c031040b400c001d00c0c581480c01d40303d42c2c0c0071504910011403a214681e034043e0301940005006589041d001d000c12005626640000d0441503c207039200c1e81d440e814405140102c43c106071a420443d0700040040c022501e400c0d0071080e41d080d404403990200b68003000100c1c00b6154014150203064a6203025040c2c585054200182c060000d000360781c4603980c50020b10200d40c110150090061b8024001009070700d02520095421464031036000c0f407061b031211300500690344000c001d110300790000240b4009025001a00d1b00c040a0001d1321004140700a030000303980c800301030140d40940c664a80707511042007041d9141240c2e048095068a820180142d40030751280894032070680402c100740d1034514a803100b0011920388101c0c80d2034030046515081405440781e0010b0604078144005054854620b03918403801411610511106a90324541114003d0035143c0070382c440d038204c182d4056600031f2074403c5080d0320024480ba282403140103102d070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 754730008 1250 754728758 754728761
    0x2030403150e0714040612080a08041b08031309231512060615070503040e0c0903251505030f0703230402040507052502131104031704030c06080901 65
    0x516001d254800ea0f4000549460b501c0003000c0300e000304440070065141e8480090b82c4140c00c004004105140c00c2054107607603405000034641190040b5032041d800c0c02005160000c2c08125000840164008603a032440c084607030381c1020142118150510885a0403030807a078103503009144001180d504540041d00000003070b0000300543d00c0080007500d1074211058050b84503c02076a15900810506c1000300c10301c001501200e03c00c1d9032200086280c94680a244a28204060001c0c1c00c035a004115100c010740e010403003c84400302007001003c4903c03076005042140540399011081003048100404040383d0041c06596105074001120640303650740341c03005c8005112100303210904040481480400181d9000080d1160740f090351700300802e845140041d01d141c05140b56030014000c99080b00c0e800c58041119a60005202038168401503080c40600d6003505e003186448013091744041810004d00c07a000e840c2500d550420003600d8a01419910389500c104024064201401040c00105152071000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 754731258 1250 754730008 754730021
    0x306050f10031214160f02030115060c0f020303090d03080601030b1005070b130210020607120524040b0405090a020112020703140a18140111010c0519020102090406060801180c0203040315 82
    0x8854110b80d05c100c041c03520042d180360f201ea00360301030f40c41c24205491007103800e5541c0041d0346030358440500c5081d0300e5554100030b61969904a805003c184800220341c0c483c2c1c113141607140e1081d00c450645191100c0010212101556158803640c1c2454840005e50b800c50205e82d0341c0ba8002110680542c3c17100c0e23000003c500b902000035040180e038507210740d0560b0b01240c060302424140d07884075900c0240d45581802d50310147c85145142d03281c10381ea980c04030f1402080040840001d00085000c149202c00901125001c03100c990580d044002d2583c1150b84c44203c0e10113040f48054110309160041d04e0003416020344050181d108000007034030200c03aa01801c10141210405c5030100e6180c0c0c1c40f000c0d1020b5401d62106036901142c046900f6152480042c01a41d60703000041d03440c2420107060101030090039006142c60015950b0800c8640a0754880340100307405400c01c0e440b02012540360082015582e81c0280345194810300d00284845019408002c2f02c04680d00104030503001c021050000006041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 754732508 1250 754731258 754731277
    0x18131103030a0305070f0e0f011b020904051f2c0a0f030f0f1e030b18010f0e0c07050c0603060103060902120118020c0c0603150a0306050f10031214 65
    0x4a080302c4216030542003148500d40d41e55803103081083e5558103444041110041d541c0c04107083c01703480501d52140c482040020f48580081000051300e801141140c102a01c0903035694004c042480701100705100100e0882c0d440085c00c200c04c400038040a03a400aa800d0b600c0b0005201a46202208008022806200740c009140c0328064895241c06440140f000031134801042014a40390481c501403040f0b03451504400d00010920842000210018400012407551003ca01c0f5030b0118000480d41e699030103004507110359443d003030801e005420503023001402c00349401d40410910001a8000c03071701140c20f12007518595129100d200059002d0b000680000c101c2e04d10101e0106a6400b494000a048032a140f81d005031038191080004180d00c5401e854404e1036201f5072000350380e41801c9004582c08140c0460803900c00c00c0050002d00004c006510a071a42074031042809a8503200600d280d03000342c0d1642c11213000600d566104103245101c05010300911002d552814500721007001282c2e6030703c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 754733758 1250 754732508 754732513
    0x9050a1d09010e0f01021e0f120702030c0a03090e220305030421030b0a0602070b180a03120503041b14060a020a020907110f010c0c1205160f02090618131103 69
    0x40085805600070340181640070070260f00d440920420018070b0b800c031203100d05c00381c1423603103005105002600c524201030000c00451004121100070101c042c0104024a0b1296440301d12040c9403007a40c0342020300150680180b020041c0980b0701241d0011a984022075150406903126501c40c04c01c402d000b490512001c0707002d00c16030510700031039a1507402040c008c5002c440d42200182c0380d80b800c83e5038200a0040f40e0000ca0200070100d145402d400d01007074030500c002c0150942c40d4981e42d0350307400607c0303103c42000031410200c180410880c02c02244025190112000d0780b500c2c0c0b40000c803021058104940034010b000014a0f030b0500c038420b000400030660003074051b044905150400a058410f12400d4040310f001d4107840f00c2250006005100620056a035160389800007600c6004550382c0c0510240c0910a04114840200080102e020182c501803d00240307440f009005202141728010300741c0e841003115222031f8003080700c03903580c041d000b4043c0c924103d44c20005180ca1408924000c9a1541c0361 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 754735008 1250 754733758 754733773
    0xc050d0606050405090c10031a030f011d01090b06010f11010e0c010e01090e1503070f0602240709030b0c040e01092c151e04060c09050a1d09010e 64
    0x120658001c1000c89100369400c100700da490b180d469450340f034104103079548002080b40c0300c01e80a100c1d4211040b05a40c049021086030612000a46061144d492800899444100003407134030006964500e00c0080d401c2c003d2006c4d640715a1981c002070300c001c0119050000159012264520032040812400d05e258000c01200300c00d0308100e65500c21703016800d40001d030141078241255100e103c0210841c1c0c00000d900005468141031911607210a44491b40c152280c1403002074880040007081004046a030041e1083c0c10a0302d20350b01705d80d20491102e080d4110310800344800030381d011610320b04172a00042007054584600035801458444c540c00040e082220400201d1140110b40c0301080801c0c0041c2d4401c0d00d140412a07a0180800010323707855590030200001442c0ca10602d003107640543c195180710030039442448821344101c0c05803820340d21181d4409009071419001045503018001c00c55005c04200d18140518085109245401507480d00c8500440c1820b0003d402444c0314900e00d1040d120704 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 754736258 1250 754735008 754735013
    0x30f090b040c060504050916020a02090708100605210c0c1f0501080703080418060512030a0305010605090312180d1b0b07030804060902031c0c03030605030c0a050d0c050d 75
    0xd00c6401d6406482190820000040450044040790220350000e04080055510b508103c50350b0f004010b0400c040d401110b4510b0b0042c0d644409483c401c00c2c40351a0f0503106d04240101e00189030440e005076060180c1080111500b88001710202c02c0d501143c0071040300c07542e4034180143c1a02902e5045452441039640561140f54441c0c040b03d00140c14400400c12a23a03200000d0b40d0b40d01183c44054401c0d0f90811090010340354140c2161540002c280c1c0c0418080c0da502c003c0395269038170000c8003103c7d4101080c001d08941d8035008080c010000c62030014280b1620391f000a48600515001070b030b501c00000f0b125038003042010703551504910001d140c440b00d10748a0510540754226400034000c4072900020200f0b403203400405441195825580d9000e8550f52952600d0080090350410399040c851224030201c1c1c412110b1030b50314a80c2d0155581c00000102d0304d0080e0035a401c1d0f41145200340c00c0010301d041c95445418100303085500c112030740070141d002800c00302c080b0b56054109507004055004c4d03400031b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 754737508 1250 754736258 754736273
    0xf090b04063b0f0a080f030a02070c060c120f0f0509150c16080a030c03110a05100b030f0a3815280e0a020408160312020a0f060507030f09 61
    0x100b60850b08107031040c43c030803c611242c807090000e400426400301401109002c0600d03001956110314120001480e1689a44410099a9450780403a00280c50b1140396410017042011031480d260030390810300c0d0801c80000c405008800c40c88411020004041801102940c521450b804c0583c201d4222640c0c40503031401d000d890340248090103000c9110080000741440d00003030303035065140e05a40c6000701d160180d64200c911641402d20301c01d840c400c00384080046a0b05011000b94a803040a00042d0240c20400785402d022080c0300010341500715a07599004a011642404800031007400c03d40904584100e00401e14060b40445c009604240010440c07501455210b40c4030720b000450314540c8224001121480c000d01c2814100350f450928182008841c1c0c0307103d040c0e0b0304410355000150501da2100025450101040074031649800940010018401d2240401d101c1300d2941c8060a50380200c0d446e011050000201d0040c9041d684900003412a8070951201c24040740c180420304c070b4405030f81007408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 754738758 1250 754737508 754737611
    0x8070c0302030f060403020c100509131508071d0408120702060a06091e0903020106150305040210030509030a11070317070506090606010e01120b040e100f090b0406 72
    0xa000380310f10ba484442d41c3c440010841c1c841c40d819802420315035901d20a02003002003548003141403107014400210981d84842e1207983c0d02c5981070000813504003202d0304d03105064255101800744e0300800c03814042840701d190313005865203e1131056074058586160951031441481c0d0690f035120740060130310203090380c040b070303258054243d081c8203115040c0c90f0050002184d0a03011002e021526800d0b40b00194000c40d0000450306009000010300c0035590303061f492060701c0007044000040e41e11010042180fa0001d00d11a55866a1a080181d440e000b03021542c0c0c0d2013041301d480188049500b40803d89101040244040c40d4000c40b5103418410704180341000d90003481c021500381c010940041d0001030300080305449a0b070169283c4404040d6140195170303076001407684240c459240c1c41d0703040b02a202c0d4055100c142d0130100043c204107481d44031400c12a140c14440d80308441c01d000340c0c007002c42d0300b5011381900075410600000740d40e030400483c04400c1c41900e44065443c4121021060035101e10302c10344 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 754740008 1250 754738758 754738763
    0x302031503160e06100e120a3c050a020618040f0c020105090f0d0f1413032a0b0a0507170c010b0306101a040810050103060b0118030204020a0c08070c03 67
    0x3d56a10307903800700a01d94103043c0c00e68000650b031b03c1c844461881d00d080c44144070340f03039101521600d0055444800300a800680f0541c82107102c02c83c641c42c030190800090704460f13070180c07441031801e405a48a40c2c444500300f00103031143c0c0c80803580c401c195005108e030b0102207100400800c90b52032030291540140c1804c241300707000b65103032500241c0000000308a600840c2601c40281015201300c40003940c50080103001c074400c02413000c2e00050721f00040001000d401c150078850b0815a8994a000c00c807444c4d100310f1440401c2e80384003040003103c0007441c00c00c00b41c510002e8181c2d2070340000d541c129050b005954010708200d41c000400c0240080301c4004102c440c500000a224080e025002c0c590340e010291542003e1000401e020884400800c1455802c49282201c1e14030b810350380c407180c03450105081007058800303945a0041082040520808070452020f08040058001111404026010500c0080d01407600003403e6400144208810028107078402c0792141c07144040e060400c081000c40c00f04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 754741258 1250 754740008 754740029
    0x70e0906040e0a0b0a060906120b1f121406071101050a020a0210021b0a120210290f0a0305060f06010203030f01121104020c0d09050103020910030203150316 69
    0x11590504140c0254124989000b0050041e1885a9190f2850140c010421904507a6500f80495034114501840c001425283c210a41030502810009030200014040e07840810101e2034100344402c5244040e001c8a411204403e0814480c0c1000001d450201242c007919028000400c0030356a00701107400184203094000300480d942e40740f015000c038842c0044d00c0025911200c82d1100c0750074140c0040c5108603205088008405035100e00c14540304001e8011615400c0400303e01819a070704001240e0701541c11402403011280b0030b141103030032140c108540003005030031100d064056111011404905000034181062441c0d49041c4507840e00400d0b90303000541030804020644643c40081903900803524085200701c00e0b4a03181142c100e0414140044500910248503901d0300c1ea120310141070036035004006494402c2c60440000c4c0703046110740001313050620511244841c0e03250700c81c0688003c001c9080c0103070b59446001039a59444e0101204039030610900c03000c44650103a240100c412600c1130b680 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 754742508 1250 754741258 754741261
    0x9060c020c01090e041103010c0503040311010603080a033308070e390a03091e03120b040902031006030b0109140601080c1603110f010207050312041a070e09 69
    0x80403038030340381007298050002c0d0401c00300b03020680c003100c411a00a0701c503422501001c07070000c02207401c0d240a4507803103010480100800080c160401c1d062243d00015500030840f0344e0444da143e28a80c0240817640e030030160340d039190010b90b03280401d141ca001030a401903040300d20071030106640801440c0c01010454060700c1301c001411413009071814010318003041714000e01e1643d1407280c03030013402c0259843c0443c2c0c03805548810206110300181031060b401c2e0380104580c54603003402c503611482d000010303114078862070340100429070000100160300105500400d02155800006028190141000e9454002c4d80e0200032842580c0d8000e4084903c00d508001250707a856080904840c81d00f1842d0b007041d40d02100007500d96101d42c03801c540c0300c08082551390400c0030b0200000c904484118048000c20314202e1040076046080010071040c008140082d07103440c3d2241e49042e16030007507a1101400350303507040120b81044440281280360668000562545141504000b018072004d0310915019804450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 754743758 1250 754742508 754742531
    0xc12011a0706051f0e0609130c0b0403080409050f040b04020402030603150c0d050609071b030c080d0c080c0705030403020409020a081002030f1b0a1413030c080f0106081e07180906 79
    0x1100e1441410014020300d101e643d00140c17100720640d1808d0440d01c1482e20007010030381d14010b070050b102440c0121a502d44560514611204a59000c0c25103403049640108200c0003d0440740146e50151781958090f849449500c00f00e441d151010320700c140701101134000c000d61040b000c4068400800d5920050000b40c5030b0405000c807a20090702c14800081c80b40c90007800010754820801201442803504002e02a10303500c403400150010381900c0c0d07481d038840120b00300f51680112041e0708054480c0300c0e42d240a11030750f11941d507441284002801661511428015503651a280380300070601a001e984100d49280c58500003540110351000841c42d043c408038600d00c016110424004409d8a41d40b4a40501c080060b200c0b05850546004403031001c204c12145622003680e600e00540c4104079240040741800c40882c1008144840070005a1602c1400c00404000080486c0e101e005410003403003584907500703500c4c1080215084941005401007214656031401e90001035201c0c00744208100510101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 754745008 1250 754743758 754743779
    0x171c0b031c0c0b04110901140a0f0501051c061706160f0504090b040b03031b06010b0315010c030314040c05010f0f051c0b09041a0c12011a0706051f 65
    0x41c40305100044000c0a07000c006505400b00c02c3d0000d0150300f2880001071040000790030034009070080d800e00c98003002c200c43e80341000b00c908000703001490030340c0c0c030400c0c10040000c150340100101c4507480030500440c1d21401c00a54062005440e00300201a10300b019101c2040d0f07201e200380d0340ca042d0700c0701080907480c6040c80307002e44903d4801c280c5c0e11a440c00741303803c60324401751400d040103652050b0b0301c0b40600c01c40d6800304020020401e5020b00c0041e1220f003152154100001640400c3c29810104108008968800003401901c5000d0914103d0090300341000c0300204a000e800ca41c900d080d1205002c10300c0544c02105c0111882680e4400c80b40c60380c03c10031609090425800004580f0170720160769100c01d0a400820000c3c4080000105040c00100190309500c00340c0d07003502d80c5410360032021400080480119444060240788500e445150307000316190040500c2141c01c0c01d020100345c6024000040102da055a8100380284000c1c1080303491100c85415074610507054a0303207004005090003c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 754746258 1250 754745008 754745053
    0x1b04030b0106050910024306030e0c0405040507290418060b070f030e030c030307080306040c17010902250b06040506031908070201180603150918171c0b03 68
    0x403102c403100d4080e100d04c480c0480b0701c03108250b4030b4103982c90b0b40c0100f2007141302c13501e1f04002c041d90307900441d4041c0d0215005040001e081e144502031800c0c003042101041c00000c01c03404641d403044e4400300c0401c001c190002c4100e02e84500c00380110380010001100759004c0341903000b03041c82400c00c00040d030380c0300b540b402544510503005020714052220400800d0207041d10136818280981503401c074849180020b421680040c504072244500032003406010b091501c0f41c0c2440000900780100c0451803a5a0540004014406e05050980006400072002c0012181d0001c1d101080070082c007900d181d10308800f04080846206000e9845d110008001d458001410b00c1025400788490705c1c0c2209a8903602c0c4076601c0041c00f80d0504c15a8010301c4610b2a2441d2110001c0c096607500082402c1c554130b02902e0208194042e141650a08482c120304003118200d0f403411a610404103503001c0401c2043c1002402805e604002c21000185003104c0704078543c00102072400110b00341c0e40d5510710b240840b8104a81c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 754747508 1250 754746258 754746283
    0xc0102090f0d1a0403031e05150306040c09020a140f090310060b0a2003040f060806010302130519170a1505270a200108100503061b04030b010605091002 67
    0x983c407030100040c060001c500d0704980203250104000c0c1030485440c41c01040440c40580d03071035480040192503090b880c4005030a0380214042c040131700f05501e8140c5000028020017243c00e40c00610052800d014144e2003000c188100941c9844428108042005801c12800240a4010f90034400e01c21a614401c44065400501c0402c0c10060441b0301101c8000204004c0c2c0080d402000286039000420805800100160980d8103042424503000400e488006404641032500520542078294a0b40c091101600c0c0291902070030714444008003410340030035500001d00e141c034079025482105000300d50b41030301500440300070ba05c032030800e507140044800403241d00030300700e24916490011608840e580d85005030401c007116200d0069444041e03103980b45004240d812101d4044001e45541c105661071341c40340303c0c0740510100c24a0400070944680c4001d1210600c400c166118500004c0c0501c15134029580200c4041800e684400740039001d80d220242c402d10030145d1440155003240b00040344084c551 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 754748758 1250 754747508 754747523
    0x20f0a0b01080d11100209030c12061608090a0b0903091801230303070222050f01140f1008190e0703052107030305060a09021c0e0a030c0803040501110c0102090f0d 72
    0x62040a450003074200440742c5a050154004a40c185d6170b43e081342e4596600c40b040948035a00301644484612140101d45d8401c2c0b128a4081100740c9100fc100302c4d203900c0d004140010656030359403501b81188034004030550b020303114182240018250340317559410307650b044245000400d013058803011500c2204080130380c540d0040000000500300945980c0282280e0780010a24405082c1200144d8204803004213000c80900010070005000b03008c01c80124006640c860045503501000c202800b558051040a000f4030f41c0c0031035000310000502c070308460300581c81005405240c240f626140d81092205540394400c2840707100444244d038104952400300101050b183c00e5643d07038140c01404009208030741c00070350b2030f100050910081c0010b088246130034185201c107140c00070110040f149074502203501070744903603400c0000070b400182e034105c3c00760483d003019104c1d034403481e08501402071f456801c680190701007801041400c0540190400080442d1b8084440000409001600e030041c1c1c405400c51 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 754750008 1250 754748758 754748773
    0x90807090e010b0a0611010c1e110c120a0c1502150a090b01060c0219081002070c092a210e01151202030606090124020f0a0b01080d11 59
    0x5181c0d01210000d0803020002c03409980c0d5400040b001045580448041080303000750041d00c02e000c1c0b15080403003080e404e041c840c0000881d41d80318030b603401d081d01070244002121903c83c10101080002010540142a02d00403850002003d4844004407402c40700140d014402003460a210802c065595805600420001e10403402055841380301a043d0000b0646d610108408078541800460182890303480381301a40c0200e10500c003104821980710100101602d8003400441c0303012450f0f1020003040c41c1c0160700c426181c20031041c0c2c0000da85c0880b0040b880c044000071020704040c5500c04030810140317401201540546d0a5071035100d407903240c0d111111000001c194604440d40f0005403400c10200000b82d090410b140412000c403143c000964035285100f00c0000c5103020800540c2c054415100c52411754035000307998003890010b0b00082861020854000c0216100308002c1d5072500d001400c5400c1200703181410188031b802800f80380c90a02403604a414403074014890b031903400c1140301c01010007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 754751258 1250 754750008 754750019
    0x5090c03090d0c15050c12062d0f0a0807030212060601020d2012030105040f0b13021e0301150e030a0506010b13080f0f01180b0112020105040503011803090501090807 73
    0xc1c00800000c6404240510f00308400600b50701c526032046d01740d00c400c280c5d182d5000011519881000b000036200d010003040c1040e220801c64480c03c0b00040710740b09000c807211240006200202615503840d00680d0150b400500c03035100180d480d085900036500803407038480d1a24101e80300d01c030448a80380540e0207001c008902c5071107107056600a490507860b80c0c00400c030704680c4904161030b0490740b10b40c02c000400148420f00e003901c281030000106c03400801181800701d02042c062290042a41c052940c0412191012008141074002c0d14459851030380c0d0b03e684501a00081500e40441100003410700b807160300726410001a0010250f40000081c0300d00d030702c2c20050b55940c1c2d1103450610364040d0034210005210070208807420161034824064a40c46602140c6982151900358640b03c007030714464815400b0682006e0340605503032920180c0a80340a00d0300058a0601c00e0b90b020310381561038101700d0038001c0501111900c4940c4203540d60000540d96000458929826020342c00e400d4000201c1000b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 754752508 1250 754751258 754751267
    0x1e021215180c07210f0f020708060a0504030918022706030a0510050d0b04061b0503150a030f030e0a051210051003081c110412080307020111030c0405090c03090d 71
    0x9442031058040d008121404020128400c5000314041171070000401043c5800112240340c82040c0d2008168140c50005041e0b80c40070041c11203c81a65100c01203410f051140400f00d020b08094a50b84500c6150614640025446030881d64010704600c60f036403900c0c02a0b045a081d041078020441c03800c41e155122440c00401d0003811001c0020103403200092251106080c1d5460140104103c007240d203000d0402006880d000c80740680d01c048003502e50181c642d00041900d81000340e20441241088290f4042034039501035410140036038100301b00070010142d00080e16400707460269040b941c0300c3da0310300a0007a01c0e2181181c1101076048501d00824400b4503921181e0721070155500c01352100d40e02d442e4850340750700030b5100000240c0003100b0b0166401d00d50150034039a0079105e00c40c0349000c1c0303400c8a1083d40d07440301c10024607e0b00004045103030a80300f50411110411810f5250b40d480c20500d450010581c068412a80250072480018405040d00d00c2524865480c2002514250040c03071401c48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 754753758 1250 754752508 754752517
    0x1b0303091f0e03010c0201140901020405100503280207201005090d0b0106081e0c07081804060f0501030c0c08070210120c02100b0609131e021215180c 66
    0x200b040b05824591030341d903909000d064004400e513000000c00c18a802c011040c401c0000b42010402e030f00400c810011900c40743d2030700754160694030b0910b032a030b00c1d03500007225143d0315105046c2c1c04080480224040009585c010305800f03200308c43e9080240602580100880c0075141150750002c5520035401c0400d0148004001001d00103203400341d255500d0360b07807181c08002a049400010003400c1004000359001224100600b24074072040c2a45c80c120500c450b2034414443e000b400c0c0040416000d100d442800640c40d014200104284600c0385c035034010b000d0003801481650300190401c0b00c0780f9080e80c00341c0ea001d4001c0780c1007000303949010115024003030261401114003040080d13240f03080d000070219104442c885682513014020004000515405603020b089040c0d110b0300c02040048100ea484800485803000b00780800301d105140101140d00b1b11500741041c003070315400080c10351110050030000d5440b80c2c80c0841d00481c21001e540500003e007040b00a1040a0010b1202040c074607105c200c05003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 754755008 1250 754753758 754753819
    0x60e0f042f03070b03060a080f0a030c1a0f090706030606020601050609060405030345012703030810060804120518131b020102160204150e091b030309 66
    0x41069195100402e00d04403184e40503c4003041c000c400e0041c2880c02011040042011400800108003420704440e115003020b00014180145203624404100c410f02c52000d042c2d185441003180b0b45041c481c6200400c008648620700b034002c1100125041e4000d1240d082a1201d55006144031b03030038103040c041158018608154000340c10b1000040c542e50030002000384c00f030490b403107500e00304496811050300f034010444580c00c4200c040b00515a48000f11032081d004609290250182c0b40c0c01d20300c021708400ca0314504280c08800f181c08414190003d80c614065000031280c405c415a0301c001c1103a8408065400404074101c41205400d41d42c4144041c00760440b030071015a0302e002050000400007481c4014126206d51642c4142a00408002c1c10300302000b2a800294644900d01d602c1d4100c08610350f500030322566590007101c1c40301c1800e10441000c0c0c00000354030501400e042c81055914010030340c100c07402021650084400e800c012050700c04083d000380c01d01c85050201071034034170140c01c6200807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 754756258 1250 754755008 754755083
    0x2031306051e030702030706060905060d0204150306181b0807060507150903110f060103030509190504020a0320190305060d05070603051906051f1704030201060e0f04 73
    0x100040c0e441401c0c0114004d2090381c00441c2d0710001c44c50110169401a8000c100f04c46c504010001d05450380100b404069604582c00910070310a020f050401e420300350005000f42d8680200c1841e50a555981007400c240175415505d09000454102d60a05031540038848c0e040c0c2095100b000b180c2d0044000c0c20000e403080342608050a2072514000489450380b4065000a000c0081d40034804020302038914020491400341c48250305584000e001d070f03c18071580364085c0a403800f540307249803524a0300c880a060020015940c40c409113000070060800300c1607020340c41f841c45945080c25514002120040035900c0303070248017001110030540042c0300c0106030503001022070080344000f0304184010006090300d5100094903041c0454503103403500340d00400e49401072410a050105070f44415151406600e01d10001c18503401c44041100c6822500d0314000c000d250a80c01c1c40105174064100c0c000340c40d00c0e038000900320740e102c41400605903c00c4e0703405031120700304c0f1441d0443c03091800c0454a011030b51884 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 754757508 1250 754756258 754756297
    0x1c050618042a0e091f020c071e0e0c0738060a150210050604150b070c0308120613050402180619030b190204030c0b34030f0203130605 59
    0x481840104111040503458200c074900040d080e178400b00030142041395490071420010503c2d0902d99070105806180fa017400480c5a03c00320003c200c903000098002c070078882c0b28604080a090303c441c0c00803e41110401d1405007448084080e40341200c0800c09800c0d15014018100c41c0c3d45040744402a0916030404010600413600c2007984d2120100d00e251035008002a000510140d002ca42c0301402c0c01c5e21844c20715011040790065101030f00190740c0e0f2034003000c4e9a00210701e010342101c5081c0d440141030707070004140d00ca5082d107184003c40c811041503035440f14084640200c2c0017142e1007224029848003e100311000202b424032521580410003030710410152100c20408030725901d80f0f03407007151210420010884418072928900c1c501403a091030642c2402e0942e95602e140c09030074011410454000320790000000000035209001881c0c01e108003010b031044180c0701d071500701044d0007a0003155105201c0384103507100008030362540200070080041103041c2042262030750301004039107009411308071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 754758758 1250 754757508 754757519
    0x60a0909020604050a0806040507061806080916030804080105070c0218270a06060f0509190b06040e091b0f040207050a0203010501060e011403040b18031c050618042a 73
    0x286517102600000000340700b949040d203091858009036411420070008003540d140c90a0144c249000c058030036508014040e503495002c440d10706611106004e8880c80c0d281d0000041c044000020003e50314034500a006569961b4416112803408460082d00000006420000c0c0a030b002a01900420036500121070140045286500c00c1c02e000d100c1503031504030203014002c1203071502c1007000520846206281c681e00d0b0400003040464000d0000501640c030781d03500841700029900014441800030203042c0c50701c0e2070314100791907082d003100ca000c02031140b036648042140c8001d0340315005140c0180082e4940c400101403201a405c0780b082115544650208100140c6e005e0181a020300003541d640001d8400f544001064a0f44140500914440c10014040482d0050320395651003284d102d030054a9036007981e0102d15611038082050082a214208080c5040325908060300030641201d000682c00c05900760b1040b41c83c4140d40c010f102180041c5512000e00c04810508003031040b001245040f00c1d0b4a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 754760008 1250 754758758 754758769
    0x16030606020a12110d0504151d06031312050d053702070218061005030403080a0b1807120e0106050105070f02061902010f182003010e100e15060a090902060405 70
    0x40c081c9401246021409002c40703626904611b0a40c0d8130ba03d0902105043c190a078509d22901c00441c901860f00000000d50740072000200054042c1d01400000e03444043d80783c007c0403500010000c91039642403401042c0e00f01c2404410158510525941f001105034a0f640a01460b600f40ca050030100d8080c84048096603a18100050803100707194440403604e07000c010440484d000f07001e0f6006011044c4207102c082030380640015402003101100140d000c400c4030000360002090741402d510a02040100200c4c1c6501001442c00041011001d0240709961030308203007680c41d1405101d000070b0302848034802081d1101e15101c4814000f030260340c986075601001420400021002c034000d40c0d11038142d07207029000f03486200d058040700046480c50a240d81c0e580c1c04038070119121070b00c0b11141c51a180381e00d0b035070a42c05040c3c8400b5a40440b040340d086116000060300103200c510f0154026111500904600c1203801c91040c04010007201070300c4d040021380340007405a90010b0342c102d402400003283e01d4403030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 754761258 1250 754760008 754760023
    0x3090504020c0a0209060301111b010914032116080c0f0a0809060703090c05130b06160201020c0603090d050a0309020303070b010e150901060302090f150316030606020a1211 76
    0x34107000d0045903e07580144070b40345d900a44958002d030714001c0034503918080305c81580c28810151500c02d0105a0480c03000b401b402c50030308007901c64901c41440d103003030300000801070080b0403015031035003680c5214480c0c180012004558042c0c141c00c02d6800c0600c4136200d00201503000b0851010b19080200b48608004681c0040c98040302082e500720038840f001c4400c00246620a03d18542404901140d50380e41c1100111841658000e940380501681503601c50707000503004c01000f920346c584845600c540c001e0752084800f016405400740c203101c8645401c0403c1202e01c241410402030a0340010044101d130164030000c007210406940e008010f006a8003440106482d038010000c03a4840d505001040707a101401403c9007286134820700c101103050300c0e0800e51604665040c2001600d2754031880105400360f00e40e028581d4400000c02e1005041c40121010b18000c900c42c078208104010400025011588140a06005680000300420001c1c1c200707401580d40b000c0600d05a031413401111016481e0090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 754762508 1250 754761258 754761277
    0x80705010204032303190c020904200108060a14011103040e011809030c02012a06090614040b0411040225060c02010605060f030405070e04080306040606090302090609040309050402 79
    0x400203410401d220800746051310711110a07004001c1d402e42014255600d21a030195801982003840340a00c1300da0182189080050700540341000750318061a248120059007100c2e100441035420700340c0d1855214412076071048402610003c3c40600b05503035042003d200c0780190b8100914500c3c2c00c0a00b2130240301610080120030f0141e00d0395410a04030740c0c0c480c1000d0750254040c500e4a1900400300364080144080590282810704050328003c0c140308410088440c010f84270f010f845083e40402c54107601c550078180c05842c0800c00940441d050703403004201514042d00d21210304001c1000300f4122201500f00d140010001807900c04854040ca800034000324a0001c02507011405506000d86c80c020030503910441c5c8002c006240c10100083c0c0540a490b10150148401000050401000b0808440602481080c00d6550326080c80d04080c01d9000311480c501660500f41c00140250107a02901c007a07070f90003802d03584150740b908180061030364001c005500f0420f441400180310384a0384000c00c840700b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 754763758 1250 754762508 754762511
    0x30706050a12111e030f010e0601021005071101090c080706051204031d0907030b03060a020a090605090d020d12090e040b010501052133010503010501050f04030c090e0f0703081b0a08070501 83
    0x80c02601401030898168001001e01c0508d0080011030b80c0d010805801d0801001030001d5036460b08201268404440d00030440c0540c81c02156000b8410703031601e2042203a117440200c8481e540c0754002164140203079110501640f9000000c41d0000e4001ea1206980c05160900c008104088000081d40080241c8a188c0441e0343d41c0c4890000d81000d100c6194071030140c03581036142c1050118010a08200c41c0300e88020014085813124083d03503032851180c040c0703030000e00841030110507007042c03511240864401800318104100001ba0300344d2884415100e0340e0401c2064003560705c1d02c0015515580080c5448521080601514030507440810b0f140d40140154003009a903415201d03110f101011919030044200d038001288400c460383d2000440b07055603401c1c0791a076102d044034403441e5424055508010722580c80b081e800f154442c1d15500201242e06281c0441c3d1200070403065084d06c4485034000642101002c000006608450190105100710500c2c1100c40d0040b081d140c0b00c0e416000404125142d9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 754765008 1250 754763758 754763761
    0x1b0a0f0c05100c030f140d050907050a09060303050712050702210d032c1011070618020a0e06033a14072006030a060302030706050a12111e03 62
    0xd0400110000390038216080c0224207240e44e840282049841051803000c10203107000c00013901200c2c405464030007684034000d100a0501c03e04013500c0d51313103501600c3e002c0c5200940005100070b10b405000c084a401d03071030721450107002d51518212040b00402000900c402003082c0303001603c2d0800740403811500410003594450300c400f103150400e0501d100c407070101801c3c0049101c16411000750740703252480b4000d510342d83c5900b005030306042007440d03180c081e1300d90302c1c1000c041784186290004010701c62103100c08000c030003802684000d500c00c041c40040d402608001d010b0014020450700941c100c1801011079100101030442c2031401559100c178140816654105e42440109401c03800340f4402c01401d107512018103050700310801d80075505024011140004015414810b0307a807a1644030040901910b0b5245450510030010f0000b5100490081c030640b500001c80600c0b4005540702810349903210000140040500c0b07000c1c0490360b00c0c0c02c400700410809502d402c084050381340032410b0b0fa1106140c1701e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 754766258 1250 754765008 754765019
    0xa0e151c0603022d0d110906040e071d060108160e0310090309090513020303030a0c0516051c02010b0a060c060b06030f09100513080711030706120b040603081b0a0f0c 73
    0xc1c1040550800d000e660701c88101d8000400d269001c5a46c1c25091301c805101303607503a4000070003030801140c0d0400ca9000b0790340003081c2c0ca4008031600091504180452950351568001143c2c00d0400707c8240b4070081b85a48124109440380041c05040c01008049401d190a00c000401c12140403400482c04905044030400042940d0b020f1950302c546d032900c0380130801c001600400d85070700c001050f41d4000e03990f50401d417019600030b102341c0340103c202103c0354510031894030340f09586619001e0b0440744031516402128280e4814040c501181c2005000020820b29004003900c00405010048643c1a2182c828440c5900c54101462140f030340091194401d050601c00d244c1400c1030504500b401c1810142006801c40602d00000031103a441504159250020300b0140d81e00c04000040c40c0d41402a2039000034069031018959440b403945030420810540b000c0c0030002116203500c001020b800d03090002107154400f81800b6104040d00038140d510304c0c481d5540d84000100198030803141c004501200340071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 754767508 1250 754766258 754766329
    0x41503050603010b0a051c330516050f0c01151e06020a03270e060102280201080c1902160801020703090512070305060a020a0e151c060302 61
    0x10042810b030000c008a005801c04101051914003a490003089452103911070000600e0126280303d41240e2200c001c00011440c50780c021140703901007410038a60700c243c0300344c0100c5482080d004e03070001ca0060500038001e00c81a14143c018100e4080707143d030103008108945900b13010b84a407013071640c100d18445608041c60348662043c404400c2c0100010b2040910400790001243c00071f00c0c0e01030404070584840b1002001c000e500401e44820401c00172400041c4000651600344d0040909030240d425002c1210600c11110b01501402102e41c82000340c900059401010f8064200340c50591070761520048140106142c842c3c441514016400006c80c1b4800061750304943c2e0190940e08020361070201941c400815100300c0d40a464454200d4201324840c80f0002c105140055030300500356003041c54007210000082d00904401008141001d0400a8600c2c1011590361007a0300501214108040d24501e410200207101144bc03510f56260f1020000d40d80f003020310702a4890604e034000a000c6000c08011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 754768758 1250 754767508 754767511
    0xc0c010603230744060601030f09110409141f050f01060e01030b1f122007120309081c0c180e1e090703030e0f1e0d0804150305 56
    0x35083c1c200c1481070058002d41c1d0604e6082d503801c3d420341402c000e07000c0a01c51100c81c1012240341c01c0d44209001c001e04c0400400e00c0351051600b42c03010411202c52403000c405136070030303160000c0584000d50032401750b51805500034000c0c14040c007200f0385c07040c2e0489540751030502d003402c43c1c0402403840c0311076404000c0c803401038035442107030070b00c1550244d4504080580300c0704a82c04220705140c0c42d994017000310b80b5206401420042e10069040201c0001d0b10003401d02a030302c09213070b1903a50400f1840102406107280700f900440c455403410346082e440391503040d020601070b10000b04150301d61440401140159026121016000000d500902e02034842072080380c61002d40c80782405a2452158981038002d81c0800c11210740c5225001250f44540001d1555034090959108841c0610140078804400290780402e5920030348400c0480c6180d0000c02611182170b9041c00da008500321390209203026081380c00601d14401814040d00340c03200c1d079541a00398000c3d42207144148640c03030240001e00d50501505 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 754770008 1250 754768758 754768823
    0x10c0206091c0801060507050a0b070e0102121305270705030f07020d020d050a0905030303010303020f120f040b0a020a060e01020c0717150615070b150103180b0c0c010603 75
    0xe00241e40b41070002d05014414816403051010110380c0c02c1c244070042c403003000b82c154030020b03461041c07500d010094495030070b4107441e90040c402d03a000c041311103082d01c0894030b00e03401c18064150410b151104008019400c0c01c07105c180311a8680d903500b80c4074001c2a2440c01502982c40709511380c074140c0212107055800806d00c1d003c41d030140a030700402c50340114200144110610309244e131011803001c1610b00408581c040f03500341c031000000100303255001c07491503032003030b609000e03640e20110250b41d4071f00d2801040803403011960204030801c403030856480203010949185c016166800510f0300c98100712140204144001d0350006003142c1100c000744090070207440040d0021510301c0d0040807117680d0311112405110002c00c8000458442d5513180740d140d0040c242d40c0b13030040c2e8559083c44e00e04a0700e981603654440700d104101da01c414940c003a0241c80840b80410a00e02c40b140c0c0c031500c0d03050b01200c0240c4000c0c0e2400c004c0201403c07050081c041c1502860080c07030425640c0e00322381c2e032a1318100c001c0c02c2c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 754771258 1250 754770008 754770043
    0x4031b081b151f08330c0d0f0e010507030608070911090d021504301101080403030f0f02030103020f0d02061e0912100b04150902031008010c020609 65
    0x41d503a2080c00e4a4055401c0348610501c501403511091901034500a940c1140080303104d060200d0039994045001701c8901d0110300e5628140c2d50610314114900c1001380e43d44c44402e0b0040c031907101d0b0f894540d48800c14454940c800425030400c064011802c443d41a1410000070751500b10520203220104040c000030640a5000c10040b85070301406111030080090003841040b00390200420f640e01c03000c114459000042a95580703e50faa00000c2500a01c440080c15010020b50b6800b403040c074408202c8800b542180103040841401c900445607810000c0084051681c0e804030b0501c680001e01c1098215404000c005036254194010002c003d0803040f0742901c02c030b400d20450001621913005441000ca0481c2490210010001078580c140c024004403039040070500b81441c0480c171000032586200003100031708010300b0141200740400d40300544005400304034a82020002142e0940c0150390012303400340d00c102903984401c2d2950035110303d1489180141e00c02d6003400f09a00061102601d0711000005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 754772508 1250 754771258 754771273
    0x3010c05031009020708040905090303160f090b0327030703090905151309021e0f01080601020d35012c0105150c1e0c240304031b081b 59
    0x18a02c202c1078090044061503a004500320041190b07000a071809001032100501442c5044c0c8202c40e1740703410840c0c203440704050f142000540345008458010703c2128594401c10300e2402e01c3d61031040c6138400b904103208a00d40b0150400d826403a8829640c8a0309024040d51351100c5e00c3c1001042ca03230303568128040d52880d010a101d80c1b5035050083c0944200d007903a2081d000d800c0d07501944024401024007a400001044200d010b042103c4a50592614120b034986501e18155004403482241110b0321405680003a9020300c51500a000e0902c01d008070f5071004440030603c00441c664082102c841035058108140144900000300c0104601c550b101c203500d541c0040812620a4010010300c24140035003880880c0c2c4070084405000c5486041e510350444000c6500e11101101044200340e084a09020344904540c00d85400544117402c0034943c10746007a040580413410302c1c1c1e580050700440c14000100100100001d55032807030b0050300c1c05440000d4489000150856440010b101c070244d00b03410565 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 754773758 1250 754772508 754772521
    0x304080604020409050a0c0306091707050a021306031707142a010c06051e07020129030c2d0a061d040204050301110d0c020118080919060e03010c0503 66
    0xe1419030207501224003081e41000c9040940c14034600b2840605844031062001c41031000c070f074101d107481520071241611b214a0b0705036a81d0690041440c01032454001051800141c64081c0c491210383c41c0c0c0c103000181080d56665500c90040d452180d100340a240810081e007480001800b042428280e0f60161074030a800c07000541c40c2e00184000d588100c114281e0801c00c0340d03c18003503080644c0d44030108001d0360800c000c0c1c0d001c1d00b2204908c0440d4000c0d000c00014041c0d48180a80c0c0b500078010f0074003450000c2400e00402e00780d5540454260184100c6100b100b469035900701000d004140700116200d0041d041e50043c40c40025a030b0317454041c04003680308100b860307480b00200110901c0440b00318800100403000030068400e55018a41c10343c01c0c901c50000c00542100100341c0100f0703e4a0400800064900c16402c0c0e0b265042d43c21090f4003504010303004074036040002c010090008200100a11808407070b4581b20b0025000680054881030508405040c24820280714112030f042003800d618009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 754775008 1250 754773758 754773763
    0x80a05090c1507050309040c02010e010b1017060d12090905090c0d1e0c090b09010f0312080403050c060412020d09032d02030d030c080a09080a11030d0606051b030408 73
    0xb4000034440b51030005000c001d11006005541900b04010400e000c0300c4c0040400a000e02000c6640248951030b001d8802c0c00351802c0ca16400d5800c41c2c03038840c100043e10035104003445c10341c0207103690380140703009a201000804158500c800d890081c0c81d05450b181c1452110801c841300208642601d43c81421115825503980c07401d81e5410740e020396100060391510003a00c0201c0700c0840c00908070302d00800049113807042034000c0b03403070384605680340d0705a81e80e507000c4542800300910002d030040010307496642c15036210b440a00d41c054080e042c842c0c60f00c00015101481c0a02c125010745806440344285010036030b041c000341c03210b074103d890a07001035411501c803514003146500021441031861030640003c003165502078a081a00142500c03400111450f020340940a110001c10000700c0b44400220140424031410100300c0e0040e294909220a5060a842c200d0b50070704407003600c2c03100b03200503840c0382d81901800000d40b034550f4440d6140c2074407202c1e80300f100508002200c015081030000340110b1400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 754776258 1250 754775008 754775029
    0x302090402120c150a020f0304180504032106030c05061c05130803090c091b0306040b0a0305010f0f0e0109021507060e030f040602100c0c06091e03080a05090c 70
    0x11204545400070040728285007122000f421604090848a6000c403490f451024154080e025001c0e66280070301e902c40313103440784601e02a042e000c00b80c84282200490300ca920081d0f0051203406c00b08040e44500c4078111a03e192588915002a128070062003001840d00e0410000c2209940b0309003440c0d441c2e915040c4144a004d050542c1d25502e900041902013101d000c0440280c02c0300c075030b40d81d07810002102070b210781071090340d540138404206c089144e5544221b00d1406a06a00c0c2c283ca0554441c8006c01000c1d010803a001a84400c08d03810100206600380f080e0090300400074400105a500112210300361041e9205a11035a4944940c80000da02c0c0c1c0058080211868070002c0d580c2c1c1921f25020006064244c03400c08144008a00c0061480410009009035107070340c0c084483c80c10a0714203031310030340c4c94110341c0400050300d480f00d00c0000383c2203802c03500043e40b06290b00c481c1d10070504040340e4a00000301d01500003070500d105004c41319480307224035500007265401400c0d503000c821001c40c4940c0c11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 754777508 1250 754776258 754776263
    0xc0709020d060e2205011107030203030a0501050909030d05060d140a2310240e0117010c05040501230d020702120714010809070e040309031505011503020f12010314061003020904 78
    0xd04d000741394200b0800b940215005189514001c0d25140c481c00d0007580d03500125010803c07549490700110300c5103401c03610780744119280c000a518084842000c000540406840d046e0003002e0992100000313260403e41c0602444404c0080c845a00c3d01c2c108a0348451a441d0040b030110310320034450f00b50400100782c10608082038080401d0034140c001018000300c400300000703607010010701004200142143c0465040303e107084001054070b112583c5182c02c80f0300040981c1d010407010801042694080c1c0c805070304507585288800d4a040130b1441e0300250390300150215186607400282441145880d410f03103009660500c00403c405400c0c00c866580001c54100700f1380c107001013080000d0848804000c50750146ca07504ca64880c0604103458040d00000b668081162140503221074403021148a10400c0d049980c041d586803000c00c42d02c0402d500950101c203000141007001c0001e03602c907490a08242e030085104111a02d454001c1e910501d080903400703031102c0c43c1340d5100c110410140e500c05210b10f400c6034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 754778758 1250 754777508 754777561
    0x50709120c0b0304050d2303011502210c24270706030518150601081308040b0403030e01020d0f05030a0f05090c03010b010905090f04080c0709020d060e 67
    0x200505007110780441980c001149180c001003000300b040000300300900c2e0032110317031103801c5050110040c0c004a1800484071506650051004000b0310740d01d6070000303041c04101d00541362040703051407008454144520390549007410005004020300c4040000280110904188883e0301262420403840414040d21516500b41e1410a503c80058460041030381c40040008999016507103043c003070701419046503211102e200f02e0080700c903594008141c00d400030600c0f092611443d41c0e0440151002c030000f41c81070041241985040c070006802c0300080001d003080550b89a119469481e00610400524040904641041310700c03011568020240300c01c400032a050454072555031081d0500241002d108001300141820180098050045401034002c1c505400910514103010b0054910105c1841441c1e0407040c0400003c0000d00b1709132070950820b100c0d03040c0300c0c41c2660188200e45003c04039003244071080d90000d051501d240a6205060080c07948541c801c03810301d0b180001c40001c40100320b902c560030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 754780008 1250 754778758 754778789
    0x60a020a031806060f090516121d0c030c010306061e03020712080711010204061b0809030616030606090e160e0a09060302040605090103050a0813050a06110c04050709 73
    0x150090700a11121444142e807494024003034107010020301031078464038880c0034042501083c104801c2c0113040c41660100e401003000f03142c02c407080b100104803500e4442c07400d0381c1d074030701d40090200c0ca07134401d041c51401d40c018040310314443e04150070401d00f403114506040c0341520400180d50030040308008802c0c40c074510089070041c500160041d215544d0f00038407c011500c2101403480c1c0200980f40180425a641c0526210410141e402c0b80720328010b9401107070046551f40180c9241c0907807490802d2040a000b400d00040e240400c0c50700d01c041d106030719210580b81c0c0b491091641480768200500ba54034284100e80d141011030088107801814150b010461801c0400c13046014442c0c0000e17841d409060818055501c00c180001003000e404224840c1d8240100020390749044c40c0200c1c180d0783c104024040303484480e130b80c010655101c40220600b00702c81c03036000152940c844c00344100071b04050300e404078003c1032248180c3c00c04201c20001ba00c40c51810b010721010940c42002d440070741c1e00300b40d43c05415 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 754781258 1250 754780008 754780027
    0x61d0412020c0603100e1e1f170a020108070203030f060d030203121008010c08061005160c03050a060e15010b030903040b0c1c09031106030709090e160f0602060a02 72
    0x20a2610b00751181c00c03060010034072441d0020a5803079011201c42d450202c0d0203494001441c2c510100512888490680c8200424031034080c454100e04152640883c0c10300145e9103190010009143c48150055034219100300d0b0103650304400360551003002c501c00f4514501e441c240b0f428042d4000340c01c5034068011640703440200b5008000311204100b28003140781d5103182460300d09840074047d0251084950801c80c0c142c09807405020814090407006214011301440390108543d244c110400b1104400d40d004c4011000c65141d903c00d501a600501c0074003a0481e1745d080c21030690314104c0500009134425107050705000c00401085054401c081c40840d601d0716010881031960203907801c01140c4400c0028110307451400019250980507a9098040041401c0101610804da2900c009800c81c1c40c21002c806051500f500215805840d5003000c05035151074000700ca04855400f16a5016a840106044041003809000c0b20081c0701c04080c880c221410910000d40700c1d280a00030410301600801c11006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 754782508 1250 754781258 754781263
    0xd0617030a0c08071e03120e06060904110904050109020f06030f0a05100f0f031a0108030f3405010518030702040902041103070f08100f0e07020c060409060603061d041202 75
    0xd16504141145140121050351101340e040c122006c4000c07445441202920180d0b600070405511040005413149035214030a0202c40e040003003003100d10141014030005070755a4501210700541c010000041ca015880c8107010702001c840702d12034880c55043c0b04110840350040060395003e406a500406c503510703490100302001307226030000b02e540740c4038510100300d0510003135403141228025520032140c03203014180100204000e00407403510347c1040100100e0700c0301c804004c01001c404224288800d000f044d40c0440200301d58146072050103004600101030240034001c40e41c001c4042c00e14035400d502c80d0110259680706190009001c0c07902c400c00345044d9511548402201c0070303020311007652446c095a0090013201124448800304205801107032a0b002d4840050050350b0201391007102c081d0815a0440c031f030300301c01482d43d0218840d10035071042c0798442d40b0180c030040188007804030b516803c03c0b202070140c5183c2e42151030f15600f0712880540318501d030780d0016049034000601c40c540301c0448004a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 754783758 1250 754782508 754782517
    0x61d060a0b0604050d0204060f080c030610051503042630150301060801024909110a0338060d081b030304021e0d030503070507050109080d0617030a0c08 67
    0x270207500603100008010502103000380000390300300c00340c444030360351045d900ba82d8865030b02403150081201210085056240340085402c58042e10010100f40c008040c150048840601e8041c601240407500400e58003480d126084100b002c124610703564240402002c0c40f0345c0c001881e41840940048213010760b030700e082d486000034105440082d03555010303a004502c0080c5a1910501d401c4112074a00d990541f0303280c8141c407445000c1001040c0c00551040408003500c04010103484801c401d02002080340c2c2c0b0705140758001c6100d80311240d0b403e0303d0900303d150110011442110810490b015140c4102d6402c031581e54000c404403650300300046581003c41082c0100320249078840000c12038400c5d180740000140d4880d901c210b590301d0002420708500941203030510340c921380000c00d07041d03c0c50009010b480955448425498498200030041c0c40701400d44039012003e0380c0d2000001501d04181030103025400140c50744407003013800361b40c0340030080d0364900c21014440200200c002d401d004000340c103030864 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 754785008 1250 754783758 754783769
    0xf0302091302040806040201140c1c030e01050403170c0f0d021e040609030506070c0302340608010812070210031109060714010b040c0c020418061d060a0b0604050d020406 75
    0x1103440d0f6032030b40d24550fa19107040c2d074147e0202d02442c40c4000e4940141040b900c16100c29009040311a01c0004001c0d0003010000e011802d1680742d04180450710000d104140c440c5000381d40309a400c91041901c07928095026144020742e039000c001c5018110f21101c210f8002e41243c000c0140e0700c6000c03034180f1450541e07001640c1403c04001030b000605a5001d0342d0201524000d0f01500c0a41c0c99403041550003002581740100540c014809008a218018140021590b40795002c1c0e0000100f80400c911482c2d0316800075000720b40c00000501855100300321903502d0340001c0c100c1e40e1400516400046500241c165090b04045d00c802ea9440c00e0002075099501508001d84050f450f0350503132401e048084048002480e46620305542132100f0703d007500540c00d804e11252591510b1031b6081d0203100c050a40c010380a4084070152001d00002403452240c40c7d0381e071150010a41c17801300141c00203410010042d0424042505080b8148142e070b45940c01c03038080b0f6004880c0c006c65454a48042400f07000540d212 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 754786258 1250 754785008 754785011
    0x1407060615030b0604060e04150819110a0b090904060e19030807090302091812031e090304060504060f020a0c0305010e010f1104090509390405070f03020913 69
    0x20501c029014410358022591024801240e0503070030b104040c0650302c101400034600030583c03041400c1c560300440ea803000081744200c05a07140d1a00364a0801402c1d904035440c1c410440c403005014018511000e013280485442c540c051810899060740e0050118007031145514002003001c21030340e48c0c020b5145490f20b070180c40c00e100044000c00d218840342c00003680814800340010350a50b02c901d11420a582d401010851705464030076180038259802e445c410280d1007104208800940c1c05405107114821420044695682220030408041d00140041780d40d13601c140028455550000b050700d041d51502d00d0140c402c40d25200c0d08078030301042d82c8006000c14042c002c01009002041d0414030981107544003d22103205030b46420307811103600440004400030300740002c1c4580c40080e081103401c0f038464402c82d00c2c1d0b245012240303c400403a03040b0b500d0403007031202d800001c081007600c50500302d241c049a08001d5031504041c0500504808565101016400500e50741c0070380d00d04007400000b4625600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 754787508 1250 754786258 754786271
    0x5090633120708250914041203060305031303110a0b03040f0c0b0c07240e0d05070f080c01090b090f211204080f0102091503072322080d140706 63
    0x3c1c1601c802c42c942044544500c51390702c0100b4610384a0007542003a010300340d10342d0703015905c54507642e1092000080040802d516040000b000c103038200041d0418145c1c4c40f840303900b840c3ca986000711511070703800440c500030300443c0c2007000070404140503a0f51058020002002e0f9085170300d04040c0003100c54009850704100864034450030740001507110152400c001016101a003107000c0f142902c6070f00c0004200050402c41d4480c010b085c502200c000c118880d000300e0f8446600c0c1d010f0003841c04000d80080715968403d640700170307156a110000c02c000307106480d80d6515016140c80072840c50340a1052003400303010100c03481034184043e000000c1805482c1010b0f180383c19500345031500c01e40d20911440d4000e105446c6115000c1c201803003200c408072002400f4429408000f14400380c540c1005011b035062000718003500810355024403041d00d601010910310356550b0320189040000c40380070b8208125202d40c1203401d000031800050580c4120b0114140403a9804100000c009079114000e00106042d04011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 754788758 1250 754787508 754787533
    0x6140103141b0909131a01050d0212010608030301121b03030c021c06020f040e100e07140d020d09020315010807141c0302060f0a0c02060f09010f05090633120708 71
    0x50303031704000310702c6510b43c0f0840c608103082c500034064081c05140c1d4002c568940c0d0000501c1c00000030905504540c0006c070b0f049a480440c2800c54100760b0065001040001c08502044807401800480002d108000303840d107800d54400501121074034000034001c0c2c4800c110b41d0a802c0c0e43c42c0003180400d40c0103078150750318502c0c1c03500344135a90000e00c51090034070f0840c1c003c05d0908410000030b4064034017042c880031b40c560f0b5020085400c1c210340e40500c00210020407070211500520b00003000404054040410180d1051040c1842c02c1e22900c007580102000000620108002060000c11122080c0a820003010320f5070000754580344400c81400c200301c601000c4002c044d0041500f920a8080103c101415960381c501d030401c0c2c42004c0181e0380140c01c60b01c000b4000c009800400c2350440501000083c0e400201009141205c5c0240c030146269841a01040f000790031802e0740c0c185251015045a010b030303010440a84503100c001c0405481100c8201c081c81d007082040061000402c4110300711000d40f480d11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 754790008 1250 754788758 754788781
    0xf0c0b0c070f030503070204021b0a05010212060907020706230d0c0314070c1b031202010b0a060504080318041b090608060109231f020106140103141b0909 68
    0xd0300440315001d00d40c0009114255070340c0c40707001c407074100b405103241010030740c00c000013580490400c000141c1c81183c52010800104000800e0901ca0400140d80d0664500780900c0702400405480c400c40070b44081043e190b82c0440c00790202c500500f400e2901407002e84003003010031008941e2090f0400041500c80d090401900031420f00c10442d00c0801080c030b001442c540380443c0c2115990082480c103112140000c4002c0b8545002c5910544842c0c42261680d0310746450440350b0f090300300140c0d1140740054041c5000d40c8078200915003410720918040c030700071109449024642030711482a6404003442d089481d5030b00507540b0007469905000212650290186c540e010341e0117400001359801000901c0b65001d00d0611b000c0d2002010a5401e90a105070071481412030881092341000c04040350030390030300440610400300c1800c0c0d0004289582000e0683d5012031016101c541090308280c1e503d4440000c0390072490700604102d21100c10224a03c0e0803a07040d1084002c1c440d04000104c0400900b160076 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 754791258 1250 754790008 754790017
    0x5250e0406060302090d110123070b090d02071701060504020406020a05010c0c08030a05040f0c06031d03040b040e09120324040b03060604092102030a090f0612090f0c0b 74
    0x129001c000c4291a54000c604038020b03440c00e00d401415a49070080412050107105000c1001490039100712242d02c0a0703007e074904c3c001c0401c0e1100700086542c104220000b070f42181d101d03005000030038403c000d05600030340c2c52603107200d001071112040142710740d4a4803c0d005140078120241042d95115543c19000350754104c0c9410940c3c0b15440d00030401ca41b031303200702102d49005820462090850300d403100b90b000105800383c82100c0d040070042550000401e15503140e00200942e440c0098081c0e0080a40c1001c0d03200401c030741c1502d80080006105480e0b154080e1000e6035404a0484590b03500c01c50300c1440d28402141203442520080100002d900c00c030034102c640690042c441e5a0340030308010611094174494080d060b41604040005440d50a180d8040580075002d4180300150441358100441480f15100340d240041e040020070124440d00109668003d100c41c02080180324038180c0c5c001d11060100040707002154445030751b9018414500040200c1542100d079508242d5691070580034152701 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 754792508 1250 754791258 754791287
    0x3070206010e0a0507091401051c02180108060622090609020d060501050c06061c020d0f111009140d06020c0a1401180f02030a1403030f0f01030f060525 67
    0x81c190024082d60800d004650040b072643c6c80745011113092003482c1510030500449281000814800340d004140c03c0309000c2c0c200c01e5070300801030346e0b9100d12660100006080c241c05041c05051014480c003511048101c0e41b100305984a10400104503d080c010700c1c0f01d07654000d14115041500110b81248103600914420581020821009a44100648543c003500d160304420b0b420901c0002c12501f03003075095a0740120201582c60f01c8015550004403a64201d080c10b5480c1000d0340744c11410400e20400324000407278100c843c00704100c50540014810403240c05a02d60040c20460f0303401183e141c02c21140e0800d03510039025500c6201c0b21038201e5072050a104c05403010110709180c0c0590401c103100e98400f50a002e4800c81c1885a15256544010601c1c00100d030035100703140480e00400e0b07c2908440c1c483d140c0002842d03480c00c281242c82c8043d00050034103010441090010800103845640410a1613401240410701e44d69402042082f103408440c080c403842c10300724440c0308107030703105004110100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 754793758 1250 754792508 754792529
    0x4150506130521100f0b030d02060a1406060f0a03090b09010510061107120c09141009270c03021903031214060112020405130207120f1d01020a05030307020601 70
    0x303c4080320009003a4038092421041e00003010940c140b0320260084d09001701502c00201d2400c000c200403c4c0f4120241d0302200058100c5410300c0b100704224011007000c904100b50f1600c49042c00e400041c41032240c0287d01c080408009116203440f40607810000390f580c1c005004034031500e0403044003800b0700b130b040b10303030309500d8903d41c00200f503980c02510021940d0716803000420046082a00b800c00c85034100d042070f10840302c0c0c0d400002d1150818082d001546082e481010000e0518141c258112845a040039600d10b091400c8051044140c00c03031030554044540001c5030075243e43c24140201003840d00080e4200c24482d5503ca038204201164208403403095903407210450b80f48503800c5c1294a02c10f048199074141780e020070899807040252420152464800624140e0f0b2800061001c0c4448446130320039540120783c40c024499004640e071f40c080300b40e00341203840581e07009005120a40241e0641294100325080c0610740c0d20070883c00300c038554007804030b81c0d99082001c4007030f503510f80c01d20440380c032403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 754795008 1250 754793758 754793779
    0x1e0203190210140a1409070603091707050c01110a2414010905071d030a0206090118082d06070518041d190c2c0411120c0906041505061305 61
    0xc6170400d0f5410302c1004400041c1101c141018012000380c00362820658941e9000100080288140c01c0204041d41c860402888451640f0f0f001400309040c910b0004540d800c6109000080340702c1c10f000c86160310700896074661034910942064000d000e41c240500d81103035104004905850310b40d1000f409480251129030303804100641305480c80300001c07242509038001103010750060800360040c044e032500c14100b001c041b800c1c100300011041115482828594800c0341c44081c040440d0215541020400e64081651180401c1c2e036a65403601409850030400001490030b40002100049200020300600a0040e8040c2d410140450000564000440e00919400203000964140301c0c00d43d25078490304041c051460310102455074a00c6082c1102d03600064120719008010b03007800325204910481e03881c0e4044605c9024031040b034042401d0703010150321804c01420103544003002c9503400042141c000c1035004c54100e19490004aa502107900110003041040d161100340c0070382c0095940988107410b85 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 754796258 1250 754795008 754795031
    0xd0908011a03030d1d0a032312070e040b180a0605040501030f080304020310060803030702010501060516020d06020f0703050d0b040c0e090402030f1c1e0203190210140a 74
    0x40505900381c0c2c0e419841007160185102d01030700400301404080350b40195183c22070442030306111403000200d00080c800324035801131038401c685102081035905000350400c84400354140b00e61801030419400d200c81e00144844075541c9400c0003240302070160000c20042c806c01c13084c0070704a0082e54209052401c0c1a00800d5500b403900c240c0d13048035001000c0c406421110303111050030b0ba001510a80e054000c0000b0b000400e82c543c000c001c028103980d0029039480c90240c400a007115010b03040030080010400588890b8884401e1264680b41c0440da41d01031132000c1e1074004020301c00c02d012402d202501040308000e042d0401c000e0401c0c5114144140011810340041008076060004600e000c83c000c0248083e15051001300554441d201800b00c4440100d04084c051400400c83c2c502e4005900d84031411022545c0540216480326200c02c011011088407400a0344900500e10344000181c1480046003003c0e2017080408804058010108218103d80061241115045400612481c10b0140c400785 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 754797508 1250 754796258 754796291
    0x904030c02311a01081603060b0a0903050c09060f01050a11070b0415030b180a090f060c1107030530210c0307120c0905061602030607110d0f0507050d090801 69
    0xd044005035074039800c3d03030f807100110480351b119001075008245e920344020807001243d030024039094603aa280e40702610300c0c610302a0726000c0c03d55403260141c40c424051202944a040b404982d445090030b040d921860541c0c2c0c125091040700221001512420b0400118204004020300680d205000030341801550880103400b070741d0f58500100d07000b00c01030110b11111100940c94030b800c524a21404602c10416480340d40d00b04110300d40644109941303440307054641d5080548595080c22420280400c10700d141c40385519145607800202d644905840c0248440503140d0441c0c41003c0e2500d013a645459843c180c13041c1013030545d080441e80c031107441c0c00300c0c18449104003600d12a003899994003480c08d07072080010300500042c1c01d01d6818401883c501103021359030600a80032413514807100c1c440400c0344e0300400d460140040e00301d50a000101036007031807102d4040343d40005040320741003d00d0303104e400e00d0742181d0a20980030013404502665140d80109075005200c103045951600080c4610344075250f6554 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 754798758 1250 754797508 754797551
    0xf0e180f06060309151009380f060315120604060f0b06190504080111180a06050f0c1c02010203040512040609031403040306090804080d05090904030c0231 68
    0x1126900c03202018440c1d40c4400b4049900589060030658003d503940c0c1040141e80c840c4a0440b00000e004881d20074030230b4010f281c2c801c460038440c14104d500320380b070010400c000c8400d810719001d82c80010001e03001c450310609160095601403c040c483c01c0c00ca055003900c070a0151021074940e0704000c06d4074003040c1c5a029401c2031182c01000645031124407840c001036059500302500620806010024a40c082841800a081039a52105640300c0b0741401240d8500a10041e0324414008540140042503201702540d4100b00544c40c0380790341d4503201030118940f00d00c0004040c10250010203d10070240d064000c0c0d4042d504c660100c8840c40540302c0700c0100f60189008241c006400c9600820100f058040307040d511900402c140c80c03419450b5114042564051241510100c01c0014100319580b410411207014020505c1c0c06070500d0020000039443e40c0c40548043d080010b02d03860601550344400d16132200c0d8a0ac071104074501180341c500d40ca888483c40c07621070030031407605041e0350207080f8149400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 754800008 1250 754798758 754798771
    0x415030605100e0a080d020d0210020a050403080f1204120e220c03020f130f0b0a09050d081207090603060803070b070503091212040611090906010f0e180f060603 71
    0xc0075221440d441200c20119403143c140d4030407282d007000101840103020740701100081d60701522070b000040728040d28089103140601100e0344108260700006038440145e40650340e222000c0b0340e0710701c42c4548241d1303e13004058a43c07500740a08002d0000304013100321480c10400c0281c994201120481c020080101d0003020032108003001407840d1170310f141e659800000066607500340141840032400e8800702c40c3d0416510941e2507402410103210700070079040c03a00c0003000e12500081c0340c813000c1d110090128a407442294080d00803482480200140002980e14034400c1c200d801c8002d01d02681c000f48090154070980010034640703100800c2005020003228040c0390000300c05440e41d01d6809007144c3c5a0310040101c10f1034014000c642040b0010750009144c0070040d5045142c040c28182812002c84a06000d9015810800c1106031a15280e0030485030b4440d109003000e04480c8454003003922858501204254000c40c59106c1d000c0c1202280855402030b012103d04040a81d10760051145910007501c18 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 754801258 1250 754800008 754800019
    0x30c27040f0b031f15150314090309130f0513020a050301060b03060613050a0305030d0f020412020907030f020403061e090f11030a020a060f110c0a030f0f080f0415030605 75
    0xa102c480340401d054848009000d08000303503000d070300c2010345c01c41c0705c15130480b1a200c41051101212942e06014035007812861110f030500b14107110406aa49106420b91b00c1d002d001d400041001c4101c0340d9000000d40c441903d0248414900100308440d1140460740403403103501407210104060034140704d1401512220300302d1500d180c0714101000a1604403023201a4588028030b070104450315586d01a01c011449440250b880e04000408003042c2d03002031410746a458410b00040186444c0740120140e07050301591181e2480d12850001c07005043c1c080d1200340d80e503000040c0002044480d90007180d08003407102184901d842c0b140b842c038003554040e02024000302561125040441d0f180b00004900c058010201e0700c0030406540403813820100740d40710f0fa010900300e0501010294210364212441d40502c0c1c06888414038190002e49804098040600402071501c2e1034010001440c1a01071021b4004800700c2c0c8499841c4007100031fa0b403081c0681005403001641c1c0b40e4019009000e06070a94100420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 754802508 1250 754801258 754801273
    0x1b050406110f19050c040c08070f0e090c091c080405060d0b0d03092c0106140f04030c1503051012150f0515091605030c27040f0b03 58
    0x28112006031001c5440d28042c014030144020401d03003002164160002650888110051400c003503080000101c0c640340240d080020001c461a8401d20701c0380e10034540d0805901c00c1c0501c0600b100d50544104940307400c441d456060090404200c03000d00a110002c4441c500c3c0d5050f44105180020381c0090001c1043c58180000e102900d4003030090003d03803007005000a88a80300100041503004900f00590109515440600071468462001d0b1040071100002d840381c212030911481480005124444c02c10024018802c0e000c1e0440045544c070600076104151500e4a9080c8071004a5180c400c1440ca440f802c80b00e1005140a4040c40348078101403080340103068601110002a40911003040300c461640803140c4121203c01c1c85800000030a44000251a02e0030700702c441310202000c60940e211304002c20410015552100700f400c0040c4161400d95182e4942c1081071245004501c000320030069010040301480d40f0706c00342000140c45c12a4140300f240400080b40c5d01703c491211005405400c2003a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 754803758 1250 754802508 754802519
    0x30e060c130605272d09010806090c04020c190c0f0e19051005060d06030506090c0307090b120303041104050c0a020309010f0504080307050703050f03162604080c041b0504 75
    0x282003641c131403005010540000301c000c3d4071880c0c2d542455224400e0302e9412032052114113000750500c0c0075105a01c000c060302e09002040599a21a20300410300c503940008400040c5a018040c810318400e243e40c204401b20300900d013842e401c02c000d001d641004811000c00103041c0c000118070718040c4000394900414030340300f01d50f60b50281200402c880000d103c1d0100c0003800c1c0d1142001004c0b0000c0700c1c4400200181145485410f00b10043d08240156006038900980c0e07a03000300d0910300300c400340440011107012150218070500000707070300500d01c0d00010040100307004400ca425100e41d0011a810010b940e02c904c40d080e10703030086662460040e0300034012442513500583c82942400d1190a101d402c1642e200351880c51540607081c221074a81100800300200481001200340c40700e119400b850500101d4501c21483c44040c000c040d10041c00d18800150400510034204000e226401440b65600d494803000e941d507103070803032809015901c2e01000355201c40380300e51525403810300c40c2d40711850140b400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 754805008 1250 754803758 754803817
    0x2090f01170a1a0d03050a020114010f1e090e030c0c060418150302042f0316050a050904090c06020d1e0507080c1501030c0906080606040c030e060c130605 68
    0x2031410f01440307501e01100c6202e55160b15400000c4c500c40c0d5200c50707071601408002800d407818451a40510f01503580148042c0e81c214a000c801d85050541c45d0b48240d1510750409400c110a0784400f0426103050900180c0440100040c040c0c8a0510103c800c03050356941800003a01c6180304110f00c0300210050b406860a0359080140c0c04040c5040d5003e140f40c60742c00140494100100b1407454800500d40800300c000e601d6402141c00045608031030440c90088a86110554441c01c110100180001e040425502030815950030a2018108001c43e08203441c08100d801954001c001c0548078690f00d00c001d640c4150003108801b600c4800d0455503414006090381c0d6600700f10400c40d081d00062104034400f1404200000c4ca4106101100055514604010007040100d0308096060390034900184044030000580c113402c0a01954005411509242d040b0028404000b14510741d001d01d809100c841c00c801c0c4081d040c0c60394040d00201606035109000e0320680b00e5100817800500f6010306960800d00c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 754806258 1250 754805008 754805021
    0x6020c090a050403031d062a04030308060316080102030402130c0c061806090530030f0411090901050105010e0102010212011703070b0c031e0105060306131e02090f01170a 75
    0x281c1400301d040c1c10380c64450311700c10061b4501140d1681c032960800c0300d15200c8881c5010f1100007003960903040912410b00200740e102e5800050103000f0314001154160b10104080c080044241e03d45084250712659214042c0d4029102071b807280300c4a54118500075068800c0311070b021941d84425100503090b82e2164060240112428100003501c105100820903a003d06030300c5a00c03500c0075155860700c00030501040e00448080c107000318211040308003058500d200701c982000320903000700825a45da2078692034400e500310b00260020384d0031043c404201c0b41500310324161a026214242c000e031042004a08030300501d10131000402c51040100064915002e20104c0c0c20041c1d401d0701c0ca042c1894488a1022005171029100d00b5400810021216500701c803e500c05d0200e21a1325000b5450000007030040c0c003024100302d11a0b080b0001c041d0b951040380c0d002e88803001c040c89044403401d0030f00c5100d50080d0081c82c41c144c055006100e08000c41d61160801e9207000070214180611a1600240340d0000e014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 754807508 1250 754806258 754806263
    0xa090f0501121a040c170c130e0a0b100305161407060905030d020c160b03070504090f14090a020a0b09060301060c0311072c010f0504090203070b0f090a06020c090a0504 74
    0x1034100028242c1d200c0c0e02450320a03102e99154460303c0034841114094480c1b0003402601c142070306228021230020a01e52003000c845416890b0310f5140c0b141e22224006007080d4030b2580d400360382e00e004a155640c040d00803500c00c0f590312129858070900c41d4000e450300004409414807d0004010500c0020950703400131103014011000c8070b062208419144003268411201e81d545584a003c1c1e41911400c4541190b0251500c05091400e6050003c0b000d07260b0300903405052200703502d0302e80c14040750b6160380c40300202d101c41e40c82090a40c2041c0200688512080b00700b40d02030820f41c2d20114203e84040110340300d1401c0549403e28580ca0f181080740c4401c0104000c40800c1355141d20801002c1d800c100c0306c000b404030b487c0c0101c802000b10901140300e20981d4000c80001400d200100105100d02c03455608544069030b005c5961622440028180585504802c00c0040046650905a58601e01a100b4294159207886040d5241d8009030798600c200c1141f540d1045000c4002140d117031258105941052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 754808758 1250 754807508 754807541
    0x61a12120a02151e1f0302040b0d1b15021c0c020d0b0108010c17070c0809060c070902030a0e06010b0f13030b0915070e0102060f090f0a080a090f050112 67
    0x2004100c644072040007903d00386540e11028032a020408020503d0340d800c5110a030b4917082d403840684d904040e503145031102920407540c509140309281c1701c1030f1aa410741c9a104a05c80400d1111006001c3c000c0c5950060090507220451400c5044e07000003071450f00700754484a200c0249000d42000c581660600600300e03000b40900c0b1a440018800c562014060001e41e07002051406410500805661003030814450703c0f610001880207a0750000c1850f14081d0b005501e065541c00340c0804100c0e24400c4403280030f898032400030f0009005416902560040c15034400078080208000c00c41aa1500280244407100d2010003034040b02c9007404006001200a01040c0c80740c030f40da252074228407050104c075100081e411020034103000c4081d104496a2010181c180030314540e6103500002c0d550300005000200c881c0781c0101280c9039100400100304250061411505c454006240400c07941d048a4070090110704100408100310039480d1000b401d85106030341d4411544d900a03034000150035460b030740c4080e64 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 754810008 1250 754808758 754808773
    0xb07060c1407030201020c15130b0a1e2406081603110403030c060522030311090d050a06051b072a0902040302030c030a0515100b0304061a12120a02 65
    0xc0721014080d00105000b9000181c4407984051403a0a05240d4000c8410044003181000f01c09041042c015082c00d0b00058680380070354446454000030b04418242440802c401203254100d8402c6030030240482c1c1c0391082403e00750290411000f041003141c00743d2008903181400141500c0603000008081303086600c2c010074072000031211454580c1c00768000b07400042121429109021440c01440e03005051200402540c58100b485c14410740b00031b480046c20107864a103242c4041620f4000e403003010304001d044021070900b46c1741155441074444c1044640c0c1d41400c00180701c90303000b40c940e81c03001413403000301300d2409043c0d6a8103040c10a42480202d8074410381d40e0000e01050308042180060440c8000041c0d031103007075004051174003c0c82d103c0c0034400ea1140c1c5d8640c000501c0440c40e588801c07000460075200303481f9600c0c0c42002ca02d554014180c5c0c50320120400041c000c06400079140c60b032400c1b10224000110400303200000415080d450180d9210040c1f82c00703000741d400010321020070700d0310640740c45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 754811258 1250 754810008 754810037
    0xc070812060405090f07091a03010c0504060206091515061902061506161b030609080d05011d0103031817010609060501230a05040513090606050a0b07060c 68
    0x80e030000c036200c0c00255111000c000090030039106103504110b4a1000303100ca501c0085219036201d5480c01010181a140e62800c241c00c5200328140c0040b40c0300500a12070a00203400c020440e41281c4182c00040c483c0e0f8020403048840800c00c03000e801c10482000c0e90300d64074220740100911052007080d0b0816400c0114042c05d452220040c0e95450040c1e0240c03a10b41041c4403075107264003407407441070710864040209403c5c5c0c60b40010054070440d032042c141040e1012510b20401c0c0d6030032940c030103003505041006180412580e0002016070352a003507410412640c8a08000c41c411080c590109505805da0005102103030096044841050140d5505081903898003820034030681c180454100c580c0d1268810711031a0340350f000c1e01c805441c00713280c8010440049100120b400101d0101003440c801c001820f00c0700207116174100c4d005440c01a1503030ba140e1508120000040401e8041508d11610307100c0040742d0703481d00c0d800c4402205d074411242c908003112900e42c10000c01100030000180444006071001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 754812508 1250 754811258 754811273
    0x4030809060306012f06180717070806010906091118130f0c09090f0209031b030106090c0507060c0806030a110a120804150f05120907031b08190b0f0c07 67
    0x210001c0c0040300717000140419105103080005000070401d03210207040300041c80c1002540301d0403550035101d40d13071701c3c24210f1010314145402900314090600540001154004a0b40c00290454104a00410560740c031489040c10501480050071040000002d604c112860f14000d81d0200004190700003448c42c050028160071503a407004c200000c00d0407120100103d0000c0d2084e452030b010010415460480010f0020380c55051581d07000d5101c5030780341041c0c0c5113520300754001805802100810813075501e134400e010b400bd4000e004101d40c41410302258405403481075590300d0080a0180040015410551b208000554480066500001545000a1035007002c001071144240203440b555911400c00f09455500c4178ad4541550900560382c154524003540300044a491541000705000300d500d45146140c20712000303074405841c1c5049000c5000203002c4442000080b03450207000c46942201031030500003a207018000c06808101d5a90020b0350140d2844aaa0360060740380c48120b00c0c0c2a400c2d502c001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 754813758 1250 754812508 754812557
    0x90f0310060810060302030c12030d18060c0c0b0714121602190206120c0d0e030c0d02070e061005161104180b07050d0207080c010b10050403080906030601 68
    0x100050700c481d820070003150103101d1000b03094500d600038801c03a4110740110303956140040c200d0f401048503040310980c0c40018000d40d80050071a24060111030030460010303030002031995054407020300e080042d00442d40151054100d480d8000600411662260020741d18a05820b0b1480384000040144a050740443c100e0688501c00600d001c2d6510071000358000d203000043c22140320030b20400c00c032400141c2d691500752015034200c0340f40c031001540c074499948001c0c01903010481c000c0341041b81c103150403800407010b40105540c11048a6000300100d0b012695403440e441717901c0d04604d07943d0218103542810407404003178190710300707149107440c490012810300188044c40903a0050355030040b209040c9010b019206010400e100b18030021100307622100d064400c083c0100c01030010024000c1070000507074040e50505504081055195080e101140c1e001e8006620b0300f600c15209d24a2649083e40118240c50175250005007190400810005104030360380040e0486045c0022462102d41c0b9080305641d10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 754815008 1250 754813758 754813783
    0xb0f010f080a022a0304170303072304050909102f090111030a09031b0602030307120e15090106091509090204021b0c030f0616080606071a180c010e0402090f03 70
    0x865480346841c0201c280b47e800844442255001002403090150b400a1944140c41d00703949a0034034500701c980c00c808d291040e0b511487d08507010204000c2101808180030004c41e1a41c0e000f40400f00701900071005031079008402c1c100c541d882c42c1422101021100241c03007040c2c018100041e60360b81c2607080d6850741c5c10090603000000c5a01c0070034810040c0d00031440d00406006101400114184003000e5224080101001e0404c0035542c0b012040700300903046281450042d0080d613580c0140d2484440a01c0c000b25110125582082000501e00c038140c4140c0d046452010410b042813402c2c16080405000c0c40d440690380a60280712303011100075100301d0040c5c81c0040c0401000030341d02501c0ed160401c1c1c1e62410301802500038800700200358503441044660b000399454110282d95610000821500039007102601c1caa1100038a0351030420036190b03650090310f041c03064841d46014640701503030b2500700381806800a110726690361031608042d000f400c10418024440d10a044206010900d0007880c01c442 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 754816258 1250 754815008 754815013
    0x1209041128020c060d0506040f0c020a02120c060405120705040513021003060605030c0a17270703201c1226010b031f090b0f010f080a022a 61
    0x444040c84035018950705a000c1c140003030400c4900b0307140061914025062a1103110341c4800000304166110390000000c8a0040c1c020030406002d000c00a5890644820881c0510001901480f0327844000581d002154801058a481c2c241000140841121700c1d030300340a1300d4410380b00302140982c0c41e40503003881180c0002e010241212507004010500e40102048401d06103050000c0c000c5680c05011281d12202907410656551440c1008981201d04101e0030609600c5401c1400b000400043c900d036041e03c40d5540281100700c0b002c810540340c0166200044c5043c41e500c2401c40341a00040f082d421545e8000c1c01003010852035088408046000b00341100c1e0015255111520150041401000c00e00c115030000c1061010441080c26000c040c00342c2c0c4180c0310080009120242035400d100c0c1080c40c0c4680c3e040f0341c03d0352202c208004d0070720700560602c41c05c1c40c0115443c2651190481351102c007115500d0308400e441e00d2161071300030f510035400c2c1b02500303600b031011220f041d00c07440c0c81e20841a0882d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 754817508 1250 754816258 754816297
    0x11715090d1e0f0f020a1a011d13030c02012d0306121104110f0c030a02012003150a0b0406020618120a080712090f020114040812090411 60
    0x8005240030b804030361800010480103000d441190307000c0340300e80201010741006030000804c40e070140d180030300304031000784401e002e00ca032820211a44000107040f0b0b42c100f00300c2c0c81178640982d42020803c6003142c000091310b607014a801d02180c881d14000c060035006040058140004007149902000000001245650000c1502242c140c0c14407500c4010321810441104003021540c8180452250285091003161244842041c1080d0ba42c2240c10f40c83d4841081d40d5144403d500030750310798001e401c4050240d480c114119140da1800103a11190000d0707004cd062665039921109959004860302e200c1d08000d51140205945005600410103845103400410991178001e654032aa040b401d0400071858000d45282c4080c1441c00054901070791340c1d410440c005542d620400c55080f00c4030341c011420a0300b0134600d6414000802d000d680300a0003030381c0340950711840c2e080d4400300c0d200340c2c0300799503150703100c2c0d40c03154898407607880a0121410f005201091003040300c48080829000718045400c618034851 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 754818758 1250 754817508 754817533
    0x7050a0602090f2e0f020d2607170a090b0f0403090e0a09060e0f0601060f02010b1305042a180e01050702010c020706090815060d0f03030c0306080708030301171509 72
    0x10744c01c001c0040c0603c3d240b1560b2080e214002d40b600d4401c1210824401040004c809501c5581c603d0f41c4203000e509414002d51812180041801e0b0710042002d4240e0130385404900418401d02801500c80c3c0c00c1101c2e460a0f4507a241c0306181190001c00030b500b000b030701a40121f008143c0c2c038541405680350303000218154810381440d0b000c9621018804101c3d5000d00200d000404010814a0442d140c50624156071440d5040a9016210a20034554800209551b08004141c9a48a10300aa00881840c01e000d01c8941b4820301c89401003040042000c1038120820520405521407020074803552000703e08000c0381540741d400c1d17075015138854025075107034824507084d40d07410000d020007008945803210b03c0d00d103041c40b550b41710008031180700c518121b10b10010709513403514110b244d02160701000840c180101030400800a00741090a02c000030b040100c00510741c580014804251000314001d14a0350746850414014030020f01c02c4640385000e0101450034100c3d80c0500c052007462181d0140005644a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 754820008 1250 754818758 754818829
    0x80d05040b06130218040504050a080d06060f0f17060112020c0c01022503020904081603020f06060a1404020d150b0901080a091e0c15030e0705030307050a0602090f 72
    0x28042c0c43ea283c810f1250005014428414103502001901c00041710b4550307080090a201d41e10202400b030340300003d800c0c030284180d80e00000440301035030f44920b1040e03620101114581b20300054600081d42e90501407411511b5111000c0e00700c03c05041520f4070122180c0404240d80100403059200e03000041f007611596018418000c0e516400c259480601d480014800350548950001074020105880014200410b01d8110b95500440261a81000780c2d54070303009503900084020310b00b49010300c00c003007035117414980180820703120317120600002803c0c1182480000d400141c0c160080303d40360030107460f4801d48a01448040e101d074142c1c07070350f54801d41d00016000140140017400300a1400b41c144000c628908084446c40240d055040d8501c0707a2030820800c3c1400316000a98151030250f58045002d80691080f5507001001c030942d031511b5552401c158580c0142440a0300740c4e000b100f105800915580c0c01020f0601d0014048203041440c01c001c41e60100070b98541c40810001d8100030821410340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 754821258 1250 754820008 754820029
    0x5070203090603010308030c04170f07062118060c170c18090a0f0c0c0b06030307230a0609110f03070b0f3414030421080d05040b06 58
    0xa0000314504021030000c14402e1005100140080c407020020801219012048900400700c01d4418a010100c040c3e0880e2101490b43e4803100c2c92140c0344d4000b072404e00510840c0382080e20f007058000c045440c002c0d00b030041e180e1408030301c1090f041a106200007519500c20710403031101c1a41c030f4000c5030b01c0200500c0e00c0c94001034802500e8490500402500c5d00ca02010079107400303000e90740401c89442d000308a0000e000340b8003031500541d00789070401d14490340c448041f40764035018100c04425a19003e0900d038480c400d448014000c01503010130403084400e4601d407102c0d1169600d04465003560303191114003c5410f24034007140d80900c0101c01c03040d60310340a540b0a043c0c100031000380c85054540380340308040f44501f01a69038140c501140c1d40341d45040c09400026500c07500c40f80710717254400041550701544102c040071582070301c0e2041c1d040005540001610240c90301c04030420b07943d0319100c17241640600300740000c0310311f101d0400442070507500c01d00809008030702c20200c0a10130300b800070810078071803503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 754822508 1250 754821258 754821271
    0xc0a05060114030a06090201052124100f09090e160501170a1a120a120c11060f040b0c010e010615090311150f090406050103090503030402040509160b090405 69
    0xc01d09918220f030b5008501072001950010000404507014030040c2c8a6010b00c0350348080c8101d03442c6400c007a00c4da040484a1040108446800405200004074030342d003803030103807916000346c1507031a0b40312928018280011030408a081c01c039031484c0c1e140080002e0b0b03459400400225009201103103140801c5641c80f070042d21017400c0c001243c000c10000b0703454503100140b601c2c04464803010139013001c0c00e40d07802009236880080c1c11640b00c00b4811512035515000f4200031604802c0304071013021a20700c6464603001c17030b55000161910340e440f5001000002c3e00100111076810204110004041500c43c0003801c1c3c060042c00042000000783c2465030846440d41e10110300d5020559400c0215a849032100c030070740390b1006803600400841d202140d01d0034064951040000f1002600c42c40055032400030b499450720444060041e11b448100441c266000040002e200d64400d04c089070040c6001d402442e807180200b0111a40401c01207210898200386a120710900100040c1000460030280203442e8845c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 754823758 1250 754822508 754822529
    0x80a1805060f03280903020a1a01050a0e061f0807022a040e030c03040f18060e01120224120c040501080103023102030108061302150a030902060c0a050601 68
    0x81c1032074060364503407000504007452041842031600f0b4401d014401403d6503800c0003800c00080540c0d11b0040d5a40401c0b10702540c010402010051121818480b140c1c180d40c80034003002100f51411400c040b600394040c10803a8440c040c46c603542c2d09040d03040e81c1101a9491a50b4a41e0142820000681440c218500103e00c548841e10b0482200d42e0007090618080802d80740025110480040d9074254011a24906258000060001038481d5a40c144c00146d80c41035034010301c155a001c02d140101c8440f8480c0710b04400f0b000c001000a002e03441c0ea04205c1600160000e1084003159400102d0070a2130603030544a6540890b006124400c5003840070b902002001c420b52806040100103010158140b000901c40d0a98003045035200018160390a10400407910307400c00303086c000c500e40c0d010b50000d018074240c0340b04000000d03904c1c1079508000300e1000d4014181c0100746903146901041c5520000707000007456120134601d00180c0310b1000a00720300c894040a04400c03240c03460694140b01d8180c0c003641265 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 754825008 1250 754823758 754823767
    0x3080603010b0f010f0207030c0f170319141c050a0c3912210c0c150b09040803390d0b1207030606051012020c0703080a180506 56
    0x7a210240c101c81994400d00b0800d089910888041f407500704240c04c001e101028401000540b058050b1082c030503102c2c2c10039810004502e8801d40f555034010b18000600400d104090111241d029602c00003805001e00c4030f503460030030241e94000c184040302c90031a003407960301d00410100e105188240d0329510364600d4156203810b05603200400525044018800250840d4601900000710f0101702e1304099011500110050749514003401c1032a840322400391a07c9591000c581d010b00912950f4158011920b55612026550b15510a010070601104101941c1c2c1c1c4200c170515600e103a10300d48100c3c8110342c295075a180203003001a00414181210801c0c058030540b07104121410101074202c0c00c112464207880700340e80030480d005082010902c036041401c415403c1483c1c3c0000c0791400c1568064401401000c0e5100d06000c43c3d4805c4405038000100c0b0700796100301001040d0020001c1c444504201c0b800b41e5180c0e00c1c2c0100c5a800200c00c000481d209082c960842500c0004880c01030204490031170031f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 754826258 1250 754825008 754825031
    0x41e03290c04030c1403010902030d02300d090c17010204050f2b080412050f0706020c0303094b06070f0602070302010e07060513050609031e030d180308060301 70
    0x150400b8010503010720317071208900c00503450962000c40000d4004003120172810b01c9040103511092040c480c184041b00712140d101c014104000403201c45c40c0701c400b401e458460040340c00d0004040242c1c0865150300c02c028002100340950f0441c22481c0c00c900c00042e0f88602d440c00300f207850049182428041d481c2600c100c200000c83d120380d1540303c50650300035001c180c860f20300307405c01c3d01c1b91b03805c0342d000d940c0000901c0c8207002000619a01c908015402c403548661075850503030740d40c0f0440241c250706070300800c1072411070708000540710510b40401d588090f915400d9080890280d5417003040460301d68070506a984401084800c8140445003901c0380b5207044400e490b400d500744541da0010b0041900002d2440030036100b54015020148220141e0340c13001d464410013403055000480002d44c0360380f50031740441e40b450503000302ca41c1440700400901b1810345948c01c0350408041503214140500052110408100103170140d0f40c214481c0402c0307038190700c4007494003030262000946207500070380c0742041c2b1075030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 754827508 1250 754826258 754826273
    0x3010c0504031211070b041d01030b070c050703050106060507120f0917030d0606030507020f120403030f12090303091218141311070605011208041e03290c0403 70
    0x940303801c415501441d02c05031001307540d06070f821004414203104040c3c0000c1e04950340c8000d44156444c056400c01029010801404880f20070b0002802c28400070011600c10b501524100300340714400d030b0650b00700c0b540c1da4480303030700f1227141c0d500070404920001024000c02400c2405101c070200e01e4180081007140d580c0f4018040304c124010280705c0800c540181c420010200141d070302244407880144841519140f00401408055078200094465005c1c1c0b00c031034580100b154451041c0e0840d529040c1841c540302140c80b00001e0400780103200420100c02144075480c02241c41041c06a1804640e0f01d000e8a400000348104070400010403444030302c00040c141c070604184003128000e800503c1c0c0c030715100340011000404040040b843c1d40c60161814a0410313100090400300780608000c100031717070ba01c41000314010381c007074801840100108800d00c10451b169203a0076044448000303500c5501d445e5601c58014026980d0b8121010594113003060029442001c000d41c448035408040d800c0038516640d542 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 754828758 1250 754827508 754827517
    0x51e07020601060f0e13060e0912070b18060112150b0607030e0301150f030c0b030f0403050c0a0c0308072d0605040218130512031e090a08131403010c05 67
    0x38104052005014a418810f80584a071788078010508010b090001c1c1c0008010203107403140c1c0c40c1c8130b500c14000504203a001304040003003003591342815151010f40d5882110b58140100846210400da0760050240141000b81c140a0240b04800340c4103580c0c50709000c100c10943c003040708003442c280100c80049489510544503004d6140c10000c000d88610b8000a0142c28014038080304c0d0003058030001129000121000112400b4406250720300d03460700311112072848211030700044204500082000248120300a01000c0200410340380c600e2180d41d130b1441246135580c42580c0080d4003191a5007402074005c01c01a400741040d800300300d60100c1d030348070303204010b00d40c40c2c0074040540da203000a0941d01c40d00340166413101c0d550b0000c4c03800d140150158166070042d4005441e90711a400741102c0800f050300469005a524060054500c40b09514000042100402c1d402480c0100707580c000c0080e40c0c07040a085004401c1d021038480e0350402080c2c1560710040e4022904c079a04211000d02055000f20407074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 754830008 1250 754828758 754828769
    0xa140115060e120a08031f0f060509010809072102030c04050907050d150207030507031101110301052e051806070b0a0b03210a1d03060a0e0a0b0901051e07020601 71
    0x204905008280d00e500341382c8114405410600004108950031400403443d82000e0407519041e0222610f980d50b80b0780000d0076004001c085401000003004660003030869036402501d980072100f509840e0182c0b140c45002800903920322200110300041185414000000d141c507060f1000c01440c41c1c0f04400542c3d44101e8850f190003942c000038480c0901c80d980705010085500305206554490852400401c2e40c0c1c010281034001410700110070b07241d00e038107005030f4100700380c1104000c1c1142d003007100b00300d0a03021000316181c1c00750010200200c410f40c0c100070240021180c1c1c5a450b11400f102100b00c0c0c03500d1005500a106180c100070010004425101080e002010800005210f04184000c240f030074414061603082d00540c8000300c545518050010011151141d944d032200420611410400155680b01a585500000c000440046969200c181c8450181080301c0421405864280e0510710940d10403400344d4442d0104054104146d80701804031010108c3c0c0b40b80d6160810b0001e481e8281806107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 754831258 1250 754830008 754830019
    0x60302040f211403090a120302011b0f14220305010b0d05190c0e160e010507150519020409020403020306071e03050c0d02030c12101802031003050a140115060e 70
    0x3e042000d2000c0050391a041e50180940f82c0c20380c3ca400e2002c1c0119002c082c00c600660074203950305444405207002500b084201c2d1243c01c80022800015298010031210300c001418040c01001c0c0381080c84202c46010b069401c5102c82c51030300b9814640c0c2581c2c075070300820b8018034040c410103002444c0000c96000014500201c0b01468082c0d2800089d00701c00c1e94400f8141104407400c1c45903074145081180b80341d14440e210541221500801075815028601000e4012010810081c8517280e081d009203612810003c0120800d10049404074100d8009802c00d00b010b581c049404d02c03c48c1010445960402c80c503003815020820b1685204105140b80380d1000205a1201c010440041c03007042036034030103200014255202d141c03044012006030488656200456001d501163b5001c1c41249079800b41c07060580d81c90b8400500c0d4088101030b43c00a402444e00c000300c42000004a0000d02c844070708980307d110141d81c0c5038124940c0e14256480c0c1104030080108205042041c1034111107030755040ca8007a5807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 754832508 1250 754831258 754831283
    0x30105010507022815081e01031203060512070f050f0603060613080615040c091a0a110f0601050a060e06090d020402070f0b0612010213050904050f07060302040f21 72
    0x4d030303000d00f440441c0301d41d10b58100210000c2800c00d0a040c60302c4a0030f046544410729542d41d9442592100f100c1e003003102d0f001e42408010310105117803203010707181c5541e94180407440d00d58407000f1460366082c115184015401661060001096480a981c0140000c50307002d0300742d2041d50000f4450b440301905151052800040eaa24115001c45081c1c1c01000b1420a5a203245441c540460050135043d410034411882d007505080c03024003c0c09143c0540703650003c48096500200c00308501540310111110074080380044004e55144100001309440d9074134800b03040f0951402040c022a2400d68000009014016040240d907844d06010368030840b8044445100f00101c80c00800c00030703c500e001c0501002510011102401415940d030303401139406849114100c010f10340014203d016a42501d050800441c40400c803a2516944040d046805a000c2e80d02000c21007268615100306540014042600400c0800542007200d401b100104005d0b0182000d614200d0180060400d1040d40140780808031130 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 754833758 1250 754832508 754832539
    0x90e010b033108040302090a182d320a1203110d0b090703020c03030406110c03040602060718060516030e060a020c1306030506070c060f181703010501050702 69
    0x80c02c01d4003400e0014804404845500306242c20758082d010a902a1841c2030104460b400c00d48100350140b1554030305103440c4081c5030344c0d60030a030f0a4140100c0c4031088c0302060340c0c00800340000340c0c8002445001d11051881a2a440151030070411008201004000a0381010018003250300d1401070f0388120fa400b040500700c0802d1300100032414445442c12400724540c140e40a081d404400886000c6840c0036a070344d00c0c0501102607201e5068060315a80040c40460300080864010641584d2003c56850510045040b0185513800542c0458016400030050240c9250031004103d07000301c241a190320700c0303803c101d000b400718030682495a81b120180d4000d40213040c4940f005407a448001004141e42e882d5183c402075a40c09550040e9104544e03100d115141c0740c5480c03003a00c041303e6002e40136112958a1000985801181200548503a81c440880f04803180340340c415400c80402c04403103403042c81a2030416012404541c020b0340c0c19510100014804c40e038000058a0700c00f98121181e503041d16145 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 754835008 1250 754833758 754833811
    0x809190c060507081c0c0206150a0b0c030c0f030417030313030f030f0f02090a0e10030f031803060e1009110402160c08030306090a0b10080a021902030307090e010b03 73
    0x41018055541150b500d4852031455904100784038186c560850f921a200c0c103180001d03600c03407982c00580c403860200c02000340310380000c003800304101800c080d1f0307050a09100140f420403211040402a61300005400e00021811412040400748030308021400c51802030f418040c07407900d03484090140300710604a16899486504140c40c1003002120903c00850407240070760180d0014241c5900c41d031003040012a5600c1801c0c2c10a02c80c01a40f10b480e840c1c146982c4811300541d0841005a08010655943c041900910807190009510039000010400001a041c605080c00e0340908403143e800c19500a020034821107e107091003208440040c0d641e2509400b001c540040e18400400c03107404003000003960940800594450300782614000800d0752001d0b80101124400c882ca25400142c13482d10f0740c4024410725407154032a4008000601e002642500d50180b031000d00e10401c01030b070000081011b001c1c1e0000318a00104070180f8101500e5040072094002c500000b0400b0010424004c03007100810000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 754836258 1250 754835008 754835017
    0x50612040203250603060806060a05010f050403140703110913032a06021305180a0203070c08190f030225030203072301140f061e0604060809190c06050708 68
    0x1a035001c0c003160f0140c24080d080304014410800401c0c905500014074010202e903032442140001d10040340350b400d02c0e00540d410800030441c501040070500011000606075102543e82206a10007040e64614610f4881080c1d81580d15403401215901c0500100041007a2140642d5500d410302040225510300e04418510000003101c0540030554001c0052160b60780c010108046551000c080080d03c80e030510148008450b10b111114a5090000714202066800795801c51400d00d01044040700301d840b28242c80e08008240c2c421080c42c400203121454000c002d1041ca60f100c0d00f001c1d800c0c110a0004008230304105d0300100e0407102c0418031101094402d00485d61a203034000b032044809000c5000c1c028000d40031025021a9620f004550120b4a0040305036600c240003400307140f6041e4ac0d5590500c1500c0c10844c04082040d80d43c1d034048106641e4000142c4003815035603860307540078501245000d1504000c208800c04402c000302c540d402144d003020380b0380162500e03410f1413036036210f05241c2980c45201c2c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 754837508 1250 754836258 754836283
    0x319021603080103021f0807230c03030f0a060b07080c0109080408061e01210201140f070c0b0307050906161b080d0207181805030313021801050612040203 68
    0x2009450502050741041c80a4140c034001da8100940c0300b201d9024807075032040c071b0000502003003440f40021a05449500308508481c0703441803001200510341d10f81c090580000c0000c151540003c0f041010580c000da40b0711b031344620501c5043c4005464a01c00d000c00c0c0c8143c6901400e110400a8180c4000d4800d401c80f01c0c4d030b5940800746603921a506c101054440d18103481e908112442c968a8503840d1038501c2916040e01c0c20b250702c46e01d61030b192201011585106000803070502c980e40b0b4902c22460880c502500c420300d05100196620049803415000180b0107400c5990216010310501a1041d030103000e0f5440e0601c00e94100e81d843c0c1444c00e000080101704880101300303503004144880045002d46082c4c040f00c3c2100100e840c041c484c00803d0381ca407501c1c0c1c01101401e0350b40d06080488081070740c014400e9031038842c0c4044003d802d039445081c25a801190000c0d01c2d036074a060b202c011403c1210300c81d003000b05100211542d40d414400020854441d15181c0210389014502240541d503051040061303441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 754838758 1250 754837508 754837537
    0x5040c0501112d0709020a0203090915030f0606041112040b1e151203091005030a06081e0705010203070b0705030c04080109142a091b0f09040501050a0b031902 70
    0x21008000c0c2441d01c1858910b00f90342c0640f8000056101141c004d0f00c80050041d00034508110b00c07003003480850300c0001c0002c580516182922480358500388000c21a6403050400703011142f500c0b500744019240c1c0400004020801040086e00c402e494410340c6400c16413200d0300d10403540382c02c0c1c0700c48241c2c01605401c41e049560b103004e000310030010a111013854a025982c0403150140700c5001d5450340942a020341c2c0110410071501c008910582c002c542c85072900d20b00180207074440e035907249005600c0540850303000101c44c0303e4050701410010500100024030007140b40c00019940c9012041000d01924144071000c404034469030140000c0c0c4005c0d20340c00c1c0003048041070701d0600d1003042c0300d010940790f1a8019841c661039011140c0302c5654804411740c6100503011802010f200e0044001440300c035010700040e4016806d43c1800b001058440c50509086485486142c100811107406a028a208403c4100b04100c1500d40303c058a074400c51200d4950b040740070042d845d03406441640380500954 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 754840008 1250 754838758 754838803
    0x50f0f0f0a0c0302071706040b090f1b09010e0405030d0b2403040303050609130213020403050d02210414060901030f06121407211b06090602010f05040c050111 70
    0x86511070b4250512500982c02c07a80f10303036925201319102101d0711300300d414980c10240c0003030089943c1440454104070b42008503922081204446030915807900e11090050120681c1c0c1040d92800c010003074090400040410f00c582802e55070349503203101d00b0041c81c40c0306880f004140c60940d540110300201e1601245903100a103c6440301104513881103804074082031411003c1140350070420303140351107a0300000b05c040c4900307180d07020865003580304c1b110508415004c00002c00040e6082c094510118401c0d00140003030400c1d610040039440c00b01a91510b444424041004410302c02c01d140745110074141da104d50307103c00840c0124043c0c0300406005082e141444c2c0001007504001802c0c825140c05400b4a010880250405a840c0c41c440c2c410700308600850360080c0c0014000c40c4050041ca031250031004216031800d5884001a141d81e40030f1004581003a808014894080c050310120000402040102745400d41c1d8040d540745103406806e04112401440d2054050104803e0b0b2075140c1518800300704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 754841258 1250 754840008 754840027
    0xf0e070e04052a21070501031d070801140f060d0b07120c051e2d0d060e061e220b030714011404030803010909080403020d0b0103051606050f0f0f 64
    0x2400c00c40c014141c06844c12400d41049881c0d01a2200c8012910700060040646040011806008919822501081d288038200e00500e42002118001c24400c400030403001714404985051060003442003020100c8041000b0983da56094001c80c0380d90301060410154903844400c6414000c139810503050280380c1a01101d1032504680601850f1100442c0034019032a14120700b011401460308c940b1420100a00d5080401000c0e481400c070720b41c0e403001c60350414040e01114001d540c007a60200c0d0000090a0501442d410210403500340341102040c203880710f2003a1004100310880010780361410030354500d00320307807a0b08142d040071140c504020300700d584451f1500850700c1040c0303004002070301140d0502c10318204010000207880c21240c2000105003540c2c43c065141014003400142182c1e003401c100704c0440140c1d039401d131143d0802c0c000c204d4404151b0443c0741240ca041c07010080c01da460104520208046540541211000c1c00c0107808c20780c480104000b2007a00703000303209481c015000e02040c11600c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 754842508 1250 754841258 754841323
    0x180703110702060307020a02090a090512070215040306090c14010e0d1412220608130807080f0702090109050105060906090307260c01030c0f030e0a150207060f0e070e0405 75
    0xc1d503072300894001103191640f12000f0203d03901940028502d8000d00765070112800170100bd41103a900142c840d030b1030760b0300005034058298015001114016a601040c01c144403c400030140074140010403402020b4280001030600c811200710180b0030303480c401c426020411060b41c1010480d003828201c9a490390444072000301a004911540c600c0350f490440410924040c484400272200d1a031103440d0580c45141a8403101130501205448401c0c0400180c40040c0b24400100510182c0e03c1c1495124209481000018001079222403a160b08000c0188003d41e5904202c400f141d01c1110036581d500d070080c020078142a829884002e58950041003000e041c0040400345646101c8035094941d07004a600c0150308860382c54040c60001201c00d80c89281ca14000c0d4855142054100100d40c0c0d004519941c3c2c54403142c5c5a00c2c5d50041035000300d0b14a0411503140030303600c2c100380a0b903024446084865111542c500103403080941c00c25107030010900b8464140a8006071000c40c400300005039110703645610 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 754843758 1250 754842508 754842523
    0x30c021c020102100203040c330503180f03180d0204141f0e010504020703021f0608010b0904021e0604080a030503071704020d080c0708250518070311070206030702 72
    0xb8003501480f40c100214901a1003240d105d660b00245043c0910b08003601400000b454881341d80c020100048407030a6842440302141034002550b81f1940d0f20310301120b5140707051400021203441603100e1010880d50a6003c003d6070340c3c4c544140285440c451040002039128040701c140070350880d1804132401d445503500343c0180d1048050501c51000c45000c881c4110301b0ed55544074141041c90070703000600282c5000d40040c25024080e20481c2e805920000300e03c2816220800c1c02410380360758a00c20002d86000703020b40541c584040b034104919107003a80125502002c80074030812668080c5641c280a82e6900d405d48001e07207421003c840e816411442c0160080d40706850340c201007155400b461f90a040c10403032091055a0141c141c415828080d56403d103241c01c02c55441049006008000c81c4144082003543c1441d0700350840d10b1001102540a68480852500124010188c1c141a1060078528008140d0011480d15000900f0110100b01075080e0080060081d4802c900105111f1119400074524 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 754845008 1250 754843758 754843763
    0x170901023c18090709030605010b040b0f0d020c03040b0c1e030d05150310140c030105100c0204060e0c03090d020c010905190e1807060212040b07030c021c 68
    0x910200a14a6a400030000c4000021070081225280700140301000005040c10596002e41c0348240d10760b01d400982d10180031621200042c0c01e0950800a011543c020240180800307000d040c070300f90402501c284039124006081000500000e40598106001e604490101d006034050760b440315100e00000700c075940a13030107044443c8540c5d030401e1580b540c0c2d80700414a010f0040c1c021450501014440006003e0003400b594820483c2c0c20003401c01d44050203070700441d5203000c1d80000d00c01600d21098100a00207000301c042000244014081611412121915241c0c83d017071025007020148000340150080383c00424030700d00c070b0405110424401e80040c5001d82000000c1d26070300100c1e45d82c1241d903050310a200300d000a9001c0c3c030411844c14000c1003d44400900c080d00e005a940b110048402031009a074207140b07201005000e1880b00d2824800c61002d46034510203441130041d88244654075005a0040138000c2070009140d00803d4043c01000b650f03103a001d801000c100182c043c001c03c507d001032106 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 754846258 1250 754845008 754845037
    0xc120a0306090209180405011409300702010c0804091a03060f06011209050708010903050c0609150a0b12070b090a0f0f060302070302030f0c0d090602061005040b0117090102 76
    0x1050182e01c0c2d0003503920714070f00076209080800f4810000c400c00b040c0a070059816560b100301203441e14400340d031160f00c02c0c1c4200e002040e0891800003180600c01042210301c0c0c40305601403e510840c41260700301c9912a409107040052080a410000c400b8070656000c4171040e072400c540d40d988030000c4030b04104140e10403400e8844540e42c500703122140400072a2010f00080c1032482e01e215400761030784000707405070040c800c6599081d10345600c142150f1a204040c0c0200b480070440c84525242048032a1780003009001401c42c0c44505a00f5280208025010317001c00340c1c0314102030400703445841c0c940c1160700070a8221303040166140c29140303c40e88550b1030940100d14805001c40c4101c540c4442100725803007010400401490180e04500a4000610440440c0820800c24505468038400b03828550501001340245010f483d001401d0982d01d40d20a00564004904201540c00098503210848002f5240411241c0c0c2010040307400055a090610100b1816400e201d03803203605501612035129020301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 754847508 1250 754846258 754846271
    0x150114040606050a020703060f0e011e1503050d051b06040b012105030f0a170c0a17060d0f02030f030f0301080601080f0304141c12021b0d02060c030c120a03 69
    0x4680d14880e150703075513015074080c040400c002080c641c0507a24000501c0300002d1450811000f0a080d103c1c001c400407464041c7c2c1d00747c0c1d140c00e039580c070912614020a50507641480e1465803100d8903408030b5582c2d581400000b042c801c1c2442101581403480b41240c50565146160920f4981020741003070003402600c000561500720041e000910710816203401100941c00c1c140190a11000c983c40f144c0c1c0101007100c29001e00c0344000000c140d460240c41a40c07500c54483c603000c43e000744000d100440c40d1302c01c41e60312401c0c82401d803101d111602e64290009100c200812090021900d002041c03410203c03107100014032840d40098800145046c1e40d07205e030565200b07913a0345013030720b6485080b01d01100c4503800400c000c002410403082c0c0ba010200020740030701801c10700c12030504440c003131100003aa00d500f0000e803029102503040c051001050542510680c00200c203102040d0802242e42d0000d024640001d20031001400402c19516440c2900c4105c8407401015540c44802e03030400a03081022030704000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 754848758 1250 754847508 754847519
    0x4090212010603200309331f17070e07030903081003033612030806090f0705070206091002010e0706081e0612061006090b1810021501140406 62
    0xd13a48a00050340020360b00c02c0408a8402030a034805003141145200f108070898212400e84404032080d00b51000e414a40d079007107403010030903039401454241d64031103204031003581c400460300320300a8895014024580040c5000402d03d400140c3c0c1041d1403030869401002841d91b4180c201481d140c0c844d50f0b60090980301c400c00a00501d109010040205103141000c210321800c445c003843c100d41580700e000007040240c0c0001e0605491503000b94490301001c04011080c9900030341904c2d0000350540d82640f4524194155a1401030050084800c001c3d000404a0555030b8041c181c8441c440000c04d00c4004020342a0080d0080009443c0c2c00d489020b0103d000078024040c845c046e20801c14031001d054074004400030b5411201f8010000c551241c035002080071320750001c104c094460007a004c411014942014005041c034216a48070000c032220030014201c80c0e488038034100e0350007442a500c1e140d400e8110907003a81004080f80114060184001c000030701a0040d43c00180350801c1030351308000071034482 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 754850008 1250 754848758 754848761
    0xf030905010f1e1808031b042606060a0e10050913020906030613290411010e100e040f02090d050a170301050f090c0f12090f010c080a050603011104090212010603 71
    0xc0501c04c0051440300c50b003c00d80c404000c40d84080b011f022082c2029616000c0c0107160402d410542161400c5c01441880580151041a183d40000c004219a141c00740000b9501190f60064442c02100b41000ca0b240380720b00302d8400080c201c002d00c100480e241034030008075440110b1100381d224600c19000728145040110f0550b020b4550110040403030249074a8500c0c5844042508552800c1c190030b6548c81d00280d002c2c1c40b03020310b100b40d10192019258400041c203c004511225100305e450b00b54080401d50480c0a85681c0b003c2030744e0110b070200c604e546c200000d000300320800f6042050b4581c0d0404102011030011406442401280b9502400c640501a0390209001c0c81e50484010018200d0600e01001415030200022802d40c1c40c03c1074040e12a19030360030201003d4514030a2a0901c11000b50911501d180302c02c2e03010003004400b001390b0000b400c12802030140c5e001c0313030f5462011451130744081d00301c210a42103d6081540c1c1c2c0744d580c00e52100a502170b50600d07413144251030003c68018401d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 754851258 1250 754850008 754850021
    0xf030c030c19030c0b06030a080a0e010801050f011706120f060405150412051819030b0c07031e030f1104050103051005030601170f060c130603110a0f030905010f1e 72
    0x151381d2400313500e41c59038902540c84406044d00768580300300181030f030001d8a20b0313008040444c03040ea0355141c18032080c070001d08001810303049580b00e00b1100c0c20898450340d0125520005402140e40c0c0b1000c2e8440a0210b5021100c0e03002040e25030007072a5009004a00015405e405544660120f406205030081d20540d24081654010f08101c03103401101e02e4207116002500620b03071800c1d19584849602c2000610192900c0315032003d0002d195410000c3c00720303002046901c0711600340c1c000d281c44021382d8000c0242000c0106040280c602c403c0000301d440c800c2d804800310720328150741004010001d224620381504613108070b900082c100b400040c050382c1c600300e15034201e940103001040b0356402d1062152064050401b41c40040c4140814003200c100e0400000d401007500d500300c942e07280c4c0e651030b001044640c0c98000c1c1d800d240c14090404081c00b000b80840d4102201c0c1e00d0201c9038a105400210050540322101034034940c00c02410444642c0e042d400b0203680a625a1120140700e0018488030994a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 754852508 1250 754851258 754851263
    0xe01090b0607060b13150602010c030e0303181606021c020309030c09060f06040e0718061e1202130807060c0803010513020f03090c09101410020f030c030c19 69
    0x40900007200000c0f060f401922015800400440420080b0040301c03044035100c40d40410440e04003c000c020300368080c0b107402d000c0405480c0922090314021207044d0782e03100103003007001c40442c807508018500300c00b446611200b210000b907645446544040003555940181c424072118003608130740358005400001110300f0544080d0107003d10140340d008000c46841c0081200d41c00c608070305480e0381d140d40d6900c001c01c00340444800c0c8031668241040014020b540d41c10464a060415000a121440d08501d1442582c3e4014890911444400e0f0003111099000074540780310030300120342070071251482c400400a45e0b008500301c448843e500d100450b50000407050260002c1c0c810001400309080100482e20b41c00720040d0098500a00c4a5145c0c0003540222440080758002000b00707215071078840c041a030080829071404200c1414031000c0c24500c0c03212025a440380d0b494494143c10f02d8003c2c8000000030000000f0f5070307202c1c40280304c140d032030358400300c042c10060085800c0109880d0038a02490b002c0fa8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 754853758 1250 754852508 754852519
    0x30f010506030405100e030c0316050c040203010302031513022d0a061b0804051f080a020712031805010c0e01120c0c08180409080c0114220f0503030c040e01090b 71
    0x12008428005180200e0020341c07d000800a1101c0180c0410007070418002d0100c43c1850b00d4000d01b0b0050030400c3d000781051050340104010800340e54001100300940801540c0d1207119140c100c009074142c4d40ca00f030020342102144400301880d88900040b8004218460700c81a054840801041040300c1c2c280070b00380c003054241c1c036000c1482411030764440001c3c4c8160010380ca00f03600e8400140500d0180701c2400ca20100e071009401c2440da000140a070040c0301b1a00550074400c0c80e60360410750200c04c01134203040507a5003406500d002e40703042281c5c0049420100800680725503405c020818084010380e280401c05020089030009100c0c0f00d200500c075296500c0d2042140c942d9100540c0d0b43c0001400d500d080d0504c081842503680d14854030080ca4030409591307580792003181006080d50421904100c05c040c0060422505541c42c001e1010441a4503011003051201490001b51001c141c1d6030103071141c803001c410403a8140c0848000e00541d07009128244182ea62003065400360340ea8030780c01c9038120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 754855008 1250 754853758 754853773
    0x302130906050f240d080705030a090f0506090d110904030201020d0e0a050a0209190204090902270106050c0313080606010305060a08101104050418020f0609011b0503120c030f010506030405 83
    0x2446130000102c42e02070000c1c81c0410b110740740d446520484e04040001e8509070000148200c03aaa045041180103219400303040c54902c3c5401c000661074000c038081c460154591550341e03001c0201189220202c0d00b8020036100c0c0605084c04d00038000d4000700c00030b410765482c05420034045d400000d01d00e001243d11400401070680603900344000840050f00740c2c072502c20051140c1c0c451b00103d0000d003010300b011a10004806032180104074040d52103294019130401907096400352400c0c0405040c5c15605281010b07a41c035000d1440b040e00c0c61280681d000c5102404040226030f00c103000c01c0040c000c1d0b2090b60b0138440713610360b41c040002141c924440c0c6001c81c1d01c042c0c40c00c0c074020000d03046001c1008007041d0117030510b96250046410381e84a040c0000081005010140c110b1809028241403118282d5034241000bc0d01740010b8a03400c1004081c03160441092a95000c001c0c0c00c000701c61004042c04d0204485081c0030071b441c04c89400950303403001061036003400803816046c04030650780308a80240052802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 754856115 1107 754855008 754855051
    0xc0806070806150306120c04020703020303010906050402031e1003060c020c03010510180e1626030f0d1823070503010b180702070302130906050f 64
    0x3c0780001402d0107100c0003440d015a58000b1060f1400407503030780402074039850880a2040d141c0d2050000485508056000c00558121080c6801c2401807507210340410083e80070844503e8030000224000103000c0542500b566008420450742c40c0c81c0d02d46175145c51041d140701144160140e0b200b00c81403184d030b0900b4821203520040d0b00f14550800ca0401040700a41c00590084031400c07515040721a40d210802c0c015080c400a4881c5401040c80d03176100541c10782d5107041c003c003002c1c02d186486c548142e0303808030441d034040603a00f402c54034040079600300600800303e507510700e0b4600d010b0800304000196105400791004e440c400343c21140c040d207026400d182c00540c0d004240240d041c403403650504d4032490340c0c2100d0481540404d600b1551680f004929000403640040d5200d0351140641018161346d0703100440d01c42c000c0c01e0a21032940e840b020740c008254140c903003010340500070620008 = true := by decide +kernel

theorem cover : BRFrame.Cov 754676258 754856115 := by
  have h0 := BRFrame.cov_init 754676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 754676258 ≤ n) (h2 : n < 754856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
