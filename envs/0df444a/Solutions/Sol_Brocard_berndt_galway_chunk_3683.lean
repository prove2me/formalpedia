-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3683
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:22:51.032877+00:00
-- url     : https://prove2.me/submissions/0c72ca4c-d600-4a33-b7eb-c81b01a629c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 662230215 ≤ n < 662410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 662231465 1250 662230215 662230241
    0x41a040e030903030c1005010902190e042c0114040c0b0c0a150b120d0503060d02040e0106030809100201050402240c1209032103060d020a08030319061d0c09030a0501 73
    0xc0510100700106d50081c2c80c0103226004081d4281003086030141800c800c908142c1050092008481d0003a0f06c454121088140000d4250102d4410b01c003614101c00d08100c2c0c0382140307540392072615000c00040022190040750443c480300b80e40ca0900240100d03e40c0094217204943c8552500500010107004806105600d84800400c200d00048140046030211300c048401d2900f124174400301c1d15500c5010f4039170110007150252006000b81c004035008041c0351008004035401e14002105000f9902c0c01444d0741941910907501480c841e07102203080b03604c00c0e14001d40c40341450640134901e020011300c1d995020810300306a840c10754451580c81c64078140c00502445020042205015890180301121403040d108444e11311002d24010041e006200091080788641040548541551100c0070f40c0310240040c0b1045a80e00d0411010065040c6c03212060045010305003400807030310701744480c00c60b03c07503c5401e8110b81850300c941e40e4069803a04440752042d01071144c0c020046c0420024081c543d450b03998 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 662232715 1250 662231465 662231473
    0x60c010e2b020d030c050906120619120b071e0909050c0c2d0a0c03020301361e03030204240c06050601021005010311010905041a040e030903030c 64
    0x16419400707001c51404401c007450041091507060503004103850945848500e00080c64101c101c070240c909001d0b40b41074541003d80850640b9403403035940204c03402003808590110883c482d45070a20340074240d43c0076014441d80c042401078001501700740100c0d005600750078a00602696030704e1903034080c205045a4400180c0542040100c481244201c5400c000200c185924002a68030442e950303002d501c0c21180c0010428102c10004e80f071203030400c0480004078040d1403004203542003c2d600083d4a0105038400d500c4e0800c860500340d1084882e0320076080d444a03441000814025229041320703085020b883e40800e9611011600a00f03040d18188284640c81c01070f1203506100041030391441021403007100111361400b5024142d0030601c084001a40b01401007400e42c1e51400403800c01c0e4101184418032410b103000441000301c1091074090400c82a0380f40320280b81d035282084203483c04400419604880a0004051414203821181110110004aa20b08888070002c240365501c5014600c000d900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 662233965 1250 662232715 662232733
    0x20d0602070f1707110a0501090311061905040f090207020a0909020d060f0f0605030f060105120c130b0f0f090c0903151e010806041502030a150e0709050607110d02060c010e 76
    0xc581c1c01130880fa0717481a240e040d80a801c0c10000f8125851501011704035171410100d016007662800b04403428540500c4602d864a0728088005d0029045070107048a0410402d00200b98040c035442564000303074004020716030b0346141141030001810301c035000341d81221258482c0e2001c640c481c0107881c10b0781c01c401070005468100c85045070494002c2e0700124400d03000b4034070040c0f514900090040c15030760112109000042e212691a04d450000041e29406c000c0f81d00260860244541c001d80340301c00107466041d024001e1404020400542d03440b010b85c040d081c0408905400e00c00c001400c1481000b500f103d40d0010703928106031040ca01200d00c1c002d0010100384071400c290403040c415004000110040060b0b0074956158807602020b00411401d041d40403000629000302c503040986810802d80003a50700c507448124020300d0030340442d00440814a40c10001a13036050902c102c6510a800c41041c401b600380701c10810170050415503060ba400034090041c00202d01080c410440d108200c01c0c02812166 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 662235215 1250 662233965 662233973
    0x60e0712090b010b0a021c020c04050c0a02100b040b060f041d0906060d0c0b1605060c070503180409080c0d020c040902130914070e0a051003020d0602070f1707 70
    0x90350980506064200350321140050407040502e4103440524849940313451807940100d18102201c030018002ca018000300c0107807550046041d00c010302d4280c2c1c0c14000d41ea20040c003030b03c09100380d0035000016408480d4030385c81491540e0012043c004010004501d0781130079400100590443c0090703151520b400901004141100054442481081410b40c40c0d2890020b03a44c545070039004100c18002d204001d610800c21003c43d00d00d601404200f66100c0e26218426a10b0540780c462600841d502d00c00c0e14003140b510868001922000d0798481d0003185480384100c1d030015200c2c1c03030310301e440d4020340c0700c801c0c842c0015001d20140441c861602c00400420305178040081c0b400801070ba40d075004618000d40040580c40d58028443e0510402c9004280366409103010f2410800b08030000b02c950042400102e0035254200e00d9502403c643c0605111070b4445840e000003100c0f651100940c400740d42240b010004501d40c0240071214010341e44d045000700380303888103880d0304103803ca41140503a000030080200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 662236465 1250 662235215 662235227
    0x6060809010b09040503040311040b0406080102070b01080f0c06180901182004030615030510020c12041d07050d090c0305010f05190f020d0603050115061107050906010210060e07 78
    0x180c0350856003003843e42004c0d100e55850b407059000c05803640500703100d602804d480d15000884058000b0b401002010b07503c8181c18001d411851048800318501000014a84000251100303100f907110041c0c008503030f035103042000e03951041d80305604034141140c00c03001a0340c030031520500803c0d5440440908206c02c46025049528803c2c000d40d031240c0081071000e44040140a982c10340c0e0b804000000c0903a0241c442d2303c10350441e6480108a071040f921125046500c9401400f0000300f0581261807840d158031042d8214000d90140d603803140b442145d85c83c03e060984071926003060260902a1a04c400c414000c400e540c1c600320155a211a00c10081041290910440b582514444010030203030500f03a0302c4403107150140620000c6d0f01e0710381100002c0384000e41d04454807860070b00403c01159540b854a14060850507644040300100340c500066506d01a9003041380000307035070015010060900040001088019205a045100310295885012a5440b90401426000402141130300e0400302c01405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 662237715 1250 662236465 662236481
    0x93c0c0f1d091906090302211c060b0f1b0f1c020a020a060e03011e050403020705010206090604170f2802010204300804120b0f2509090606080901 64
    0x1040c1e1000599115002c103c1d004807002c150b00020100d51300c0141d040807840c20f589058441c808094440300c03030340c5001c003040040030503078650359052050944455200007103e4061290020fa44810841c40c411036078400028406000900420030407101074150b070b646003040160702c0320030a070b00c20030781e2041111000e441da01211010344000c101034071851b4045502014944120400e0100c1c2d84250505a50290065140a110900139480c0b40c1000d0a00c3c4014010549082d07015000304c0d40c01149030751010411602c9818581d0061109881d2659070301481003201d100c00741407281c140560506255102c2c000e04550310440d03200001c038004141000b2030700f520710000c407040d60300c10081044802c1c241401000380000303492002404a1000404405250803054000d00300c220004002c151500c0c4030520311802406046000d26690340d10307119900305141610f0407140020070310703540241c2600c0b40300c100c41d1714440380c0780416400340d60300140300941f8840c1c1c0040d4089440c0f0020441c140d6401d120b0001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 662238965 1250 662237715 662237731
    0x30903100911040c030227090105043812030903070e06010c140c03011d07061d0f1305180c24030a0b1003093c0c0f1d 52
    0x40401e2640d41c0d456001546144503d009503110004281007900a6050303c9034440e01c1c80c00c56240060b1000705d80c10301c89803828070602c5410104000305450a16120b0711034100e4000d0408900c0903c00840e00e11218110b4000217000f841003006540c01b0385411004207151204200190f440d90030030310070182043c0640d041410510080d0701004030980c0d01404a01e81180c000124a501243c8210224188560401d00d190150f0804007650300078401d0085401640103840e040e2417640f619154201c1d07104a0b0442004490401c160306007a6030300e0003c0e41c08940e1031f0003c1014405d040866035901c1614030482e0078260f07030160048039070000941800010310580c0700300d44d03403042d140b0079402c002080302c0c0355201d5040f0081c0100c00101c00e102958040064000014030f03000c03003c9400c50000700030707244031700080f81c80c00e4034408403583d0b021310703214400d0408003401c0b2052013502d112607030602600041001511604158103002800419404110380904600e01a03400240140c042c01000d418014150003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 662240215 1250 662238965 662238971
    0xd0206060306070c140706090614190503061309050f07120203070e18010509060a0609140c030a0605190e07020601030c0312090e27010b0612040f0b0903090310 70
    0x40d169901060031540001c072802e04048403071481c01d006102c828034102d1396000f0304c1280c2020441e590443c0d0304030211007003030346c41c010500000203d43e455030143c0c102c124110302580e8401c1c0345860041009e95807100e809081c1454041c1c100d482e4900740d629901003a01c29401510a40c20901c400f80000806400081c0c0300d03404e803c0b03c1b503011039501d20b081c0c0b0950f20300d54600d0300800d0303081011040c0703600c0302052807000b0300803410888a080c1d00c900f4150303014a40189054000511910303540228140b0509603490f0520b40e54441c000350b00d0540c0014180106a076503610041f9440c1d6448071480d103600300d211090703403440341083c4e00e4940200c4d01810781010365201000410000c0ea8030f5000b0001d403907000550000101a043d41a11100065084041e490130386c002002103011030f84402d805401e004980900110315164685400c1310410030b0700d580c1103041002a00701404a1090343c6030003e22406c1100c8503000c6c1d90301d4200001d28240c80d1007000d40c00015a03c0010701d81004404400000000d0030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 662241465 1250 662240215 662240221
    0x6050c0c06161d060301090e210909180607120b1c0b070c0f0f030509120a12110712020a0b03101e14090703090b090d110706081b070c060801080d0206 66
    0x520300c5d0005114035403110b502c0701940c0c640300e031040c04030303090b030030b110303401070000e00d000c1c601203241982248128600984103000000c00d007502000384140c0e09803004015000715211110100c0d00c94110110b10a40c2980701c0384158042c2d201c0045080d002c8140b40e440b50000394061402c10324400028005904012070080141d02040420185004441c0d200c82341c0107540c4a1440c0c152001d015402c0c980d0350200302c940d40342d14007620200703001c510a0701c1400c800a100140f1270043d103a0602d60684003030140d21a0a050214503400c101c2d83c7c0980e40024080d58040e950303041e10071000e9008403811601144910010170091510303c02d1080e2401c480b080703403010282400d501e1407a505401c4082449088a1004146030f14000e61245d0306540d048000c401d06444c141000301d82d03400006000030009a0032001c03510740b1800104206040e2405540c0f610100d0b1600c0a0942036880c0050558032008010070021000455004d50140144050f40380d0700600e62402900b0750034500742c4940d00056400000030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 662242715 1250 662241465 662241469
    0x1f120f051006120b09100806390c03070503041502070320060904090305180402071208060303370507020f24030405010b090709030f06050c0c06161d 65
    0x14041510b02034580300881c900584100405495240c080700e8004c810842440070a10080c014042a200c0d0074040310fa00351201c40c180d600f080803204075440d01d40700b0062855845146001403a184031880b10701913013002c085001c1c07542076a00041080b569540002010404165400780041440c0800c4c0090708580d4959203914800c2403072100004e01601d540c6118103003c1da00c40e4190340c03a003400684200f010460300e00c1e000e010b9170301000081000f120010001c0b80c6034030385170084036903ca90143d10045000340016050341d00b0f01c801b40590f80d050106000348030840c48000e40d82001c080101c182181d4405940000c42181d0002c181000704010b810414080541c50b0030030b40c030701174010540e46540100e400d10b000d201d80e40749a4200c440419000400e101c00e210054000c0c0d0421401107540000d42d0700e651105840750b01061000400007001d038445840819025030001f80d012a50500780c46c5070000c00c4942c86d051a40845000002d03918031041844801c9d0300408803000080c012110314591440c1b840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 662243965 1250 662242715 662242741
    0x1140307020307230a050a020301180c1403030c0d081609032003120403050c090c070c120503090a06080a0501090507140f04090c11011404030c111f120f05 68
    0x10081c0048550056110340010062504e402c00c409010503105400400e14101d83c8484091400b6442907003001051304e0316004802c0c4090390380ea805011440c03c149003048079003c1500140030382c0d1b8903000030f00020003046024440140341040719540c1345802d250011751031000a010044090407c540030340305000280c20003550b1260202c000201e6550b0b09060030000e49044251070f5082078550002c10000108407000850400f00102214103003290390f20507502c41c0b07890040d000090f003c045410410001c0c00c00346a000c0900a000c0d0301528544944103010540160043d441a000200b01c442044a00d0400b4800e15014205810b024007a42c10b045100a1507202094064181494000b44545660030717410300315002130207a0328080c0903920740401d010740101100e40c2d094a440d400d00302400c1c610400700e071000380300c0c6516440307900e00c981403921240052242c529035190010b01000021140e64210041c4000450007039948089603014072081c013080d105481c00d4000304130f00340401d010340b00c41200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 662245215 1250 662243965 662243977
    0x4050105010b070209041b0b0f0d0e011a0108040c0e040b04020f01111b06130b1306020601180e0a0213052403190503040b0a0507060b030c150a0201060b18011403070203 74
    0x603402d6041002c2c242c0d40e000b0b0510340740d000d40c2c8c4450000403202207000194002e4400c128110b5020046450b00c40b0505090360319504144007500e40e02031642c1c0039980210039964208d40502040700400c1d8890786000005901601c0c02d41701030780500208011494034401030000344000b8600207485181107440196600911954814403040600c5000c4494070749070160f4140702050180341001c182c4d01e0801e40c80c20740c02000c180c41440f55240c400700b103483c00012f019049031403c87c013030346940d00e10340d108000801c0074100d1030102e402888007030b0300941d82d010a01200c00d240e1b04400603246c10082803a01500155072810b64410718040c14440721594041001800e44c45000034800c0c05c0001850401c1c00c520841d0840c1030120b20116216412950100140c00b03800c1c841c5404010480c002e104150751405500344aa52100003101180344100042016150314446400040f40240d121800075a10382c02c18401c4408070950385e045150b036903900000342c540003007010882620318208950000d480e80310304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 662246465 1250 662245215 662245223
    0x90b07030c0c0606030f02011e080604050a0902040e0d03050105030705090c0d060f03080a08010e0903180a090f0207110105090607030e030a14010f05090304050105040509090106030c0e04050105010b07020904 91
    0xd4159049182d004a60388a04540c1c0107600300601c903201d1601040c40d140c0000d059000038103900e04e6110758244034148101e032900ea5200c00020b035907840304001c003500000740741c10122034407601d4150041c0c40707030700503030311484200d0300903110821b120b580003412034405178002442075010f40c1d010007068585205968000c3e0f5000103455550008003003e201401907544800c01d901315100d000024814000003802641c80b590755985516603a4194004241405803004419904200800d84100820001301d10f10080050803622101c3d588101c003404850000ca40c103004590005410420890192050303010794809003000307810080e000000c80d41c540a100802410312816590f03503001070383c0070401d54544903445001902d28050000c8000e0184c140e241035038003080d080c1004210b1081d00401518241e07201a5120b0303007054989000c11001160252200b01e1a55840d00003001241903404030070044d000780305044071a0700f454035089084030b10503071000449002c240003000c010f075221a806a049900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 662247715 1250 662246465 662246471
    0x90203060a12051c050a1d041508010b0102010b030109030804200603012607051309032102120c071110021c0f090e040c061b0f0507030c0603090b0703 66
    0x3850010590301100c5070000ea00c180d6019000e5810040300060314044500403420154440d0704819040c1c445019000c0c3e01004100c401154103a0b5a521586000b0301c0c01d4010004500b001126070305298400490300260410394640040556550302401040034200302074000704030083ea60b4800500002002d40010b00315060760411220448190907090780c0040014960b942e42c0d65900b018046180d45c0030900e20241d01c203000e640c6800403010402b0801c4441c0901000300c09e2007410340c00c3c4010010500f00305c0520076204072951020450880707518210306520300c010b9440070024919000000e0003011000180d000300407100000ea01d040007d820900c00350390b01d40042c8084001a07042011002d8000034a40f240360044007401d40c083c05040740c5080b140c8801120948980c900302000404450140102c404800304000380c03481580c05a0517000f504141c01c0c0e0246a131396605041500e550320665095100030703070500610403600260320040105080030400902a603482c21031680b002004101031583d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 662248965 1250 662247715 662247721
    0x110c010e01021c1206120c0b0913051305011508030405040f02090603040c0311040c020312040201020a15050106200c01030b031e013312030c020603040501050a0f06050a090203 77
    0x4000c0049640ca001e804648100e0f94544020044c14070481958a120241c20100002003400c503072141420b07490303004440c07081d074613041c4050004144e0200c00c000390003a02500544c5440325061003074034001c20072035044d440c2c0942e0718101b0b00d0179034400e0383c010020303411460010000140c0000441c0c08641c0117940101d2401c0c01511448024050340040329000840001013100308040c800c140c006581c0305a458520850000003404210b40c0e81044500140c0d0040040e11215081d000707900d0361107841441115141c003030903a91140181c070440c1d041200c44d512400140003e980010038014540c071105450000c00c02406031007a83c42c5460350001d07041c5a03803103003680241d880601000000044021606031004c600b00112802480d034482502c0122002a0040884a4440c0c0d14203400024000709070140f9800e050030764200b000c2c40c1004506011083c03400c84016110203025512440c0100000103107898003d81807020742d01c1510a1000c841e00d000014400e40e9610036800d8240d134050240142c07656 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 662250215 1250 662248965 662248967
    0x280203071208090f0303070c080f0910020d0f030c0801032603010b0d06120201050418020d05040309150e1f051303050a1a0906040303020a02100509010c020d110c010e01 74
    0x4420204003030075151a070340c200400c094104620601075820401103d40c0c644014844c5500d900050322000d00085d940071850020a00075400b030324040541c02d040b14a010748110000392110030103074180c0d015803c40344244240caa0040011045030250381000d0000c2410150003c00850050000070102c506c2c0c0d00d00ca180101074114020702400c910f0000d42d44e80c1d6103500e0039a4060b04200301c00c115581c05e1100110b01c1d84008400320025a506031075180c1440d0800805070041e03180704440c1c42031039500348001c082d500024001c2a0149009481d080c1403681015480410320702441d02541c140000100e00107840e4403000b003007583c12042c66584101c0c0c11304011084560384944000ca90011422100200500130041010714496100b5050381c4503008031100c14001d5014221000c07240c0d13401220014000c41e0103500200140b4200340b05480d0315001c0c0f00c2c03003e0111041a11482116991450340d001940d80400c6081c10307100702401d0103c200100c02001e2590360381d4480e00d15041000c6800e01ca0728a03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 662251465 1250 662250215 662250217
    0x609061214061516050606120106050d170708030c0702270a020307020a050304080607090503190303020a17040b010611010e071203140403210906020c040527061b280203 74
    0x383c48000382e003502130114181240d4400c02915054070480c00d110008000c22814400c010840e040546404000700560f2501d070704041c0e00000b4080b04050802c090710002d00c0d90030040d445855415441a100d001030300500103070001d05203500740c480203a050030030035242611072450f900004044003d6030300c2d51080c2040b4241407203030000810500c804a004a50303080c01040c06440ba901039616455803a50720401c141c7e40d200d210b4024049940343e00c182c0e5001c03d00c240c00a20111310721741404011440920307800d80c0304080c03c0390300342d4903100b0110041c0310465001c90011426a800c400a1000001c1414659112081c51186024400c0b80d48004c40405008094102040000e120500e07150340d5a42031400c0454245940c0c50080454014400003040c001c01100c829244a58010442480c00000344001803901520088005c10741a14000340400001e0301d400d00f000200006e004141410380c004d014060514902c017400075002e02440c0f290040b451003028103c10131009868042d44018003c0e415 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 662252715 1250 662251465 662251477
    0x30612011803021c03060f0605130e01140102010e0606010905040207020a12080a110a03121d1213050f030a0b18010f060302130608030f09040608010606090612140615 73
    0x11101c0d69540d000149500824032134500e000304078030000900a588411012074440d4042c0b400c503200016010302002d071103240909006e11310510049010790700c3d50088840304001741e2243e2800d01444030100e0a03560b0a0041c00d0710603100d14010300007410315500207070100c5164003407280695070100748a0150342d18070754000014285902c1d010301d50f8031076040c0352503070394800542000802e680d0186069003400c0009c040050b15096681d0665016001c1c1c00103018150359413000d0810039040101e404480d00a2000c41d86641a022440e6a46e07803440200a4003079206502c01ca1040859840300101c6450109a503c000740d4040420792155954070011030703c40900e12880d00c1c0a42c80c040850035442115407051054034022161803601c44045012101652494000c03040590814403041071482c040d2400b034030314540001e002151b200e4894880c01c0c02c61341d56600c180001864114200704a071341206036405440c072008070a0002507014400ea112200c009440d450050380e00c103c031101144458819545 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 662253965 1250 662252715 662252741
    0xe010c0609080409050915060d030302222709050a02041e1103010512010c0905120a0b09060610170408030c0705010c02060103020f030d021e030f030a060f0e070503061201 75
    0x91500d0300ca403030303507001000200ea0850382c1d4451140c0041280c0c41004c00103108000049c021304040c0201c1d83c04901a41124001d10b210011f0311001050602c0c1c0d440d9240040d2111510b480304050700c1e2450840200307007000c82c481c003c80ca010381c0000411400300f05038110907010b940c041070808030300641c803035805404444002802e207401814004c0b800840c000718104c48040340d4500603880412601b50807100c542021002049140d8000c200505040c00e907801072199010a80b040200b413a2240d406860040310481c416030415820090145030200c0ca184107841c02d89042d40c08150405180140c0c502c02a002801900010001400040400e01110b40307656004000340a148070002010703545140a0004922410b00e048452445050000c0c140c000300c01c4990040c010040f5001500b0801c03813103640701d240c3c6d50008010490301d20034a040154003451341c1800009142d850801d14800c00a880e812a031403c88803001405141c9074020103981d000042110098230507a06200150300601c400e40781c0070307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 662255215 1250 662253965 662253967
    0x606030c080c070c0e010f061403012105030f210112050703150f020c0f010b0108160e040213080d0206010801051b1602040510051203070228050901150f09060e010c060908 75
    0x411850b51304a428030864234943c54403107900402c0104020140800d00400300c2400304000385100c0202c0c00e000c62940785024006a03890140c252000c0800c1ea440044007919460300c803410002c20700710303c80544d030041c015180e0408407925190b5450380c41d11018403000d41451907103041d20024480e80d50002020f850303030090031503503030100068043d20303120b042900f0b100e01d510340440c00d078295000d014154815481610448d01032030102000b5111481c0002580b500300383c0c00d0140c10b0368000640d26110241c10840b0003080304e800c24000091a084058205007540d904102c240022080c04e5040c0c8480c490804048649950101890401482000002a6001e8100b8040c480d4008000403c507043d10300c180e40303100180d2a900407482e524403c600700250071054840c0811805d0f1907007100105072034005000064120741e1800001c034035203400e8210799a00220034204140d41c6401220140d040501030400220180c60075102400c11100300c44624107122150200302c08100e8030354014032049620038009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 662256465 1250 662255215 662255219
    0x50c040b0607121817060f150d06020d0f02030919021e0d02040903050a0306052d220b010f0e030d110f0304080a0c06110309040b0a08011a040606030c080c070c0e01 72
    0x703c00f5070f0300301039031550b00e0b000e9071b40442c0c01c80642c8030b040ba1050840e1126882c0c1440070740e0a200c0c6d8001031100654080b81d09105200280105016191070381032058005600c90070906201414260035900802400d00041480f60050300c0b400c120765100c0e10450360b04201540d015020503542039400500035489443c064135030040603008005041800010750f0100180f50b15101800703004510206007420704003420144c0f280600150305070301c1e80614003030104c501100344580d00340003498005000c03004160b2151054440b83d603225402c408482410325200603482c0e0208082500c40034442c4140e070400c030400c646143e0592080240d290b55403034031012669501d982d082180d8541042c00d00c11a400c01500d88000707a103610501d00380c80c80b101c002e0051886c00755a40308100040088400035500070300341000000b0107600078800d04e8000c8100344480440040c1110070001119603940000040c075150003c00022242c1c808280c95210210391a245e0341c800c41c6081890103c146644581d1030100101c0c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 662257715 1250 662256465 662256479
    0x11090a0f0504051b0a0e15040b0a0605030114040506091303051c27150903020c0901080c19080a0201080a1d10050705120c210a020403050c040b06071218 67
    0x4003118044594035001c4040000d0300c10040c20017014820480301c00c03000300100d0001591011003a647c903800910005120780500040f440603242d0358440e0003c5203000c0010000c20f03003004c5440c01c0d250821501003202d440c200000440549000e88038500c0b10414400c0c8000709030151084522480240035080c91030b8020030b10802c0170f8038911840300078400d9892040000a03c064250b840507075401300d1710001c01906030304210010001804150304500c1a1f82c54010140c0f40c0700c5840340a0990300001c2c018015958043c8101c0c08490303103202074502034450040019041c0400c15510b071341e50902c1c100485407074500310000a090b50403140c0c1c8491140e1480425018000078518000107065030050140e23a5965406403114061600c0d00404252034100107005004034000510014590303482030008240d5580004151032000c540044410341d0000e420320520000300030b030329440001290305007c8102d40b2408210a4082c82c9002005102e002d0501c044040c06220f04896020f9040b0400300c042da07403000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 662258965 1250 662257715 662257723
    0x3071a04060306081917090a0b0a0e2b030e1203030906071e0804021809070602010f1b1803151506030c0c1403040506070c0f0602070311090a0f050405 66
    0x2007030401092422034000703251032010131812102d802004011502020548483c04082c240c4003400d010203a0800c0340420310703600c2e41e213424058001842900d0300d030720511001502e806c8044103180e20900c00c02083ca02c8001400c10f03544842c01c2e1008001188106614080d11915000030410364840b8003034035a041201e80010207540320360842c00842d03510ba110394101342e8185280e0341400f440d1502601506071440d0240102c140c000c0d1014112010280b600141d0800c0c40300c0c2070310030803d150410a0208482d41d1309001d421241d142c881400c00841c0241c003c032139a00031192034150240041a69020b14038060320300120011a08410005007030590301240e54000d0040c20b159401800c0f0002c00490024401c2c0b0031803401d64415180c410108880e42c4690803059061100d8071401e2000b0400412280c44a8000c5c0c003046104000e480b6425050881d400c01404090b08041d0443d400036004001107080300c104103601c3c3d401030710303c50001e480c1c800c2401c02801c41241001e1000d8102f6003070004100c4005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 662260215 1250 662258965 662258969
    0x30503071209120c0323060f040213020c0309090703110304030206061314130c0f0303020f060108010216060903032c071502120c070f06080a05011212030b03071a04 72
    0x165920042c1c0da2121511003903100c40c501c025140c0740b01c164040c00010b0f4200d58420f2004035014001b01d011403803524003031401c003003107074540000100d01c411710003141440400c182030742c13044110540c10042500b000d90356a0050540c820b1103007944401007080c0e54081ea00801c004003041e88541d0340d900d01410081d56502058400d00e008250700c0a400d1402e0185104520fa40c407204004c030340003920341010021022500c51825103030301445003c0014940c5075184008001c5100c1d40180210344420a101360505105900001459004100c3c1c180d080c00d40203902c0d061558408400034006084c2c1c2400c800502c0c90800d0200203619490b03207682c107c0b03405c0042c190010104400c0318186503d501c101c4c1c0000c41c19401d0440945d12802da024440e0850001400e46034898100300c804065403085683c00181c1c281d8000404103016200744002d550090154078003504030803800d20072078981079552401c01c0c90928181c0e410160782e407994025942d03080c03103000010101d610030215045110740382010294054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 662261465 1250 662260215 662260217
    0x90108060d020a06082a0d0c03110301060f080c030402030d0f0203070b070804021e0f040e03090a030b0f090607050a1d0a090e010b040612021504151d180712060305030712 75
    0x7007034006c1120786000141d600d5040c40140983d0600038980c81003009443d064030303043d0601d80c0701c5603c01542c44901e0055030082985a5601d01d0390041c0c0c480290800c00080d000c130600708410001c00015071800105151550001c4c40c02012035215040105d0541c00740c410024540560041406a41a444940075004e40c0c0202c407680503805540745040da4403100748403215048021582c00e080c0342d150503400151142c2502c400c4d41e1501000d04005200012103800891702c8480340010b1140002c21041d49540c801010350007071090342400e5a000e81140226000907003001002614404508503034101c103004008050303c0c1051090720b41510f50054920910813000342d6183c8008100305103014040c000846010390782e4201c0c1d0f402c5540030b100c510b000c0d140700c6034082c580811000070302000910342588010126907a08010102120f4410241d803a1507080a2117040a01000c0d9007a607102c04035641c0001c5641020803400c8503007011a03002d40f101d0303403001c0e00a01010a101c4144440b94540220805d11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 662262715 1250 662261465 662261491
    0x9070b210f0412030504050c061e040f170313030f0c080f0709050702030a2a0210051306140a0c03021f1a030f190c270507020f03090108060d020a0608 66
    0x140403002c50484404560150081c4c2c001c8400c83c9807130278000018407131401c0e201ca4007003822010700707032400c210707802603000407000c0d428140c08100151143c80c0319080c80141c140a58505074684002501c0d81d007060102814180218940f40e0404c1103400c2e5500050805005650007254440400c030f407209030a20407910700c1800c01c800a0b100901c0401101c0111b45140c540c4010010b030401600e51440c9508103e00342000c2d4101c0d00001750341c80c00d4100000e0342c5181e070b51a64500d0076502e9019000403560101c0140305100000400c034990039402e85000405600e0043c041c03101a0904a01e020010080c455040e2000344507184440d0b21600000807050300400d01b00c2040c0d0401050665a02015a9110498000032264100d0301d0100d1280064607006a0107210700b00d0311480988600207200c410f090640046100510b0b08880e240a000d50040c284e002421110010b285419264030604040038100b011081c009011980c2d100b00e80c0b0700c401e4010380301030241521a2009071620f9020742d500c0c181514 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 662263965 1250 662262715 662262743
    0xf0506040516080a03050904060e091b0a051e0d0c080c030601170a021002010e1209010318030e060a020a17090118060c080906090301090605100e09070b210f04 70
    0x841c0b4074070b4044403890030042c100342c1c1c0552022201500090303507080e4004d40f034410000b4409001c041c0b85000b01452000f80080401c034840341c41e821241d0094580c000c0c16514410000b036034485400845034404440c80400027070200d400a03010440d01140140501205071000c44c0c48840000d240e400742ca420f40407a01684d0304c2d0b0b07000091201583c84800306650142d09540c00605003481003110345074a900000c50080c018482e21424606181c0c95401040c0c00400d0300e014940c0e040c00b0301c0b0410980d10001910545981e02c1c02000e001801ca0010300404000520002c018400c11030106000e400c40070203256a02100d4414180354044481035000860500d01652003004030700580c4125115a19040c251a030f580e50744003041e4100011055021900b0300c01e20500340c50078081c000c0c5461041100142a28020910b07006400d6503800a1041101041c00c001c40413034001070754401e443c40100c04a84074250b41080a080d40050215042e20103598006d001c48000c01d04105800f4034401c24041840310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 662265215 1250 662263965 662263993
    0x15010305160e10060e03030d05070e010f081501033c0c05030f190b030d020a0b1005010e0f150d0c2a1205040504110d11121f030f05060405 61
    0x70000c2e140444403940200c0100191401440840390482c5d0180c107a0341060342d80c044640807944212851000705a141e02d44100e1036038801400100980c00342024551400c042c1d0240c2848021014003e041c503a4488a4903003004a9140f10b03c16000d4200c0b1005803c01803040004621318000005408141800b003041342d0580078000b2b6920a40280070030f22125070755104401c441c4003a030489103240c50355074015100340e518140200c20703070300a02c0d800408503818289400344c603405004180090760140c9081c00e012582c0e00000d61030010340116442074018003d08006240e0413551021f200c890007000130040d00c040f01e0b0f0781009104299030f0325803079142c3d0516006000e8080030400341c024091128900000098403103090251700034694034000d0b041c0f90f16100410f04031440010300b03190601000c0b0743c11142c0069800f8a9000c0c051425980b81421020084401518005030883da180140c0521884220a180e00540003c5801a00b203900b03c03049420480d40710f020594050b9524014014004844 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 662266465 1250 662265215 662265239
    0xc0d15170a02101b0209040b06010e0f1c110405160906020309010912031205180708030f1c0f09080406030c14180415090c0f081603020c1501030516 65
    0x81600501100c03c11100000c0894050481120544012001401d19409612004081841248110700c40304d00e500386180050640407132041500c1c41441c101c440701000782c5903800010000290701000341d281d81e00030b10b06007108842e030303250383c5410a15100c104003101d00490040071030303c240758540740000d03174a8820407a00e80c4a903420304d80c08564092000c100c2510440c0c010b02d1080d02a1034a58640440c080691081d0745094403002d105035418048080c8000d02840600001d00344640198a000140da451000c1800f80042d01103003800b40c3c4c80d2107524003085420810601c3c0e0121002c000404075860002d406401601030000000e242c06c41000b002ca010b450520031440780c0c4c080250400d41610205903400d50a528907030340103521101e20a040100d0402100e02074406068041060314602c580101300070707050074a0008020800047c45031032058029010009440c51a0160780c44050304a042d1600546828401a107003c95000005001c8085010f00301010b803078000012040d5103030100040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 662267715 1250 662266465 662266483
    0x20d1208070e030c01050904090c030c0f0603090f060c090f030305030106120b030c0603060402070c0e06030c10230f0a0908190206042607060206060f0d0f02090c0d1517 74
    0x2543c452601320109601400c00b030211040700400110f002003540c2c0c1e5200c4445c1d02a4001c40d6210504e5400f80103043e0365400e100d010780101e14080000b00f059840f101c814000c3d000004e001b40b9030303d0710140c0c0d000d841401c1071006400c00c000f83e0103682c5d99901e802002940240310313000008405454805a5010b00d001d01d00100c8002030050540000480400040360b202a006560203607007001244002001000c202c001001524a040003502d007501c00c1c10f0400c0308000c80b19201d815200002c211045d01305130f030403201c0e4003941d02901c44140c01c171002c079015100e40392a4200307644001c500104816402032907403041e0340e04a4156072140040009042c003039044168000d600400a1009008040390100121058142408400602d482c1ca0503500d0800645412000c01030700120308221b120304100c2e461901051003524120852882a01c03415018001010002d1140001e1404038141c042c0d07860a561400304c01001c2040003450341d0018211100c1d843c0b144d41500d60700080a07002010020684000d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 662268965 1250 662267715 662267719
    0xc13050c07031805130f0f020a170601140f0711030303060a03081c020c06090606010e0f0d020f0604080714030706090608070201510b090d020d1208070e 67
    0x30900e6080e076000c0d00c445283d1100c048404030807000008882e40c9545901c0b4107001181e00000741600030404020580e04d07500da00340d09041c0100600baa400307a2202c1d4140841a1701d0f9924021902e400740100c50800724101080005000403410304c00300c91001d00105a079038401c51101940b100c03e041803541300d0100b11082036005414a2040001c41d02200003840b0403100e0444007120203180ca51004101e03000506d0240140d448681007044507171081041540002003400d1079a400c41c1c461001031125074540700154010f104030b00c2c1c090210b40310303544a01003141c8001d04680d00c0310385942440b50344030380c9440754441100c51440000d0081c280428044250341ea00d50f02c006040f030505406a501001c050b000b40110340d690034110404440c583d40200d40c4c02d00341d5568910b2808404030348036414281540b210f0034031515510003031084018280c1d0000701d0702c1c0d007003400b0340310b1b02004001124090440f030080d401c00048101c460811403901c900c40c04030b0902c1c2d11002c40b140c0b14440121803042c803090703c0907 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 662270215 1250 662268965 662268967
    0x603010903050d2d1e060b0904020a02101d10050402090403140403150b0109051f0f141204060c08090c360a060501141602040b0306090c13050c 63
    0x284401541000e4071548413000e1035546054000740200e00c1c07009460588a05983e6104030091141c807241c0b0700070030350800e180c0c10b2000c2800c041d6415418422800160700c9107038000740403c421402845803c00d0a034400101304458a02c040446604201110f85901c060080c142d40340c1c01c00c141030bca100e000d140c025285219503541e5035010780c0e40918a041c0385041c40310a000000000d1101c1454450043c03201001180c0e000d07900c40050030003000c07074104501c2405100130704041203050340780b4041d04094070300c1e080e1200e403601042a03d50f602c0c012200800b0010001d007020b101070114038001e00852103403508018086c140d0404403001c400a03100e44146402801180d030f45840c180a02d0718100c408910702c4000d10101c500c1083c040d0200407100d09144070b42e0010459200403500c03600c0c0c000e003001c3c281204001c4070400345032003910a1400e45a950004611001c0039500c0b590300c210903080d0094101c07403440c284550680d56900c5104c0b000740c42030440198003007401920b401000e000b6a1400619 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 662271465 1250 662270215 662270227
    0x12020607020d0e0f01020309150c011404030c15150b0712050f1b0319020a051c09090e01020d0e1f0216060506011817060a060819050c090c030a05060301090305 70
    0x900e080c1c000004d50441c03109020050080d031705c0c44480e0f58038002c40501123031785030010055203017951441c24a0040c0100d00e1000c00c008640c0014001d10309540c4540c010328040514204440140f600070044100e281c1c00080209152010304010106d1501030f03c032900491035a00005c4032584030317040c80c1d69403054052029035417519140d492000c448c1e00050035281405445542e44120b10303540353304900181d1090380070b02c091200c18041c0128950140240c00310103810210003510340000d40c8901c8504a6451210310584002136040c0d610403d80d41401f40146842d15000c00d580e01070b50a08458551402d1070800381310001c0e031084078000d60898000d1902d821860721000001c100040c0514140181d9040400032034903030080503400b401007400681103244626550514084004003225030040c5040d00034429440c3c0001c218054a1a114220400c4030b032500d0306500f015007240300560030000503010f00c400740d0f082c0b8010398402c0c0303c81c00c4108143c5e9030366010182680c00c582e0f00507010134020011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 662272715 1250 662271465 662271469
    0xe150705041a21040303090f0c092a0f051908070f05070c0b03070302090d0602190503091203040213110403020f030c10080a0b0d05010f06050901150818010912020607020d0e 76
    0x40c4d000d4001d06001401c103480e62640c1891803105201141c0101c800203007405003079040d1280e01c0300c1c100e0511481c45903801c003010003909854201e80d003000b440a0500400100e82c440d1003140d103004410b403824041c50030180d802801c01b2400380d81d41404200c4101084645603c51411b0f500340704c0d00310300d18051183c03404801a000d036001404560426408100c410081c4d240c10490203001440741500503660124070714040088100700108034100f05080080c880f00a900280703500310013805224090750303a110752002904038004032090500f0076041a403403401000614010700110b070700039210300c00111142c6080546820004080d90340c045992005200ca440c801c40c12107600035454503000441321040b80002e504e541c0c9402d4111070f10303915445000c000011500441006040c151444115941094190700c1e0400100855604000001001913074443c0344016201a01310071100801c250304190501940e500c021030040c001610a1801085c08103100041600b1940f4450381e036610f4024050003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 662273965 1250 662272715 662272777
    0x30804110a090c020c190305030409180c09150504023901020408071707060212030406060e04290108070603020d09050105130605090703030e01030e150705041a 70
    0x20308940000129002003955001803251011014803500200240e5078030304100701b0301c030644240d002901ea9040d4010070005600106071010f5802c1800c2c00301c2e040341080c1403c44001601e000142c010701c91110001801607a55204e41c0c9084d521801c1c00703035515190020300069100300042001760310f410024840702d0f400d09200c0030301c01c1511212440900d60ad01e507051400da81080e04003880c10340010100304904440d44c11a49001c0c0d9000c406883c4262901102940742ca0641340c41400c50301c80080000c0401c009903010390b0150080c0100b0b00c1030b0b828241042c0d05204400c45082c4002d540c030070f404034035800741d03211034034100c03142800101200b5040c40c0c0304034080e400807459003625503210350070800014020301601d84240c3d540041305410309264140f00c01600d00c040c0940c0c0c034581003094288040b940c0540581c003054003e09000c680e203074800003810715085c40041010041c980c090180a0000e500500400850b40c220100d0300ca189500d0000080d14460318602988038481c030090202ea0ba0f035000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 662275215 1250 662273965 662273993
    0x10207120b0a3312200d0203100c08160203070b1801140103060b0306010e0c2101080319050c0304030b13050601030308091005010b070204051801051f094b0506010912030804 76
    0x10305a00201b0100e640805e14269003000e90020594035030904901441d40041d134554400402d918043c82c074000201f0194480c410705c100507010f9030554001441415064841000e4428000001c10582141134180c403182602808104e4240b401c01490414038230300000c001e0f044c1d5100b060f0031405a211035600c001594410901c500326111f8200b42001d103070b80d80a0700b06008085100103550386d82c180c104008136041801c020401802018041031a804a0003c02d41e030903240d100900d021561110540084a2580346400412500c2a980040700309588108924010102c00c01240c81c030480c45081c0500341d0b0000d0141426074281031000341c01503e803582180c2e8101540816030300d00030721000105070a54204031444600d01115040401880b2a0040c0d04002000000c101708514031820113108100c000030b041c0380048290040300c202402045441c1d100308600c040382001044a074904c82c3c50082e090449015001c03903484040022002d08170000c480c091541641c80701205e580c2d5a0300c01006031409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 662276465 1250 662275215 662275219
    0xc04030809190801051b09031513080705060108060f15010f09081603031404050d061a030d0c0c0e07020c01110c0607111003110a05070615081605010207120b0a331220 73
    0x1100ad00c00400c202e04000c150320703070140018005035810700c1480c900c0d020003d032a00c403403165041d04014011560000700400d14900b4604540418a200e50441d0010120b030041c1180c1c0c01001c0d00c80010002503a800801c40e032190321035001e40582003c040750300d4040c3c0d21410b90040960302c0c0200000780c041d0f102a00a13181c81c01c1000c0201345c008013180c5825200c8040c071010903c0341c404d440c107001400c16510018020038001c1006440c02680003503c034210006814184240345813150015002030020072010003010b01215110101c83c01d08440c040c1c4d1034200c4601801401c024040424400e000e00c20909a8030900c1c20f15050217400115403030b46c0456401c0d00c00c6940d540e0000304968900711600018008007009150030040c901c0000c0030f000040c0e22140c150b6105120822050013004450042c1d503800c2503850301160360f40340c0d810340034005050240c28010008500b801000b203540708002c8000680203000c2c0759154440300480440503240901070101c41842078a03803401c1554a802d051307003030300c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 662277715 1250 662276465 662276491
    0x6040f0608060a17100e06061c052109040b03010911150f0406050703031503050c04020d0b03250906060e09040f0611210c04030809190801051b090315 66
    0x9295004900070061401113090354002000b504c44455890203010760402d6841d02804480c101400004c2d10703114040d5405100c510000c100e5010b01034103001d0704140080d140203508010b0b02e1444000640d52002e14041d00c960711b054220400c41c10140300c0c100019511444c4203400320358107400c12406003042071035400c02c0c82e400c001c0c0705407495015000d000103080544409449140601d005015105030302d020215440c240b65082020810000302081c200d0020340d030040e900c100c41205000605440f0103a03d4040c440c000c500e84402c3c00e00004240b41040e06a03130900d000b904d940d0310f002502c2c0f045c49580c00040385e0b2002c000c55031034022000c0f07401a108105036042035456558003016954001c150109920000c510310031808100b80088880b8041042103050b03602d0005000103181c00f5a00002d0244c6001007000c140345d854400071400100310b900c8068500d00d654080c0c0c030b406000211042246494140c903182c42c0c0240c3c0340141c52104d50018041c2003441000a0003c4240380020000031904003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 662278965 1250 662277715 662277719
    0x703120906180e06121006091b1d0102030d150e0117250302090709031b031a040c1a0a030606030e0c040509010f0f0209180f1602030910020c09010506040f0608060a 72
    0x1d00300042c0d5011b0890740d1000c180d40d403500c0210401c8449101d45a0303210801c1601c05078402da070104028110f046103220720074a4203a040c2c0100c5c61800303240c0d900320200d480e262a400028414001c502d08031800c800340f100e842c1c4c0c0c0740d0380440c0c0071020402a01c800780d80051110030081d0115034483d400c0000402c03054005542d82e800003001e07000291044000704030410001d1050180c1c6950400728200001381c81041c06180d42d8814040300ba6899549004002c050b010400b00084c0300071a8006151140780f84050394032020182c2283c0d4031681104000c01d20702000000d481d4000d005d032680000340c2d600075022020b210424000a80002040280e40c1c0d56200b084240c442c402d0700c0b078514800b00c14600140c851003420207001410350270111021711024140108003500707074006151503020424010141c8c1c800b881050680c5180201ca1400d5400a82d1030030182d64683e0003d1034548040701200d1011450341d07220140503032403142e4000e40d41a2842c000302440700c0390081000a400c00005070104040c0d0b0703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 662280215 1250 662278965 662278999
    0x9051507170307030c031410060e03010b060a0f02010e060f0c1e190909020f03010b07082a19020a0915030804140a0609080c1201020c0703120906180e06 67
    0xa0300c2180d0201c0131076aa5070f05080300c503a0522034080c484044c008801100d0404014120101a2a22400c010000c601007400d9803501d0a40080c1d50f0143c003d0111511050081c00141416502d0403080c80107629001035601100b60000781342e0301070b03a02c2124400d21512680c1071036540d90721240d201c03d0405110701070055803c0058000380102040c64610300c41003640c850000b084110f895000507101d0b40103020b2000c8505c6007034104c074112810320000b01d1381c66940d480c113200d03d4040c10f0901075034a49807869280c1200b4214489a1034012414191804002500c025080100b07941d0f5019402c601013000a01403054158010f4520308a901d0001c44071320b81c1c0350b03030303164142c0d105801c03503451810b02e00d0090004d400c4c1301c581000a4601d60401011460509076000c0e07079144500c0c400e600c0303000d42030401e0060344020750440c1c00d24070054003510031003038480c140b0303d01e0f444400c034039180058000380c0001541481094104601800c2200401d01c082c50310120300c40c40c00d030250102e81d10049407074240040c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 662281465 1250 662280215 662280217
    0x70c0b06011106010608060a09060e06010513080303010f0f0905160f09030203060c1803060403020a082a0a021003020a05041e15020c041a060d051005031501050405070905150717 78
    0x20903050f86ca0f4500c500d00502400188001da510401c03a540c1403001c140507003202c6c1610194070510a181c40740c0c54102e960401c130307802c1800340d1229007140400000030491300c14114107070080d078414040342401c00d80d80d0001c1a048840840d01c41c03848409807401104900c1c4180001d004100079032920780d10603501c0340c0010b4100001a5142c0a4000c4009a0307000344000c55042e0309072800c8201c01070074132032819807400382d1640a0000000e00300c1000080d0503591488655003410700c2d07180c20a600b8503c000c113810840d540c6204400c244d02c60041d0704116615248a40225002059240d868509061030000301c40220540d4000c4501d04980494010030031640c100c050a030107e1381d542c0205492980d40f0140001ca4100075065201070310b0001c1c242442d07444040c200c41009440001c0000c00d80c0d0307400201c231502111600150350500420b000f994041100c012414140ca4040340d04011584844509a032142024800c0e960010b420701002005586948050410a03014945500c01180da580100714a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 662282715 1250 662281465 662281469
    0x40e01020f0d06080d12020307180611060a0c05040306051003080f071205071a180f010c02120712080405010b041506201e030d090c051305070c0b0601110601 69
    0x8920020540702c0b200e594a01a050081203001c011700669081c58130001c010070011110341c500580c0000c0450300f06840b504a00c42e4040500c1601d980301516040300038a50702003040703104124031520002c100c3d4086075100e412414013098455901d8246540d480300c0149c00001c00c0080e0a43d551007001004c18061001482502242a803240da1404949000103085102501d100c00308042800114005000d8004800c5040c0c1200c1d0520190754a442043c2081459010701012a005a410840c1c5807441500001c61800d056001d94510f45445003040d81c1600468070007400c0d044445a82c0c400c013500a401c0c55400c00c0c01039001151114411000c6015644c0c41e54404010600c1f03070308200032a030341c8003060003d025640c0a12030004441041019070ba004c8105000308826210905c1800c1500e040080f00c0000b40d940e5014010110705003071005078a00c191082030300a481035040c50301222824800e03a481a040d5440d49560400307180c450070030000c4001c0515040c44906145114040c40410010b80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 662283965 1250 662282715 662282737
    0x7023c0703061a130b0d030318050d020106081221090304030602030f0115020312160507020406091401050a06020a0b060103141303020f0307020d0f020315011202041103070e010e040e0102 82
    0x401005810510000d00320640c122000e0929100902805e580c800c400044240d4162801090700d540400e0503001c0d040242c50010130a03c03888ac0c1200e040c030b40640000b81221950310036208400103d0103420300360701c41d1150327440060007012014800402c002c40f02d5504425060100c03400d01d91a60741d0102264026220760140360510001000648400140c2d903107080403500c05181400c0005540119100c0d0180c4804909203450030300b92400c17031041064a42c80ba0b00200b05000195441d54030314000c00c0d00c07800c86c141c0d402d960400454503050180810b0100c445079401040c0044090f2a01c0d49600b0016048504040d09c1c0c4001800703040c10340440c20b000380c0d15010005c6c0c61030000e10740a403410101014400c11908140049009a0f440303c042e031040d03d400540304c4164206d6031002900704000d1190740b2001c001c070080041444407160200c400142c0c804d0b90b0810132031166092080e9140012140b41c000240e8107407170000654844c94080120807001380001c200340c0c801150040c20790300040b85c086 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 662285215 1250 662283965 662284001
    0x10240305070315181203020910030603110f030d08250f03050708130b1b07030804110a0311060a030f020d09031b05030f03100504110307023c070306 65
    0x4824011901400c61140305030083c100070150904900398030b01c2c042441d015102401c1c00a110300f0b054040d40458082110040103a418580e103600c014004000501050301d00300c2d5140c4a414060030010350230304500380010010010100000400c445004000b4482146002c0900c44981550b50120100a82081d90b4840201d601c115020040c1100c20003004501001040814810021094070302090241d0700850030303004599881804000c80700000c0526440c6150000702c10040c140d0001c803103401144100a003002d00c9591004005000e4045c1c0001341c020f203d10301520019180200048c0301a824909020030204402c00c01c2070100d0704150b004a02540d11603070242d04051b40b1003070045406c107010b022846004040d0b240e065990041045140c0481c1000000c2103403440c0c04c1c0320020082000800034844011200e00d4551030360402e0b40c40e14054402c007440c0c11401965030220b10700c003031414010b5003c8200c7c018041900721319140f1824090740214217010011540c14010f0354010036400e1014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 662286465 1250 662285215 662285219
    0x303070305220320151210170c21010e060703061d0a020a050f0406262412100b030d0c0309091e0203041b050109081024030507 56
    0x48106604400140e8000c29890818000592113600803078650209180d040510801c1c503000c6440c03080030002d06074803040081002840d02c0d000b8984a4413424201683d841121354400510300740c5801c1448680e0960440340403040139040890158203001826541408081c01c0c501d2840d084842d1910301180540142e42040921500b60103010020f080b44240c3e14080c0c00c030803c0c21050600b025040000e5581c00040505e600ca00c00c505403518a0034110303c0c0d9a03150340e64500075222840c400380c0080c1b06035400b01510100107400d003c941c452070440c2038200300003540a00003196545841c1405520980c103000d1079500e170301c003080311141c500064100003406202d124101490704020a010408000d09245036400082c2c1c0a4084412180c001d200403030000d1503442d15100d1810030041c451401c620103c20401881f11100d55020400c240306844581d85885c3c10046640d13010600902505a10183c4000b0a4084a9006410150700f40200c00b44102c10301c2c903400c0204107140d00607202540074082c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 662287715 1250 662286465 662286487
    0x30f0507090e0c070308040b070c140c0a060908030d0c020f07061d0a0807061404030602030a02030423071205070e1f080d08010b0904060b0406030609050606090622050303070305 78
    0x40c0b030b5005940c100c40e16003410450740c0c008001d0f40c001040240590f00075004140503a00565500300102c1c0d02136071030700c0000c0e15210307019500c0e01c004c09104d00c6498071040c0024040d01610a420075500b000003c4c600e868850658100900114900c290440c4241038045800560a010900c050b1041e82d50f0201d482945600750310b00c0c10030a00030188100c100c01c4080040001c0060103600312500307030819902042c0c00c90700c51720490140da8030280595000008001103140107900030b42c17250344220f0300c0c0600b091292004094642a101000c0603d5024031014850010081501161a4400c030110ba50954072050106944030065480c141c1000455103100b800170040131055001e401d5040082240900760980100500810b1103440344030b4100007050b48080d1101e030041d001600082514075591580c6050050040c4103a05c2080c13503441c9042d012490303515017103040342d0410000821148c2000b8070040d1103c2c40d41d0366551060894811024002650344042c0003416000c1c2c0030352103ca0310f401607040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 662288965 1250 662287715 662287739
    0xf0b03330f10050306150403061406090a11251208062b080c0a0b070f120506101809060305012721090e1503010c0203121303030f050709 60
    0x40d08500c10524500400d00d65907202c02601d0380010121001806c1d0900050340000e20b00c030340d80001d085203040074103000c0081c0c201600103026070010395442d403690750b0707140c070000031951400900c3c40c031000c04000100000829407007062043c0700b118005100b030741003036036400c0c813014800300703508042541a0200002c5143c03900c2c40021303003280003a000311f00011b90600051012948c0b000108810700103d0402e0f0345020400510b903a0b9607000d034442105050011002e000c0b8030034240c1410001d00541c1844040c45401e005542c001c1c07801901000044415a2042c1da01a0030104040f00b440c180e2000010701001d035014400046002c1e000004801c3c50780081035003101031128a400246004402c0c1e04c3c0080c0004d1750700382c01400d0080c4a0240c287c41114115580d031056402521002029001d012540381c1540f00859a681b0460081144800c00300d000c4c0d889001d075050304220b00002034002418aa17403000c400013541d1082c58002000307a030050000c0121407068612000003036400c00c090003980103e003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 662290215 1250 662288965 662288989
    0x1312030e010c080a0507031b11030c0105130b07060b06070309030b1305100506060d061707090c0801060c15020a0e040c0327050c12030c010b06040f0b0333 68
    0x7103460016091a5183c2e04400d108000101e07007088030000318081803510400325402c0e8060705111150900d407039403c1c40715060003400701072486400381c1d020310004d0b580641c048940070304402c5806000b261501c031107010b150300410f02c01d840141e1140440d2a071640e4400c010280c0c64070070b0300c034412154118140040c49550003002c800c5c00c03075400070241c4046000080c00601060750480082026505c07103010841d540204402e072540320303003805004203d41d0b07000c142c40000f0240c404201d8141540d2061040c098812008543c0c1c0890b807150018051144551040803c050007282c540000c0760040320300c1d0b01281c0c49001601d0000310030081e10300152070039018010702c02156290501202c40054048038198101c880d110082c0702c02c600100080017818000e0441c8681d0080141050f010b07403000150326039100c10060406940381c80a40100c601d8600141d030f05580c441e1004081c00e03030400d410940f142d4005003140c2414554031681d0b1860200e00c8800018094000b00c41180001a5006020b0080840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 662291465 1250 662290215 662290217
    0x10061d24073005090d03121104080606040203010e0f0703090b0a0c0f03061503021c050703020c0f0d0203031b0c0609010e0d0c0b0a020327160e09150601051312030e01 73
    0x910b5610070a5072000903207100a0085944641e03150a906d0141c4282d44048810300100c3d0a0210f0180d04901da4405402240c0d039a00a46a45540d11400c00040744002d02031850081c0700c100c0452814010b4506071030b8803560782d00f00040d0403a41c07911120010001240d035011103945503203c140960354000c19180100c6c140e27040900c0450f007081d03480908205100803040425602064031010414400d15800108100e08001c01603800c0252004010707500c0142d950040c2c0c41542800e40104a000a00005946083d8007850854079400100b100d4115082403604006809220b414a0094140184e502960784900002070043c000300c200c0b4140300d02541400d040c0072901090700007096124650940c8440700c41780040c0d0302d03981c0d16103d1004840c0c118058550000c4621640110200024041c0585001c580c40030311290b6244006070500300100c503650050f8000c2034150800301d8840d0009900f000050400905100c540d40e580c1c400c9c140c03950302030000c07200301c0110b0005242c0c04c014145074445007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 662292715 1250 662291465 662291543
    0x1009081b1e0a0309052b08370f09080609071509140402070503070c0603050406180302150403021e01051e07091203020c060309010510061d2407 63
    0x42c0303032005041d00060784103840c0203030303403015a403a1603014003407032100c6c8200a401420450340d01c030300f4007000540188998011100e0260142403280020000b0066814030056400c044040a408121401c10001140d2001c0c05213129000c100e240042c03010038801d01d1134000070281d0030301d0310004c00e107801d200101c40f406011143e0f070140880300704071500340d0801c0025500541d85d11031034504203140d8480c00d0b901500041c4d01790f4001c00c2071a40350700114011406000706101005500c1391000c11040c4400f80180543d05c51000e80c0c09000b4030a00c0b00d40d00038000d00640e400d40c0107044400c440b890200c841100d040e5920390030006c03004c1003207405241799000f158052000d0300c0c1c119000381c16045070740a00e92402d50544900c50805100b0455483c907035070040c2000d80c580c10300ea031005010f04015520600b035580254402300e20342d8416019800008100b160f00c01e00440c000060140c00e065001040a2121419182d840c0022503440105a540c0c810006060380015030b08403400c0b0b40301041910010685e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 662293965 1250 662292715 662292733
    0x9010e061608031b0a0206070e040510030b06030c150d0f0606020307020918100c0807020604030816020a0807030906110c1f020f010e010b010e121009081b1e 69
    0x685801c0a44600e80c4005401e6890719007604079034080c01100190081c180d4009680713501c07103a010880070700038141c0b40c41e07283d848007003d010401130303030021603100c02001c842a0041001c505c00c0406144c001d44081e05440d0600101404541e030791801d04a6500903040008020039564114031032650403c0a41d441002507504101c0004d46920030010044c1c46862441b001c9208600100320032200c01a050b1b040392164a412050140940003510030200824000b10014114900102d16030f4429941a0b40750801640c03a50100c00c03000045200c004110f20a0b0340342d103400180b90b0342c020004103000b51208103c0914000d001000e0030782c0c01108440319042a0200742d41900c039005005490b082e81540003e80f50300d03000040345008118040e544040d802c082e04000c0720031043d40f1013100890281e0300e0b4842c440f0410140004800c042c69403001030750000540300d2181c0c4050344840c4400c0c1c41049214540140400c0340b001e00c281f0054007120b69000030310f441d6082014185060f243c401e440002d00a00c1e2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 662295215 1250 662293965 662293987
    0x1060303030234020621190e010203330d0c0503010501051f052506060e01080f0c0d02010512250e09070f050409021b060702151b0d0e0309010e06 64
    0x1100300300217000e200f0100e00312009881030804019a08a1541c0c0c3e2800b0b80b0301841007942c0c600c1c0e41e51507148203074900000101c0300d1106000b00e0b44075130a421078005001c196444060516120550304000341c24040c003204d69285d58541002c02d0a5004507010858142013004240c00c50304c069100d644941454030b800103844e602010518290032150400949400c4202001446401e01d0b000b4250390300d081e1255101003251503841031080e6407000004a006a8850001541d180260f504588441c3c0c001c29449a00d49024031941810600c103150543c10460b9005980c4403547c81a20440c084605415100d03000c00841100070140004a1615100004005000c45c000d42000350201d01040111842403558500580840d4018810403804660352141c0c8a02401c3c3d00740605112160bc0c002c100c0400d9801c1c1c80040c03041c030401c540e0560020301752500c4041c3c807901d00d6400c90030351071080e090000440b0103140d8401d5292040c14107002d1903880c007100000424120603020308510031201802090509 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 662296465 1250 662295215 662295307
    0x5070602070f060302090f04090311101a09090102133312020306180c04080c0a0608010b0a090302031905010c140405060a1701060f090605120c160203010603030302 72
    0x80b0184c3c00c0041e55800d813080852000300315208415001400c000a090809d940f010035041d40e403101030250341001410781040d00980d22403800818070300e4280700103c2818501100529001400000011300c0c040340c50342d00f4240d5880c0c6500c465004076413002d40003160401c2d00d0529004a25100d0403c0b903c50243e0b00190550085002c040c0050754044001740c81d5840f081078402c01e81c0005d02040c5054a00303114041e03515031240c0038046850089000207a91410714004000540b10151500c090304d80c02d01034031016603080300c41d1a0040211440340000541c4050002041004900c070440c00b14448500300b032401d40342d001a80d103040000c10924951300c3d01707503682a80c0c00c1d03507400c440341540c3c0c0b40180d604962a081c0344050b402c0500c48c20340006000c03030b0071560307103080c04c0034a80f00e0010096560005580c24000c604011050000c4400003580103401d000085c40e00c013a0040140c5440d4200c1e40203e800c48040741c108030b021a0b400103940341701c0c14a85100d420310700320411000c542d1403500fa000e2481 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 662297715 1250 662296465 662296469
    0x3040f06050f40120b041b0f031101020303060d03050a021515100819050c12070201051012021c0204020936010e04020907030f0608030705070602070f 66
    0x20044081601a00001400c00f00c901c12a2142c510140341500104010101c25100207415589841c0d80841051480011080d1048890750305005690f1415611150140c400040c8102c5244081e009405d41401c501d100c070340003800070b01d01452003c50541ca00180485502c0d42c0e260b06552080c020040c26a841290003110b02d941403501940318803002005034600300010a8414a6007240e03030400c06c140e04004445504004110740032036010403d05420355140109031b910031159092003260050408103a004150460a2001101e04d40102d034005401d000200341c03203030720041c4d440d0700c14000b280c1d04d9031480f030010b08000f4010300800314080c0d0000d98880018034400910303654404100c404c0d03541d11341c1941e02e9200c018041c0c5030305038203045410250200208080c18005e4444a4601150015980e20b0b41610031020301c0d181540c40780c1e000c120002100420501c00c254450035021b100c005940140030040034214019a1200045e2400c2410181e03113411400071540500010001da0600c501c2d0030013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 662298965 1250 662297715 662297717
    0x120810050306160e030d021f0623010909020703080702010b010e01051c0b030a051c032702030a080c070e09011109130609060b180904080d0e1c05040e070203040f06 72
    0x500d01e9100095500c1072a80d0b0f104e80e0305001e100d00714414181c0104648211040c000b001c0c203a5600f9038210402220440e01800c40c00041500d500360312100340e07103801c440310300c0141040102159900900d5040e603120810032800103d6440601012a40900803038400700801d0904203c0c213051500002c10700d000d00a420341480f06c03007a44014051140d0782c040002e43c01c0c0a000d5615100300c2d410b00302c1d56039000c0004402c1a25602085600991280c41070881203014000c007440700803282e0b10700107142441c5d04800e0764540204181d40d000522090014910040f00c14060420f05180c004407011488008003000c6650b410b14600c0707242180c90740f040340d009071000c580e501c09601d502c212620081525410034001f46180c1980840d48150303103005032030a0f451010781b2103440c08000d02840151041614010541c1c54144180d46c44071405803c48103480408800321000721250408603030503000d0046c60040030070400070f810710900c04059071543d400400c0780011483c0034500040c1c00c1d00c040c081d22a4038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 662300215 1250 662298965 662298991
    0x31e050601140904180506010807060c0c170c0d2108131b0b121b0702090f130507240c0b0f100312030e07092c07030b0103120810050306 60
    0x343c002d55895120401e040040b43c401c070301e40ba21a1900c15a00c000a004007000d81c42081c10001d200c81c40b450614810f19480884111110300d001200d0828100c0c1030b200841d0390007010030b0500c035038a80300302c0540b205016142001c0c0608104504e001e450705546100b008000c441e408025619036560440320503d42d10a52100110000342c0b0201c000c40225000f10103c148000740a080d03043d0300e00c50070340c0078642607045405206010364808040d449000002908030000200050102d44890482e039402289555160441005907035100c0c20050f0a0700708656a00c1c1c0b84181790700b040e5001d02c01390007040c0541070894402c2020f4580e00e00e848030040c0305a2a29200d4800220401c2c0040300a4008650045105581100088004d405401c0000c0340300c1040c0305803500051000d80b03602502e0400011547d0b000c04080d4a001c0420118030b01c1d03950412244590100040000c1d201642da50095000e8180075460f40f054010041c00620003034080880c01c8459101030155540214410b600030b00650851 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 662301465 1250 662300215 662300227
    0x108040b0606092d010c0f0303050c090a090e060a05060307031101051207030e060609160c0602073815010c03020c09090307051c0e010516080406031e05060114 70
    0x20003e200d040511900300c10100440d02c0070340302500e0007011655a000030042c4030010031004640c0214560720141c82810700f0580c030004240690b10080d0450111100300745481464408203032504c001342e01c21001c14ae520345000fa0745910a1001a4100e011100c0c24496410a040000d9a800d0f070fa000180042640c070308403240a0f8055400c0740c4a102c0d908288500b60300c0d00741005001028081a010490b0181e1000502d0f2803030000e400074403850110355144511a0f0b071640417a50200740f610100e40381a8200b0107200418071134105000c1c9020072442c22249038011600003c00341200031405080c001c200b1050103542c80c4801d0081201c02c0003860710180085840c00c1c2285800c6010b0f41c020b42181c00f040a000e0100c202000030f04c0c480d4018801c991184030400030000f07516604c045040d00044103200c0341405507209000800d20b01e000c7d9000c2d10105003d98840d00425803040e8003001c04242e40e80368140301140c0c640c51102008400460401580c278185002812041c01000d642c020f6a00000c1c038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 662302715 1250 662301465 662301469
    0x406050c01021606050106021c1b240b0a0902070816032006060f30100e06040201030b100e0f04020d02030109050402210a021509040507020d0e0f0108040b06 69
    0x1034074601001c40b200910799034a20b013040d070000d007002e0150b480180901803480c04800b00c45408010030790060b580e20700c5080d101c18048511034040700401c4a184898401d00714010700124000c0c0440110f81c0c03000105002d02400b000068200c544c4407444031030040c0200750110300c603001600c01e1002c41c240800e1380059030b40340071901c00116460413042c51140c4151034104200c0010614842c0d10706585800c00509c2200410100d000b05070403c0700c40702415043e03403010040705002c000c406500d0104a4400300982d154a070b09980c00082844850350200080005540e814011101049019201c50170703130843c6440014000d07680340500d54040d48001d41821590340f5651304448400b03489071700440d03e03942c5402c00c50001c0d100941e011b911900380c102000c4d00014500a070300d44019440c02c000c0c0300c000510360074005a11114480354903246030030300184200b51204e0103121b11a0007280c0c09080741c09203d20700642103130209002d0074010110358094600c84c0e600482c40680140e0481c1c000c105945d29000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 662303965 1250 662302715 662302717
    0x7081305030d1d060d180c05040b0a03060e0a020d0302060405100603080d09021f273f030f0207061b060f181a0106140d050403021c020304080705150406050c0102 71
    0x1d030700d01545d0702d0026141030141d400d801b2000d005200c1c5141008066490040002b918181d82040c2d600c03003031400042000030b006a100c00f690654032000d48800b401e05400050f84140c1800c804d0f80983c108a0400007044004d10840884142c610002c100c001d003103480341e40c07140c02100c0301c0182e01a42c407080c0360191340e03d542e610350a0140c40c0ca4100410621158028818208501305220300c2d00c3c5c0d0501c20409042811071741041d17440c4a1207001e0703000d80302044c0044102030480000002c0c058901c40b800b40c440300e20b501c21032040c06501c440315500f480c801c0080c0f038108242d000008100100b407a03442d00103100c50790480c0c5150006004950b0601d4840300400038440c3e148640c04200041901004110089409040b030483e0088000c3c06607907915800d94000524200700c3c203054104101000a1075120b50096401900034030449101181c1c0300c0c02c0da01400c001c0d120340c4026a1011034100031a01c0c04011980141c0340640321300c46858040515102d850003107000f00c40c1442008600303007190b04000d43c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 662305215 1250 662303965 662303977
    0x5091b19080d1206080f0a030c080d150806060f1e0301060f080f0d02010621140a21021605280311040c1d09091207081305030d1d06 58
    0x220507241034802c1e641c00034151020341c00d540e568490500e5000503420001003559614441103c0280100140c550382c2240c10398818001103807130103007d01c15a000c00780a481140c645e140140c2e14420010306041c3e00038907100000f1f1400744100502800e201d01904c0e403c0780602d855081c000e8620210451000083c0076200701e420001c0c0880000c4c500183d00400003503041c10040d01082030f244c54200d4800128207035170b000d004200d0040200d43d031001070b00da244214844102d00410108a0f084162054507050040307640c02600c0b6910802280954902624141c85e0740c241d140c00188502c01355051288040c40e545d206031481010940048102521582b43d00c407080d200d91407400c1c04081d103a181980c08a82c0c8002e5150240307142c415007000d0240118910038200b031000b540041d840c03002c10100040800300501035a030501410740c141e11222107260142245c28403411405445140c0940911440030741580100d2081e132049003040f0b680790f000a02900e1592241c04080d04240001d400f280d8148185 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 662306465 1250 662305215 662305229
    0x20609040e1005160801031e02040603061e050907030c0509100f0305030d0f050624131412010b011704050c0a0305030a02010f050c090d02031603080d05091b19 70
    0x1c2c080305988501962005108500c0040d08810002150a08546266003400024804d070030303070240300070780c200031400c8005403510041000c20318680b2a5a640159291200040c03087e600302d100242401c1660f000d80b40e40405146d004214181c51a00d130348a500c1903900c140744c00741d800540030544250b501c4414030301400f41150f1151a055407858110b82d00d60286d0401d042c218903010306025102c86034041c0d280910002880105d00d0f6081c0b40e83c1e50900c6100c607646840220081003c03c0d00c20042d401c1850007041c925030b040d1282c01c0d82409101591103c01e0384500541d2404118143e26a0030a1817154031140d40141030034566100e203002c501c0c000d80b084a0030780c040c01c1018008100704002004001c0080342c4d500a1081d00414141002610425641d902c40200140140b40a40c1002008809020b0005003281c8c1030200b0034503885c20b0744031243c0082e20052000140ca500d50100c502420342c122200c01c004101440240e207011316041da410310428070170f60b01b0901c94188038503800c070080003030041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 662307715 1250 662306465 662306473
    0xb0c0c04091a190b010c0c06080a1b020f010f060b04180204080a0b060f09040b1f120c080609211c0c020f011d0706180b07080307090e13020609040e 65
    0x741083d42903114581c0060700014140003003200b00b54854514100c07015440000c0b0070080b0304044050390060310042400314240d40c1c1d043d115210040603680d10324000c4c42900a0074061065000203400c0d00c0b07918207520581810100104000519041118200c901000000600c1000411450080c0c0300d254004074540c8920f003a84014002d80c02c2410340550800c030307240c40008a084051024814040301c002d000000c410b800a0b80714882d002130b10f08055611001c802c1405d0301d40a0540c51303080849407d482c1c07012880003d0107841800c000c01c0303070041c909000426030200e0850b00e02000c14030041190420b841c020036002c205064101415102c082c01150601c40c01c00d030100c0c025650b01603240f40201c250b007050074401612410041c005080340072030000d001480d09000e4280c070000130004a040280241d40b00c0095100202d0740901140c610444040d0790700e0404443c024601c01c0c25130005140e806d041e1092015501c0040f0348654a01ea06551054803800f600780080e00a00c48440180d206010b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 662308965 1250 662307715 662307721
    0x3110303010e01240807121d0607110304081c090b03131e08071b03080d06080607050405030a0b0601030618060f08030307021015030804030303020c070b0c0c04091a 72
    0x40e402c40310b410303210681c512151041c09100f00441c03011a016481c0046508400450200d0f4802c1d0700c44000d0a20745071001c40c8003460107800410103581c404038113149400003404e00c203090740c1c01149482d400f07902d07000071410036007014102034688004801e045504d4241a955541d41801001c4003c0100803400c050f6490f8646051444070b26405602c0c100c03030640708050a84044290702440b0404075420a20b40ca04100003607840810711a240365000103201014480000090302e01c10084c211058003120105c0c1052401e00501d281c43c1c0090004030501206000620190320002410110f580d0002d00c0c0c001d95031101c03001a402000150460b0b00c0c0d214140c5039182e001541a00248119000035000040e4555940112078403800141c48500050f000b0740b09900400b01d5075003115441403076400c0c140c900da07982c82d0340300300180d8032551049001c260080746a0f065181c0a0006000170300410710120314000d0303085031281d220904274440e184a41e988000f14002c0c8031700e1140c000040e010801c0d20f400141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 662310215 1250 662308965 662308979
    0x311030c0306130c0509150909011206060510080402061305040608071a040617040c05101205070f0801090c0c06060303230408060f0a2903100608030a0c0311030301 72
    0x94011516540210045074082044030701c83d00c030b8016215191760320305003401e803040b007000000907401e60480c1100c130042c02107610700da07a100d40440c000c00c00d92400c044811600e00c1d2180a0f25442c6e480b151246590310580000c0035006009198095030407540c05548951002044440c02e000703030042c0b500207180080104421000080c0d0409070b03001c14000701400303100e41c50360004500c51030141c03000242c401d003088a9080e00d0340d50081d0300148140c103203680030b0fa26440172a00c54035900300d142000a200700d6495180551a12a80d5081940c91904900010903c1e00c094200d1034113101d00d0409580c0c400c410030049104036216028154824004d00c101d030b549003801002d02e500c018034054010310034815000548801c4088034100c3c3d0b51440039207555035490101c0e00c1c901c2401066101340617100c04c4c0542454010150001415503511441c046c501c6035036050500e0090450b0364a0242072400205100100000040d19406841c52820310100d0450385001c41d5810100728680b0f60304d110100012940d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 662311465 1250 662310215 662310217
    0xc0c20030f010e03041502100f060f0e060d03110a050601030b0f06031c031e0e070920040504091a010320040b01080601030f061d160c170a0311030c 65
    0x20048044a01522840104900301c0d540078401d540554802c0004200a41d0016020450001e0f24010b440c00c030840403000c48265015026075600a954850091109003001c20145c8040e20422110511500c0d100c00454040716840c003010302072050720100300a581c4002c12191403203603800416100035594070f01d40490f8a0074103503950842c3c4a0604000360560800154240c0443d411036010050a036241006030000c0c00090603e16803150010010b003603503c03403801103440c8214400e006114140ca0708c5201c5042301c0e014596850100c80b07160000c2d050780016010b48003603e1b03080b1400901680649401340c0740c120008a0782c00e4044c0c003c0000010f0003000340079000111071840d03c0c0c254045072034041200b03c5110414503801f0480c0d800215565502c03da02115010381400000601d03c0e498a20380690000c2c014881c0d001c043e903810030050007042505d018003121600e410810003564141d52501844c0c0c0e029007820a0455000c03030201300d00e901ca40c00c40b107007052850303910366982e0600c001d80f1001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 662312715 1250 662311465 662311523
    0x30209281409010605030d08040b0a020d1a04050601030c050702130204030b0f01080105060603040f0605070903170d0b0925020102191d012a06230f010b0a02030d0c0c 73
    0x343d440d00c50006518103021400da90f604c600c0d03039a280c1700d03035595a407050001c05000d0499054598240204004140240b298040314400b8640051440444400300415684014400c1f41003604040b00f660815400009860fa116412911220000ca50030301036002800345510162681c50f50009008040050008180c140c650130b100070b110f113940360002d0100034802070b6002030016082d540f102c0007150955004a81105403840c241c5400d0369652206c04d4035503000c0940305882300002440d01000e4246208001c07940300140d07035098092414141c003080f6a0408120586084910301e00151036034800c1d03040f141d40480010225400580c0b060000346201d40c074401c004000050519244029801460301c40701501051104448500d40700000402803000c04030b088800c01d1312201920700d07080c0031602030300c0200c0c1c1c0419a0310403403500c0d28400284603c181c1c000050030b1000c0010f1710740c280c1c0c040200c4040e449240f10200c0e04043c01a401c84a0103100c0d0b0b00a02280e004200d210002211000341c420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 662313965 1250 662312715 662312731
    0x912031d0a1a060d0515070f030b060d18080c030d050606070c03060b0d06060308130b070b0103020603130210272301050408060a050118060302092814 66
    0x100010a00d0240c0d540903091000c2c040806040120030140701d100800380c2d1201001d0f052000c21010b940c0c03841e1400713007801c4c1e4040714800320074100144a54040340c089155a203624081c8690001680420803502c510303491303902001d4441c510340402101ca0f060300300b90f0039440413849640703050f0500800d48130b40101d00d01e00300050a00003c11210f240c02c1e002c0d10013150308004000c8181e40381d03036601c0009061310409250044560222a000328506114100045014003016651044010f000c45400f2503a07410142604009001c264085640d03030b254107043d245c1c180d070040e40d20344036600032100940850100941c840c0300c404501c1e0440740c1c428031039100da0420f210203015546c41d6501d2001c080e52070340200e000329070106800d20113180d4900301400d01c07400103041080c90f05407202c12041c00c08800320341d180340700c0e6150f00c0104110301c02905141900b20305074404000c9541180d0000301c200d600500200795140a000c040503000402812464213100d215030200031004440417651051b0104503001a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 662315215 1250 662313965 662314001
    0x504050105041e05092103011401020706230f04080d0801170d120f0513031205100e040204150909020a0909050a080c0f0a110316140d0204091203 64
    0x6414181401000c10400c010718540140b40d2020f1124002414000c101249030710540c4107006500d540ba007240601ea10b4100403580d603a604001102602d0710340005040d04641c08070714100f18055124004c2140d050303000364a100c40c0000126080c2046c081c842010b0b1000c0310016000504c4000050005a041415115015283c0c3c0c1c134414250408290003d096080e0800086c5191071841052800039079048030100058103503c0c00f0146040701c03011968078442d80d5070b00b00d0352803d0581018042c0d403a0035800340c0602075803030703c04029524181036214070404500c00b03102107003c55841d504a20104140081001d1581e0fa40e00c52280c06000c403550160b01684084102044154507030203094a22600000100103010745a03485c9072199005402000c3c940c059451400c0410406100b0740c83d0a0303002e41c0171651402c80340390815080001c442040009600074070400c103c03850120106080c102c1c1c04440640e05014039001203805841c801600600400c03208400e808180d400d0303070150b2b84040b641640c030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 662316465 1250 662315215 662315219
    0x6300f02130f0b0f010e061c09050a14011a040e150405100c02070509072102040807061409010801050f0a1706010303181836030e03010c0c080a0504080a050705040501 73
    0xb02060881c0c49001d01c1c0020072501b5030f0b0115041000c01007030200c1c80280c01c80c0d400d1001c0c1800380c1c11903400040883d00d640061300007100340108510400c021200100007005204607005151251486c400505402291541100143c558007032200d00c01d64000254120070900c1e00c0e06d4030f180c58100c18404602e07042e19003403004490b00d1001654000740c0b500600101d0064403801001c1d1000c402c103010b0841181010080040c46484500103400105104002000b08070304000c4080d0020b826505038903001082800220010703a8010409811036030300f581c01329141c11054000c01c0500b00c454011a0305a0701e0540341c141c441d60002a514100d0b030113551750b101c1d0f0100700a128280769203203204100307521140100c011a21511648801190003411b00341c580c3d0913200b04600e13020301c039842c41029a0580d4103400d2905264010030b2040285030201d0080207041200d62018100e00b00f0030001602d100004039240e000c5a0045040700c014004000840d400c024544c504180e42e1511384c064030380103d00709000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 662317715 1250 662316465 662316469
    0x504030305010303080705040f1403160312031a030309040e10061215050907090203150a030501020706050f010807060810050a2705060108070f1e1206300f02130f0b 72
    0x13560207503459a0350f49d003841803502035610040d1305060300c207550501030041150400c0e00000420402544281041c10712440e4002c005812900241024030303c82c0d4504010481e00d59000c0700f12000d0900403203000900400002200380f07440c00580e20f6002c1ca5240c2100071801d000003420340004140300d5040100206014558001500c43c1511140b01c20340c0310350000d004c2034919402460b402030310300c841e034008011164000303414440a41e1003510f080e58002050014040c0c40e004850340034808140e02c401551400c030080d69940340b0b62044600b00441440403446030b000c3c0c00c0042c00200402024810304070f865801010382809114079a844007074424026101c401c14a00540b03202d00d00c16141e0700d4031aa1040b40507600e08203400f4000d4100910058541d280a44042e041e1501d80180c1c0d403940301151540c40c01c003046684540052091940c4800c03010b80700b049030a10400400351065141d08402c000d850715200e40001020000c0d03000380c402d040c2d802c0b40300044d171001566040e07050090029070550b00c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 662318965 1250 662317715 662317717
    0x2101110901020a030f020307021801060225060c11031b01020d0c0507060e180108070911030103050c041805060906040201081e070f051e0d0b0a0f1202060405040504030305010303080705 81
    0xe00140580c126080e000080707806261040f49020850040d6440c0911960025100fa44d80022054010103141c005001850b8100405c0b0403095400200704d0754801000a5150782e40d07002d21a04040020078800202005611404910b403001c1c06000c81c0c07180c9401058880840c032085440c1401403144424407094644144464600d081e040b5001e820202c4c1410001c4800c40c011023076464000b50b80e4018030040e002e88061450007440c540700038010303d03402c1003a00016684401d0604029070310900052002c42d0010410301400d44088038000f03040300000c25484060dd00c0b070900a011400f83d0320403c44441c1010440c1d41c40760340300b42c0c3d5022180d5954032070024409041074007400c1800545000400d418046c040c41150300032242010340c14145880d01c105041c0c001c00c00301540551020a2807a00709519001d81141c54408a421050240c02d00c540c40300d10102038400c0c0c14102c1d54451030304040d91a1700701241c001d040d0290061242c1c2c507241c14090042c03c0b0a02c012400100840700003055035100720 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 662320215 1250 662318965 662318977
    0x708060429010510110f0604050d180504022d0d14070c140c1e090a0c0c1e0c0b1206030d020a02042a17010e19021305210111 55
    0x184a03140703909000900c040c040e10469204c0030720040d925404500001045100400707100c4000074001441d0078908182004641c2c68150706018070b0202c02c0444d14682c80c038203801d46006441c0180c591820442007001c80d00d80c1140120f440c41341e8200000032180c0d01000340000c004003441405410395136144130400c00350458000c000100119900c1e0300044100c000c40820345c41e2107040395030040302c0790001401c3c0220011210940d214246801c20f0070700b441e51120384d004401400401c0f0b6001016405885009242001421100c0c04004801000800c00c000f004003600180346480703483e01c980100300241d01113401003106200070400130320280380c0002c0030700a0710403a50140103250392a03801d000103040c0030003110110808410f2241d4103031160322b90355140c0212507642c2000003004c001c81451181c05c1a0041e0344181000810030a499031200d035080f01400c15048016640c0c090314504810318001504503d600840030403c080100d451800c2605c0304100d410700030071514032110040000d501c958 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 662321465 1250 662320215 662320283
    0x1e0307121208221e0b09150a0203010303020607080417190e030c0f010302090607050321070804080a0804060b0910050a060801030c0b1608070503040f06020d090315090507080604 78
    0x420a084005815074611320f42d20070310580c1c00f4583c90240c1d52281055001107a03000c0c2251f220455000c20300d4030480c40c103a0020f00d624000c52840d411524001c5d04c403400200980140449040030404011000f002c070a0400440c0784080d03100c2c040003140c014500c0c0304400500010310201c640c88443d281c04243ca2507001d800801061000302c0b40c00c010340194000808a0343d0000c01030003100d0100d4802d100a02404014806d110032911404000c0140c07280040d0801e801c00802c2c00c10880041c002c002110b00280a5041c629540d5030b592030b062000e03204584105800103210f000b40241c0a00f130389652030545408030340c0d8500d01501c0b40411540618244000b070007080e2910820001b401072400246103031030010f00c144141031910f0b120400f00742d00169042741c266000040c10030003855910441005050300744003038030328070003d900002c03d80400c0c0d0102400c2c901d411904072084400d207900040b100782e400015214425964010700b5210401202c059540310202000580c0480400729400d40340455 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 662322715 1250 662321465 662321521
    0x30c02010908011e1509150905180303070c022803020a0803090105160f0206120103020f060405130b0102070f032009060a0902070f08070f03120b1e0307121208 70
    0x2014401c0001d001c1c981445d03482c10a0901c0045124289401035500c0d04c54009103400352503203000301e5035044810041015080d04410741801502d248003004594000d4443d00d016228220701c1c0c00040c4001c1013403103190348511410000380120488200000080b00e000303d03400e070b062540da002d9403034403489146501800520100a04182000640342200340c0c58011540f10003400800d50202d100f96110a0b4440910a00b580c010821480c203a2400e04c01c42c00b0954003542001d181c000803440d500d40b03080281c0384060301c0b044903103c070f0b0f403007004403800074482c58100114050fa20709000c20349021550840c244003881030002903040c100624064001c030400b505121030301d454128450000c1d00544c0d0101e481d003c080310150003042000c00502150350046060540c044420300e40503001d401c9031500503160b94101001008e04d9501c3e9440c3c2d131681000103003c0400083c3e540002030800c0c07600c0e007100f490101154003040500074801a8666042c1064944403034584400050a44502c0c0c40380b101c81c40342c06 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 662323965 1250 662322715 662322761
    0x21b120c12031008060108030c01200405040914010c030b01091205060f040302030d0219020f01051909170c07210f11032b0306090b03061b07050a030c0201090801 71
    0x105220055621a40b8450300f8044940ca0708403072810500d0a034000281640041794241481c0402e114400d01110210f05130070140c0c0e0000c1d4005a140110700ca042c0c030503903443c402d01341031002415103a40c0c0d170b0b4050310007041a004250f10150003030100701e0500b40001e10010020903044020f40c090700006170848010501a50b442156018000004004404500040c48164144816030014051030518000324180c466400e40b0000e207806001803904180745e041034103000501081e02181d402c0d0b101810404900d00c500740c148080c0341034508120005451000400d008a188042880c02c151344c0d0480800440c8100c01000c0a00e8500780d0740d0142104c100481c181c1c0c00100308030401803102c900079080d510141103400010b06001020040c400c0f0790000380e00852243d42d49880b030103016000014003044500182c8021a5441c40010860a0f4020400a8420030f500c50030068800003548101120300c03081c098a4000c0181e40e208000300e0201e21402c8003c201c040040c041c120550149004c1d0b5a50300c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 662325215 1250 662323965 662323993
    0x9030a09090908071b081606170f1f23040b01020a03080606132d0902040b041e0e0c1201060e28080a140606190b09060d021b120c 57
    0x17000c0b504203c8030700002d4000020742c08810712a05c2c131030104656005001c1440c29401420300b400c01e030001c544141882041181720f003404101ca03600120150f555500d01c9030050205030f8203d026030410481103a0003907504c1c001c90311200301044181d000361010311015100000583c1d0318082c4030002804200d00d07030001000c030704008000d03007501c003045402200d13070319911700300187c6955200554a4a07001ca5802d10994041c1d814084030080220003403c6103440c1c90302002e49802e015500612140c05a45503084102c0d60804ca8441c0150040c0018494107052000da41c00c0780e0340c0950700030510000308800001d0050f00031000e0803400e51010742100b00051846010283c5c190300d05208400031107100c440442d001004211240259101ba0b50410000c041d4005451030400020406885000d0303800001a100c18510030748000c90b02020007242d01e03061048002141c074000c030b80c0d40d0000d80d03101169000303a6070810300c4420a10440142034810000742c04541e5996031060b01200895544043e0050000b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 662326465 1250 662325215 662325233
    0x2010903020a110f04180311060c121e27030a120506011e0309260a11190f0b061906050f0c160812030702070e0a02070b09030a0909090807 61
    0x48800810040d01300c00c4003000038044030060000102d00c81c80300d003081400c03d41c2000341c951100b42000c000f0043c03843e141141c46a6032182c030003000c420076408008202101c1c0000d2411a40a0102e015802107103000700c49102143e00c0c04414507003006103100e255030012004000c4440e8a82d49030b54140c1d41c0f41c1e0510001026000181001e81080051a0048100200e613000c1c68450180c07560042a01e01d118103003142203461000c8120240c81000188060300e91104040300e14080c901c0c2030052529601180450034820800d0700900603e40d1260540104001901c40c80302045c820188e076800c0d5250881405072556000001140780f4803115814408140544050403e40500c90a00d92601003186100d40c14480c0052204034207415801040c072031030310305014204100c1c900c0040d0714158501160000c1d601c100600c980105081c3c90004503080625640458266542011008a0781c0c200048200d0b541e6000c0b01d82e00300054240c1c100032030301c4842c50003070500702c54000e00c2c940c0c141420b40d1643d070700e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 662327715 1250 662326465 662326493
    0x102030306100c0b071101061706070c050a0b13060509010203040507050f06130807050f030a0c060f090e0f0105040c020304060507122606041422050718090c0602010903020a 76
    0x2d0110040c1000300203110854290712174443c5a84856031b4002c011540f0b03094424a800c000040c45284071881124040065002c4e442045490142c0c41d02c441c50400a051441e900c1003e441800002c08000300b115041d048880c3d01880b507503082080d6900da5000c0c500300d01060700c00030265084008201b1441c505840d20a03078910b001082e5519098111344030303810500e1079501076140e582180d0020842072506000182502400360b028200900c0c4c0c40d56000054055800351005000c48414494080c9114060b446c01a0074107907020140c9080c1034100b01f5036500700744074481c80382d42010300400f900b505c0407080e5000c82e016500d54505018855032510701e400c40786850f410820880d00060078001c9220001c10010f078000c800303a070070942040010b200666040320906030840c10323540140202d000480a154004d407800c1304404105c1400c40c5802814480d455000d10700100b00b409040030305600c140c0c17004030302c184507040c80e454442c0d031000e040e4207031066007601074090380011482d9404900381c0713100c00341 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 662328965 1250 662327715 662327717
    0x4050403200c040605030d140c0c040207051506010f14181512070e0d1113020a020f0c271009150311120709020904090c032906010203030610 62
    0x90700310194000344030020807031140003410b034405101c2c00c11904080c49072038050407040d4086c1407045041c1c81c3c00341026140050b9014601e00004d551080000d081c403514800c03ca0050040d5074900203030400c41c0c2d81d040b0044000354001103031000304e8142d6029581442a124242d02c1c2d40c4500c01094030100c0c0c484e04607030000e120381d80144043c11055600c103041440e10100d50040561252409240300d500424010500000e00c95040828045950303202c400d108042d40c0205061800200f030000300c0c99501c20b00341000d09450010804416264010440c845013055071011610090b290500b0001242d4805d0505040700703e481c3c0321899501400b039440c90b808800c422115003600d81e00d841210031541c91466540315507a44040920404c4002c0c401484429030450301d40070100c41d0342c10080c2d1108014070540001e107034001030314010b41c1c8860b001080c1c1260004450320000741c2d070781800d40f5204003003141546d054010311943d10740001c000203401d00804060b40118110390f80ca20502c5104001501c0b100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 662330215 1250 662328965 662328977
    0x906010e1503090109030207060306030c0909060902120c150313060504050307050714010f0e0109090b0a03080315180f01030f06140a0b01181d180604060203070806010e0f04050403 79
    0x4455070102400450044a100c000040c500c080d90800a04018084c0c00401c1010f0410004002180702c00c1840701c01d0b41c0c021100055440350500d0000018036421070000c0d08028907080c18003800501180401000c5000c1e215400400008160308056200440e880c0300c001c0181c40409021070580d601c0b045d4454820400c69241c00c0c1c06031580c920f0080e913644814101c0440c0756007107401c1e50f031100b0207074101d21050070228081105030001821102090054002d216950b100e041c64a07510f40c10b00c1c90096400c104a242da03130900d51210800c0076168507815019501d144188541083c91031b0043c0e10400d20712040784c00b50b0342180e8656030300c200f038038400307451081e2100402c2421443d01c940381e40c090344038020001a55041d04001614910040c120240c442a5200d81000800354200300c4031082d007083c0101d09826a80c00c0480c031803c210406240100340700b00c004100030400c290b130085014500903183c908083c0d0706d2400440341501d01c01210341e003024002c1c241c0e0b0005c0c10203421440d040340c03090a0003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 662331465 1250 662330215 662330239
    0x90527010608071202092a0708030108070b07150e0304050d080322200d020414070e0103050108030f030c0f040f17070f1203270306051e04080f040906260c0906010e 72
    0x2000780381c01c2340c001980c03031709000001040003c008220000092004440700d07402c04010740c50301821000078040100e4915110701e4003504400e0300740112006000020309881100e491402e114080b50001c8480d0391505150a2100c0c100c2c6880365a1000700d80e0344100c05003055410440302c0b980c0103804603811500300030385101520042e9030b50701a201c010f00a100002500f49041100104003155aa518505251030500180a070b00408001c66400d940226034541e40e80d111595460301610440103598051100482c02003825480350203d00c080301d508031505104240002074886d20340d0f200380704403105010300d440200490a180401005124000d08110803103482c1c012030340c07413490055400c0c0a00f401c440882402080b00750320505402c4134081c4e001030080306101c541081d103034001400162407900c002c602d10035803042d030310100e0b0003406103088144039480d5140000c000402d2101129480c100060742002c080d900c2c000341d660941c3e400102503061395200c04006450004022000541044580b604 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 662332715 1250 662331465 662331541
    0x905092701060b0d090201032412111305010512031303120c02030f01050105030d0c05071e171b01020a0302100e011811010306150203030109052701060807120209 71
    0x1070503001d1305400c4c02040101c8144001030403510200b12190f1100c0305101e4142d050000498540140c07094062070608688060500c503030705054110040ba406070560307882c488891100c1e00110b04075081520640c00034014091015220302031300c0461a8103044130b41c2c04001240c00c80042050303d6080d0f0a0190188040d900071074180b21000d120400140e4448004011a0070304018040d18649140b5041007005200e9592945a59035072082a49a5482d001c0c41071054004010510003041c41545100600307110119440d20f8509913441e000002848030107100a950010842c0c6070703126130641c041d100c81c810300e8100400419401c419000d42e59640e881403500c44040144003007290303001c0d0441c2c40c04801d80100040c159070032600004801c81c0a0020103003440e400006482c15903054110104850780c401e180710100700840700610300c8064087e40400022941940090141c2c4e490006031500e840e03d4180341040c2c1103841c00e0094010410310700292882e481549200d00c0b01030303031100b80b039078401104c2d0f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 662333965 1250 662332715 662332717
    0x40810110c0f0a0b0606070b060f1f030c080604050403080a09060f092f0607030806040b0a03030f080718171203010f0f060309020d140f120a0905092701060b 69
    0x21114100fa4010035001e4103000c501d4402d10f502c1041203030703007516054442d912a02c4e4440302514003400741c070400105580990303d03181c507400340210513074044046040001d00107010b4004e800e9864045000c032000b10b2190306242c010584507542545072203049484506254006105042c026560b80759681401c84549801d4082e94030501c0c082c1e0710a03079017903107480c2407940980045502c00301284901600080a5210312007941c0c0e4140c1c050910601680d18600401d02810306200d0786c550242416101008246e00280411803030301c120f969014443d0b5a803441071318422000c440c05c00b00c59032040020401404006080c1c076205070241c0c20764455149800140c45160000c0c2c0003403843c4a00e040d4144031105100700c4940013002c0c0b40c0703028003140ca816008078115000394140a000f440345001030200e100002c0206950015140d42103940c200800302140340143c01500214002451403000010f091400c12880c6020302600508401024000c142991501c8600032422090b5504c0c0e003000140c000540c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 662335215 1250 662333965 662333983
    0xa080408030c0c03010e12031b07031205070f080c0f0403050607020105340c240203071b0512070c0b04090b360903042414040810110c 59
    0x3000075901c518005540c18100304904030038034081e0b0324080050340384040019480b44052001c0c2d007203aa50b503c401300c40c0280380344100441742160000040c441c040652000c0d0303076407401b030000c07200300159164800201d41c81301a880c4488002202c181c04585840030300350080c05035000d8801010300c0d0543d43c1e0740d00c41c2440000c82d00c110150b5943d100b040395560601c84a2103c2440e0150790840c1d1812003040043c1c0010440511006c201c00c442c4158100030141d03c10081e11850025042d40c42200441c810001e54012901c1c03030009042c05544400202e459000b0a0381d883d8480040c004410308420b884010b0b410046098039003a2580a0001c0c00602c0100100040d1100583c04502d0f043d140f818485842c168260b0b003c845a5001d460340030040c051142540310040182e91400719480300d0051a185000b644c11040540030300540d6000605400700d041c40d0b195800343ca03450841317035400c1500c407454080c43c802d000c020b0b005207a403119010010fa124032904515090041d060a20403204185000402c2c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 662336465 1250 662335215 662335229
    0x6050309010e16080d02030406020d08070525171e0a0e0a030f031e0804020f0604080d080a110412080901021c02032101050a03020405060d0b040b040308160903140a0804 74
    0xe0f0300c090040901c1030040013042203860004600d400e14217a4000c3d641c2e2208075000c000c02a0800124501034810000c079240900910100e6100f08552111040e02c3c90703000720205d41c500c100700c45804406138002c081e11038181c04212a05007070202c85515201b07961007001030000f0044621410f83d41592407074a00e201071400f4410991154240d0f02d4050503c1400c604034882402030a040c0c1426240e0203040181c2c03065059801441100180000c280da501a981020072035000784215038604c0740d4041840380c4511000304042c428103200c11001d20062003a03004030100f401c2c0098845000c500c1c010003c10f1020410304c1100c64864034040056890169030000d030780140c2000074200140d13022610a01d90000380360065804a514040004042620038070000f4040c40c5c80348000360a42c0d0f12000320320b1085400402c2c4016900d003c0c40d1480c400752003200e040340030580d00d40103c0c0074a00c040c084490014116240d500c02c550840c0c0f00c070a50b00361600002030191080c0c141c048001240c1c0307000340c8010300d12 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 662337715 1250 662336465 662336503
    0x30506010e1803190e0a0305030d09020f040e06180309060307050a0f020106080601120503040503060705040519030f0809030f010c2f03030f0709030c030506041e0c06050309010e 78
    0x844100305010803561515865658014080c8615820384c01c082d0080781031550922000843c1114003144415016034170240c501d000c00b20700d500712802c16030072403020980308071600d000c0480b00c001000f0031a0345484010415510420020b12880040940c0502c8000d081c01124101517800d00000c4c19680121545800070b440881c40180c1907401100700300103100d1600080c008507040041d083c1e44d032681441500f00e1600810180c01c240207086c01154041c100c090250b444c145060b42d0058101e5009104150090058032005109020282e04403000c0c1c0e9400300c9a183c45408a480300c10b01d43d0002040e00c1d6060042120300064480e091246411411043e11750045036419031507518001d8034074203107030303002e03d21488081e030154013020080300c0d88060180380304103032a103840c0c0045821035000d0708010281e031b09584003c01170000c00512188540c0c8505443c0807420968940102850b0000c40001d0070b40304008001d0294900410141d030f4092000c500000d0a601c0000005184c4a03200d007111140c004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 662338965 1250 662337715 662337721
    0x204060c1112060a050c041d040227040f0c0b0d0f1b1710050a030b22120c2405060306010512030409090206070b09031305032e0204030506010e 63
    0x3040504250464500702c601e6840070a80100c2a070303c443d001043c03038a10f195a41d002401d041103801c103403009400810700f0102181803010108042040540d001d0303105100c2540906d181c1954018000210303414a080000a0307141c59403064890b500210301100c0140d5401d80c0860700b204c0f0040a0038008584210114240c4081c6401c01c0444040b0710900e004003690070070750000030f030f080480320141e05c190b90840340c22a622058103000140080c0c2205900c40c015500000c103100c0211003160150910708080b0581c5403061901c1c41c0c01c29260038004044513002d149100070b99011f0712444034500e0040d8a20720480e245a07050403000511420141100f0340d031401171010500b42004824003400c01515001d0040c00c941c1c100d00c0d640c2c01940300305441d06494140b40c00031900d9102c1076030603547d80b01c5c6600c0c502d4100300c0950fa4072908001035a80d800c508403400040c1c1882d0016000580380500c6080540ca02c1d18a205507009411001080402580810000000807000c022032030080400121590a0742 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 662340215 1250 662338965 662338973
    0x60105040b0c060a0c03050705040b0705010204080a080d14010f060f140c100e030a1e020a0b040b01030302060f060a06030e03070c03080301050102240a0b130e0f10060317030603030d0204060c 84
    0x1401482808201861f0200704000d550700f20301180c0598004e42c03003080d05e900e500e2410341e0181c4980c0d0090701890084003030b000c00300704804020300031a03146544103003c0c0b140078000707040c810142489802c0d054886490200942400b440b400306104805291042c402c2d44407425411480d4005003d60007140d100c0313041c400c000d2901d403162407519a4490055458200304a00040164200807828910300e4500d101ca014524000c0060896995010b0725210b072a10f01344c00c004c00100d0b030034401600540990710000344111500c00e03101d485460b004100e0b10150b81819002c500500d030328403004580384820000b40c804140301c02d081e00015032042c1c41103540ca41c10304000a0410341100c6603150b404154002060310101024241c0340d100e07400c0d0000164503111480007652015182042840581c50480c0d010f500002c04240c00c121001d0450031034050001803a542c500711001d40c440540040305000e80c190440c9910002560002c100808132410b1480007075082040381e01507401f80c008901409001c00802c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 662341465 1250 662340215 662340221
    0x109080405010f2f10240608040201080403120b1203180d1104200310090612051e0304031b050108072a06180507050f090717060105040b0c060a 63
    0xc460b0b454200080026507200500000c1342c504c03c805001402030340013003490401c10444550a81d610b0303040c4040429500702c3d40e0303ca010810304d41c0307802181030000b203006806000d80038001e96040e5501a0b103542c6e03580b411152860b4810225803065162007580d045035903000030b404a01c0c8204e802442d03030703003074032440c807c11002c1240c00301030141c40c0188400300402d403110324a0305403407415140072489039400f180e0705500010603a0203904205000c014000f85100d8500188155030a03810100079890700c940c40d00317411812042009045a001207082480c0042c0e901035582e000710700c0c100300c80c1800d85a68540a000203058103c000c0441c030300c5410091981e10004107030304220141491000f100e402000c078a920142d915100c4100e04000c01a501002a5903000c3e590410b000400c0481c1d00405280258880900d031244038402e02e20b5400c49641440c00544507170140420761141039081c050000b89015000c030050505041c03000c00d00000400010190080c40b002c1c0d080c50290440303281c508882c500f1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 662342715 1250 662341465 662341487
    0x20a053106020327090106050f0d05010801091101030b061c0e0d020a031d090414250504110f03070f020f0706030e16030b011701061203020d090b030c03010306020306040e010908040501 81
    0x110b4040c507400e140c903202c0e65405da05680c118508079a5603800b00b41a41e129120741244421224540800011010341c10361129003450300c00d145000c00303072194000440a5035800c0c0103c551051003000f6114040300c242109007981c61a81130046004a110300d011414400070800510141c0c1002468800b0183c0c0000c841620000b0090760f00c040103020030100b06400f400510060459500c01000804001d0810681d0f06860a03141100c21007404000c0c408082d0801e4454140900d0815200c00b06500714441a520050300554029007036a854110845040c00941ca41005600130385003209c10030802030000102506160724040303103079205203181da4580301000c0d903404c1642e15058420720000700300350400d90448004a100158654001100c14010480c99001c201c80d01c0c00d19000c1010560007241c041960705580c0c50b042e00641c2d40340346d041c03060710048401c91b8a01808000600000d40c443d80a560400405000000c8546076940c1e2503013100d04007101034905c4440854100080e41e403190f80105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 662343965 1250 662342715 662342767
    0x30103030507050f120d0e1c020d020f0105090a030305060a0b030a0c080f100329010e0105090105060c07050402031902070303050603100204030b0610030207051005040c09020a0531060203 82
    0x312105d0011007000c050042c10504884251206181e40c0030210030401200340c05c41100c3e90701c1c4890281079011b540c542003a000032026000b100400550140180700e524030070f100d4000a0410a0b600d0f0b6400c40081c400280795030781c014170710030b8042684019200a1441817004e1a0006400009094044c0600d20001c02c1260201000700802090440c1080c40030112030340074031040a5014480d4002c4004003c11041c50307c160b45c1440005820300d450031285048442c02c0e9405084c0b07903250b81c244402c40c0700d503c86003034442d40b20a2040105003816070066a01c001030700225030502d02c980441600340d900c00b0394154002034032070007030025500d01880f01d54140301a00d0003c51405156686c0d4000c00c000082c80103100b4080701c40305020f094000e404580840381c2c090300303503031841800b401000001c0c5826a402d541071102e104022840306042e1003100d562030011b450f502d090034420400c60110341c1e440280c00300c2c410540300221a0200182d400c0001514032030300950741ba18500080603913031a0104001314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 662345215 1250 662343965 662343973
    0x1812060f020301060e04050a060b0f030105100509030d0f0e0a060807080708010515031905090607091e0b210703090b090d09030b0a02090316031b05060d0b010c0602030103030507050f 80
    0x4c41d43e900b0618501402c83c05071004119aa10170520700010025a030151030401400945420040e8640e0300440c1a96000c0b65482c2c980300c2c45010454080c001d40c050560158084c1c40840039140c050020070040c03000742d25140c244400c41002007101541540d1000001c60036081c14009095082110316034440c04078a030041c41585000d0004685048031060842c0381c12000020030040c2c803030242146880b0001d0724040c0018217004c0c0842d40d4034002201c0b24400510010400326814484020340c0c0d1950f200f0076049289142003200000c156442402441ca0100c107140c4c880c1000035010407000e124590603117001031030700032070304014101c45001803030703107100350011901350b0481c9400840304000e0369003101c442e144a07541c1d03009041c020700c10450059803500c100101903040480000014003a28070403c440b0144803040002d86111516038042c05501100c02e02000080884c941d003d00c1d90020305140a441d0507840f40c8030031040364170070703002600001d03800240b56082c030404100400e00304400c98010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 662346465 1250 662345215 662345219
    0x5070309030e06090105090a120201120c0806041a0d080a030c0509060d0506122b0e010e011b0b09010209100504060504030204110903060703140108010603030e0904031812060f020301 80
    0x1460ba0850140840c481c3c140490080001d07486a0152140800003a0444140607160148410048450340c0b00b02d0000c2c0c0c080103c042c5121040c060005060200e44400a03941c696000b000007802501c145001402c40504400d60305036101c42001c0b02d00c078000d5800d1a03503070300020701c010241c070304262645090210800c000c000c04d403900c104031600400c0b9090000790365284c0100007081c1c0031032a80c05840030310603541100541804075550710078860f054001c030703070205046240507a00d805c618003829011401d129400d80403940244540380308003024103a841720300e0348180d40d00d44c100b00303050761a40116035001c80d405d856801d1810714603440315082d0406504251034964010400d12a03804028015500c400491080261040a4540100f0002c5c19120140f4202c0c40c020020008480e01d030140b20610000052050810700c03940b8166a01541c0e610340e60921407080c80160b00c0d002d03004504005804040b9140080e51400c2140174107025000260800c1d101d044c000203071610212920103241c410401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 662347715 1250 662346465 662346467
    0x109170307060b2808010b0a080307110411040f080601060804170a09180b090a06050a0509091c2d120b12032d0304020d030c0c0f030c03060507030903 66
    0x581e4900769001d038001c1092a4a080031404422004800c45003c607409190283d130301c3c666950344010740307000c04020040c00e4003003010400c2c80d00e007921800c0390350b8104010210100709610308035a8038040c054070201e02c0100e4403401285035441540300d400581400d079001d20200006100260040005150201c00340c10151078101c4110240c1459003080e44000420340c980900411035040209807101c00400003003a45200b100240820361551841104ca000000e0a00c48180c8650382c107880b80507003d4201d050509050000c5941c0103402c1c05868072402c03400d41da03074028400d0180c80030a6241d5440c481c0d58109031004203051803540b2501182005201c0241c0c40d02e6010380c0013501c03c0d10004011451a50640101d940500304072120000d9010024010120400b0340342036140840c00040701000d440c41c4d01514800500082e10020f5110000c00448000300e0311450810b1090ba00800340044040d40d507520003400400039610890781e11007002030400911800e0311541c1e0340400c26050500500c801550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 662348965 1250 662347715 662347717
    0xc180626060609040f150516110c0d0c0306020f0702012607120f05010b2a031209150901092d0339050105010f06090504230403080601091703 62
    0x4901e0f400f4990101c000341c24400e1040d401c00440d078200c02d030b4403007070b07400201c4490151a0459411022108200609016074414031034070a0940d01e107c00b500248013a0400c0145803448500c080d105e00705a402c01001180261004010b020000700c4101c0e62150580f00141c00d041c01c003050703401e0f0308001c2641c1c110a0404202a558424a946410f00d410704403841035500034030040c0388404003145801d00100d514141e007401040c003154102201d1201c0c00d40074040b0803000c02500c0000d4190340082c40402d004640595500e03030409400001d90382c1030401e00840781c2000d6001c480302a000c1e910342c2c064405102c3c04480c801d03162b0305001a49414407a8440700d850044590b80f500a01b0070080060840d51f1848091017690a80243c105651b03440c048032550030b91280382e020081c0c44a51a1400004d02c401d2400809004ca0b00241c46190000c3c0ca40801c010003044040c010902c0007180c0002c1e8030028440603003252240348280c98040a50030544001030003101c85400400000c00b02030b2103600c503650004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 662350215 1250 662348965 662348971
    0x803070e0625020a05061c0b0105040e160311070201051c0204121109090c090117071505130602070803120405010e030c030d0b09010506160c18062606 66
    0xc00c00c0412403409201007000c42c070420b030000c01c180c111a8115208100030038030410b0b80c0360003142c01060103601d403420000305201e00750305101112280b0668420300e0400d6009000d490388141407282c20b080d03070744085c21040b80301240c3c102020000c0070b603403e201a070140f141d94841c09070308240506220f055030000e000c40c8100c000303074054007094200102415074180c044030040c05001040328284207040c603200c1110082d22011a21807080b940010703040c180d0001d2440f500f54401006551070380d10f480c0c2d03102606100d60916190a0240365008940f80c21071202440b4100c5160b80c030140e552304040c3e100107a1041300d800031000c54000040402401100000f601d15030152010990b1203a02e46141c50350061030103425002e0f0900000c03520000030800403014100d8500b03886030a11032601040200410f4481c2401040c4e13200e0703c00c0c04458094200c5400b9410910b02c2941e84d0701c00c132911074444650400b008000e802000307440c1d640c1400307010400450903550041000d22052030355801c0b00001d403142001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 662351465 1250 662350215 662350217
    0x60702010804021203190206090a020a03080318070b040512011b121b03090210030902010c20030601030c05031612020f01020709020304080702040e060f0f06040b1801091503080307 79
    0x10340400d0035556503500b803040c5130200c6801c513a504e544403c40079988541916030080940a07907070008002a8000c2071b0201d8996004221008a900790f50707907030500d6000039020400804410170819401e00301000800d001d03111003403649481b50f1400040240104d0f004800702c005d6410300c14025070f07070020055100202d607080e0800c00c00300a5100a080024210f0000086290380184100d0800d01cbe01075201c0c059090007507641c2c090003419008107400760750784044001e0000b408801908007084107807a81c4028802080342ca15175807400f0800280c9407080a0b04103684107100724408029515003007080b040d5400103540402600d038039002c2d0200c503074050710788041c0c0598024180310809a10074801c20014080c100000c54503810203060003961500010004c900451810706403603107907080001c1c45407003000c202a502405542d010061401e421000d403c0e250420744030b100302a56690740020f0f2045c904a20328800e002989840d140e034080e513861160146000c04413150500c0410844011680e001c43c903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 662352715 1250 662351465 662351477
    0x1020c33070e0105070b0109141614160209070e03070f0605091e09010e0103060c14030a1a0d050a060b0f01020d050f0f030405010f110a0207031e02030f0d080c0906070201 75
    0x41d001a602c9125049000300180c00303010008c100d40701c0d103500018640b0004100e240aa0b90b88034494551582010342410118024081d020140034912004000c60104604070682207c1c041e8081007916a00f0354211010071400022802141010814103000b8a4140d2500355400d181c0f81e809803141c03207040d030f84a010b000010700ba001031500340e00c0c0c99400c101002e080003140750703503813803180c003088030300b800b04075082414400a42c40e074601c80d01eaa08100030307200d00d00ca4516110f40c0704500c01840905d400010681607004132000d542e0321b122066602a00410113000031946514008040302d1003c006640300b164501e45880181e603000400c0c0109a045050042c1d403502c0307000000441c0d001c0d2400420044900000300410031006410044480004003428015584800d55284480c02a624a040168801a010408a40c0703903030104032406c104005180380c11489801090500707030070160550040e44090120300314143d000b000030303500c440701243c144d04140f8008005610b601c904140a410040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 662353965 1250 662352715 662352737
    0x90c13050d0204150e190203010b1210090c0309021801060c02120c04050c07052a0d020409080c0d0f05120c030a021b1b011106161101020c3307 63
    0x260340d40501e4640f01c104d0300f040f10300c1d43e84205402c080070301140c01c00c201c440b401c40308004050107802901e040c0d45452844500388061052000708460b401040498000c44c0120300207100351280c030624181080c80c0e50003180c1e1440303500510507100b4110f91a0303c110207204004202c581e81c00226075000d0340e41141c03441e05803444902e1a0b490000c20141c2184c0c00791504090050340400030005001072071080d0306840740c1a004810a4015403090020782c464501825004030407443c280301c20740c40d43d6100402c001424000360300c81f00c0342604040200c44883c0e1118010903400c9401400742e0712444000d1402c00d140000c3c1903480011090b01400782115100f0102c0402c49401c1e058040e17619031440742c6100700c00c040450002954490301941040000c0d41c003207410540b41c1d442809040100d01c041d100030011500c8140c031580041010607401d10811541d81084402ea810038001450034080000060001c1c1d84809600c01c0c014400b8442e426903180c1a04602003074034002c1c003000354080c40038100ad40c0d24035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 662355215 1250 662353965 662353969
    0x31803030424030515100f1202120919050d0f09030803100e0603010209060720180f01050f03060a0c090b0f0c060c0c031806040f0b09090c13050d02 65
    0x80a03607040010904000812280300181c4140600601e040c2c40d0307820f000685841002c0702c40b40c0c0c41610700e0b0b500a00c2c0f110160400174064222448118480c0c545114000011048030007240c000001d0918204420814410364000c01c029017280800000701f40c1d091741e42c00760358490340c03609841c0b1840d09102c003141c40000c041e03005001e0f03407008540000607507039203107030850034401c5513100d90042d000c0c6850030001103103003400c0501c00c1d02c0c2d8140000d400c452074228143c540040100043c002041005450b0b5840607280d1102c4146001c140405050140c460610707100d60f03050002d050300304900880c0703442e80401030703030b070303000841a4220b480140d000402e044000030840d0041c0094212018507880000d19456440c403c500411052850805441139503d03070ad540354031148210004e514241c1d00920030054084146801d01003402d42c000c2c49540f419640d0328101581e26616401126511004074200c09103060203001c00350701880c8408010300e000c5582e02c55650b8882503004541c041c0b20315590307580440d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 662356465 1250 662355215 662355217
    0xe0108190204060302090a021207110709051b0703210212010b0711090c070606050a030c2601090f03030b0414010b0a020a0b101e0308031506070f050d030e060903180303 74
    0x4d0364000e800d0103410304d00071020201075406000b010504480361400100650312401c103580e00031310560043c2c940d1914200690307006c2c10018050300b00c8003142e9866190f038100d01d00018018240b1a45800e00203c0d0b82008440c0d02c622966015000320f0300400c03114860100000030141941c102401098880181c0e04040c900c00d0210001e4a4220311a0001d205480340c1d050054414103224007814031003030f521401400030000984c84018008071500d002031102e061041004d116070a0600c0899800d52550718142c3d080d104c2d035101c01d940429034260460117055140c002d00300c0c490000e40e800e0221441006a11030102014444e8004d440c07004180d000666108cc840c61036010342040d10b50800703040c8240c544e400b13200a0311a04064840b01c00000c0c18540340c1002110440e600b141c8054155600c40b858641d002c202d04220642c00340c0d080110f200001d208015000245019000801c0c0c100a080400350031207040b003407110070075030101c2c0400001d401c0000c200d4030080c61503204403180c006104040380c59 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 662357715 1250 662356465 662356469
    0x9050604090f14041407120f02041d0718110304150f021605012a08011509051e0102010b0415090f09022e1b020f03101d070e010819020406 61
    0x350f4620300b80b006106906030841e5000d100c0c503082d1810f180d5a20301400340000c01c004010420102c04c0c0048026240c40da001121051750071180c070198401c46107482d401e080302c64102140720444585514aa0032461207540001205051983d03e5410182c0351803000883c400764001d5416164012a1100710458050300c1401c07400c4a00d54008a08030314009000c1d0200620300c0c40c0c00840e40c200314108480c104031008540c2c200d40c03504c3c081e690a04040400880900c1c0440051103129400092030b9200e840c0100b4000000c51054101070864000080c00e52340007019071031146090bc0c7c40b5144207080c88420034101e80b400e480c0099a00b4021000c0b201400b40040003a42c040300420f44202d4070b81c8404802560094002d43e9a200444620010380c0d0034140c036829455241c007480030b00d50040c2041c03440302451050083c112a00002d5402103602550354001c49800143c04110405018080400000e00940200b10304003000307604100c071040d40c40b0007103010000e513416410b03d02c1044d520b46600c140c2c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 662358965 1250 662357715 662357741
    0xb040605031504141b090a1107081623070f270f0c0203030f010902160201050a140a17010801020c25120b180a02010e1002010b031509070609050604090f 67
    0x100031003171082d40c500c243c581c0c400031381c080c3c48800e0000d010000c03d4441c2443c0348003500c0c03c0508000180c2c90345074040c0c100c054190744070a000d482d07038400704004500b4486d20b80088100c6a440b11b9607c50ac95007011003030303800008003174609a000e100c0004281e218100e60601141c003a121a2102c011100241a80041e110240c6e0324001c0c8d0700464590201c021480381e65001e0541a0990f40c0f645482d04070b20a42100110f0754010440c10401503100310300410386004c0c40e1030f000d03010802c0e00320f040700d1a5210b45020004180c003030900404000741100454014aa1100210300744551624010780790000b649040700c500b9000c080d090258000080070901503d21846145e401d4905450081ca0b40c04042d00d42c003480f208041810701e403820303002440d40c60f103c0e411794552071120724180910181c230a10112080030b55407140900e03138882d10708200001101c6007039001e100c128201880d1003810441a80c00190401c03907103103814450368444008403022500105800a40d00c0322401c4890014040108484 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 662360215 1250 662358965 662358973
    0x30e12120d09030f08100314031e0414060f0406110a0602030709061116150306030602030a4503050c06070c1101020c0108011a0405060a020f010b04060503150414 71
    0x1070003409242e01c01900c0030300c00d448018607440411000e070b80c07103001200e99840e00080c2d0402480015125400249140d0385d090481e820201c4282440d284d9983e0f0a01c44041c9007804135003000b40034180d80c2a0b0001c03000a0380e095150654004040c200c1d403080c0e0064106001c0c49901c20703d0062801c01c400204680c00c0740b8210f40301e080c01c031001408040984603072000205400d80c8104404004150198540c09085d10403030320515042c41101d140e03154541c1e0a0505540780c00001c0407540e81d00045110b03520241000030100c07400c60340c0c0c40072040d803120342084500d00c3d21100f07a200b1000044c0d00200081a8080311082c0e1198034085400c1c4c42401c18858443c0152010b00004a41107008501f4251152120f0001401e065004990340d2000f038080d10b0015581c071004100744591074007001240e4030001d20043c905502c800c0401c00c264800c903011001070740000c1290940351400c0c4115412500211001c1c0515440c00001030742d220301703115803900f1115800c00403504200d140c00d850659102090700795 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 662361465 1250 662360215 662360227
    0x3130f080304111f0c03030f020f0c01140c0301081f0b0d1101080c0322060605060a0504061211070605100e130b0a1803210513050118030e1212 63
    0x81d400e074a502e0020a0098507845042c0c0d80c80008501c180c0c1214890b17540e6003824200d161001c40260060004040116500300416541d490109005011001c50b207400840c0c0c90305201e007200c0c1d04500084c0421200d0b0024401880141000b082074408034000c041102070b4414514800402131290f1070900d5171000b801041030003041307640c0d03d0301e2080e01026211ba1407a56a4903a041100744800c0725400482c0b440903074409001043c00e60b801071814003605000800d80e0301c0303a0204106511051070540401e50100c0c041010592047d1460350305207000400b44094560583c642c5e034a40140d510042520391514002003026900803940c04c018080b00300c40503110309100c00c0c0d20400005490041c0d0341d04010500140754000c1500905c0701070358048511811702c09983e1000c580303c0c4045508441c02e000c2c00c0e00744002203103207401401e00506190344a40c80d58940c80c9400c90031030310042c8598034061152030402001c00d030004000c0c104450300361481d110064600710a107042400965910100b42d03804288 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 662362715 1250 662361465 662361473
    0x3050409060e041a0c09040e070902040906170102090102030706110c07091d07031a070c171801020109020f09060f0a0308090111190807080423130c0503130f080304 72
    0x842c07401680518010490b8480145207080d0840c4100d40d64000100e0400054160b0700b00340c1c0c001c0250301e60302020b841c41103481c0c8041d802a40d01580c0450b90b03040d00c80c002403048082125080181400640086207807540e1040003030746902450402800c0f01e5503a041d040141200d00044422404480f0305480c9100e4940402000400140301c00c880020356010b4038180041e8005044009da80c0c03c10b28400c9201e2a40d421411000c04c0241684104003e500d00d1200152180398440c00c0200728484440d1141c0d40b91301e4010559440700401411603060409242c05a19900902d04403400d042c1c2c0c041c0800e58074040441c0120381c040320320303d07003003006210000140f03d0124003074006054241c0c0c8805580413100c600d40d17a241c04c01e49081d002c400319a92030305c00061a4000030441180b103101c0310350402d03580301807507040721129100009849410385003c4419103402c10351000701404100c02000644203441005009000003880b6171581e00c0700c680307484103010720304504017240c40c1e11005480d620b18252074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 662363965 1250 662362715 662362739
    0x906070b01082401051201020f04030b01030326150f030a0501140c0a05040e0430090906081b0409062c0c090604020702010c0b0a06080c0d05190305040906 68
    0x105140c020f0060140c1d5405541c1601549044001c10700e401c00d0169003803504000c104401400700001544d4200022107003042458050320045006080f10501985181400740c030445201a200d00050005102c100084e201e10002e9030300400c10642c0810f03000e100c42c0120300014058028280d2611520200c88204141500000a0482107605108080d11040700303100b004e00410f1401c0b404030f10300344000d104008689d03224039070107400380d1048440c91080c41c00c4a04000200d5a4641c41510303c81404c0c0c114940028004c03009000f040820407805281c459101c3e103404044c1070313100b880d280305422201582e5031900403244164008404120034446a210280c0c0750301c4c0d420003a83c80d28420f051402c10001e002c175000700c0c0010098041607040d0303201c1c002c00000750710040c022410b009240403180040b5070340d8218903219942c030200000c4c4070341c14843c03414a0a0041c0c100301d841011400b840c10b00081c0c000c594101d02040b0490580d6080749140303006d4405006e181c00105002d460b222000611222140c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 662365215 1250 662363965 662363969
    0xf091e010629030609040309030215180d020a06200105070207082a2b030f021515010825051c15030b07020304030212010c020c060c1b060906070b01 65
    0x4210310b980405220880ca14a42e0030341070200804428400985217050005055510070303c0391401035405a1a9400105160300c04030940100001c042013002c05a03c0002e421002682d040300c035003600301900d07030000340010741c80d005100c20007005101600401192401900c50084801c001380442e10300450000c1d6a100984200215480b0780c1c01d60320701c08030b14161031045600d4000a07441d00c11240b8004d00c0140a2440e503e56000c880c2e4088885001c43c40c4622819554840c0e07a82941080701d680d80289000c034001012603c50350000140118400301002c40e61000000b800d004070181d6a85204c00c3e43c04060700c41183d001703801c0d8880704030007583c403c0003040284a405e03101c102c0c10030750700692000c40f4140c003442d50541c0c040c0c1c0818004241c2c40f9040360740c00103081c4100d9107896203c0d070126454510810b00d0000a0b9100c00e005554140c05101149010f0400d407140c44c10850058459641d4004503505c40508000790030022040c1c2d11241c00b11f0300040c02c040e1040e952840380307107800503d80c00c00f4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 662366465 1250 662365215 662365229
    0x3020c2506080f010918020415051306050105030f04061d06040b010902040b0306010e040b04060b030a1a18040302070308030717071b031b0228080d05030f091e0106 72
    0xe100800c40c02d00481286014802c0b41c0d844820716803d1245000081c000c000d1a9410001c0320f4600e1801655107008802140c024401c00b41d40304c074a403c0500c1003130074820720b40b0030782c0138140030080c001079a02000f5240d1206001c003a02e0040d444270f09240c0014552003100d1841c1c001c681140b8400050300041c4c540c010752094694036600ea90b43c03c1072404134015401a15503a140c1000401c400d51310528000c07142c0e41d0028030020f105518000010b089881035445910780c600c01104019100d07046100700705214154007900c001140b48503002815031b413a1844032240759001400850b091603c2003000501541d0f00450031942c0303060113070300544031100c000b034002044801000014142d80c0b1400c4515010348694010003044107040d0703026186d40300c58079824030941076280041c40244c0d40e204840b07400090b80d0780852030b1840381d1a280b0361000b111070308000f840e50300c1501318014050b0b00908599109184012503070403030715501d9002c2e041c2680e481e55141c0f04000c0d80600d0350b082c001940030b0710458542c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 662367715 1250 662366465 662366533
    0x117030a1d0d0c171c0c2a05010e060415200318120721031e051c02070c05040e0309030d09081504050601030308070c050d020307020109120b1603020c 66
    0x3030454035507070307070441010400954015000c44981382130184503148002c42c031807c00c4602e907500311450b012901181a602c00c80f03132070b01250100003e5811a5100895950a4034240e01d49400e01d2145021000b1049044040040c1801211f4000606004010801c65030300140c1c1e43d940300d0340f6940816400406880c92146000071040821100d001900104450507003a109103080d83e0540e0b030700254118584280d0034410311020380e00f008032014481d02d000d00c002d500c40a0300d4240d14150002400c62a0004020842c810400c3c2d0000c102410f4209c41101c800b181c0202b158001241421b0071402582c03919a014440c02400411094200c40e005003580c100314211085030001c06410703c50300c0d40545024243d80c10040061022a200d000541e52050719400c06804a02d0740d40c0d216494020b042e007501c00181c0012940304115a1b200d070590004059900024009442c180c50722449048040c0607043c04a030f002c444901528041c0d01620403072500707603050b10403100040d01d1226806064203120303440361403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 662368965 1250 662367715 662367749
    0xe1302041d1c020c09010f03060608060c070204020a0507060c030b191d04060b060d06150c1a150409050109060e01140a05071803080a080117030a1d0d0c 67
    0x91078400406444903400108952200141c005100320803240d0b50700218004c207600e00c0c2017901c901a0f40c900074031445a10011603469404d24a040f1002900150f44075040340c402e000c5a05501401d0ba020345404071401640d52140c1c0340142d41c6071180703c0c030007440c0038100220902a540c160b07000c41740d00074043e5180c140c182802100340c0c1003441940154010441564080074140c112030f00b0641d0f010348924000111580c10320b0014016400050045c44040e895041c1841100b56103810704040c10400c0c01c14528480c8556210f00c40090110b0203203002e17000310340000d24a40340381341602c417005001901c00c00c1404040e0601d51701a01901405445107400c02c1020084800f0512810300f8000c2c0c3c0c29140303101910382403e918084d10001e0b104070100000e200d10b416444841d2150180194841e800f00340e07541b114800c001d005030034164086800403091038261349526030048221601e8103441e2502000380031144a8041c10700b40b031801d210b5088030340e540201c0c041100015009003500d1501e510202452 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 662370215 1250 662368965 662368991
    0x1a0a0f09050102031606020d050103050a151a010f0215070c050609062502010603150204030201170c0d0209371e1a0c0a030e0f031203070f02070e130204 67
    0x200d0203200e2240141c2c802c1000d030b06440e00b10840c505105101d9500035103408c003078480e4282034074420782094400380c205003a12000c000c200480740415a480b03001c1840312000600c065020130f04e070780c0c2c0c2241c1802038214243d503441e07100f84002c0c80142c24001d40e80c9018206030400500040420108803110312420340892118603001070058455610189190b0150b00f6201b442c852030060760002c0b00940d034035402d020000a910404074044c1903c941c00050f180c81c48c5000041c0480d080700c05880709602d2034420300070a0000682140c800c88610600541d680f82c814010070b9426076903210318440f4408aa09070020f0b1198807403034904000000054086090702e424414001101071240041d41c0c0c0c80740d240400c1105400750145000d219114001030400c11885400781c2000e094407022000034030000c4070b5154629011400090701d1a00740d0080982180780d001182e180c2c8000741212040c02240945840064400c0041c4d00c040c28403110612924100300310b180b40c030003102d244101d10403424130610034004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 662371465 1250 662370215 662370227
    0x50a06030204080c061b0d2a0228030c0b04080607050a020c0f060f070b060109080f0a1b0b0f030108210304030f050906070506010e0f041205090a1a0a0f 67
    0xa190b610f0098000d8010103030400c1015400785102e981c0d06144c000e001d030114070081c03006d642c6d0145a51120003104840b070400ca501c650300c00d000c0001c080c0d02102901d005d42c4450302034a2001c000200e1012948030300080765000624280d00040450054030340104501e14000040d10840b041d01c02101d00e1a255030000780c3d581d00a0819080059006400b200103d26020681e075200540291071a4076102ca402c0c5442a82e1740a40c0c01074030500705080510015582c0458808003d22154018280c12440b202d1450348400814001620390303203010030051120084150800004c1c045004284d540d01c48035120b4010642003403242a40307602501c02c1103080a5000e00707041c903440030442d01951071940c45a90507035070948220751000400006003c2000d01d034882d4002419401c0c0250001e00c515850719a8410400400905200d042200f4605000c0080c5030b01c1404802c1569a092480c0c6400504000c51a00360244e4000b150350074100e4801030f0518003080040000c0400f5a4542106500008043c4e40d6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 662372715 1250 662371465 662371469
    0xd09050f121c02040f06020c12241e1f060804020d14070b040906050405060609030703020108040302010b13050414070621020f0a021e010c080105040506040b1504050a06030204 77
    0xc1c00c5001c104082c400c09001946184045010030014100740d201c10785240c0e405010b07000301003da44050009400c0746890080101a44285401070241410300d848088241e10030a83d56449161440c002c54544420000c4585010750031464083c0ca038075104c05d00c045200001c41d05012007100302840400d44501c60003501303100320340107010040681c0341d607035a600205101004184440c01800000300c3e6071009035008100030501f02c54045004d5061104020403a10054009403180b1010410000b4980b80801c0c55000c403502401d002020352fa0310304082c1d01509881e0340c200d901c10800c0c4d45a451402e1150f00c0a0700550007060f1200202c60154103060780d8203203d005080104054802c0d954001d00e90803800d00c0d100995140241c02c05840742c2c1d9441d03164000c204600050382012461082c1018420101e029417100e4a00a00c5910b24032100980011418001d07640074580703580000e484d80c0c03615001040001d81c0a4030a00c030107500d881c10b000f00c41d005801014030030220000005601d9100c5d00a40e01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 662373965 1250 662372715 662372743
    0xa08062a09030325050a06020a030c020118290a020301061106070806120a0605090f0115061d220f240b0a1106090102070515040521040b0d09050f 64
    0x850b04540c0051040c54001e11048058020030140d20113001031401e10042a0140c81280c1c090b032968031414010302039030b0342466001d08581c0741140c0740141c101c0100b580c180c00c94201694483d600c45000c60014080c00044480c050700502e601405040c001c00d900039412a4400c1c0d581d40d082e02d8200340425180d04054480c040051aa080460360341c1c40d0500800c0d00e0950300707100315010781185070303a24402e03150708450040080d00581c01c0107500540a0240c102e0388041c48000003000c90802001400114441c2180702c51050200d194641c60340310181c0348444100c0c001c2c050110901411a0341000e040b84904103502c2d40d05004054810b00c3c5810a010507031301c1c095030100c64050170240e11040d283c1142380b500c800c01c03d8a1070b201c844180280300841c060360410001503660003071414810321302a23000c41d281c1c1304035000300e0404c0045140410708000c8125000c249540308141d07000c1a01c9180101d40140324031a100240d008050313a604c1c2d11840d000307031185095030041c207940d8903a55280c4a1206200d9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 662375215 1250 662373965 662373967
    0x90b0901051207020f01110408010b090f010303080606130e1b0301081b0303070209070818030f03070f030e030309151608060904150c2105060307050f0a08062a090303 73
    0xc01e21105660586a000c00f25104440f0f1000d410344032282510550240001c80d035900080c103200c1c61100b801146c1c0030080070707a040308c442e003440304501480a00c140704c00b41c00c000a0001003030155071510200c0304d010080c88118a0307c01d03140c8500f2161a4400e48008984070fa44160440b00500e009064074105c50891001d000c4081407121208001d00000e5034140d81400200708400040c2d66242d4401c3c0944280e0f030710031240785031080343c03640c1c02c664010700c004941d88103100c5402040d8808040340d90180311840e08003002c44400c0c4c0c095025041200c04030495000c0402040680d802c0016140194201f9000710029034a404800d811500900c001c1d140c00907080100280e82e03824038a0306190041d01c16071602d800190106281e4048800340042d00300000c02040344580041c00c0003400300b41424100710104594140580081e0703441009202e4603024884903451200c8a582e1813250000501071a001d907403503440d0040b20541555620081c0c04c0d4840c10103800000800302a00507203000050140c021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 662376465 1250 662375215 662375227
    0xb180a0f0c021b0a0302040908071406040f020f0112060314011104150c1e20012c0d060216062403030806130e010c0e100c150e03160201090b090105 65
    0xf002030850007006850b00000300c0c2c01c00200603107451051740030319802908490744907842403074a00c07203548641450b40b6040e4403d00520021400e085100c2c0c5c940c80d811513400154400717440058621200e031b9488100801c0c07410750000180301e05e0081009010003098004c0001203a2040012114043c50041100c10500205010700140c01800140c00c0b0307601a41c1600c44028941040d55402003140304100c03014011200f44200e11440107c6210108109090045202248001e180104c0400c4500d080070035110742c2000c203054861a00d82d4402680001c020740da1844d04c5c0e020440090b1550008440c00b070b10380014180448640814002007101d201c80c56840300e032454a04a600d5003026015030313402000c0703003000688269144a1040740d100c03c44004902420481405001040d5801100f070080b00e0000b0420343c056402000351042e184c0c0119200d08503800822010018002602c01031030030b04c4009030003200e11020005030000a0304c01d0f654618440d0b00c911100019000d84c4151038040f0340c0074448 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 662377715 1250 662376465 662376493
    0x120906050f0c2b0f050f090f0f03010e0f07050301020c10230108010504140d090605070606050a0f03060c052b0e03030c0d150305031b010b180a0f0c02 66
    0x4100a000703002c11030b1085030450003d5050400030140600000004011100e12030390800c2080d034a0f200380e41400703400c00c0740e1181014031510403501d8030f503c6a100c00f24058102d60350300c2c2102c2c140c3e00001d0000c00c00e1200b46082c045c1c1c1e800a0030101c10543c4100003001641b49014001c8a007100d6012000d00042c081d01d0344100064042d41a65221707441324410090300603219510310900030014107001050a00f01420540000c085034030000c181900803c5100c0f1510380c0000d50300088641c06e24040d076460146040460040c0511b400482d881a0000400540704031402c044009803801340d00100104c5002c401c065039107124071003007010300c100d4800400c00e5000d05d0085600b40328082200202c0c100481240c0380e0304550003180c8101004401040340f103034045182c455400b101e06150b00c2201403904544680c0c0ea01e000740c903c1860480e0400341410120700e82904040301010003c0c02d81079521021030350f510380888044800807101c0d4540900540001220300a0343c00f07200690300036150034185240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 662378965 1250 662377715 662377717
    0x60906101b080f0306011806050a0c020a0914011d010303020c061c11041502060c0d020313060c080402043918080d0806030a11060a110d0c120906050f 66
    0x251144411444001d41c4010824840003000b201040303000d126a07902e00480054555040440028401690020180701054001085a03d03a150798100044120340c80d100091641000b07070041045c0e9410301055400e58a0f0582603641622002c2c102402c1c158000ca2710352158040074480500141d000e200c1d6107405042060040580154440422080a032120030150a44410561011001000007002c00507a05042b103041e8002d2001e1014180ca81410b030702c65110760146081006d00e103503000001c40c581100300f00600707410607400319042c042000c81c4480544422002c60b0243d00881c1062601d50340d04143c00b07884290b040401111110140c1304d01241c8200c80d0170240e03400203100884034011a0761040800d003c0007080c03030100030b2421883c1003a00400d040000b62989003c3d5010120100010303d44c0300102c8062003003611031588800301072004440306401d050042e011401031100c10055580c0c40038894041078020000d119030445a0802120500300600c9540000740003884405120f0072000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 662380215 1250 662378965 662378987
    0x150f0a05090402030f0f0901230c0405030f01020d060b0c03030403180503011a040e0d02071e18090605010b03090d0503042d050709020304170c01110c03090906090610 73
    0xc90101e04081a031000315080360300540358800c10784001020805403010000c00640c2c00062507000340445031008110781c0440344c0403074000701c01c004038000081074001d6003800e5500070f05000381102e00011003501c00d18000c0d0f000a40141c50b060520300c000c9161500703071045a002c410340d44000c62039950b468130211054075032022917071099800020b0001b0655424000e25001c0d079126014992003600c24400c1100315800340d80710103600d8110040110060f900440c2c41e200f01d8002e00c00c2c15181c805801504070703d411040c7c105542c3c1c05c103400d42040808405a220780d85041c0b0419013046543d0303c52500500502045601c800701d9071001031407001c00392050b00a5500306101c0e01c0d201c08182e04442c0404014011095140706400742c0d414001e0501a00700510f0340101048001140746003419142c10862920240d403410401d0310024411041da1025072188030720b200203507030a80d10744003c603041030b449078403c108440c85461400045061442c18014050041c04003d0408401003480b64094401d0031071380c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 662381465 1250 662380215 662380217
    0x10606090909060b031002090f180721050a0b101103030c2b3206150d060902040f060201140a05070210020c03070b010b070f110d050a05010911150f0a 66
    0xc0e113103064464404006e4007401c0c4e0701c81440540c40d5141c01040c4100340e80b02400c05842003042c2c190040304011051a51030f040106843c0403600c0075003c500410042031805250a41c0070300d04001c002441c005075100fa1440903007103400a5911024141c1103a0a2244c01c0c854040b50b00204042903216162000a104c0c1413900591154601c0308215544c00052030308200d2000c1d01d4484810381950016045007403805810320040710380d05800c65510700e907001d0b4010b14807070245500140340a400003422055400340801e242c0c06104454030340380640c0194203c0e01c50900d540c5100600480c6403401801048018035010305140030654030194450068a006444601913000d5035500e808455950b000038010440e082005540e40c1000303203484022110164000200c082080c041040000c860080ca10055500604250754a05e24400043d41000903190001c20501c5239101910030040b06400019800d405010007601c002581c0042c440340c6144100703a034400c01d00030080c0d01d40015100c03014051503c51 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 662382715 1250 662381465 662381471
    0x806010329030705090a050103230a021003020d0513050f0309060306060901050403020d031713050a030309230a1e03050a050c0304030611131e060e03030f0f130801060609090906 78
    0xb071a00460704201003691000c000a84078801441480500411480c10b08080c0c8012244d030002070b8ac2ca1912803030708100003441036460012091507039120760140e130801e0b00711075800c10007401c10000081c1c175025030090442d0603010b5016070680c3d0480210030703100c0c07181e00030b400b4600e191384d00010448280c5c0b08401c03680c1031060502c4080050b032255080c1400c124031a03100c5001c01c0d5410040c514100e000200101844120840007800003100403c80220256260501290b020301c145130810b628006c2040d080d11460051009440c020f03000168228103c1c090f040e04524120350b0f00c0d491114007045d0201802050b030822110401e10f10640080c00304201000070340e4213040d102e80d13960054509500885c0d002003000300308100f44269030035441c001442c010303015807545020074026104400c008d01c500c40501034003407060500354509004545400225060450780d900c01c000d192002d80c1c11804000e00003003170b41000803e00d05014428502950181d48456040d2071901304840050000640119407041e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 662383965 1250 662382715 662382719
    0x161d0904060e160f0e010501050906130302030f0a06141e092503020f010305150f030a0f030c0b15010504090209030109020a06030c0f0305160804050f03031608060103290307 76
    0x4103101c80030b40000c0500f0206580c82c940407442c1c0c03440007039800054101a41c000100300303c3e0b801c1011240211015200d4945a06102400e05010f140a60000e5094050440065903c07603000c10309048551050b00c0c20080d080c0620002044104200c1700580400d10184485c0c440403429203070903070b10041c40ca0807683d02c45c5a40f00600c4003520031000c558003100040400740110300e0a030891407140c460030f20303081205143c846060030f81c0d406403414560240f41d50400900e802d0314203001804985030868102c4114000c02c4c500180403010200c016292041c1b0500407c40c081c1417043c070b00740089030595a4604050402c04404001e50050070410f0303140d0361f20108000180c40e00c0d10a4070040c00e0319280000c40d440c29003c098070000900140c039081520304410440c0c802d6016050203c0030b1090f140c11441070b074072407600900e00100261314800a22011040200000180c00da070040000c02c3d0f910414541c40d840d0065040d11745640c48070110b81c04240a0740e40d20141001e5803a0040c1000b0308680f6515 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 662385215 1250 662383965 662383991
    0x280809041d070608042a03021017041a011a030708060a0302030d08010906060e010c08070c0e040b0703061d04110a33050f220302060a08161d090406 65
    0x724060b0f002101248180040200b44034541c050f05004008030340b5a50b00c0003032002c8002042c5041404028801c0d2425840c1e00102c034030507245000e028960050741034481c149820041d078810300d0500c440c00500c5201c6d001007140088131840d02e0f49900c40c4690345085891310391040e115180001e104a821590011000015075020040b0b01e05400c0243c039400c1d620350400d010103080d24000d410035820720855089003141039a11940100391142c002c40350356250001840c0c818203400c21603120303200400ca611f0900007031083ca0700c189030040445840070000f140d80d90055a000d02e508402d01c040c0e9180d81800a400320791601c3c050f12400b40c1c001c1c102109140c50710030184c941040512501428803881c074950f1a0f01c01ca6055007d0303004818102182405081800202c10740714801e10591040201d035840340b0b52000c3c52006002940e401842181c9a44400a00030310540f0111161007040c000305040464040c018130180d200d0055041213422000316103000d010b0304005c0544112034080ea24042c580b250 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 662386465 1250 662385215 662385223
    0x3030221150102070911161403030c0c01060f1d1503100b030601080309092809120e04060b0406201608060a1a010c02130501030302280809041d 63
    0x10700d08002910803141c201e0300024070300b40071074000b1405076240102e00c1c03101210744001c0c3d40084000038a00900c411a61400c0041c506440000241e80c1c40040184821454401c02500700e000b51000208021075071008980c003215494818065010144001040b19084142c44181d12404030750350803109010b01c90109103007613101c046080d41c0c1d59403404020500c2c50148a01030051484100030f5080c01e02c03080010301050740180c1400d822060103484075040300b502000444400d01038641c1006190a81d051850204a043c6003c0f030008490000030300c0c01d840e041c855101611002540c950a040c20540d080d642e9507001e040040c01a00d51844041e603640c001c2150724801c4004c40e80c14142a0302c1c01d0012458020f02800b00c0c4109428410408850300300f0080041c80c00c50240703071400c2c804070700b170000c175588105280e00e04802d582018008414144c0001d22180140781810500410940250199442c500345403030003040b0907820045e0301e100c3d140542109407004550303941e800312590200000c030300d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 662387715 1250 662386465 662386471
    0xc210705091905100e030f0f0d080612070b090a1703070506130f0b0403120e25030b040f0611030703090501050606190c212f060403030221 61
    0x54000071010210306224240c04081d89804580c210a07a040000041825490141c000d04101920800c1c0403190360030440040c6840c210300680322100221031440303442d820000c60000215401d0004035030a800c0082196603004204400781600310708000c400210f591008407900d42c01034032410040758078000c0c0c480842e501c0c1d6409008598070222446d04500781200201600510050f0190100101315981d00c07103000950301000c00e0800b6500c5181c09c2d030b08404054892040c1924000e151200381200081c0703a800740724040d01c41980c1049100d00300741d503842c003030100401d80c1c0090400f080001e0300e4500030700750a074416203011840c0890000c0f18a040d8204883c450000380c0c5481881c41841800c1c494281c1050003034031020f1600020f103007040a400c01182c0d003101000000c20310394003400f01c40d680b80d0410868401003181509000d10006024014680844904c01d104220301c0032004650014442c0a941e84009040c8954440c0c070260002d410a020340120000d502e105055008544040144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 662388965 1250 662387715 662387717
    0x50c0415090302040b0f0d0b0603010207120503242b060c02150f130b040512040603200a09051212040e040b0907050603010510030f050103140f06010e0c2107 69
    0x10260b20758010082580c81c1810b16900402d20a041012240c84a081000c0d80c25000214910a40c0703800c4040380c021f2041140103013600e0303415050940ca4030750007401940940300c4e43d00111300d10346103000f0314800004103000b8254448a00e443c0c008400a203150714035100200c0c80e4003401c03803011584400c03043ea00c51404142c0103811100c56590000390b6a1203954202c2944030291246242c100407039001504900d5001d018079a41100107000c2101c1005401c2a800030341740311945942e5500b0f070290151850345042c01c1070010b44482d02c60212040400c7d00c1c104c180030758401031010316110034040c042c4c10050340c46060303005508151041c901020300420041c001046503d03064139040c10015004000942100c00310f400c421b6007000581c0d101015a4156042264a0400b041d8800d200740d000f0245c01040060301400c040c000000d02440750b0800140358100016101c0166034030040c1500c03074000f401041400200342c0c01281205d8441405400c4d210001c69600000780ca0b441d0010b09420030842d0500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 662390215 1250 662388965 662388977
    0x9010504120e010c020103020708070221100912030b01050c060f1b09090609060d020a080a140a0c12080d02130303030e0109080405040902190303030b040c110c04050c0415 75
    0xc4100480c45030344400a2050345001600c46080b200020050b890556000c3c4c10550081408000e00090b40102d803641540242001c03007050305c02461002c0c88043d0303403060000c1d001c2d0b10314001c2c3c050100d004040040d0350040c5400d40d50601d005050340240001c81202d41003000030b200045601108010740e81c0111000c0550003500e2414040c04100741c4c0b00c41d544404c9100003400031101036200d041d041e641100007183c6c0d2445035a210310106000080801000e035000410417000150b982d000f00b404a46140550550007a17001204025960388903403d100030040140400108188507868044116103441103a42c5850702d01480e084034180e070400350b41034280c20a0800c08204140e0113200728500c2c42c6000009028150590300d844d4201d004034407869018035110319504007151383d2106007071194012107041000712901e0381001001000c6041038079000b0740c40d00c1d90146441e80580c42050b410858403008155106a001c04c0c4405864040d0074016001000c0c0300c08262148512100b0000740050365901e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 662391465 1250 662390215 662390221
    0xf0c120c080d09120905060d0f1503080d05010f12060b060904091208160917030903010c090f0906050a0909020f04230a020c0316080c070902180916030c0306050603090105 75
    0x131202c060300002c010f60900010001c00c00c151f84a100664095a01480c00081c886004500c0200a0081c080c800c0e491900109804000c014100d0090300d0004515041040701e603803680d520860041e824059100310b0ba031140501000240c80360040c603004200508620704210b00365001c02c056849012040310b0304100c001c0e05141c15548451103aa00000d41c1c81c5003011114401c60141c140c031124001c1c2d05011007400d8110a00010070001c0b5200444058020003c0402080009003a49858000c00d50000d40f4440001204842c5001e02c80c2580c000424140e40035103816082002000c500c44204d80040c0e01000e0ad0f000c0c0c0e95240703d007140c1c3c0c650515004100340103003c291110110024400e074003852040c03040c800c80c52000829605d2090050030300740b003254003d0800e8100360049065404440c40350040c003141000e025005040b0032000304e04030176101800350041002d219400c417801040404602c407403070511482034001400180103810300041c0d280d1100c0102da603c1c0c1c0101c0e44510305039100c40038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 662392715 1250 662391465 662391473
    0xd1a07230d050906060630100608160203040b0912010603030818010e1e030d05010609091404120e0a08060f10060c0b040f03110a05010e07060f0c120c080d09 69
    0xa92039000c001040076010b680341c141c00080700c2d8017070358091f88500c2058058a052552001801e80da030030190344044000c030b190035024021800c3c102e001e508005507192011030198481107441c41c030b2901d9107401444c02c1c00d040a100f5000d40d000040b01d26441a02c5179498001014203104110145002e603070340c054280f41220b03031440d4000400c810701e01d0316854210380b004902000306241c000c00741503c2810a20885407642645035003c0c0076118581d0300c0c03506000080b11608a9a8a01122802c55013449010f0004042240d0f481040347e001c0d1412031990303d00407045120309421421202c00038020b9115503140c0c540035280000481c1d1a8a00918010910042003c0c0b060703100e006000b02d260a401125965a66000c40c40e00a4070090a400c8000c2c644420180515001d14640411804940c0d0f81c807000e0800318060f20078400000c9040c010480c1c0401c20502c1420681800d41194568101c24141c42ea12801d001d808d0000c21020800441c00050006901e1001800c240030841e401080c09146410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 662393965 1250 662392715 662392721
    0xf07050106030221151f060e090109050403050d050703061a0909010b1603030e0712111216030f0203030904060e010e0606030f0a090f2406050d1a07230d 67
    0x15680031020320313080d403001445400144190580b1019202c4091036103a4800d03680c8011104825401c442041c030b1000320301164001ea52800b007442c00c6490300303100c2e60ba408030b0070122441a500900001c0e8108156080040650082c0d500400d5502c3c0c0010200da0360b10000460801e10400005a5000080c5800752403810342040340c007400f4a01c1409203400c43c148002d40001b031039010000c0515840d40e64178180c005081c09094000c03c1c032044070a100b43c0c036528010098101d5071180601c0356000c24287c40d40c801000400c261010b04c040780401e8030b40e046460f128001601e48400320b0f4584010001e0401c2901c440c000d000c021300c005c2c04800f0455040a114419001300100301900842c81071040100110581c100540c00c00d06100000500310424100102c41c0c568951002e8050324040b4101d020501d00300d00312034407083c1c400d02d0800200d6290420407005011094000d81074900040b400ca02c0740c04500340e5107070084680d00b042460030014a0710810702030b500f61120a8403504c00300e210380080c40940 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 662395215 1250 662393965 662393989
    0xe0c1209030405220603021f170106090b0d0609021201082b111e1612050a02100207080d030603030e010e240c030304081b03040b0a03020f0f070501060302 68
    0xc0607608003810100400d010400d5121440000081d43c41010349a10165000780d01640c2c01802d22103003402002000a895000f140d408000581074100d1885240b6400d18994103858090b55076104007450104940602d811100c80080380b940d44540c0000d45094920007040307007124201001d503541d07240c03a0005040580340da01240701c2e03e4500b0700742160381c5418101004940100e00708101051100404240f5101c0100c0c043d104a51040c241d06e038100b80700186040080c1e40203083d01c00e076940c80b4110024109080c000040013980b00c9914500185000d0680364440062031040f60411680c800c40310b850140304003940c1d400b09694031340610034551301c105a009031250a02b0301e001b042e001c5401203001d9180c0d0820a401c110301000080c442d0412030f504031200d04c4d40b41d03404c81ea120705041c20030b28034540c40741c08045000086889280c43c03600c1c0c04002c0c5d90465007240713045410000514002e80281d4049550240d08420030007c03c21403219100140c10414055000024254214030520500c0d043e00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 662396465 1250 662395215 662395231
    0x30c220f051207050607150c0201270818181905252d051210030803130c030c030308090c060301050a0611070e09030a140a0f0e0102070e0c12 62
    0x1c1821500305800039035001100c00507104260341d150316041c401102c4211580c501f244d50300340021800e02650541001c0d1602a034108031b0308030340d08a100180e0010f120780310001c1a242e001c0c0404010701d2020a00f0019a4102510030110801c156602108900d0b08407884c5c410350308104011000b0350310700e00ca50f5138000e807058040924400c034036031207258a038005200c9008122606400581d500040041010702102e0040c0e03044204100e84005400350f00001c1400da26451018001580e0115005000301100d400015888c690f071a009100e46500a204030180ca02100d4560000005a61440d84070025070181e030707482d0f0580c201441c1d9281002030a03110305110700010f000600035507403a02111f1045a80070b08241440625079200c1506041c2c683d1310417107185124500f04901a40084003d2100042d160f6a5044d643e015010141050050340d10341c02c0054941035080c0d0f4524040c10138015903540500481c0c6030250740340d440c0c02010000700c0f030314101002c0100303004005044405c0415042094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 662397715 1250 662396465 662396479
    0xa0f030f021504020d2103090311060c030103080d0b0303030123030615101209080a120c090302090405150703021b0303160516152717030c220f05 64
    0x48030a64481c1480251002c4d11071700c520a404020060040e4a0b460207012a9001c0e0041c2410380c00c0c0a0010315505500707402040500c1702e5012440e0000c01e09921410616101e10b0450342143c4600455400410300780607050f40c0d81803c50500e5804102446c02820480e00c0201c0605150030b00c140501d0780701924501940c004814030240c0d400c48100740f0540b14080e54542c50720410b40108851003508407000000592a110058040c000c85800422044510391110307030046041e400c1920813203100102280024048400070300040ca4442409504513018a08480000c041700c0140d080100c07080d900305020070b500203a0385404e001a007101b04e01b01c0c1810f401460641c580001075020500d00c22110f0010085c3c0020300307110312020300301c118020319082032981c0e0b5000d406000c0f0302c00910504c025541104107902c400c0308079000c021440d00c4455809103074600d00318208211030400d9003001e000045000e85c24416409800003903600502102000810b440c01310f45410000344c00d59141d60001802011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 662398965 1250 662397715 662397733
    0x140c01030609050f0c0c21130f1212171003060b0d02060d090c0b0703050301030c1208070b0c0d09060b100219110102030909180106081c0806060702030a0f030f02 71
    0x4000d03496136a00c50494402e03643c0e500c10f1003255a0902100d08415044032009440a240185d201d5001c1c2c0110180f9410000c03040e600c0d011001da100c85a813090391044100c1048001c005001d02c00700c0700510fa41da00b400103c5410311201d1420300b0508403413400c7e285086000400c10302680340112001c1035400d88900810101d960042a040d100346200b00603030a032200e0128041244607203101c1c000706940c0040d26125000d92400411980c0700703100660b4020b0340642d01043c00d210030603007803017200d920941e59850070207107a0b01c080384c0b0b40c0010410143c581e81848801f131029018041c11085511505000500500d20000c00c03140c030040c0000b4504642c40071742e107003c0030030112b442800459000540c8140c41094400101d14610070031107042e0b00b188026080c81007007100a0200c16030440f01c01c0c001d111554440e00d1141e5034200c61f00884131142c0540e503803540194050702c1c0d00d640140018102c240350021036000300b03141c866260400c803a1b21041c200d205080c50f51000d5006020f5642d0303c0a045224 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 662400215 1250 662398965 662398981
    0x150509010b040e1009140403020d080705220810290108061e060d0614010f02061911070503030709060e060405100c05060709140111031801020a140c0103060905 70
    0x1018500501d2204600031003c990700704d0410540380014880100103100e0310100b4180c10741e9134141500d08602601c21240c60008590041d003080d48036a0f410394560381404032009806014020740341251004040280700414200c01c2400303405030703210ba1a07d002c1003105010f4854800040300c45036546042c010b810341510a0780e0310070201600b04c64100d03016000c2010603001c802c0c542c9048114280d0064000810f038490708016003002d021100204007586c0901510390042d075030325200000c42c10044e0070074000110b0040401b890405c8030711446d0b200190702c0c4110004048141e1100707509403031a910120070040d0301c0740c2c840032403c09800140313081c003001c60552000c50243d0140d8010240710701000d520030722506104030314840080d81c00400703c408604200344c01406112441c050071280101003418130b006540504801d003c84018040251b00d001c1e0b01c0810384680348080039520381180503400800c404143c201c0103482c1d840700c1d124050b2044020400025040b110300f0b40c0201d10032410712040000702 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 662401465 1250 662400215 662400217
    0x7031e020319021204091e0f0605090a02031e070e03190c06090810020d2a020c04090f020405060a0305070e0105010806040b030c09150d050a1e0b070c0204091203150509010b 76
    0x41b4030071030000c00d01180920002c0d141c1710540d111013a0b4580744c5403d41c12a481d131034010104aa02c10784100c0b0300e41c0c0714254020b007a444112190205011100d9140242c0d8420410300c650010031880d100e40442c620000103414054081d40308882014003854030424840d02c1c0c2c07035200091035542004040d25240959081c0c0b541c3e5829142c0042035804200c071000a01d0581040130341040205800380000c020581452a0040302d40314080180310729480414542058854507451079080381d0080c0d00c0c210164200070280c03d000f060741c0c0d04074110b5030700080000c404105840142154025500d540d605100c00100b090100515451141e0708000f07600d07c094801103038400c2d24004c1a0340b50701c1c4a43c0d4007903003100c500054801c5a034100281341284811300c80c1c04a2400c0c030051154100c112080a103503038060601440c000c0107000008020b0200303000342d01131b4400074199440600089103044041d261341465600c80306500300440e0301c0d40c007071810304e91a82c00c4140c085d040482d168106541441441082 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 662402715 1250 662401465 662401469
    0x1f05010504141612020a2001050114130b091806070e0625120504030203150108030901050c0a1b060e01020a030206070c06020d0e0a1a07050f07031e020319021204 71
    0x90301e402445090309a80c884d03009a42602000039055580741881c00300141440b029440f050303005800d03940e43e0b0b01241010b0103054120b800402d5a0030f28290142c04202100140c00c80f03620001360354840030102511020016441011141c03400b0010300030860090b03092100041401f41040742d5100c1100a5549810550300702e05420002254414080301d180d1122041d282009010341d242d803510209401c0d40480140140ca100342d081d21300a40e00c4078100d240c2c130303402030040c40450741041c0141540c95200742d01a103500303610007048450800051b29040080d502e426600d20303001d00d405078280304440e08001d000035111000c0c40106140703103c94400a4130303010003624040800c101c003c8080188205030701a94102803800c082007040c3d505078100da41d41c0e038a0408003150075a18144076031b400501e4903000c1d144200c1507519410b2a185508207410007075800208200c2c184241d24070a0072003140900030041d201026a00159921028210342401e50000c28181d5000c643c0720380401c1062548500030303502 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 662403965 1250 662402715 662402731
    0x4111c050a0b1f031203110910050703020a0606090b010e121e100e0705041b0804151404140616140c030c030c0102090a0504060320060405031f0501050414 68
    0x1940741c440915840c0d07030003607611804000e4602c80d0000f10501407405c5069441200e41d85003041101c50b082107a041c103003d5015001d620a5040510b148500c0c000c0004291040c864419070b00c9003121a42c42008452a60b000308084540c0c1d2181e4003003550f0400d425024008040b07a9501c4a401c02c03001c010303601c0d440c0c8000c180c10250203841c0615035250030040d070030704800c55100034040c1600c0000203960f10420382c441c0c0c1d07100314240308510303128505c000790012003a09207a0b203000c81d640d166251031183c8802d00d51a010b5a541d9140701a03126150b810f40140114801c504048a100450381ca0720320780940909900310784142d820061070544e40207a03010240504140100391074104184481d4114000c00c0c2e05102c2900001900d0300141c0c0d8190300400151070300715001015640c4407400d10040341c180b4000140b80b00402c104036500b460054882c251a1207004080c2c5140039152000719040440e020a04a40100e00d0080300f2031b0541c5d980903c5000d0b100a803030400586014851010301c80d00d003e40022 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 662405215 1250 662403965 662403983
    0x9021204060c2a0b0708060105030703200c0309030c0906030c150c011503050d140f0711060a120b27090c030a0804050301050f0601020705040e070e04111c050a 70
    0x15030f0103048581103d144a10924002c2c240032034164400e48a007500c101c0d81c0361008400203036210b01901000340103c9060f0756490a5507240709040d001000c1d20b03e080d5044250b18040a400c071184400204842e15200015545030090030050602d00360a00c521540708030500c00410009031000a500c0e40c01500c01c40301c0e00314180c4e030021215541d2142c070800c11225400c05500746044038101c10f0710402c581c404d1044500d0180c00c1d007021112075450300c03580504540308000c2c641d030410351100a44823a501541c0b00f120f41680c403c001422590190109202240d01540d800880800900c80d6912004003551544020300034a84410404548102510280401d40e000709003003100801c250506e60704041d08072043d00c2503c1c06d02610f10340003807107024801c0d0300b400c0c0000c01c5695010300c071324042c40f01a001045103d050008200182017040708560440c0325401000420390025820140141e0040e52a000005004428002007146011000c120181c100c0e0b2101c000030800100d9010650b00407a00d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 662406465 1250 662405215 662405231
    0x501180c03020f0d021201091505150c060a05060a08070e0f280209040506060a09150309172101060503070c0c0308070515070f08042303031f0902120406 67
    0x9800a01500c9040245200f000c110741c0014286580201446200c041d005400750b07a03680440000d8176041d407a08564603044100070015418444008020030321021881030500714040401864000100e540060b62615001400030b1410050206005006514050800301d41407420718104e419016251529a02210303001400f440001040c003551004085058400b490740086184040d40042d0780161182d0300c0c0c1030115185252010071502840a90340383d0412480ca0078052810398101445014103043d01d40c0c1c8007100281c4001640d07890501c41c0b03a42180c031203540c1d050940c030b408031400c2d103c2501c210360750044c81290b8114042e00d500c84c030789280c12a00d0840c140b8201c865140541c2c4000d10503403011900d034041000200d6940c8000740040c0c503030416540c1e0800121500c40d0b0184950010070044808500400c1124a28056815550a81d0078088811034207061942e0700440b6000002140c000810004c5c08800c0c3c61040103180c4240c0c191b0504410f0b140c401c96184024100511084d81d440d14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 662407715 1250 662406465 662406467
    0xc02072904050319020109061b02040e011803110c0a03210c060204060c061401060e0f030304050d051e0c13020c1507050717070b0c0a0c05030a0309150501180c 70
    0x40380c010b000080c05440002d20f115110a800400d041022400700e42520360101d8528815078150791018124450800d0803a060f4003848001d02085078962030135521010200c0600c010244028110762180d40c42e0585049a00d14060401c404100050301c13401141d002000480d104103480c6c0010300280b411641000700612091f1101b8440308401000f540c004100020300580002c54080d800c0d015080501614660302000b0707801341c0c0709000c0c11340818080503420546007400015601e10100140c1100d240c2911180010340c0c05444d14011542640070100440240c0c514841d50389050100324001c01c020742c4c11100003020000e00c503c0c07042c0700a9011804003080c500401582082c1c505043c003107081c0d41400345000348a680810f070300365011160030340c03a840154060012104003540151181d8100d0f00ca6030368412041d4003d1051104010640c0c0940340401e506000400060030151400903110000b4a0a240c940a0413881c11441600d41401003007020b90000d2645440400b1000025504042c0d1380 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 662408965 1250 662407715 662407717
    0x306011e020a0203061006080a0603080f0717030109020307020d09080604110d2001180b0703081801020313120f09030602030c0f04120605091207080711030a060504060c020729 77
    0x84044e5240c4100c006000014692048103000d4560726a10084141d41d10a14001034404611000300208001c02101c0c040000b10009402c846119244134100c075850450303005002e820a811141384282e0000902c42840c2e010894040c81c0405c0342084d003655881d1030581a210a00200080e014115603607490329a540c46405160780e050740461131080e03500101d40100102c0402a0b0707120701003403800c0041c604007008501400100c0e01440b04151801d05a6642101d4243c4007508031030908101e4001d00c82d0860081c0059071143d0544000050300070300c5403c0c8440c1c1207441a49001c2409840070210103400e0340301c00f12509483c1c01c1003016940751511030800707850740705404400c0c01103400401c0100d24100348858035908a40201c4050005407a40394501d0784407401d10000100780e941c03c01030500080c14074400b8005503801761021002c0317106507002007420900c2c0e8980c119403095803907003044100407041c4601440241244001e10b030031810400110890701c410044009846460040902c1200603d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 662410071 1106 662408965 662408983
    0x1230306040903030e03211605030f071b05150108070e070f0212040306021e1e070609020a06050c0f0c1309050a080408150a020306011e02 61
    0x1034100002010041c00c00c80905486075202d2000c02018405485400881c0f6580303504111882e400400180000381000d40000759105000c02107513000c02a203500c0907803d62403a0b655250800c05a03542800342d80031110028642c0c8152081180101d015029448400c203c25410f90300c48802a403641464024007041d4000c40340000d1855104820001d0000c005005503405c00103800c890011661298000703440c03640e00021401c4911815500c1c50480e000084203d038100720601e82100750010007407441c40410a8003041c184213002a580c0303d540e003154024540b01503180d4980018119400504042c0e410307000d1006548100c0030041880452040000c129000c01c800c002164130003401c60302c4050b1900d10071759000800051100c4010800b8105403402007540b910000c010350a00f00c00244001c0b01d8900500510020f070b600201003107158031804101c07104003140030030120301d80709084c = true := by decide +kernel

theorem cover : BRFrame.Cov 662230215 662410071 := by
  have h0 := BRFrame.cov_init 662230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 662230215 ≤ n) (h2 : n < 662410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
