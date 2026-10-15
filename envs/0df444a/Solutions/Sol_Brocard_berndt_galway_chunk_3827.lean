-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3827
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:47:58.57398+00:00
-- url     : https://prove2.me/submissions/74c1277d-d745-4da2-aea9-9a8c0eff4c49

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 688129496 ≤ n < 688309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 688130746 1250 688129496 688129513
    0x30c0d1404021305091e0313060306080712020904140c040f0f060f030503040e0711010603030306050a14010819020f19080106170c0a030b060d0516090b04030b1f0305 73
    0x18030610f003860703000d03114249040400b008049100010803810020341004140d44400160070040d0540c0114102000720450500000880c0380d8503420000a80b2462015aa1210781d100307070b04520b040c04854000e401030074200000e40450700803030348411003014031000e0710313140640030300020120f8405d1080e06101d83e83e0383d00c080c0a4080c00344a410050288184c4c10010942507854960340c9004134881c000e03100411600194201380718020b17681c1c403800701500078401961070313140150103401240102c6005010150300010032151003103803001c10900685500d0065119080703089080c50045100041e034680030880c0c2c549400011008082d102c40c20020145d10007840c1600826660040c1d021400f045040c8030b424101c51131044c44150000031000c1280d44e683c0c1d28140c1036001d064040b9085034000800301d06604590566006940302d6035036007181004410206106a6802c40d0307502690440600c10f00042c0b0001e075040c0c440e04d820038141c01c03002d5404c0f400c83d420f40c400c1c0c40007600216200c2d0400e0b049c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 688131996 1250 688130746 688130749
    0x402160803070c03180326041214060708060627030304090f1401051e19060807021e07030f0204020702040603080c010b0102151f030206220f0303020307020105030c0d140402 76
    0x106510152143c01d003012180c6e10307607124400701c19a00740e0703409228000012102043d08080c001c036001400030000d40ba82001c40c2d4103100107014805544114240204000102183d1003606034500c1110020521800e000f980d007180300010070b410060440c0c0c240c00d402004a29a01000608010000104013241800e00014050243c400141d03c0f040114117680c014003040d924407a040a030046d0001c91128880c0e00c0000250b040c21502008215410299030045426644001c1151103000b145e001c840381c485900d0075a41c801c4030365030007000894020f40c0d81800003c401c42c0c40301c1c6ca9030307000503c0941440502d030005422680c2540c41103414003000507004600800a0003040e05966003400070303110494070944c1008981400805410300e820b0720050302504119918008000b454014142030348030075002c82c1055900709603405012010600c4040003542c044e49041170002d42e075066015509040b5a030b4010340c0d00340c00240003c45010802e02c14141090124420800300341c0e040001c030344941c04c0600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 688133246 1250 688131996 688132007
    0xa090305060112050c1509060310051e0117040b0109021b0105090a0309090c1b1e0303020d1401031205032505071a0907050f03030702090901090b070f0e0402160803070c03 75
    0x58106010303261b10340481501c0d40d490010f0703c650440c10f60301c45030b80341d44090329410010740542016600c0391980100b0100b0703200642101210250a2702ea500c443c020901119041d00000c440082c001410f4030018800840c1d603030083d03d041d2035224564866880b40001650941d0703001c0b128000141c0c44a02c2000605521100705070040101c0c4000300840600100010001d1055002c0c100c003000d00303c2840ca08011545000c100d90005080050321025090b00c0c000b4080c2d0301c0071a00700e03000d60410180e1100f50390100c0145049aa0084d045555070348201c40c00c4d00c081d040140400c18060b195104110102224064505c02c81415500e04c3d95541f207504d001c01c08402103141c03e9051691070020861021000111581030f68401c4500902420341080000e2543c410700038001e420070410805c1c00181101500009461845241200101e03650b0003000c9070517511a0140b140007901d000091490390805500070480c42e0225043e0030000344c1a81c44101241e4030583c3e00c1400100a941001c0c1030540c0076 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 688134496 1250 688133246 688133263
    0x509030f0d140307020c0d0c0b070f1b05060d1808120f16020a031227050c06031306090804050d14010c021903030b06040f0320010f080106050a09030506011205 70
    0x52550743c0c00c5060040c0029074400907103003c54010080070740705409024880c0c41c40f8001300700c82a821130740c0b81c1040ca0b0070140c02500200883c0c054024091001d5000143e880b01c0c420f4500140856040a1401700901c0207003041110b0380019100c070620301d001007100700c00200005210710340c4160281c2444584904882c8008005c004e0b405e1001701c02240c66640410240e1842e901850f010511100c8611010010320240c0300c00301003040810b001c80003030442c07080929905809032003030340e0360000c169082c0807007484201c81c002822200c55841e00005440b6600080700700e4080c142540c245901e903000301300758010014013a2540c071241031108103001424090110341a0461020b00f01044030407408580c54424410000c0c01e01d9210700b0782c0c4081d521007000f510000c0240210b15403020b079807420458403014801c9090062500115480c503015406040c0c201c0d007480103031761070681d580e190403001c84054101c03134036050400958440c000041001001900c0c0604a4424110f44030340251400b607117401c549 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 688135746 1250 688134496 688134527
    0x312180308090613031e271403011413050708030f180d0c060f0c02040c210b09010b030402032a0f0a08060604050601090308040f180b031c0509030f0d 66
    0x4103554006640b00190301e2141c0c0c0c020340d50490a81b403c1d0340035900c41c5401c040c80e07000c0030402000c06c14425080e090400c102c48017910410f0740a81b07048149801e99901005200d01c0c0301c1c8150201e0ad091111071880301086006000391101d00e0707160900542103521810210704c40280c04180041810518a92290a040d04070780450380f4404035a9040b4500d030083c403403142440703104080d007040300d0300650640b122580d0080040089005450014280c0804158502c030508554092041082c3c000e00c22034180c010001c100c00b5081e8601292012107500041040742c16014080031440015289180314800902c2119145c2aa504e0b80092040e141549150b0034418205001e04110600001c100c454011400780c0b004110741d40c9600c010b9600580640c0024602500001c002070320311034074000e070310031380d041092888210060200c806003030740d2009160310382c1a0080b09109621076110406d940c0d01050605082d4103080ca5800085c1c10030b407044550150725001b41c46182c2d00e0130390044000044010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 688136996 1250 688135746 688135771
    0x90f0b0a020604020f15030103060c080903130e060411070c2102011704030215010b0a02060a1127031609050f0106080c0f07060614010e0102061303121803080906 71
    0xd1410300a55940015101034098848481d82d904c482d244e001910b80c0301a03110703004c103030341e542c0d00d16081d401009111560b400041c40c0341c01044101300040110340740d041c01180001d140071700f4540b11803c105c3e00904060761141da62030300c000b00e50ba240070140c000700b8041c1428107803440c078100f801c086502444451101c2c0d0b090300407080740143c0c0c02c09045401c40c01070f0003c480c095503039803505900d04038040080011421101000003203110210b0300601a009003a42a03446a07180c8a051806641c400c2605150f081c0c01804071070340b406116034400c89014001c40d141110500198040b90405c5030a941140448104140900008181e4028a5080745420001328003d41c50108010002403019200800402d40051301100640c5590305480f00d040e003044007003000682d80c40611640d1a410b00b902030120701e010322507541c698008203881d031003034440f2200034188401950f1700700d5181900000ca180c01560b1020792492070b8900c4000c0b68642803103526804054102940c1040c98081c3c0146114002407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 688138246 1250 688136996 688137007
    0x2070e0c3a110417070306020c0d0e09010b0a0509040609150905060f061e0d06060c030210050907140a0e1e010f0312031107060516030c090f06230406090f0b 69
    0x141c40001c83d821910842814059070072a410007908005031544043c1405002090512040201085160113052551240540d08518a0038015500c209202e01c07402d4017000d002e0b80d40318a000d0002448120720050002840303940f200402804c4074004110800780760780000d418030986200344207550700400200e407108c0015081c0c4002481350f101c0c60f0070f1000001c103441c560800721140c00058407410700c078000041c0522922a40000c0c500401644154018401c00d224031900720240d1040e1406103200c0c07400b50054034140401d03010400d00380d50840d90040e203110800075800c41d407030002e2401413143c11000407101100303080840040360180c01080d101144018204002030504044840d100a94200841e114805008203111401854409008682030500300520307615100800c5407010402d0700c0402608000000c100d840e81e80314020f05e4861000150107100e62406490b49030012507901c00a40000c2d0709805889006803c164042d01c0496035600043c80700403c031056090151402841e980c1c03c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 688139496 1250 688138246 688138271
    0x30b060c07061107090608060a0605060a08040b06031207080c0705030f0601030f032007090c0e0a1e080d0807021902060715230906060103090302070e0c3a 68
    0x245003501c120810300c00c414450114410080c42050000c210700c1008110040d070707c42955407191000c443e03401d2851310f42a0082014900f03a01950710240d034503076401c0010303074880da00c02d9411318000d00201e504d44103801071242980004001450307054401c00c43c0c02e032140003a080d22407500e040740d0022031094020b1543c01c0c804040014030541101d8200310400e802d0031460506035030f41c510490f244502124103880030111800c0018041003140c010307200410022080d098201c41c1101c2b210200e03644150030440400144e080e0000c3d00c02c40b4580350107105866559010703020300c0c0c60314034141c0d0004644008108200e4030f4052041c2e80003d0080e00140100f143c0507070008880e841944002442282c01d070700088144139443d4040c20701d04101c1c2c6103000d000800414a4560400304440802c041d00c2a00c0005407254864050000350903495002001101e06064042e191140c00801d444c1c101c9100b40705072500d4a01131011a1608071600d4009256104108001d0040006640181c901c0c03500b000041c5860 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 688140746 1250 688139496 688139503
    0xc0d090c0e1b0d0b01140d0c09090e03040603020c0f030a110c010903081605150a0b0a080a05190f0b0f0603061f1a1608040806010906060c02040203070c0c15030b060c 73
    0x8600304140c0001e61503c4030340181d50400c2006d5044948000214410080c01c2d102e0340715a000c0e0440da01d80c41500b40e59040c02d03000341c0d00f0410000c4480e81040c4010810140681c002c1c0c0f00c1d452410302507031a030050124209107550401541d035000a000041076103000c030740500101103007203403c4c40c001084900710b2319282514840c0c4a001248820038400c12411b1003024400720326400b4141000c056281043c070310356070280c400c0c00c003211b220704885040005c07800e4002030084c074180d5012000c1c00b048802d1700314088034056501c1042e03c94018460008d00020a01048d80d440f03828006080c94050030320005051a00300700501601c03140c541203003145290000600313060100d419140c42d07111101050422031249005480000410a0600050728100440d801c06841510103040807543c06e6070f652946881a00e03128030590340894400041d000c09805c00d5001940d04c240306084c0422100655907072101e6051031070b4060190503585c401d00c402e44642c14003c5080d001c5040721014100000c1c102e41d181c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 688141996 1250 688140746 688140757
    0xa0b011505070f14070f090b06090f01050708041e180903170a0f020f04061107061209020409021f020601050102010b060d0c11060408090307091406090c0d090c0e1b 72
    0x207121140c0e218004008048252540c4d0b45001025604000d03941e072281964041c460140713012003810324043c0321301c0d4207150050f41c0c034170180100380340c0d04442d07110700555070383d072113600c00781c0780ca880401010508001c0b5225400c4a007240000518216191109250016240d200d04545042c104815980030039030141e0030405280395442000095107c5980400c01413022200c000360042c008100b08541c03013a035401038000c86026464000007032014100194072101ca6004080129915801c021007101d910b41c406030001d44090800550081160000303061040048500e403d4080040d421300c1c4c2e420381c148005401040d080c0000e20903407226000090f01c5028100d0741008861f6140c401d250f103903100b00c900212200c00c03242a11500c1c14581440304642e8070160509010384602e05000904503202d103c1ca401c106d01140c44032400792691402c002c060040a00709440072001808622038090f003500c6540c0540d03201d038600e6100f003440c0c46d85650a02030014021242d095005031400400717232900342180c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 688143246 1250 688141996 688142003
    0x110405060102031c05091203091f110309030d111303030806060d0908070b090705010801180e01110408061e160201182906030319020c04020c0a0b01150507 68
    0x180554030580100d241d40202c0b15000c1d500706401500c1380066149900c0940502c00300810780e04c0e030000c1c9108180c607500c0141d4400306c0b02c0d0700c12001c034800011006c1242c10001210480801d45040300c0781d240d00d1540007a10700141035040080e117180c04e45254454900402d942905c600c2c00d042d980c1161800c8201c00f48005814041c032400041c04540e200000c440844000e100c04119812041c1804206030700121021281c29080780d001c03400340c10b00040d1001c02c03120144e42c2d001c0396a080600000c014a00650071011030740d1142c5221850900a008951a00c210342c0c0002c0d80f00c40ca0580f6080c5044000f6200e880000042c80da404040610344110350750200348007508545003164441d041740100a0030080c0c0e8a90211695103100b002048102c1c00801d498680903010760130300b448032410080900f900c04a6059204004800c682040040c02c00075209050055440900d10000031506aa11556060b810758002e01c85c60070402900c58402405032030641140208010050b06c050410b00c260f20026 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 688144496 1250 688143246 688143251
    0xb040e0d03020703090f0f06111515060c07080f1b06090d08120a0c080603010e0a0312020409061404050916030b1503030703020a030305060607021f09050d080408011104031104 77
    0x2002c0c1409104101c0c01880030f0144c02003003654130754480441707013610b000e00c00001e1035509d0b15a4401d84c0000e01d0a5101051150550081e181c501e403194028032210f00c07030b40d0410701c103000a00d4800d030280b10f820f00400150024082400c1c0e101a40c60400c185881500f800f05400707185507100b034568000b078076000780e81070380c0340700e0310420310309210810303000d00c00b50b140100c0c5ea100104000d00c801608001104402d41e01c98040a85071381c0201420707284000c0d010441940000009404a0b05c904882c2030624a101c20051a01e500c8801c400e090301d40c2da41021315180c08091002070581818070803030390310540d17010245c80d9043c000d80200821041500c4003800b8408200041001c00741e040800c181c88035402402c880c5d98914030315002c2c6d180d140d5a141940403074030b020000b03042420000d0403103803119401042003034100340c03100c0c4400d11700c0c41c01d0500c00c0800c09105d4002c074403074564880740e01c02300340110b00b402c0c0c855140c011441d00703540070b51081c0d03006960b081c802000058601e90b460313015401d089401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 688145746 1250 688144496 688144507
    0x8150c030709080613060f020429040503010e070f06030212070c051c080610050306010c0b1803210106050405130e0c0406090603170a2c030102070303020a030b040e0d0302 75
    0x440b01d080a507000380300b03140210801e1000f5020861099a5820701c100340500054642c08040012402a489245041d882c00814481c4913031000d0040b024051508448608107522072000c03a01311010740035001120362003080140120b0b1802c070780030401098203240651500c040e003245154120000391036002403050802c080b408008061021007081101d180c440f4030b000e0111480144a00800e642d100d00401e0b01d85922442c00d84907038100c922032407041c0c40781c07000702c910f50f940c4142c1082d00a202c601d5500ca618400340c03150100744020a54003141120800781c2c032601000d00e046001040e4840c1013400320800003008240c030740c0d1042140342860000005100842c60000600309400150340c260b0080c81c14102080e54003640e813100081c1c03806a602d030510041c812007065181c0c41100e0f07074400411b0b80c1c048059030b145405051404401c0d840c0e003003075000c94842804030382a07821450048010980200d800600c1a03030507c601103042c1f03001c4409200c150b03101c15040b5241c141c0f203880c030810580c00250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 688146996 1250 688145746 688145761
    0x10504050904061d0f104209020f04051c0b07050c070905070203030603160e010902071e0c06020c012d020304030501050a0603020117040c03030f0905190e0c0f0415030e060403020601080708150c03 86
    0xb03908004040b00e003400c1d2b5440407885002d190591060040900c52195541000410701d58910f00b0b0102d503900212076011a1201c130020f55840d08030003d03400182c420305c4004104000203001c0d090103903000c0e8004549074100b000030542002e071002e108400340200ca40c0104446803091040781d044842c0c01031700513510103003401c1a0022151441e0840706c0e600d80c00000a04010b000e11800b801c4948980c00d41c0c51041341040115010820f42181c15425030300c035174100724600e00c00310602450f100030b4011070b85000e54a60314a401d40b035080b02d48802c074a6480c00e040095503048001c02156405054125005141030781d900c03050f0500c1400003030708100c44c451044c840a4020b82401003e484000c183c6074040c0c0500c010201403501038012044143d84050104520750710000c01e84000b810911603960500b41485942c0010006085e100c00070541c5505401c40320071b03001d11030240614081c2d405070200e58101103450340b074001c065108108950000200804000c29140e00c0da410224041d4219545d881e24907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 688148246 1250 688146996 688147121
    0x3602180319021e041503050d02070b030a0c030603021302090f121905070b0d060311030f0d0302030703151502060f060a1a130b0a0e010504050904061d0f10 68
    0x10703c0c0300c2d001841c007159981d4402ca100c10311800c8a1180c81164540900034008a80742e02e042e100386424210184045281102250045130350404c41d494000341003070f0350b900001c1070030704402d6101c103000340c5c0094240340c4d505004024280340700d001d07900300042d080f030324a000380d890700d202c0c188080c040d4140590070200b20081c0154002050245c1a16889074141c2031650000c141500c411220303400700042009942c00c0124481003c2481c41000c1c10000040c0d1105a021b50700042c80c0e00201603840c01c1208118080581c050080c09103031520059280c4030440c0645001c030b0241410040c00c0c851000c00100340d03035804091040d14600c50051030400241c2140d00c0d10303809400c08440f14000c40110210784a1505c4001d0000c14607103039a44500307210741100540311849140070b11500541514006004a2002c0e0031804010700d086407560407980c50000002d0900e01507034850f1120707070003554080f4445000d0307019013909603a11010319113405025452a01003820200001804286181c006802000a10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 688149496 1250 688148246 688148299
    0x15060e010804020d14030a0221030105060d060e0403050a180e0a15030609121704020604091d010606020c01022e0507140d0605131401360218031902 65
    0x346617404065a40c1300c040c2d140e80028000600501c65000c0d400ca01382c0e40582442083c41c02c030284a0700d140d0030042400010380c000e1400510480c0c480710b000030200300c0f6002d10b62155009070794013a11541000b800030103404241d00103500004981005006502c000b4a1013900030782c0009000814240c04600e02044000b00e80c00900342c07038504100041802480600c0c0e601c1d82c078540d6100d8101d05071038080815481000d84d4041d401c0941844107201846041e405234110b1803100d02d8044090440001d01030130b540242e04181f0040c5c212290343d0003075503010842d0f81400220b801c9020301e9010018001c07a401a844258011095261000b05601c00c0c0100300c0d0360f034450041c0c25640d80c0c84d4055081000944001d105c0c41c0d000d046144884000840644155010000039202c3c0700306030391809101000c080004030142d8050340b4902d44d00c54002061440c1d01c5a242c010007005170300e07022000440605503c40f0205c05003e42c0000310103a803c42141048190040c0c4d0403609480070320040c0c0210305054005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 688150746 1250 688149496 688149503
    0x240603100b03250914011d04020a030f03022107050c09101a03060f04020c030313110d1109090c03060a200a0806030606030d0215040204150e0a15060e010804020d 71
    0x16036482c10b01c148030844400e000d441a02d801400f42c2012804505d001d100244902c003108201d50211400f685460805241c0160005260610050f180d84650620340101907044001d47c2c01400703200c07940c0d02008800c22441e04010302203800e280b01911007035121007204508500c50303015400041d5503200602209000307488209466003006803131f82c4000b919544169407080c400d030000707003c0300281c0c94540211120001420055030454a8404c40c8000310b107111034040f94083d000c0c0c2c901030302507201c061030090880e0203184a018510380050500014000207492140c0d603401001e0401c0e915100020b0058000c43d0420000131000101a403000b50340040300c0d01c0b0039a169001844440061380b011580340141d600320b0076a54a611000200b40e40c0c1d07400c1041100168110b18421030321700c81d0603103d03a94440d0000c0c0c8003080c0c402d42044000d1800741c4c103800c440011040c210500030118143c1c81004401c3c190441542880750420101810032966400c40c241040800c0300002e0442d100d184405004036030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 688151996 1250 688150746 688150783
    0x1a190e010b0403050708030310031b2705130c0611010207020402180102010c0e03060a11190305041e0b060906120a0b1801060b07020409020a080609240603100b03 71
    0x21078000034003542e07016120544a61045800108845401100b20ba010700748801030316042601d5a503232024a080165407175085108261000100c4440c0c5410000000d1181081403c003800a039003000101c842c003500c0f20122074401710400d00081d800565003015504a4140140203061310a156406482241c0000303400600105103400d03034110341c0000c4101c0d604c0c05d800a0007801c1c0c035914101c440404036400294140c2c0410007180742c1600310ba000080e50490505c04501d00744d0f145942689800c6240c941a000980d80c004200a015511040a82d4003500580142c01d080b1151500300d08004041d203428400d955070804181c10395244120040c564250006889900106040019020108039800340d5902170102c090629500184201015100215001418541c1580920006240351030701240c01002e0703400d021489400820280703103c0d180400c000d06446000301403c50660b081008444030b544c0166090001544d80440d1104d050328400000003604c64010300041d10b044091304100e1b42d0401d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 688153246 1250 688151996 688151999
    0x110c2a09062106100509070f120b0d0b011a0307021b0a030609060c0f02030a0c060f1d0705011b03020d0f02033702030405030d050f1201180c031a190e01 67
    0x1002242184c030a09001c01030100190360384003400901d200c04c4409000148092202604890181d45062950005030030002099014800890f440b02400038043c1c2d01140f01500402c64401040304500c58440700d8040981075007001200a503981041c507020350508560400487d034030381c03241c1520000030360704040180200042d604020300140811030750800000c0da80d1707010f00090303030001080316200003050b60350710f0700200e290310340c2c01c010085001049602500d0b840c00c10030301e0000c0b01007203c0900f041400360100ca03140c0350002d01424000b0100c150074200380e061101c0440e402180150ba072143d141021007840c607400c1001c0381180300f5240b03501011440c0104115220700c280002c803011000c0c240d101a030030f0f02c3c5410b0980c0d8a001d2352243c10f60641c000c0610035201c5120328081c00740400d2000c40103003000742c0d4070b82d44001d104098204007811000b1010081c20150306001e0340485503403e040400074100e5001146658900c0d202c1103030701640d500d0790303001c5c05c0d031000c1c120040c01401205d00500c09135 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 688154496 1250 688153246 688153309
    0x3b0409060b0103060803091302031503030712090f0b070303020304020d05190201020c03031e070503090405130218152806050307081006020601060f030e01110c2a0906 73
    0x38000032908070b000a00e0207101180031040001200e1394114001c0c4440310f80326044012002039400284507144804036030a0030041924100050f108061140012440c081c110703150040620209c0c2d800b45c0c0c1c001c201004108041c242d18012162242d424ac41e02681e2903480380082441b0119500004190b0300c140000012010b80000113001414404d0f0300780d901800301e100030543d981c0113008020201036440400c000b0044801002842840d218000741d03402d1840140002d802c4030f408940503484100304241c844114500399001c03003440d07610040207074018244a824201d240f811200f00b50b014400848900e611042e918104a051981000b00140701d181c441d10020440d030002d03140309000c125000041070081802d00c8904042e00c145071300401d003681c41d150080712141b1240d240b2105165844440c10810f040c00c0c001c0704200ba0200c2d410755500c1200042a900e000d803240e102400507022480c2c0d0141b02c4041240440e001c01c4212582c1701a5150400003503e003400050741058014051040f46242 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 688155746 1250 688154496 688154501
    0x3090512241605070305221a07020307091d010c0206150607030c031209060504050f1203041a1b0a030902010e01020309010518040b030d0e031b01080703151211040c3b040906 76
    0xb96801c0780c3e504003a83d0301c0329400032307298003c800700203605800541c3d0a001c407203100c2e8010004d010101c0e0502c00c080b844240c1c3c2d01c7c21039058a80c0440182c0202c0304014444610090f0039640306c10583e0101e01d130142c1da0310014400c140f401c8c002810407815441112011100303811081c60260003000c01c01c25401c1c10b00e0110b903605101200d04c810ba0081c85550003c078612001070324452904604900b03a103415983d204401140010094540c03032110961002481503080c018000342c08042c0c50002c2c00150b6400090030142c0f500fa9070f94115407003003001c0c0e4605e9a1240513240348103d813012030811850200e0008001d401130105641d01485944045009241c0c480c04421140c201642580d175000000040c82c204444034218847c00319445d1008542c80c54405c1d0312044120921000c066141074403040000c4010301d4010003526100c02444802c140c614283c031402c401c09540d814122141001c000100c0301030751804948107148010f001d2401007e440060300700729020b030018070400580700e007840c00100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 688156996 1250 688155746 688155749
    0x260f060415080c13050c16150203091615120509011d0d0306080705010905010c1a0c1c150b1b06011205011404031b0309051224160507030522 62
    0x4035018007a0300e09040c1c0845c1c4104c41c0103014040c50079180a42d220320b80e1440410381502110401d01200e80344001c00d406101441c0501100c0000d401504810b15a0785203c503000d0b00801307081d0000703c080100780ca41140d20090380bc00c840e000850f06642d0101698010b1041158044102589200303800c440c001c0270400106406450320b041180301d403a03000d000c0e030701d244502640b80407420100301440340d980a00040c0301c07154481c0410300b48503917400c524500d044105580181d0f4040c0d002c602c9100d5403268003044909070000b01c8007044100e20305101c00e2920241e52080c090701840001c0c254a03021040283d080750000d689046608959480c0c001e010442c6040c00b0548442d403a02d010040f41d03e4000001c203002c0c5406d0b940c0d02a05184100b0042940750415004405001540c034000506842e146000c0500800c541c018140300c4078010386801c101d0b0851030300311300941103160400407000c00316003401c85003c12610340710352100c0213031070242e659200d04896078121407014140003020007003600c0b100d070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 688158246 1250 688156996 688156999
    0x20a0e0106020708030c030f03150a060f14030906010302010e030f010519060b120a0f0603021e01090e010e01120311060406060501030f020a0e040f0912050703260f060415080c 77
    0x10612684e81e0142601d90003000c80024154204100740380e0001c0005026580151007945401d62841c50100040e10302c00c4030382e0020000c035542c520711206260700041100301c0000500c03521891807a08880e5603445940c1400000e05000c50b4151820141d10108002d801110302c0310001c100c142402c00924150717480421a0801c0281070000214991622a00303880440e450015420b00da82c44501d40180904001c03803291440540c0d800d40000503a0710701e646404c40b1440314203214407243c0a00001003040300d081e00000045844080100a0381250b920140d044440502550651000c41e1604a48100503038240c19814800c0700e05000520515603c6502203801c00d1300c040040710740d403245003000d030300449602c0008200b0007402a04103080a80020004241d40440001c4c4010315940740e600142c1000c0d983d60000780e000c140e200070160400f01080001a6081c0082c001c40c1451400e924441c5004010082003500840411344d151a82e0300304424040e8a9802410f4264580c4011030b139426500c00d096 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 688159496 1250 688158246 688158253
    0x703020a0209060a08031806090d0b180304030b0408130302090106020d0306151d030703080a08100b0403020603040312141f050f060708130f0e07020c040515010c050307020a0e010602 80
    0x2d48604d0907112103422181000c0140d810921580640400c151604041e250004800c0212023025640e12400050503442210740344401d090996282403980043c40780c0c4a50395000700004c0c0041032420940d545c0c4994420034103592406003010340720b0026040c0d400290001c08241c00841e2240d00030403020031204a1b96420081c3c00d9a802c01d140d001d8030b0520441000c611b04108514012002024641c2d6404018080307424240d603d40c0e507622203912415501c1e000440b1a820312030700060f22a400d8000b03080c4041070a0400d41990000340c079601c0701500003001d026003a070a144000030542c010381002006600d003200c25191111a044d21211003000200c41e00c00320400100d0149000c6081d02d0380b110018000506007007103a80c404030284d20459500780c1000405400103280180e12b20f003c405410000f83c003001c42c0c07c016901034600f009003240c4600c035034240010008030310001c1e0305e07411983c042483d204402c0700c210304200381503200b80e0398041e40003202049c2c0841c02030069a8503038121041c136404c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 688160746 1250 688159496 688159501
    0x218040c09061d01030213090603020112110a052506020c071a0f0a090f0f06080f0f0610171509160816030617100f09050c1201110703020a0209 63
    0x200c82002542c0288008111510203141402c0040d098030306410f14103040040c0303080200c55410820000b50380c0701c1c940c07142c2c0340c840500455902c41c0e4050006403001d5414030003c0c00c1d0801d030240c58042d200308030081000208400c8000402000160440b13200c0094690500700c1d9428808080e5011070068402c82c424000c0c0001c0c09440e03100a038502c2480d1400b5107040c928024048070041e40008003480400c5891800071030941a40c102c0341000b440720383c0d0742251040c40c042002d0b04e42100144520354000c034540410085621001c000f85d84502c048032002c003100700d142c0c4107403505031045c0034122194505008114040544020b59443d00004441048c150b5883c09064244d00c0040c031701c41800600c0c0038000c00e641e21144400ca20516616090201d1000c1d210980c40f04030500c0310054010301d512060007031781d003060b0a100c1c0880d015443c40301448044400e0325101c1d030311402d50162501950b81c44e200c0000c441400c0d07000201c0320002c9004541d03251380b80e080085d901e240303212040c1e1085c07624102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 688161996 1250 688160746 688160771
    0x20d150903110a0224090a060816030227150a030609050f01030f03030b0d020d0b0703050903190e06040f080f0f010911010813050706030e0c040b0607020d08040306021804 75
    0x20100c1c03d40b0f600620200410030200c3e50030988050070f06103c02d10b46070500042c910b5940d08400341c405030050380d48940c2c19140050743c1d2000740d14071560400515204206076401d0342e141d500c0c00001c2a204a90549444481c900841c5404051029484850394040788150721a603050304920121419441c0034002da032180d400034151040b00703100007412145a6040d02c40001d02a810503820020000c1694030125220327004605e60800e2604c04a400d20200c7c0c00700304049801d4032420350040d004400841c00c03c018502125040307005c035110031b801c2c4001c030714905842c2c0c1d941c98200c03005482c1c2005203d19003503032401103030b40c1c60303039540140d04190040c064980c00f650350510403043c080e508001b10210101600b070042d90480409411072000d600d120603840c01090041204c0c3d802458650743c000351015100140a0612211a5099125909010818050781da6000c241e865160b0108d0b04200200326610b03044a0911841d40001c1c041400450040d10200c5481c44c6034000c1882540d062295501125 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 688163246 1250 688161996 688162003
    0x703090509011d0a020403020612041506050f010302073915230c0d0207090b060c073302011e0902030d0503070201140a0615050f03070c020d15090311 66
    0xd01002071150080d81c0c60318880c0103096134001c90a0107005182680720b0b00801d0f01544002804540620b40d101400204030b024a5110701214000404000b49d03400d1100056550b5081c2d5011070400d600820200180329080705a095822001440f8501ca90044c50b1414501c0c108415228012151428002405c280c0c40c0c803a51004070580ea2048203500c4166031026402052100060841c40c042c00b015014403005c1014407140010750f0028032049d86402c40103030645420611141c018401400080c02d0310700001003040a0381c0c000b8147e0315500a00c04080300c4c0540201041100034031115507a600c03865019440698025408016a04000a254020b130290f40382d10800940641c8150948028188030710069a00200e8070700c004141075680c40002040080113940000400351784000070014074040412050800c400c1742400b600341403410421340d01c0d600004000a0a1001051010701103503a0125180d0346075510051100500310324028110040603900d0381203000c01c441583c06002143c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 688164496 1250 688163246 688163249
    0x10090e06090705060d02040e040b0a0f0612060c1809021c18060b0310021c1b020706211e0f110f090d0210080f06040b09041b08010203010902070309050901 68
    0x750018900389140109211040d40038128800a041d820300c00031030f0360050030080d24005d40c0200440d12075420180c4c0e008044411100d003060b002e600e0840f0800040d01ca02d001240c0882d080100001c411641007002c1d10740d81070700c05494110441d074510100b80e1100b580d0142c800c81d080c8141441403a20b4090161046030186101c03c1c03007009075004201c00040c0140c0040d070003c00090180c0d9191010380144d034060382c1200d45201403d50a85c41d8041d0841c0d081c0c411142e9040445e03404401c1c45103100c401130b4031040d81340070721820040b07500211421507003010440000d2080700741040019503003114200d00c0c01600310102c00c80d602d08115400d04002c54600401c894958580c2c0c109180089500e45254258440180c00c1d42228180140304096501d00814642d21001900c50f01414504181720308051980207141a03c5a4a007440b200011307194001c95940c0694002e44003c01011108441842c01e0503503480b582603507000000110790024141c0192591500c00c0e202c2c43e0219860350100280c9403000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 688165746 1250 688164496 688164511
    0x20c0f10060524210702010b15090d120509031e160b0d020d060f030503070215070f030c030302090a0f05150f030a110f0c0c1503130215090910090e06 66
    0x1642003000c3d081140004101a94003c030441c4035008803450720605410088031a80051703503545030301c40b80a0600c3c2c4a9420070b082078404541c034100e200b500164000203060405012000480130350801280903000301e81101500a0459400032072840346200585080d410010070390080c0c004203011010400c82420030744070300409444c10300741180c0010000b5001501c1500c80700e238072080c0000f460306080001c40d0180d800b503005999a540180107009c0340004214101040001c00c01c681b2020803070344000720b44c2c1140d1501c0d01030b000c0d20307030343c20110041d0080c0780340e50394400102040050ac0c03058426061003110f9003500c0c0d60000f1268403500907064050740c00c101580b08410000211000c2c4c583d403002c260000050007031800d02a10480100c0181c1082800f120181d0080c0d107464114507100880c2d60703c084039034407024a5032808140703002c500100010b00034021800d45082d42d440c940c81c40151000030344041c2911070a0300e0302040a405d250a14400c440d03006140c2500035504410200310544542358 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 688166996 1250 688165746 688165789
    0x9020a12150b030a06031a0106090603022a0607020615030a02040c0908160e10140d0204110a03050a1d1504240207060b040216080d020c0f100605 64
    0x40340300001d8040d00c00c103040d8410001c40702080001d031000c0690b00892a08400190450541ca8984461500c0c0e00c403001c0c1500b46580100800e5512500e01400c3d2511072030003507164000c1034080c1003580c111800d1010009000b810030300440c58000340780740c0300c0d41042d802c464003601c4405292240209004102c2e40607001050604054201600002d84500c428940002c4859a402c1514200060041c8846400000850801c0480c6882d0840350f000701e0600e41c500612880d01d07401040c040c075440070031405203504400440555072694000d20340029000001c60303450000743c0c0000c005100840710000c020b450103141e040b10651882040100041640007040065465040e800200000038412101050701d107001507400c90040e696601022610135003d41c592807549040400d542121548034041c0b803041c805104420755240c20003450030b400070906e50b030f604840040e0b20003a00c03901c6260b5407148910b4182545030000021b007540d0320038004400300a501c1d107420400c56a1f154180c8400c070001d0703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 688168246 1250 688166996 688167017
    0xc010605011d060c0307050118050c0916110a0c080f0124030b25030501151103041401020c0d03081b03070e0f0d02090c030115020601080d0c03090b041e09020a 70
    0x414000500130001810700301c0e07040000540d240b03425610342c00c400480700079a21000204104082021030105c02d0308443e05840c9242140c0600b46115014071800100005400e13990b500d150240460354039030341c01901442400340c4414002c3d9864901f0114901c2d43c0d8a4440e418000032009114003000b1203840c552810541c2c81d5440c2c605103100082d000c2c0000030070711101d85504485603803002c14008095207012540758504001c100031850a4155203050054a118030b8107211008811102555924000c148070816440b0040b8a004007181c409a00300580d8440715040c50b401005007449a140044100740b031040e11140706174103000a94040001c5641141e9050f203900e046000d010074490041c1250080000940000d9405981512400d071a25000001441303464121407183e880d92496000420341c5500d0440d643e5070381d50092040008004140c1c0c0a401014410b0319004014010320b10f04a40340c80e103a030482100302c48038a070035100c0c82100030301c0054520b41500a4030a00d41d1942c80320100307039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 688169496 1250 688168246 688168249
    0x204020304020117040501060603060602161e052d01020d050d090311010504031106060a05030717160906090606080411010e06090d0302010b040b0d26040b0409020c010605011d 77
    0x35000034104a06104011803820844400302e12464400c5000300c0021441074585000617040310056005181190844030700c00d0001c60820507000c0c11641302c1403000c2c402030350000d080c0c0604401500501da0012300c02c241581403109080c06401e40084032000c11401c0c0c050310b4010780e510101e0000c85070225405200c81c21100c0b80a6100664250080c2000146554083c100e2400c481c0112000c80124008820228107201c080151710790050003920380c0da0407a4240800a0b90b140700904c207030b4440c600d1503030a0402d103050501031103000c803014068072950540c5030440300014107070070b020301402640350032000030312188940c0841c0c1c01650008101c401c20402d040c01100c02c03582d490013180e0000000c010207030307294a0306003007541858000d0b0700004800455274200025181024009071145450481c00301c0801c03c0310480242c1c004400325001c6032032006900d1240719000d2580b1844c80d52800bc2400580510740b81c0042000c00a0740f8003c0000b9900e81005564500801420820f14180724101d0000b5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 688170746 1250 688169496 688169501
    0x20c10111e071404090c060206070906030e0c0f0d0606030b010819172d0901120b01050a08090c04051e0a060f181103180d0212090f1c06051602010203090a0204 70
    0x20f48080c001041e508456203881c88400c1850780500c1c0141c0c0709004104005a2002180740a8001441c0501c80c5120503a00c05d641c519032603415510130080301680302c07050b81d143d000c0200200d5100c00300340300e00f0384e807030034000340a0a091107008080d0054851030f482c45030250b94080c03500366101580c1103103a1020001101280c001c89007105006118107100b030030440c9400d440001004070320610540e070348401000100280c0500b2070300ba00980c1001440b07449681c215003965860b81d402c1c940108540c2da041407244ca890091544180c00524203418850317440040007020944400d00ca01441450310380403284422100d19204400c00c02109a100344210400140c0580124044901c0841ca0000000000640c0c2d40240d49071213100e030044503500c42d80803050003141e004042d540040c1c960b02d000c40d64884000c0c800d8407102840b806041500b84030650710200c040c1d0807108141d0707040c021402140380c60340c0100f10689862001c00000180f0000040c07050007103e110301ea80700060044a80c440d03090202 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 688171996 1250 688170746 688170779
    0x506010509130b0103060501020304030f12050d05040609110d02010212032d010501030b0315010621020d0905060121140c0316090c0f0c0b0601020c10111e07 69
    0x40200030080030300166102d5040d405118501280094203502031800034040317407096485581990420b0008001003140d9000c00b100700368002802c01040c054907903017150144030340e10b52024200c3c60305003804240801a4060700c4660f1003a004001d00203800000c2105140c401c80c80280140d00854030b807066050b441c0080c58100c15000c885105000c0b003140f140c050900c01c0960b200180da104001000107680c540104003010070142c1c090400410100100180b0000500603e030510183c19800034119030a04007030a1220b0381c02100315140c543c588040f201501d600e81c41070303419109400002c14805030481540344091905128081141d40d40c1d42d5210081c00700d406814928021548041107a45061048260002c42d9820f44c2002508200c1e075201181d42c0700480808100da1852844429604030951002042d001807240762541d0741c00c00101d190443c1d00012541060b0001040304065410000c08954000e02c1c41c140c5150b40d002d007020341300e48003411080749640da01181003000400f021961003070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 688173246 1250 688171996 688171999
    0x3020d030605060324030114041205030c0d0e030708030a020a08090d1205040503040e0106090810020307050403060902040905070f0e0c0f070f0611030103080307080f0115050a0201020715020c06090a030c060506 92
    0x2441c84000780001b90031100c00b00e2044042c1d1140360100020004d2201281001484a0911a00390300701094561900c0c010343c0f0094003019a28002d081d40c5000406c141c43c0a1035104001c01d43e2464145030b040013035042005100c1c085807485020890006011903449401800c95581000100d42400080003030031019105032001d0100300000b00c1c0c000c1d4070400b46800303030400e5144c00144601d0310340561300c3d010004003c1880b40c1e105000f40840160320200f12001c498100718013207905005070001500500040c50028194030075248006007066441c402d0004886030f40e041141190b841001044640c0b2851350300b444118810481c060010310001c000115003402101c001078428480203e0311120761083e00107485a10010bc1082403d23a400100c0c1580590089030002da954984203410004540b150001d04c01e001000c00d00c0800703d4800d505580c43c1c0e41e08010691150500e0350440d400942c0514003803d0140280400550300c0000003842c584003c1d07051340c588403e40d509444010003000d02a0803203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 688174496 1250 688173246 688173301
    0xf2703190c150206061e150c0f0d0315050109121707060509032701020606281706010e0c180f060c01050709080d080a020d0902130903020d0306050603 66
    0x10031888500400705101c0c02e01c0e80c00410103800e01d43c041200104050090120480030340358119010b46400c2d9001a490032001c0b10b07662501c0000d210682010140c1104140e00d22607409285007155258000345e07007007007031a240071070084d40301e42c011180200c40d80102789513005283c81c5540048d155000c0c00240c40e184d400100d00300001596942c040c0c50054402031a19440898814552181d00d250400041d8400084200008280300040d48505000786180c1c0b05140449119a10080c046540801c000e4407001d600c0c0102d0700c400080304d43c3c10042c2c0d46113501e840345000200f038090756a84264042c0ea0342152460030420001103108400c1140c01c1c1c81600f00c41c090981c032484c0d8403143c0161002e9070240340007203100d190458004146044581c0140420b0380217003034030340754990071026141d007050416101687d10321100106c41b002d032104040c001d402c096076501c00c142da51500e600c0444190b10960a8400791200b20300c040381904c4040c00f52940c0200d081001c100c25440c002c1c80b602d20520143d545 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 688175746 1250 688174496 688174499
    0x1209120308010e1b0a090e0f010315050702011b110105090f0303041106130605070611040b0901050706061203050301030303291002070b0d02090117040b0402011b0501020f2703190c 79
    0xc120f1302c3c0c100072400c00c0422180c0c0e0040c440020403010302580b10400c840c090106600d50b49941030707480501c072180f1465079961004910203a200b9045000c0c502e210709642c04e91030464003801054134412031705103000b651078107010480c5908080303810710081540100950943e22141c442c6110304134100b08040c2c0c0b1520810858181714100b602d03080040c0056154140c840001c0e04148094407905480e12001c280104000d0000c00003000a54074104028606592514481d1400c01d00421382500005500c201005c0c02508042d4004011416030b440307940c003440050f6035072400300c1042d04641c1040c48501e0300001400d0007400c06040090980080348111004182c0c1e8180d01c0900380d00c03505039240b40c242c0020b00c05c8844e503004015440c0302ca17269a5100c005244c917444003048103001502c028100a5085c0e24021050790303980d001030010741c111000315aa541104980446a480070740781c048002203000154607585a1031000d903111082c0580a040500e0703428211041003009a60b08a0750824103080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 688176996 1250 688175746 688175791
    0x1206100b0a211a0f031902060904020c010e0d0206013204050702160b04050a03141f051b070b01060503060301060305070b07020406120f060f020904091209120308010e 73
    0x4244000845a141c00210f010101100001d40d89540c1503040c0a42c2c80d909034044140c400244864a21410760300c084010b000c5840000e02030300c85d00e00982e030711900102e05803906c0300c0190f01007124498000e0441700364860f103540590312400c007407081450a900018580b81d0001456584d00f04003141c0c50028028280e1040004080395810768503840145d018000800c0c0d1814003081000150000c540f0581c2060b00c0c010006114200c0e0b400000c250b20200080f69402060420161070003000c681207000300c8076280b0186000030b10044420b4440c0022070030018001c411404200c0b0314064200b50100160382c00c022054403964030141c441901503680e4000000070400912424014010703081c1c0543c0d4800440c0100025519281c200d15400340c40394080320f00085182211010f00c60b8017080204482e070700c1c051610001d0040710281500035003001150741c20080760b010107041246050f1521100d41e0f445001e059400c0340e4441000b00441c1070740c030040c4903134030650072040d0380000000d0080c0f43d607c0300f154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 688178246 1250 688176996 688177037
    0x30d1d07080a470c0408030d020f0f0301140a090203012312190b0601020d02070905041104090615081606080c040302040912140901080f0601110601141206100b0a 71
    0x42c20a502c198583d528031038200c01d00d52016000315032851514142814480a180c0728032591001d650203940c00200c4905110043e820b407985442c080d04a50340300d40c0d5403c0e10102e051801946a44101119a00403400190a01c2524180c8400c01002601003544a901c141c96110390024070381c1c8141450103803200242c00b0040884bc13207507001d0600292111500c0c007207441200c05403840e81990444c50801403042e90004407041158030b141d8011aa81d2128209031030300c070910240c0141c0050900f4001c00900c0941c0d0030010b8900942071100c40b90f10394a1003a261500d209444150017050015400c0055138847c04042c0d030840e000241d801e14155495002074101d4040340021549a2045d1600c0c40c140c3d60003003800c1070f10074040b2590611f06031038440001d080903c01412005a400010301240c81e030303480ba0a0300306810b4103060440f591035171242c03402d5610220b1003283c14443c02910005a8010f01d0119540e8081c04031250b1459060b4204402003c980c0c024200b44410040824005d405084000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 688179496 1250 688178246 688178333
    0x51804020d110a0f030e07080d0f030e070306020714070b160507091a01141323030f030301090c03090206030c070f1209051005120a150305030d1d07080a 67
    0xb900c139400155100f440c041d00361849242085040c0d008250708104400c0041405021000d29141038003556800141c1a4020040c0030100c0396540b05110000c0100016540104107081c0142030000d01c4100f01070815a6828440c011706049502c00d20480480110001c01c82050900c21000d072060785e6141c61681c412107030302c3c244151400300c50503100122960421380700d41102c1c0c59a403001d46020102c03a0410851240b41c03090b402100340502c4c40c0d804514043c08001d020100040c2036410b000c0e034004095640e60420b001e100c200300d160500c4111514043d2107603510040e0f001d40424103544c0c030001070012030f41002d80141d4488800000c107100141070b040c00903050a40680b200403c03d820003003031004001a113a01501440002c0241c0321104645016059000b4007600001ca40d4070f1441c4000301800d01541e01c020014400410107500c070340c060380c0010445020008400c20960b00c28010940d403500c0c51721a905a6070881c991810100d03040c0640341e00c2030041c4030040103525090001743d0355a001b54 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 688180746 1250 688179496 688179517
    0x702030a20011e0e0d0203100906060819060e010209130504060507080f060405100b13050301050604110304062703030c020606041b050c10050f011401051804020d11 72
    0xe8901015a50802981c8000c101001e1900c02102d0050301071442d40320515010030424402503100007000d40d03880d68903030140035501406a444445100360a04050810301c1000c4456074180000800c16000003e04008003240404da40c0b1600c05032500d551004044504005602e9502000010f003151210b03408641105640c60001616180c5410903d0440d00090214000c10800b4000d122030300020081c1c158003e4030442d00040e0a80324400c011038154102c0d4880812001d01080241000c5522030109080710000c0c1d0007400b05035510301c1080b088680700c40d45031420f030400b403011030045241c56000900b40c2b082d81c01480c43e0f070740300d85050152800320613408500194807030341c1c0740361192f07418000e02ea0000429541440044103101030740f6400d4408298440c100800441d000003c3c9000b0049401000007803481044a03091180d49013840300000d0141c1030a41c82c800b4500281c1394401c0d400c5034001c580300404556418528000c2001952110a0840d04c0d503803a040f4841d80c81d0700d42002030074203496 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 688181996 1250 688180746 688180763
    0x151a13150908070b0702040c0215181e0a0b07110109060203092103010b0d090b04064701030b28050a050901060807050c0d08010501080f1302150702030a 67
    0x25000060140c41150007403100d07a00000000c100368511344003070340c10040c5d0403071703012809101c0498128070389070740d80d107901181038000814000003807580c0d01071035415020071094400322103000180c20340302c8008107024100c40e40422245d5011070600340031150000f480e46440440e48a1158219080d901611020b60b012035001091108040d81086051510340102c0d2000c0d5416a00b0741540019010502c02d2515800000500628660403039010307107009540002039507807a09082c100300300201207030a030880844506060044070740c3c10111f0650701c142e00c142d4034855507121040100c03240c8071000340e15905042c0c0300e10900f00142d0f16241110708201d00401c0d10078020010081a09a2094550006014042030300050040e0f490301c4480382c0c10b4031030900b010725094a503070388100e83c0c80c495400b00040718015410013041e4141e20004684c100c42007640d5500c0e0b1500d0b4a440c036041001d0036210072114a00c00d641020060502903001c5200021400e9500d003011656000b29013040071070007084880c40e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 688183246 1250 688181996 688182029
    0x302030f090c01020c060a170a0219050c07061d04020c060a11070f0228080d0f0801080a0b04050715050309240408090a0f03030302130603151a13 64
    0x18208a000d55006401030020b0030030058940002c0d49507410490f950380507000000c0c1070403815010710448a110300c0070100701d8009240c0003900b0030003034000d9103031080c403200c4c40a00d01511502c26015101203102d200701810406142480540e80b260901c070080400d00781e00041c4191980d1180302034100e100c0e400c006000186049000d000071181c0ca21425040d0b100184594404900c4c2c144225100c20340c113480288507030441c051404501d4111400802e410a10740c43c002c1161900419808580011038540c0089200c080c0d509488030700003402040b078542e0158142c400030501056005030028068400d5814071902c49551800d51100c840001300403403c0001400080b4504222a40000034022064141c0070310000c0c207594858405803003d0210b0f940803c0e03640e001d41d10032907584020144076500400341541da140c054007035042581a00c000701d01c80103000945034081e00030381c1c0b02d0010080484c42000e041c81c0c2400c81000c034624032000c1c030f20000d007c0c240400c1101070412003c3e10146182e0752510303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 688184496 1250 688183246 688183261
    0xf021c05060108190f02131d01060302071e11040203010801060e101d0903090607150f060807050d050f060103050312011707061b02090106120e06040f03030207021c03030203 76
    0x15034014000c0c6040240500401045504804098180440c0613401040c1601100e055002a02038003079901c00c041100c940000d0450440c1d074818400703a1030311018413120781c2da5407800e0b000c0740a14100070b480001c902c200003900d01002c40803418030a00c2107031180303d4203540001207130480c2c00c243c010030481e0b035460809216800d04004c030582d0200842a5203040207041420041c071140010a14500c2500b0080102e40c1c680d030f0034000e80c0c1c511100034100c903889807640d04101108a07083c0b001505054a0508201e1400c135a6000e00c9042d40c1a5000a1145519080c1030200d40030521500340d510f03006801c5070441c140400d1062034000e60007180150340341d007045803a900f5090b1060b8030206810a0840300848041d00125401c4216999802d05640418018200030ba81908400000f54044802c00002c1016030300b2489264000426090070801c80445c003c140380d9524041d5006040380c118003a81c040028420303001081164405031428080003d161003408030310f00002c45c110082030b004810070840 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 688185746 1250 688184496 688184501
    0x200309070503013b0604050c0913050a11010c050102040b18010512010e0c0706050a0f060617061e060304140d0c3f0c0606060309030813060f021c 64
    0x5070004500802003d100068025101da0b601c0f6140b00242e411140341115010b030f1000103460800600050702d0541c609480c2c00d0751105550810706100318200000f140c01d004840160b404141d5100000703002c0448251105441084500d40c0c5904000c04455040001502800a84010070f40031001e9911451003c0120408401d040081c0e8104001403009800c00ca000d05051170446098411494050302c418003e80d44511440340c02501c030030700708414442d51001c00c0d48100049030344101c007086045c2e104d06040781c0c10580c0b028884111f0104101084041c6008990008905500754000c2001c011b049d0126100d40c1040b2800d0320100c40d403508240360141c00380003000e09400c0c280f03003442c0500a1565504904940c0356003003144684000369129a01013812020030220801100001c01c26914103c0108100c800714000c4808504010300010300070300038052020065410b4031b400c1880d039100d014180c607010401500355203103620350100100758500c5100078189040514403624a40c05c034124910207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 688186996 1250 688185746 688185749
    0xb0f011d0c0912060a0c17070e1804031805010503011401030e03130b040303110a0b04080a03090c082406010c1e060c0c05062511070305060a140a0203010303020307110420030907 78
    0x2408003500d10803c0e407e5071040d90b20303401421400c04400c004599800318406102080b004a03402d56074000348024140c2115445508130340c0d015a03405426100e500440341d500003032050000c022144420314505601a42105488440b540216070030721340c20190000a1502591001c1240c40f40060280107141c0c0c089244248540000020101c283e51075a80f034245240090001e007098802042510205109411200342c1a41006070646055226402c254807601d070480c00080c000302010445480900100d240351246030140c4400000450351307226506004400442c42010300e07007146104001468920415001c03d241d5031702d2a01c004440d2500e90b1a0850141000700c400c4400d050025640c8000350411a1518051400d80c0900300c00c041c02e9880c2000e5030f08001d2480c0244403c000013030034154095050980b01c50481e007a0703500d07500d03842d000720f01c000e020140050f0005c02c150004640b00d100a6103942d00701400000d2180306040d10140e003448a50a9502c04242c00001d0040c0058200083e00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 688188246 1250 688186996 688187021
    0x403080a0207140a090203040f0b15030d091d04080f0d0b212e050a2f0a030507050408030a0e090a060b040e0402010507050303130b0f011d0c0912060a 66
    0x842c3c80403000002000759001c0d00c200720f40290000001070410120441e41300e03015512062401d06428041c00d204054002a4520b40c001c0c071400d008401c1c2680700b0680303801214142c0ca1030a5071681203440d0f910400344010b01c00d41c1c43e54001c01250241c013625000410b20440c004c6000540c4490341002c004090701c0b509e0548a498628940761008100c011440b444102c0400c02c3c0c0702c0030407081802404a90b000c52400d4102e003454101000104844d07600020b0510440c03052142c1c0c4810304038010303032101d500095003005c000c07410300c40318580358042e074000c98000351107051035403c25540d950311380c2c40c0d0b40c0218820400140812141d401601309403441e1900305074843d030140082810945034585600a074420741c1084030201010500356405801102c501c25041001c0d44e0343da107400e4a80341071150289038201c40c1040104000303003030889216880c90607510404124a11140c8404200300101c0000d4003c05100070b04000600035691a518201000c11852000d0007103407403c40381c58002c450785444441d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 688189496 1250 688188246 688188269
    0x209010305010e062805100f0b030609100305100b01020a170a1d1e04060506210a0c0f050309120c0f150405151504050a1b030b0303032205030403080a0207 68
    0x20900304000c1c030418500800d000008047d43d44900807c0700c4d0915a00994070605821070108442c40c0f2100110311603001500ca051180d100c100c040b0511a01703038403002c2e040790001c0d81401034198954100d00c0d12000c051044500c0f0354850b44aa8440d288001017102e944072002900240c02504a0b804500994010076201d60f02c04021780402c40034040302c003c000d118140100924499910b560040c00179000c040c1c1200d481c0c2062030300011a00340c01245107076181d004600058102d00d000c0c000c0000050351aa40c0c0341c0911129002922580c001410000c01801141c0703032281d82c8945000901880c00f5031100802207101c0c0000c0700341c20301c0d10814007460805107031020003021070750008561001e07282804442c10580e9a0400345a0074046104c00c141d400382c201820b11a0072586508040468000280b1044502440020039011101e40100c0907406810038400548240c010a0741203035842d1030004a04042c0c6055078230242142d00a40088580b0346011848c54400c0d035041081102500f1400c201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 688190746 1250 688189496 688189531
    0x80105011416081201030c1202010914030c0d080918040f080705070e0c0d050112020a2c04061a1c1506090c1d041401050d020105070209010305010e06 66
    0x200072219111100c101e0304000642d003100c00001d840310030342e0142c02181298032080d0b4540800460042031000760f50203500010f0100340c1c9186036541200309035058484c03090841c60f204041c11040c045107040c660501400c440a6041d840f444a0640c2e40791092101c03554a5105c1410003828140b4441215603040a0400308030016004148400500390050304c8680ca07143d481c40c2c010f2801446801c007440d6600c54000f4444064150001390030f05105241050010348e07224008002803c0400300040d5211503034580030818206000200c01444240c0c5248065440119501000c641c900303680444146035503510b100c2d81d100210400c034440c42d10071616903410404a032107841c8844031803a0090401441c0c070000444450080d0302440080070b81100c00c0c0b0000600d004042e00080300c43c031030102d80d585241200a441c1c5841c0c840c0201e050800380700c815250b4248002e210400408030310407414040f04014041c050fa0310540440d00a43c401c1002144500e0070400e01400c00307102900c00301c0915940201d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 688191996 1250 688190746 688190749
    0x321031a03120d150f050a0e07051605010b031902150928050d0501091b060c112103030405070b21040c0504020c0f0c030f0601030b0406061a040312080105 68
    0x2403a80d18000300b0704203180c48a10503071810001342462100200700710101c1c4000500d499100041c601141d070111a20300c02680d49440d98111104100c5140700050420005030044109800c900c41040d07000e0340000a07802c490101182c9040349c0310882c0444408800090f03000c500c4c0c4091411510382090002c60f0402544d0001300e4200d200c2c05007003c00b12004090200d000b6041000101d0013008024101080320307105080c040e00801d0000c80a403548825107a00c1d400345010912000c4c21100940d41e050b0300c40d625500d6450b141c2d0150b44800750300c4152407070625140c65800c0c104001f07240c050405199a410309240c642d281c020b848e40001407044050142c4010b100c0040560f03585040a031542031b0745541c0f18500030840c60820740040350300c05d202143c109845000011154540584001200c0c2107005a0040690b104500d0103001d03150f0340040010300c002480c07100901d40041c41002d02150442d210001c50241e81d003001034941010b03001150403c07e122505420345518061810204400c1d4141380 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 688193246 1250 688191996 688192003
    0x20606010c050307021003020a030e0d0504051201020d021b0f12091318030306050a080c1003110d090308041e021305071407050d0216080601120204060321031a03 71
    0x105110305101580492805000051045480c050b90050481041032041d42000e802500294030a01c00646040e444d0054801c000412101500c1c464466030b0a10b45000308003d900340ba807510240c140d54080c01400ca252480d80041c2c040060540704818210382c41d1207000b485c00f40300e056412048d50104804a00f03e422402c05c803940e105050f1900d01e120240c0e020380c6009094225103c600025072061100d0038543d040d48480292481114124081036481c0022580d40c01300c1694241c3c080180341c41c0300d000a0003075000030b1011041e025100d060142c1a2031040442d80c2d8008141c000ca92014100810460100c03070248018a4001d041a10f4454a801044840c1414040d070001c06603100013146c4c026004801c42c3d4120180c0f007003090707903410140c5001919048690340c0d00005d4443e01005054004240401800342c6601d00020704040c0c1c60181d8a0545000360002030f6000756503110044046040d00c407036040e031142d031a11010b4070074410040081c00c03140340c060644d4a490400c20842038554012 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 688194496 1250 688193246 688193251
    0x301092d0b0a0510030b03010f270c0302030303010e0f07080c0d091104020706020c1009150c140c010203090d020c030703020d1a0709081612320124060206 68
    0x3010000e081c814100102c1c0d160300c02904056845a0702865811419030316403c034442100c000d80080c4192005540000c1c103440074082103c99068540818040d02d40f10b0000150f10300d40101e40340004c46581c0d802081c119030083e00246e4402c04000104104040340280d441e401c01c80c20310b0110140d24222a400340180600b2038540e00f0755444d01080c03c248100c45d2504010841c004104650391102c61034000025403100001d00c04500503e0030210b844041807180c1d556458224801c1c0c0440140841204c0041c500c4850800c20b014040708110140240c80001d030590b2440c03c800141d4901b44260301c80c0c9001c0011020034110741c40031013126850784011076080100e83e4113464002c0c103140241741c0b46806c0c000326540d1460340076000313040200381e5900c100c20000700c419450030b8468603850070000307170307103615903800b45003640012000250000f5030600d0008041c0844c040300050084040342e6003180c40d000039100110b99070b465100560092504030513441c40d583c100c1c0b40042c1c10701d10707080020b920f44900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 688195746 1250 688194496 688194581
    0x3210c040501080709050a120605090a0c18060e10080c0a0b0d020f0403080c03190905060f0f0706050a1a0402250201090e0c030f06060c2e090503030109 67
    0x4035008911104d00400e4445d02400c1e0041a00b25884c0c0c40b030120a00e2407003001c4054880e10706001c04642d440b500400c084003020707000032a003030219050620704c007070f007074005a21040781e940c1e40c00001030001e0b240c40c0054040c4580c404254041860701c0061403a03c1c070903400043c494480030f4010850031202c2e2046812040d003032500544c640b00e007041e82c103000b400f03aa4070180903444005050348101c0400f0000740428168035080c0d043e480700800003101e00000ca4050b1a03080f4004100400390003c450000d080c2d0398211101070f84ca4038040d9650b42040e00c00030780d5414001034441c4040c20200644480a401003103050344c04500b482c1e0860094100074110103511011500811400002e5901c1040d803440500304800740045e00f0f08150045107010b9004450014520303410f10046030051038480112001d604150004048000161044c034501c2c80584518518201c0038100c180c0220709a4051a00341d5401000a19260b6250400340342c02e4486c0242e500c15a80300c91881e283c3c80180010000486580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 688196996 1250 688195746 688195757
    0x50604060302180f070c1a060a03150605010e0f09010515130816060c030c0b0a0608070806041a040506040b070311030a0b030d030c0e060d0603021203210c040501 71
    0x4404010400a1100e41c1010b03400c000654203e030304600d2012103c5006600e000740011143d5548030702219071226000000b88440c1d050300341040000396500c0500e8003c90002c01e100a0b0640d43e90310403600a101900f402e18203a140c200400c100d680110402800f010269060700340743c0301800001c1d5400c85c05001d66031242c495610001561142c0e40c040ea211156243c03a540341d0aa283c40d201c40d66065a124aa03661801951000c1400b6104440181c121030740b6855140b071007040390350703000d000000c000c2691208581e240703070001c1c1c01d50f010041c1d070300100f003c8005800581080d0400b00325041540300e4403a4403e14900910001540014540703034416081a00d640da10340715800304401804c1c80700c0c01046201c50120501032484007541c00200d05142c01ca046851540000f43c080c0d0a48a034403401e80b02184510209044500b0072800811600d50038070b0000400540700d07800540c01484201c0d801c0041d61020a6204110141c612691030707016035031121441034941010480d82074820760107814108074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 688198246 1250 688196996 688197001
    0x5062d1309090807080f0c07050612040308070c050106060302120c0309031903110a1106070201110306010f03060503010c09050a081c0e060d14060415080d0e0102030d0606030f050606180405 83
    0x5510031342d100c055210440e03c0d580d448510015049800800701e400c03042c000d50000281520b0040300302d035042c40d5284001c0300c5960720754038166030880000346075406210401c0900b10002e00207100f0840a030080341c03401616400b06400440b09100000c0030004440f004200f8401032610020a580d1801d0102049044070084480124054000c041e260010010b0104040b80340b9900544017050b800840021107a031940d84110803400e88a021840e50680d00c010000f0a42c1d80d4450301d06950300c42c1060801040141c2d9a0b0042400c560f8001862000108402c44c00e2001c0c0c42d1644500c4020590b07003000740890120400d08802e6109030a501e0414010035030201c107510f80f2000d040da8000040041c040060102d00c00302c1040307000c4112080d9100d80e10340354814011000b0308002c01c0649242c04010805040704000030303175582d00181b50007410340c881840080c1c0c1c907101c50700440001c0c2c076050b1b402007030070640000403100343c0d9000340004c0c0c4034010a1044a002400e242c6050181400458000c600c68 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 688199496 1250 688198246 688198253
    0x6080118060531090605060112151419030b18070f0504020702041d0a02101106060603040501111603030c050a0503070c0618050a0b011403060103080a0905062d130909 73
    0x10008044042c3c803803d0040e40c20601c07003194000381c400c4200fa2035500010b19001b001000b140c450703000c403003941e0360100700c00e0040702120007090200c00c8000d0201d160742d100a4071000f85160481d0b20483d44807085e103080000c0380c9001d60003140003400c0d40700107280d0b03a403c0459554035503110780071362030041d5404504170301035548a800441c100da00d4401c0c030f00c6182503002202c0ea1140d9040700282e000b095000070020b20340b8464051101d481c41d410004d001039031604170403c003031940f001e801580c1540d02c8204580030000303803000802a446000c802001e50107401e00d070103400c0c0c07841c4892204c01e100382405030a5404d074020049035803003405458261502d4246203000070081100000050f9445031440c1d01314200500010202e010300d000c0c4402a1582c1e0780d035602c0d01001c0f10f4404030950035401150041000400308809028854a2801d1054038161540b021a056801240d08603070301c074547c00d840301c0314821403a006403200c08400d4001890a0f01303032120401001103c3c0b10340348a5580d5800b0503000d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 688200746 1250 688199496 688199569
    0x81605120d02090a0b0c0709110f0f0c01060b03060d06051510020a0c05010201330e0a0603150603020315040507090513060f0b030303160c06050109020309151b0c0a0b01060801180605 80
    0x3400c808074072070b848210b414bd00c1003040d0051002c0c070042c0c0d1729115000c80d01035040000c2da031058400030215550301300660368900c0a07002c05050828a10226090340000e65580c0b0b8880c2c40b00d000780e80c001c001c1900c480c2271108004060b540300c1070559140021142c0e01c00c2c54041459404500304158212050b04d030001a0b0114002e58007620342c144180f400c1c0b00740d0040707581045085a00540c2c1c0c0103040d05c0804510b4045646c40d1100a41c1980b00301c08003d40d201890303500d107074001d000f50140c0d014965500e03503000c00d45804441141a07413015404000410103207100f140c000c0076586608102c000e0004020036034a20002c0c2c8981401280d400017040c84502c118024564240c1c06071007406103587d21000440030750001d07201071265020f241b43c0030000040302c1c00312511a20101e82402900740081c200f4001c941c0c0401c095040038083e141403540859a02c0c0c001c54003c3c0540d59640e6940d40c9031849808023528504030300c4c8900e908100e020442907903030807485c1c001516422031140402d401582280ca0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 688201996 1250 688200746 688200757
    0x60c050705010e0d0306080318270403081905040521071b08010608030c0a08030414060f04020a080d020c13060e0114010e01030603081605120d02090a0b0c070911 71
    0x465820f1a54019140c00003050010300e00c007642e1002d0003440d8a90350303655200e01840e5000d4002ca0340303001c1c180c4454a40b4107002101c0c40500810048076403182609419110b03000ca8055020070303001d000f806411140352944e400f20303010640003001136041030b556a82d02d810107540040360300045e1150b001001d101d80d01c1100e213995800f41298400c0400401400c5c04549540300c0c2010300d520b4001c0c00105e504012084a0380c580c13011307016184000e41592000103a0300042d200b910304d03040074030011401c0c0404105143c01003030203960304035041c581f51040112051903608141f50b6504804240c02005400048880b8110ba0807910081104200030b641c10003002203030f03c103040100d441c4000140003c0c40030241c050f424802c0e40c8203108001020015401c0d0f9950740b0004064947c10030401440e0f174884489401054070500950301c4040320604201419004900d521081590006501d00c039443c283c41084001d003007079240c85052501c04030b801074803002148109000152550390900300c000500080b01c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 688203246 1250 688201996 688202003
    0x4050601110304030c150507051002130315150b04060f0c020418080a18050d0816060203070e0f0a0b120702010902180a0e0106050f0f0102011119120209010903060c0507 74
    0xf07860765500c2c201503c03030003150700c200d2175a450b5003180400c49131301c01c1d41100c40c500e811000404040404001c003230029070021031650054140380c480440050203210503010501004a0f0200d054600c001621240700840c2d0f000e0b040c0124100400c02855030400303900180380011781004c0520b6003490012030040e0a001c415021030081c1e820100342003080c1c80002c0c06030981d003a0740c0c001a04800070b00c01c0754000d000e0301607580d1100b80b0782c0b804000103214a000b02046605500b0300d1340c03c075443d9070700c07201a45c005440200104030781e0020700640e81018105840c10020403213203040341e980b0b4010044091301ca01c5a565440c0d0403900000382410f4001d4120600459010705403585005d01d80d10a00b811200aa41c0c1c8a0719a0a03d20000c2c42501d05010352401c0e03d10042001e080c1c040304400300303c080d107086581681503540f1048043d4804526001400002140c08010040340400342001460303120394040440a403031051260302e4950360f101c0c0840b01641d6120400007250001e030902666140201e20004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 688204496 1250 688203246 688203253
    0xf010e030f0a031d010c0b0c1308030c15060d0314250b1e0a0c090f090b030d2c041d01090c060e010c06020906160b0121050307020405060111 62
    0x206a44a000258500041c3c002da50b010106072102c2281804890050207040c00105403224000104061824450304a1000c070745e181d10780b451098001c2c1031000c480c0d01001c465000411b0800090a0521021900e09159000d10225203081c0d40091a030514070304014041209001d042401c203045041201c030444140e00c4928120340e60740c200d026110031403100c11121070040e840420501d0240e8010364090209401002c0120340e922041003000b44803d0768082d00300a04c08500050380302e4060191000303000c1d000d00200b10f03580001c0a142c584056100182c0800806c42030fa054564005d49160300100c1c107808000807a100b49100080281040140112050040d80c1c0701c14407d01055002003100c510441c00341d6151540c40f0000e03a00b001c80001c2d86404200072001c80800035000e540106000407006140d181055012000e44940007460101242c078188030030010f00c01c00140300d6126480710a55408481c0707001003030351030507140d02551800a003d030340c40d080404c08a07806010003c00d41803030b034000c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 688205746 1250 688204496 688204513
    0x60503030c0c01031407020307021e120f060f060924090a0b09240904020418030c0611092209080d06030b010b0307020307020d0c0e2809020f0f010e03 66
    0x12035118480c2d01c0082d40481e107040b44102400512594461003440c0e541c0203035080030703190340900130b1008200c1d410f01d8000d000d088000c80d8a82c0c5c0c0b10800f8903c91803000c0148208601c013a4814a844006028401c903101414100035440d900d00250541c44200c070703030b003991032001208081d44088000c188a0390348070041504100f824080c9511801c010681154035507071b143c85103155a240c0380010903151200842d41412001c4504280a00b40e801c40d00c0500005480c1c1030024807210b8030000e0381c0003200003610b40c2c0c0b1010140b28160061a00e841d8007140d00c245040c030b07007000207000080d0b00901e01400103283c44504a996005512090280c0d411280340e80d9036005c030b0760403c030092046003c101e4070812558000305084641e84240c80c070034485500110301d0b10740b49130200000d01c0740c6031408a80c0c2c2c04a044011600100108215000744445101c0d90b800c40c80d102240251043c214601110040c9054032420240e60b40811020f40004140d4852018043c000012605007284000032501481135244 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 688206996 1250 688205746 688205767
    0x210050f120a020705210301050409150f0b10080105030d0305190603050d09061403150a080d0f030c230f0d11032d01210b0906060f060a050316020106050303 69
    0x40c040e00744583c06446d9078070600096021000400d00f05036024800a0005105c0d0341000da009040c1079001c4c401618940305040810000e44441100808019480c1c010994031810191844012181c503410b010354150b042c0400309a907100f040d110502015208d001081c0344c0383c14111060030030703841c605090016a4803818081d90b540c90140d00e880001c0c103451800100944501c0240c065102d0400e0058519100e42e20100080c0880204041d400500c0c00c00024070044108004100c601c441e844660b0504042c40e4060101e40c0c00e2000b039404d100c0d15506041811226108074042c40400c0032a542d02d0b990713031001c440828003540b61048030710b034034012034468041019805140b182c01e40c0c0c254140c107807400102c040408013180881103480404d000041c448a049c007990700d068041700d1300404e14602d1150300d503100e602038117940e0a0025000076040c0069400c10050782071581d0002c0e60300034600307443c2c0d0000524900c00107090204c8103100120084410b4401c0d00007138010a001011203403210032510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 688208246 1250 688206996 688207001
    0x10f03060b03030c03030a0504112e0504050604050409020103060e0a091b080a0f03030b060a0305040c0b0f040e0c0d0603110301060b0a05071b03050a050d031a0a0b071106031e0907030210050f120a 86
    0x100e188020042f242d001c0b01f9140e10070b00885081e2b803009440300382498641400c2c0400f602c1c1d035460403414981c071520003143d03400b44920154031030b82c19214041007035125410005c0000805c02c90300f6890308401d074414007005400160b40b241c1194040801010320a050404500030f00c100d9030400e501c4000040c10341d0515605401c0240201e005070b0700c2950f0180d85003402c280343e01c15081b030112500d00501c41040040000e092460340489108d841602c2d0002d000191002ca542d2500100e5096045020b48181c60600340f1541e0302410071032200c03500e490603540e0003034100d0081e818002c02135130b2120305e1040303a1440c0300c0c803a100440c1d002e000c03640c4107101840d0003a1608440c030308940000b03280401030030040d901c89407616000078002d400000424100f181900c5180d02c0343d50184c580c01464006003010b500d410009500c5000b000901380c1d400c540c02c0d43d018168801c00303424082c0b0703a80b1401c024409665104044e081c0d03208030f41440b0b07031b4810346842001e03410f0060201350b900d95840401005140304c1d0a4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 688209496 1250 688208246 688208299
    0xe0913061d070e060904331b09030c05132a02060f07080708070c0218220c0e04020d080c01090b061f0e010c0b010f03060b03030c03030a050411 63
    0x7081034aa04a03141c121590071a01c0031030b5103da11248010104e00130514042ca000090302010f25120341180c404605147d5403da404808043c540e03440702c1c2846143d02500039500340040f14a05001c2d59460750315508090b00a501601e4800c1c1000488590141055440302c0c5014480501003490314a8021070740604041d80c07001d0350054028500080c00c1174151650360340c82044640c0701c01619403200d2070304980e5071030000d22040c2441205040000560f550303990040b4924000641c0c01ea9900c0c0c0040c291300c07035660740c03542c1c0c0101c6600312501c000040c6032000700c10301b0703100700e070b00b14428950b11b900020b000e00c25448405804500001141b500112064002400030740c0200041c00864540c10f05010020f000304020350446003051880c40245440360084014a07001454042400c00003a00c0e0744d005036100381c2c0125a481c0c0b020800b00304106a038024004a094201d000e0340c100b040d042c203903d442c0d1100038240400c0c282c2e150f000030100034440c503040819803c042d106030f99100321a1810490719000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 688210746 1250 688209496 688209551
    0x1401030203060c120a05180a050706090f080307060f020412050105010f050d2102161404050106030905030a0e01140408030307031116020f060d0203090304180207030e091306 76
    0x214030000f03402a080d0802c4032810750311241d401c0c00b2950303509042d100414000c0e00317018014085000c4c84030b1104040108410070b60240c0080c08150303140441c050000b0b03249030301040310000300502c1000485000700544480e00c0d00300c076012401114021185000740700d690007560b40301d100c040b000c4041c4a015031201e410703140130903640b2400b2074448080003030303013003801074014100e07840c04642040803015811400c0c10045580100d4609078101068460401003d4100500d070108100c0661141d1900b805900e005056906080180c0b42d074580311a0344921a55000d2020700c040a0100410360748103c2801a003005046a00c54480da1113511071502c80d07105aa9140c00242051401e104100300b6000711031126841c003118124000c0f5690a0000181040016a0744040700340b01c140392190a6000640c45110a031014555a50415033000c048407030b0602506e0311a881400440d0010303800c6100c49841800403168225259110070a0f1601001311510040646041101109a82c1d584186080c52140d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 688211996 1250 688210746 688210753
    0x70e0105010201140a0902030c090c120f04030c1b05031506031b1e060708041d0a060608010603022203080d0b09101505070b070c1208090606221401030203 68
    0x203031800124240ea2565012030702100030310002c036042c000e042d4003808242d403010b81501c1e070352a02c000c00950038a80848603007002c6480065040c03000c0d080260703010307030103001e42c01800d9040c141510000c0008668141c0104244000010415022826002d60700204001811900007050145004001c540d0541e007040c000c0c46035103103401a2502001c50b65034040c002610240b00381c02c185039800304140382c0200094100b44100846008680c0303100040019180d83c070515104162030346c8035044038200003050301400d02d161107428030010307500003c8541121207914000d6182c0758144030100d201041c0340c444103502d0040034400420032005a0290408880324041009007155000522601980840700c0759903171805004180450040c0c0e036a80880803805142040c10706400e42d81d4001c6440f01503c1c41c002044215020204100c003000c0c506000801c945404030b0342d400c280c61400e03551800641050300c50b01c5040344001c8007047c0c400095102c1d081c4c0040600401400403180e010580080c007060b8004d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 688213246 1250 688211996 688211999
    0x110a0c090e010b0f060f1b0a020307050102120307210218090c0408061f18090b0c04050d030804170a2118060905150106030c0207170a080c0f060702070e01 68
    0x62054458410028180f011000b104408202c000da200780d9908654200500c1400703044807d114030118108800401025044c00314010149844100d0340401d045501500428843c540101d060301e8101007103003414802c80d501000d0b6601404048100c80580a02c0815016150145540b20310704640050f07807407600940320b640c101d034001c1c801c80c0505407240d8003c5011415241c110692405042c0c2018401c1d00780300d842d1000e4920342c5144200c0780140320b440e260b00d01c080c031840c442078076001145c1c1142180b502e071504000c508030f0b0b2100e510207000e00400d100060180005090108001c6480065040e078842201902822107204140202e80c1c880320039119040144041c440e280080305100c0c400c1c01020306660300c0c82c0203449042c10482c2c190107485114002000e902e01480d000c0c100c10740b80469034502d09000289455016800070030741c1450300760030401030000402c46000b800c2e00150000c2d52502d04031074840c6005182148616944242001c101c6156070109104040e1010800555802e9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 688214496 1250 688213246 688213271
    0x604060b060301080717010213030305041401230306042a020c030d05032215020304020906090408040603020f091806120f03040b0d09150510080724110a0c09 69
    0x9002c01d000d0340126500c0841c0038448034508440070301070006800c00140c81d1114030b0300401610655580101c000c2031003c0b9003402168164540b10074000000e1a014200c010220005860388031500f24000441200001103400f82d141e541003000f9521160903c40841e1100b070894249450600ca450710050180e03007554002031402191044000d80c585c1c0e540c1e41036490b561a0305000d420400c07c0e11314010348070024180050141402c0800e1014031510041e101d02d80b0340140a01008014181031040072423401300f00014240100707950644680d8070300140c98030554982c03000b40b880750b440600c0c0d0105022440c241ca08200320381d191712032030090b00d52100d2640b1000c00a591415002d00b188441d0300706110030f0208a103201e01a007403905032403c0101319100c03135441d12020542c0041c00728000548544c200320a000d040c5880c00010861003005200042ca00780030148400224902c001c6024242101480014070811030403060b84180e80030345d078400c680381c41c11542e094460f02c620341c0d0ba0341c1400c419220701c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 688215746 1250 688214496 688214509
    0x12406020c03150f180f07090e0a05120a0e090a05010302040b0109140d020a1701060f05100206150d240b1020070b0f070507320604090c020604060b 65
    0x100d03800c0c3c00c07151601e072101c0031565903c2070000d0200345041d040c10804100c0310010000b1104842841d0050503160341440c0c0400d0031b8591034058040c5941c0202c140d031300068000940c0b0011205011103540d20703004640b00445105032442c4203168811140c0f0140300566806a1282c1c0c100d82c421182000124040b40c015143d24800c1e208955a0107420284031083d03080400e682c0101905c0284020103280c0c465802400c80b003a110f0b11480e0680d0f40c0d01c1c1c1440b100c000401c000d00500021213505903501c0c036600009644d00303001016080c08502c9588810640c3d190740614031560b0384c2c007000065400e0326540101100028084c203c405035400c00d100310801782041069040c6404050f600d400503900c01c3c110b001d001c140400c203609103c2c0300b41c0c0320000f40a20010040d004108008007507540e1866103003403151a000360f0350002007141d031040100e841c05088156800c90106080d400303005402c10650009017a5001715444160030798200b01d201400b40c0d5010400328842e61142d1000c010449446051209 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 688216996 1250 688215746 688215763
    0x901050d0b0103060f0f090308070909200d0213180f020708090913140d0908030a0e1003150902361c051006060f1b03030b03012406020c03 61
    0x7600c0c03019401400860050b0704140c0b035081c0456004601556040741300d50071a00041410750002d0503c205021085074445030030002003101c00c009102c4001743c5403103417a00c1200500c59504100d4000f40801c6040c40c190141c034000e8204218450303c5680d200d540c04160b081c401c4d1a41c144510b40a03003003414192074420b540146400041d41801c08420703800f400741440000d8082c80e801140c09403801c0001d0422010000e01c0d4039804090300d030580714090080d202140c070350040c2041d90010f1041d9012140e0240700340c4014081100c0b2249e80030724514080e001001d4900c03144400c400002000308446441d500101026560710541a42184150750b1807689030320b9030341c482c1f0041810440d0042440c600001142e01008140004000101d076994800303186c0841d25901e8503610f0b440fa0400c00890f9000300f60004500e4983c1040300000c01004950841281900c50080c10301d42e035429228402c3d202581700e140440301c140c0280031080c06070050110b05201d14070031500144030f0702d108a09a801d000c1131000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 688218246 1250 688216996 688217003
    0x807030507030b0c0c01050109060503010b010e0d03260f01060e030109030f140d061d0105100504060503181603021e0a0b0d0e03120a05012c06011b030503060901050d 73
    0x301e0181036030f071010340b01d100c00381110041410500c0340c00e40d000344c02c3c40381e14000d0070440300c001030707084c03400d0207050a6454040724107040c001d909950b68010b03252845c2c19442d6942c186030000040e804482c0101500d0307944801c00b8000c1900348204100c803585401124180c40b2140c4824011407140c4042600344c80180300700500068080310810081e0f4044c0d9400a014074032200c22508011603902c4160072075216901040c620798003000b1110255880072442800340c10140c40d0421b000b404101e010b42144654850038040050000014148010848442d80525240025100214072030303000402d41e03140d540401da1050500d01c0b241d500400a0b0903c6812843c400b41801090520b850040c44468008a0700004025100c4c201c114280320140002c00c04103020f94412805410b103502c2c42821100c0503003011080710704241c921085514540c944103004401c0d400304c20144c1d564600100d03032940d5607588981d00b104051300540100340e00900510711840d020386242e07900382e90720703410400201c01006c8040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 688219496 1250 688218246 688218253
    0x30213051501080603030408030a0e0f04050606030c0f1b0d09080f0c041a1914010806010e04020c0f0607030e010b0d0201090b0c0a17090103050a09020105031315060303030b090108070305 82
    0x409550183d540c859000d11300909485c1002e58540c130150441d40003004560004681c1c031004109031070808040402520241c0301007086103041804640315100103050a2810400410046c52100c0742104079221515200e80c600c81e0f44203c0307001165180c030307844005008900340102c04100c0c4a07001034016000003595005145e1405801c0034000100301c2403044c482440822010407109444e9013205103120b80c1582d10b8082180d00d400c00280c802185110fa1b0740c10080c98070300303222040c0c1e404000e01c21880030495006030380d16a00407026161040b5840700c51214080c50702007050f2181c0542c080b44042400000034405403402e1020011180c070901e500034045080103005204048151024000f5107400004881a00711207441d1210030407105c1000411b920301c006821501564107000707041e0081c042003002e101182490740040c1c01404010020381c451007176021800b050020504544941c92030070707401080f1035a12401c006010340248880f043c01607003038000016a075440082c0d2407003200d8128018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 688220746 1250 688219496 688219531
    0x2060702071e260d08010302030703020f04020d0c18090506060a030509030c191502091e010302071410060806070f030c0507060c0908010501120c120201020a08120103021305 76
    0x1181e41101c038889080685002c1c000304002d22890110381e1514003030822203110641d903418035458025031071440300410030050700400050300e0015620041c0c90341202d00c010a10065000714000b4020314507501240741c24a9500c2e07075a1038100080c51103480e013a1111003285070711452102c050758000c0d1402034011000300300740510702d8420f42c0583d81042d40b0006a034030301071250841619082485210382c0c1c922026502c0d100c100303d84a013401444c000009019420400c0b00000118940219200c211101024094203009a8401d41c120742c20f4036071008140c1644080040074a0790ba0404400204200e468018049041d40000a220b4841d1000b82d07034401241d0f1494200710081c00f06400307014240700092048000048180c0203a92030200190b40c1d030306c2203901c0c050b01c5a0035205c0603030011510003654801e0a0100e0b05025002003518215201c0d0128480c071840100d00c2c0100709280600078a401081d41118081c842e140d030390403280200d0342030030ba4446205044085403000c0d240040128002c0c0780 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 688221996 1250 688220746 688220759
    0x9060316031a090f041b080c0306010e0c030403030b0f031005040b090c0904030509180f0406050c0f1b1e0a0c06020129010c170c2a21030708190206070207 68
    0x568058403481980c000c040605511b03c1d500d64031600300b800e9542007441c0312181810704216241c01007100403003d04803401d002c0003c014901c005400030381010f4807440006015140c03a500500412405402c48510901c411140c50060034180c40480340d680c0141c0102e0107043e00020281d90300e0b1001415480329445607a41034030302e5400310590b117410181e0003041905502c201400315100d842002c860410b1031a1902d4044200d1b200204802c42c0b414080c07180d02c2e0003959035403e0303404500700207010703001040b10303100c0181c6440d00e0800f00070550101500f21003100c1501062a0668074414030716295911744482061f42a2a400c0c150000000d00341e4103911401c00001d58020125074041c1483e00125459444421030080140d081395280a40020294040340040249000503001c0c0d0309840114000307556588209001c6085591080310b028002d1900d1110303a2100c0100c00d0340c40f40407039513511301d1850300720426040030036017400c00840d11212402170381c0041036192103101720358050698581441d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 688223246 1250 688221996 688222021
    0x314011527020712110633090108010902010f050a0c06050a0b0d0b060f1c2307180506060c120c01020906070506220b0f040809060316031a09 62
    0x16441030304401149241258103000b840140726280c003070080a04405207550740501001c0d4a010502000e0f0b0100302000f43c0025040b100c0300c4898125808903920140860b043c04091040071102a8800c0c81c00d00000f80204055000e071130000e2003a01c03400d400c080d101d101620b00780103140d0350802060051001c0c1c80001c070035a000c103074030214440c0d00060800c1c0c900c000c200075941700b038411540892071400f4000c091a040c0341a003c10502251842a11b0407904051002c00d409103100420100004e1000c4540c0da0060f14070000740c0c490f540840315825581c1d012000c003000e80800901e116403814022403400d0034100c080392941c0460324002c140740d083c0d540003043d8a45c041505807840d550f003803042102581e1050010042240500300405107418105c003079100281030682c20741244e81003503412400084e4100901f990140100c40c0c041c80300d998501b8290014443e1001259011100004210210500e96404d41000380c003071354100401c070180007084007204009040755a20031030410004035000c07103d9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 688224496 1250 688223246 688223279
    0xb0c060105101b0308011703040501020a08030a060b030403121103060f090601091a07060b010f0f08130c031a090f0307150204050a08070311100903021c0507090603140115 75
    0x40c40c00f04005507030590b14041100d11440b003100003481c02c000402c100300b4410071020140300a00c02962919140000103540c0303c010010081000c1c07004000a42500900d9001030020080303003604076964079040c41c0007001000042e013484000361a007070410308060307110030941e0701c1030001500e1244a5000201084440d0700000c11440c10030082c500c010801e43e0714080d200c54104050000c9a840e10310310715260050302d080200301410807104000b4107101c9584402000c4d003a0119040c0300d0803c0d02d4032551400040a007400c046c000c01000000007041000018003d0100074001d10810b5aa0322a15140c5445502030a91144240e20601041010442c03e0703d0324008501c1d420740c01843c1079610f002081d9a00c825a00102050304004000c005201600c0d070228522070040701c0d02c44851200100180c003a150500002e4000d42c1c4081171101e400314044442d50714903801404072218075035038038589005092580004c03100440e0300754043c48800c10501620200041e0f008094600d98104030701e01503031035180c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 688225746 1250 688224496 688224529
    0xe0c37050c1f0204060e061303020907270303020607080403021e160b04030b072a060b0d23070f0504020a02030d020703030b210a0602030901060f0b0d060b0c060105 72
    0x1081c81030303000303a071202c41c0262010003840400f44c0c41e2450550041d204e5100e01c24110f0050b10700300110340c0b0302004401c1c100242da50444442c040b54407210011980c00340010b00c107e8420482c00c0032403100c100f001d1200c50840c2e10a0b82110800d0703452100c1252009000d8400401581c001100a914030000c00c004200ca041090104ea144240b6005c41e8215003250b0380c030046a11200160620074000400040c40e4060071500b444105850049000c0401c010740100d520460000100100f00b00000b0340c0081000010082c072117001c28985044c00a20700e00e000003402c081c1d450040d0041d501c010040b80a0741114a0110306040240c581018000a03600101d060b40c2140001c000c020000700d081e01c040c0003064001e540000310841400248a100d19114030301150350400340b1a404500240040d600180c40d0b8803130405078594a80c0c91905025081130b40042403100141003010821008400240c038001914420620265075114a904110310800b20b03000290b8210300300602c40d600707005a01200b50b012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 688226996 1250 688225746 688225753
    0x29040e012309011506020714040f0f0b04051e040b06010c080a0915090506030a090816060e0118170715050112020109210311070e0c37050c 61
    0x108001c050094030905040107035036040304280010141c0c01d1143d089442c1403c0007000703000303080c000d010350380c0c00061240780d11004602c440707511241c0303030380e045080000c505c04000c1c40700965001120000c4c0255070405406245000d0014605282004469400d030002050040058a840d26141c80c1d8040040c015814844801c1442c0c0018036400000e0400000c1c075540e100206003400c01a6a2100606805038200300314403005001a83e03c810032a50000814500007420300041d203040354080c015903003030051604018002e9028001c207a0401407605001c0340080142036041c10030b111180c0020000030307080c0c07200d00400d0dc2800c0200d4008180311801203216448031080300c2d601d101541c100740c100001703501c100d844580855810a5610018111038646141c0901140c490f00e0044039a0b1400901040404a00340e04480410f0080d1001383c4802901d5180b20300e086640c80b500342e801051a4001143d01c003154003000390b140110701d148003940c009008ca00d01407019044842d070300015080707800c500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 688228246 1250 688226996 688227011
    0xe1509120106081917030105220608030a3b010507060f0f1d071a07030909020304030305011d1005040f0e0d0905180606090118030c030f0629040e01 65
    0x204205113000384103820810802c011061a010815003d503c0261008000030300040c0034555414010010301c065441107441c100840c96440c002801d00c1e0f501810309800001100709a46605c03500a501c1c105c2a00fa803902224001c842c021042509074a0200c105110301ca140c1800313602c190300a00a69000707086c00b06010395020031100458004001400c1456503521580100c3c204c000030701308080c11608041c108803440c01034040d55081c0d4440c100b81c0e204c2800030b2030000309406050030201400e4020000c40d121718051402170000e000a001c3c0003007440001001e50301d04c90300b1311392040c032825010b455090014030381410b010107010780b2110340041d6500c403081d03034002c00030130050b0200c1280039548040d1610700d030106100641c920804026080358681c0208031558951000f1a81901800c0c0380564054020701190040317114580c00080c03200041c0c1100009000c0407007120004280500c81c00c006030300701d03110405691190b9100900e020449180c0c11700071454640d102130058441e181c000708054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 688229496 1250 688228246 688228259
    0x30b0d080733061a031005040e100504060f0605031b040903050903011b03050709030308010b07020d1406090d170403031a120f06010f030803010306240305030a0e1509120106 76
    0x5110520001a962480100701e601142250209032038034000c004c0b03140d800c2c8034882c00c1282d0b44902071580616181c521500b8041307000c04c080c00310744886103003c002900345031500c00c02400e21280280d02080c02c10394045250700e4003055107448401d6a10880e102a0000030a10000d00f007000020f50a022013480913549540302805000a581055600c0c400c0c2c1840c0c0c020301908544002c0c0120b400c0102e00d0106100007604104214192802009107a072100414400102d48485128004110b6039200805a941c04400074040340a400300201f50b41c205484402e0403591b003e0f0703a203481d82c10b0285010104022070f02035070058042c0000301c104e1007244030444010462520044480d0b80c801d5200b400020f04a00c01030142c1c07400b50100c1000000801d1442c0c4031294107000c1070002802c103a03603c04101c0714408080c101502d2008007400c212020075035a040264070b81d04501014004501c2e0215911002d01e00304e0840d01d62a40d620144a042044c40c03030a0120540802d0300d000071941d40d4400c007003400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 688230746 1250 688229496 688229573
    0x110106030227150604090902030330070311040509060307090c0e190f0501050a03060504090f03020607090501020d030e0309030a0b04020307080f1c020c0d03050406030b0d0807 77
    0xc207a0451041030840b484440e80d40522800030542d14a0101d8000c111540795103004c1103e0480d180803201003501d08081c00000d00b10300c00c1c0703050f1001c2007070344a064082514000f60703840483e20b10003809000c26a01d0190941c180c5a4080c0a6180410108400d000c5458110501d54202c0405400c454039a13031134146000031100b00b078558401107110705130081d0309450b2034440d150940c00d90b410010741307081c54604188003904150040c207040c050041005680703a03101e54083c030001d00000384180210741c210b080071101010700c80400c1d00140101000181814015000b07803044030010390040c54455a0300714200d00601a407600c0c0701c51070004000c0403103181d07420000c420402c0d0168441880c41d0420384101403030f2400640c010400d0782c210442c510f6008001060300109002d840d000c00c3c00c50104004224108003401c0380c1746a01c800002240c01c1490341c041c0241041d1105600c041240c0140002007200040c0307911001880b0700c00420016001440c805001140c40c100c00d8540e068590300300440b11074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 688231996 1250 688230746 688230769
    0xf02150c031501090e0609130803101d04030807110717160e01080c01080a0b040c020d0807140306060714030f0d060509040b1803040b0a08100506191101060302 70
    0x105030040140b0000103815100000c208200b42009020580340c881c3c0d4690b80d100080a03540300d1205000081c1020b0765140d92581c03a0750707000701da0035500c0c034241588016110090007492403c9200d904443e206250560a0034082c5405444504680d0398028013210840801d640007a114003400000251410000f0036006103000e40101516098100001c155161525944187c215510007001040707035010105080304d0710a07007881c003038170300d6612041940c000e080c18850340e44d0450b1801e07030300c1c100a560114201c4c0010404d0b595114042c2c8a100081b210f4078500f03011908003640800118103280340c004010300003035105207003100c599402d10690358115000004200005200000d4804510010f48034a40140004070b4800e000c900b4a51201460140c00900c502c848910074011040030032420005e5034010010018034694070300c91150000c00c2d40405075500000404148004102803810109842103030b402107030030f8a040c540c00711041707500701e204007e1020295a6000c000c005615016007020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 688233246 1250 688231996 688232011
    0x150d05010302032b030207020402120726071d190b0307080f070801060c110616060e0f151f03030306060e03011a042c010e060a02090d030f0215 63
    0x9115855801410704010030000d8003400281880d200c00080020001880251040c6180041e200c2c030031071004c10300070b210341011080c10324011000c0140d251b074000391041098108c100946e00030301155090381d5144006a410354042044010b2581118080d0840d600d24080e00502c1c403207803403880444072215404950012512200000200100c140e0000107030754102c0c2450079040940d26090000508180301030280504106810f0740f03c9080c8601d0a800900c006030040000d6a111030012032130301e1101c442c48080312010308021351010b903124003043c0c11481c162030745c0c041c00d10316a03811010100c0d0030005001e4815144007085001080041c4002c1001944c481e0300d0000b281410041c0c050701e00035a208013203100713038100401d0320f44003003440e0001d454041096074085640c100006402a0044070004400c00807490301d0042d00c400601500612010619003099500035100d40e008442a44580640c05030440712510f460700c0000c0c4281c1c4411000c400d02d1059520b61900181c68840d690400e69940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 688234496 1250 688233246 688233251
    0x110a050403120e1509010203130f050f011e03090f0501050c12090a0210081b1c050108030708071506080d03090201030e0c032104170604061802030a0f02150d 69
    0x10310400c0003002d440754104549040c030440c2c0c83e40d9000010700680d01e080c0c654140c0303000861200300c41d9008200391240c240c0c0c2e01101105203034980403058268a2940709151040c82500c481d400d441d400f4042646202107020705079141010010819005881d01610845041c0701c403a4420b40460420f100780c40c020100e41c02e5440d5100c0c1ea00740704c3c14100c00041c0440500780c1191195400681e18001c0041d81803200c3d041c00103040c0e49a030440b800c1351084c2103a1200c5c00000041e08074000e500220b003100c10b080b110f502009540d0f00c2c1c030625562402410310003012003000300000d80201e500d040444402c40e100748408500580c8640e00e59041c04215464500800d8032080d007a0b08560b0180900d070707407802c0352100518000e40341d03000007950381c08440f05186803960625050041008120100e50241005803130703020344181e0440445a070b80350112070585039035207080000d004c45140e1f5000040b80c16002002400050516141e42e960856101c00482e4040aa4100c02c0c0ca001c13844001307006540d07501c0000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 688235746 1250 688234496 688234499
    0x106030204110f1206030f0d0206040507080f10020d020d0c030915110a030b1206040c060809030301060c020603090109061d011a18040c0806280e100c03110a0504 71
    0x144020b8801c0c44a000c0c010040520905142c0102902922600d881d6040d420b28a6214840400d05200e41c00820744001d0103091000f0086603000919036000c2c0e44100d0403184240d80d200800d6458041e020031105294002c000b001d0201f11158020301a00407140900518140040d050001240c8417041c842001c00e448000841c10700400f030000c031100d0161980305124000c4580002c0840b4419040c0c181e052654407030000801c2d0301d56079114942d08100608840b064203081c209002c10003003601c07850f00060070072000509500408400d603412039030280c0300c54402810347d81c20459241c1008001843d90766075410900040b44107400341c0341c941450010145101c6150b00103d50035554080140e00106405c0401800c1540341d030307444101034186800700d88907582c44500d0a454114459440032115102d00014070580a03016040781203100003941c2c0380400078010042c2c9000391541e0075450402d6402800c80300002506c80d800982002c0c04c18500029002329100301c14096401410a4100203400071a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 688236996 1250 688235746 688235749
    0x60f16030b1011030706180209010801090201091214340f03120c050102070c050a150c030305070507140102122a0f070203011a130e0c12030f0c01060302 67
    0x501021000514041c04480d81c040049582040280e0490b02080090420342c0f51100040c01179424643e8020800e100c8129400f201080b0003414850991080c000d1400000d00c841051089070700300c070b6040c1c44403d1301c0d0b8a8412900c01c17035544198151180c05440b00c03081c0010400b40b0070060784144807d58900880c04100080340ca01c100e034425100000d0140c601800742d0801590a4030071654007044183e081c41445404549a005004005100e507001203032110070400000504000d9440c143c0b401c0030745030350b0384c0804501c4004485900c004569014600c3c000329200e500199800b1203503003403540c030b48102595106601d1309032183e5003101d82d41c08a0b00000807029169025005a1408c0d4089210703600e0201030250072280c0c0140f641e401100040d240d110108080940740f02c06c2c1c00500802a42c5a440e40c07440480c0720182001d80b013001e4424600250701d500b0310844030403180d510000c04104034400144041c0b0200d402d807414a6100074041039034402400001403040411480c000300b0490724510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 688238246 1250 688236996 688237021
    0x6011e02060106032f1605060c12060108130b180307150608070303020d030b03100501120501050106050f0915040e0405160902070f02061b0609010b090a0b010206070f11060f 76
    0x9611310301000d18421700d5402e500b8000515030443c441d0113000c03aa20b45106990300c3c1e07016600b41004100c6d002d803d080104420303014001d0b200116089004c181c0300e41d00c1c0801114188411900081001c2c410117000c4089008000303482d078004c01c0c0c0032021500b40c9580104e03e1454002400417541c8079034805020740282003a0103880010b15280005014282c01c690300a521100b80201300003c00d5030f11402e0030400d66040021010700d0010b01c00822440d6142c034880310700b9600200c0266500e6003408000940c3c944100e0486a00c555006011800c14401500b00031803120780140d110145441030002064060b60110381c41c1c0110320440003000000d203061038035a041c03445a84800d80c5584140300c108041144010f0400300e0130350444090b5583d04071000b108495180e0203400c1c1c5898450001000b01c0d80c041584030700b03e554800c503940242503131461244030540d56000c1c01c0745e006811002c0401e20207406074003034003000b09160030b01d9107128000384056403402c81c0c11180b4042c0d40821005104500c82e80c403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 688239496 1250 688238246 688238261
    0x10030519051018020915060403060b330904020f120907120b18012306040f060506120702250515070b070e01031d0a020109050910030b06011e0206010603 67
    0x103003000d0102c0100e6040f041c41c0d01c2d11064002c0c0c0100d0300000000d00352810003202c8112104014160361701c40ea1207080c200c0c010035040001d00d0060484201401c01600c59212440264012500d183d50000f958140a107503908103044450b00b003030f000e0064042c14402c000181c2070500c00f4444c014605c4c50b084141034688405035010300b81e24507031000840041403001c0005a400700c030880390284900302c1445690300400c1c28080d104c4010301c142005112003514003440e540a00c00c06c41d01170000510808000003101c12600c141c030790083c02005040c6816451a402d41e51000f036a0050f07400521142d03080d03441c402e40d048d0002c05a60801402884545050b40c01d0020380540c564078541461071980d0340202c61a000f6000390107001a081148400e41c0c440e82003101010041d9089482044100c076007290b031042082c03000c0340446c149400106143c107020203042c1c8548400c0325130310185440d5455501c0004400752205041100c0041041040e10030000300c141a000140d004100c81d40c9803100c02011940c2c6d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 688240746 1250 688239496 688239523
    0xb010b070b010f0b1215091e070e031b0303130e100e09030d09080c07030614070e0901030809190803092e111c050409061208121003051905 61
    0x10810704c8901c1d0107606480c1e4840d1440c071400320544504e5800000712420182c07080d0300c80003040c208070303c902c0784400d040712034060a5075044150320341d107001343c03148880060401c2e0184d015561034800000c241290005000010742580e1030441c0c401e0003040c41004c95000450040300d0b00301401a0113074011900d02c010410b400c40c06040d0308000080303545a1042807004140b13241c4498004061203042011506140480c1080751143c035928038101c005020880403054103a0724540000300420f00541d0680360101c0c00502e052005d03825980c8000e250b4000150b0709130400354140c80d2189002071804980090a0940d00540d00d031681030702000700e6a460140da82456003035940c0344004180315030300401e0b40f0341d0f046d0504907008402001d1251504039032915640381d0070358808448034929040300013002941c1242c071050103056100c152104280c5600349000f001090100012402c11104205450300b00d0400750301410403d64946503517182c416034069109500301c031202e64000700300d81040100c115505 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 688241996 1250 688240746 688240769
    0x1260a0308041121071703030412110f030423012d03020909100312020d08191e0c030b03010b130b0111060906040638010302070b010b070b01 62
    0x1000e5034020021200604010b007055041d8044640d0341c0d075a21014502c0300c140e000504001301501c400319503182518400c0111406a503c268000300c000801100d200d180c001c410001100700324141180d41200070241b50550f03000d070220546852000b80021b10007030090702805c41c10308800500780c2c2d0a440600000034184141280d0947d400000d84140c0c811341d8440e0300c400b9000b080740c92030a030044e200780c2c12265403103840782d4204442c3c2041034070309200380e9014180b00140c42d400c40c2030503643c0d00f010761503000208180200081182007084002144910004408120317049070418003800100140c007180c4401e1b4076031071520b003000c0e4548034410880804500a2000425450100b030242c2000a00b4903201521089095002d0340154802d0b0b58442501d0102c8405190485001c0c0c0c94800c1a5030803107555040c5401e4030000610301108000c140c440460500f40e4403082440b0341c100584010b07840341419001d2186002081d03403141040e000704114410140e0300d4042d880c2212110105030040001440c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 688243246 1250 688241996 688242013
    0x100b010201020a020a080f040302221b0509090c0f0a020106170c0f041d060c09130b0120010f0606050306030106090606020a06020306030c06040305011b0908250e0126 73
    0x1d6002403059202d5070404603551f80c802e80c130b0340c0002d030900c40d540010b500011512406008414102c0304d6480c43c00182504016101107865403070200d1803041d1040f000910103003c00f0b1094540050701c0394003e1003001c299460211340e5081ea20160300f002e40d50f4000760b55200b00400107007010604280c808005e201c0648880240000003406c600002146280226aa09a00082505008442064894003000325122403034203400c0c800296110744400e6004039142c48030201940a107004802d124141610780750116114400941404094003283d1896592102140b07618990248510800341c0803903981e2940ea85020b40605007517a005a01a01006190480401210380c0c045080c0034410781c400d20159a82d102c02c00041c0c41e240050080300d80c004000240001041015884500d2600d030f110f030582c25080002c1c034161031403602489000502e03000708810240b100c8000c1c521003098030444c01080781c85500d40f0600031915409802103c0201e458115032350701c00100000c10702074444154001d00409 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 688244496 1250 688243246 688243267
    0x20c03030703120b03070b0d06050415060516140c010825080c22061709030a0e010302042409150912050a12050409060f0b07030f0c14100b01020102 65
    0x1d10a0900241c00c1041140c4040910316190300040700700c550040403500503684480c41c2c681c0c80d41c00400e400d103c6038134280000070790f421b1030700030865010b00494006864510b480c0c4140e5156210300303200c04149a0705240d00c00003552941c1144c44000d2034400400c1c43c410054000340c860080508108040580110030342c003240d80c824180c01c13545685140035000c80d121049100b951303000e070081695a04400a034844420b00e0400c5a64044441d10b17501e041e0f0042d8407502c80d85c0b42141c02c2c0c0765120a80c1040128040c2d2500510010305810f0041c50018a042e0340d0729440e29111402c4620300741050421014203042c0c917031049024000e4641c181c034002401c8408000034220071150f100d01c0c1f50f0082880100b038140310341400101410b0342c01400c400014091908000d08580c0039001c0e01c10b07914901040401c0511808809200f45c8a4400c9528500718103510180c2da20900e02c40580200032b00c04c4914000281e0441c0000b662514280061007031558054030310b4103403505504102c0c1107a01c14003000046 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 688245746 1250 688244496 688244503
    0x80606012c1219050309010306060c0b0a0b12030408010b190f0510091d040c090e0c06030c041d04020a05010c02010507020409060e160f050108010e0a1a10021507020c03 74
    0x469007100c001d100c2c24480b05155090001401601280b00604a030510030700c40084014107841d00241d07810011651148801e950400403000003030401c0707031075900080306014194454441604004c0a03034100c81944038280d4a15031164000c1c0402d42d441c1c50906c071a070306002c054210340d000300aa24810181c18070541d4003c90410348a02c511417503e06103560ba291703001d4120f04010b00300c043c0d2194420130403002c0e1322119281c15542203a28000300e8400240e0300c501c0784209948ac101c0c800140c078607101a4401c10005030030280c6900700f0b010303080100207514100300382403902501502c0780425003031078035004101080b509640824113010320700b501440180e90080441d14101d504480c002018529810028000c0001040b803482d24402c02c20b04029040d045064501150b40c0c52481c2400036482d4001110460028460009080200c2003c02c002c0070380c94101d14298110354000c0048041140c00107034160031030908d008003507081071202e0100c141c01078015980c880031070300052089105000210350f5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 688246996 1250 688245746 688245827
    0x1109130305370e0a080c040b030c100206070e0a0501050f03040507170a0611090109150c120314070e09070c140709151e030b04110a08060601 62
    0x10003100080d45001d80203900101c003520b00408040000c141020540b0181d80c03481500c0b9140030410401e10320702240303040c80928042c1c40c144009040340c0e901031404e2002404407140c0813641030040d42441010b507100d019410030140c01541c001c01c500e0a003000080c1c40b400c50301400301d01400c0907050600071039170001704484418500f807000c0e981da07681c0d6041c510704240c5070750000250040c011040d0300000100245c900741207409103c0801c052094030301c4d0040580324182d00a070110303108000801100800d4800e46007500d980d41000420650a50380710241101407000030008255104841c015103518584800e50182c030340d00708031055a41820000300a144018002810412448021402c01c0405070340c031003003905400115480f0b0340d11403500d1000380c02c0f542c00c080303440c1002c5213000904034108440402e200c400c807a0001e80c40c6045803a4000c50f000b000b0016201d44010348061038003901c070165004001e0180b01c015200c54100080010300381e01a028502c2c0c0c62022035032544080d854420100c5d807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 688248246 1250 688246996 688247003
    0x3390e12010c120e150a09120e13050907170304030b2d070210180b01030b0601111b0108070905030a0f0605061509040b01030b0910060e060721030209040207050703110913 75
    0x28106d86d6410000c002070020784000070a908124103841d004641c000a0801d40000100c40c0c000b0b02d9007902e014402117410440e1505610390108004210104000441c4501104550252840c0039102e0320f420032890b006841c020542d00114107140c000c1d50b04000c07020010300b00706034040036504021340000c2d901c5070f49510342c1d402c2c01e41c0c610f81c1074490940400c8421905030b019003050640c2d030b501c1c00d004014103000c855450200d01031421074010b00c000403402c1c404403682e1070401c5180380d400034011200010300900300e00034403500301c10114895900700319250f5175038401c1c6a40c803101d042c1c5241072001e44402501c01c60041c00c184004446100b03008040c1c0d201050240e80c0003440618840040f40074182c81c10380710340c0103a6540203001e0103a545002d01002d50b403103526400c1e01100284140516031050910261690300c0845028244007071200b003100364400980f40140c10500350b0300014040b82c0c41100110350550102808008120070916942c052910880c0e601c00289045405000481007004004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 688249496 1250 688248246 688248283
    0x5040504240e0d05040905010e0105030d08130f150c030608071a090a06050d06080a0b061e0303040f060e0f0114030c0708031603390e12010c120e 64
    0x3845040b03901c45007000d00c0c05012100c40c01003480d0b02a100d50302ca4064100726071f0800c400410070582540c1c2c080d040f54009002020a4510404100c0f640807004d4040903414a071140d0341c40110764079948101d00e4600540300d070307804240c0d03100c003840c05c0b01d100f0713001881450b0803c181005088070106418013241d00704440760410210700c005070b544611403d5020b0b60b10801e51072003c9801c50344000601590340405030100701141d2038041150703603041030040041048a0800c0050400d00306000a0b482050b1b1480c2903042c0a070003140000e003903070007680015081c00e8020a08212507540318402c9007403154180d0b900f10110420f04002001c0381d20296070950313411800000704421212402c11a061190860501d50b12404c0049202d80204011810b5400090405070601a06003181280c028081c001c03214121345041c86000301c02c001000b0062410501c018035110920f540c40d46d07019030365a000c80070000200e01072811405440d000403810300a164a10345180c400c2c3d541e00009480030a5031401420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 688250746 1250 688249496 688249553
    0xd02061605280504050a0e01030f031b06060305030a020c12030304080307020322060f020105061e03030d05100816060c030e0a030f0501290603240904031805040504 72
    0x801c50703410a00303185000c1006400381c03540ba8840d0301c00c018000ba01e40450751112569a2850b9117620007100b800003400e2500307081904c8002a01070201d41980c041d0006449000d8003143d280d0204071480795205a03455080001e220a00c198140880d07440314004640241000301d0201040b91740f40801400142a02400000704515600820541c0d0296050000e60802c2240220381003c001d00b55100c0d100200e2180071058a181d0f00600031980302d11710103030201f4500e0f491035a2035140c0e14000928182c06000070054001d1070352a5024481c07003149242d03a40541145400102450040000752001c0300f40000c4100748503103980508001d40d100e0700341c6401a0010510b9000640c00b031203036840280020b4041824408001d410b4001444880b29080180380d0016180e041d80200c05078035107a180c1c80041000003411020001d000280030041c118042040c290200c80031641011058405074042811f00c104150440c01649503100503000c25107060102d0b0525544480c1128a001c200900e01c0941920 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 688251996 1250 688250746 688250767
    0x40b09060703030228080109060605030a0c03060b0706020301051804080f0309010b060408160b03010605120a1d0708010c1b030f120f060f050a05010507080a0513060306080d02061605 80
    0x180c0796484514040b105c101a00342c0ca03540018400044020045000c0c600001014802e6208580031101d00e52641441c540c0c45120410042031440b00400c185559074030702150543d88a030250001e03503c00e5030011303a0f0394109810062080440701e0000000050030081000181030701d03040e200f1401c14044411b4070b940710b501d01c0364050081c100d6810b403c00d002060000720701c4c40c005407511400350100450341d1256103402d00c28103544000d029a0780400c00c200b00c601c05185107a12101d6020380c480200065480c0c2008000b200520401e0380ca1040354403045c1c051145800c03e00c6040310002160900c00d480e034841502c140211040e0301005401c1c07250075646108403a01803208099130300d001d105e0030000000c0711002c400040007103014244029120300000314441c244042011b0646205849860170f01101c0c2c0d076141140e030301100ca840300f044824441000154200c030f400c500580901d80b00401c01c0750509803050b15200d064460402158070980034070080c1003017503c1000b13a00d0003510b042680d584c100b01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 688253246 1250 688251996 688252001
    0xf07050114121e060109050109120501020c10020a090e0f22060f150f1a0f07060608030a14030f01050405071103031321050307081302090412110102040b0906070303 72
    0x2c004000322102e000700050b110340710104001c0c1c140c070241d85640b1902c848004450030341a034010b44d8042595164280051101801c1f54010a445080003500d802e00e4071103c0e60900c09402c00307a2000c0c51700800c51010f002c4d007100541c005062021850032491400884000c2880005840114107200c1d484010425000c2078208141080e00a14140309805860460100030000c2205840c1e10f1a01e0640c0440c8940085020904540940015a205860440c101025540b010402d103aa40da020448440021500d006400044c454840659120b600190000d042c7d01d04829041804441c2001006812207480100a056076410380c4e00007241d80d1400310035208180c806030900c50903c00442041142e8444500c1400c440d4443d20b009a1180020321100d0200301e600005400800c5061002442841c4114229988280044050389042c000e503008603039481c80035201034036946019000058140c0d080b2100c0680f4101da84021440d041c5443c200440e14040c0c000c466104680c00580e00041c140f20380c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 688254496 1250 688253246 688253257
    0xb0a0903081b031204050c03070302030c10020c030708030a090e1e04020118030c14060c0613050a0b09010209090916090b0f091311012c040e0102031f080f07050114 72
    0x180850340c1d1140028505010804d00319021519071041e56040c000300c3c100403500d00b00700c0398060000c2c101c1c200803400304100c01c00d1000c00c10007140705070400800d059908000010050407a0f0025665401d94648020710380c80301ca8105031045e40b0309006221081803003a95541c0c000300c20401181c01503ca610048807100070381290050202c0d0403810110a0044040c545030403240c50504400450304038006208050150110010607078201c480001d00e145048880000c1e0280701d44280c0742c0b074050903a541482a441074442d040560b6001c1a100000d09010844036041958100100309800342d0050f1100a100c446c080d00c104107031038554100d00d507110760b49010840d1070020000f610610700352031781d48280c580004081e40c1c0303130030b28407016601c650042030303400c007a1100405ca4407651265480038880c151801c440f10f50f00726650300040c400c1e00340203201560041e0104a51103656a1800015514007001c64104254036081200c401030140c0700011f03143e0441d00d0038200303104030980d070901d01d004500a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 688255746 1250 688254496 688254547
    0xc020907020111180108010509010b030615041a070b070206060619020703050a032a08120402030a05010501090e070b0f030a110f040306060603240302060c07032a0b0a090308 76
    0x8034100c08011340c81e030311000c1c110b1030aa031410480c0e0f0ba60740070040d080c4400e10032900c00034801c0011441074107291011002603001101ca103441c0c282e80d0341c0000151407040407908841c1501161540402000c101001d03004480d92005280741d0600360009071862080e0b10b100c496451201320b0700107225001740302c14002150000d0550310301359904d040280690814080c0e050040d003605981d0f1850a00310123043c099150072000803411b105901094000d01d09019000341d074035109409542d0000741d42406820701030402d50a0100361200a90103c0e440d11205410241c081d4000b80f050003400041c04060720b40c00403c101002c1031860610113804514410048403411034000010040180006504802c04507000781d0340800000310820071045a0920851014000e0325044401304007520304800646440788141c0155900035550350750f101100c082c0e5869030842914000801c1d0300040500415000a01c00b05d4a403614105212600a01d500101e0100606a40001c01e41b00600984920710400c0c6021 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 688256996 1250 688255746 688255781
    0x30d0f111213050a031703040804090e0c090a0b0105090409080c030a090515040e0f0417180909060925171c0504050f091305060712050603010b010c0209070201 70
    0x301c000c41180c55511494040d00e11401214001580742070480048080703a81000b110602c9482070a1550500d600107801503c50030421320003c200c6807050b210309400d40c16038800500590203020240150700600820520000f46006108142c50360090b040354800002140c00007104041c504d082015401180c09000c81c0e40b101042002040b40c01c03000000590b80202c0b0034030801b00704001d044100d84a180601380304100c40c1008034540c1c0580003501d50b0414840c480c400000540c0f603c40888680100910744405203d55040d64001c3c149505800e0300080c22502400702494403d10003640ca01441c88100c2064846410850360185064a800041c0088031200407500d80c050500d10b5544144004030005a4164030207842142d008008860448001400d140c1f4804407510800000701c40007080d1280c91000c1c891101e00085091190501c1040700c0c0d2100b2205044c0012074100301c40c001084940070341e2400c181652684c1e0046a19807556504441d0070208dd039900e0000c07805004601001200e004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 688258246 1250 688256996 688257013
    0xb1c0f05150106031425030f0f060501080c030402090c031305010212040203060901140c0a02070503010230040809090402131a10170601030902030a1a060a0501030902030d0f11 77
    0x40035181114120340040e502440b000010462031030361a0301c2918005510041c04070f40d00c021031190342c1111b036906440c1c18002855001421601e040e20905d44040e009203595801c02d00213580c1000d6104e4000034458840c80c10352030700d81d0116040d000b018000c00b441c440c0100000700070742512100d0504441d070100c003c2d902c0d0722011215040c805019038040744a40610300003da007060051007503503528010141c544d521a00e40c22441d800b030317a10045480c82107008803400807600392400d000914440f20400c05000c40c549110300c06080e1007070a41d510403416204007040c48041103440c015911105800c880c000590b88540c400100440d05280e0b9a104040c200600d10680400303001003010842002c1c3d91000000c840c0d080d044a03001c2ea0070003240c84c0203a59030041034441d4440da04c015a598400f404907001d9401a403901c00e40d0011003c011040b8451090411405041180695006101c01e0038148541c100ca940081d49a1103528450310030071a454490b20b40051203030113000040003c80042d1426503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 688259496 1250 688258246 688258273
    0x10c080d1e0f0e0a02040c121b26010306181406010305120a0c111809070513050f0703090510020a11070515120a14011e08010b1c0f05 59
    0x2000070859000003585440d401c02c4200041c1d0052412545010000d8071011130795600300310040c10004003040800c203000031405055072042c0314108201066440c0c0101b804075171040144949074085419000c0c2031807071002071032900c4201c06c0c3c5054a80c80240400d8010307845083c080c0012104102800d603c0d1480545403211a002c1070550690f809034003514244461545003014510465419500044509410b0800710b60700320aa10000503005110385080b5408640900442e20151020700703198000c00400c1095242c440d4107000c4000d034542c020301042c40c080720024212040281a00c00f07043e11900c00908115050250850380c0080010840d1100b540100c02000180c2c1602a01c0191240290108462400c0b4004204e41803414884924159026201c8040ca400c06446850183d8440c100240fa03040703802c002a01820201e00e4540b01c0200c0e081032000d00c86102d6005e2061a458046a0000d41e160215019900c00c03041120f404980d0151030102c5403909240390151040c055100d11403000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 688260746 1250 688259496 688259531
    0x1f09050c03242d0f0705090a0605030a0e0321070f0f0309110910180501030507061805030d080a0c0e0303160c0902031e280c1b080309070b0f09010c080d 67
    0x84c00800c9690240c90780e501c507040d2514030440c0b0169a110340b0b150800c1001c98850703001550320482030340c00401c40291a004080c85c54200700c80c01c9400c100c210001d42d451200c41d204580e80680140340c191001e01100d58083c1000300c41102c0d410415854030305640901c044030142c100300c04c0001c1d200d46290b1400b1280746060b010345014000e46040400d80c020142e1030540141c50503203800c0b41c081c2611529001040d2001103002e6084011483d82d11000109a64140f005464030303c0b40d074031840301510b000300c0440308550180642c43e003800103003118031103641c0340081512140085400d04c0c90005149041c114008806540041e4250340000200a2801c9540c02c2c0e07010740301001445015651075021a458030a000101e000e0020800022851150000d80e003095010700030710704007980b03520a020000d00031035040000a0728006070000074407110036010007404000380441c1039043d0402c1c50070081c807100e03441b8083c181410820400c90500502420b041140d2041003403240c10400c003440340d01c2840e803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 688261996 1250 688260746 688260751
    0x6010e090a0e0d230901140d02040501120207050705060c0f03040801060302030c030a050d0806041d0105071b0c09020708043602121303021f09050c03242d 68
    0x2c1c90300440420440c440c0c010440d8641d18007501101c5002080342c424400b000d90080c40019040002410a0700003c3e0000802010850b620800c056a15400d250014112818100b66020780714410480140495404075840c820340d0000c6824135940d08180842c285400046130038503c1500002030f0000d184d4005510200403648240d00b03484650b01101c0405407240000b200c003034440e420510700c99130481e214214450b840301c401000007600c010300402c501d08103c28201c01131566950341c400c2c0255941c000c000410507040505103501c100c000b907a00c440c08040705124040420703401060400820128000355405080b401d01280c50444401010703910110000180c0c0c010000c640600c8140b480c01030085a032000340a0038007500e80c0d01d80e03d052129080d00c41001b9400c5003d49840511025071020303d0400c8401c8209010907003081e2030819174280409407404a03c01d501210301041001c0350070502d1445a4000304405007690782d2108500114200004000c0301141500d100c40c0503004541c11560 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 688263246 1250 688261996 688262021
    0x706031d0607080a05091e030a090503060615070c0305060c040306060602010203060604060e0d1b030c090221040f0503030f07170103081e0913020918071706010e090a 73
    0xd5889803294103516810151503040c00119540001100c00201e5003002d5000b5022400316100b1b04c584010142507106000d0a020b000c0c0c00000e00c21071203542c014040f40161008501802241c106040000e0b01a04403d81d0144a9440400c03000280444c5600c0f140003160004166070252418100f160a99030050004545043c84c02401252291051080d42d210365800b07040980303000c0c20a80107880b0752181008440d81704d82c11501c00d00004428980c075805001a0000c4200387c1d5055260181400b20650440360b00c8510601001c503110a62034910714000e000703118540660b4650b4105030f0340c08100c80e4000f44c6036100c000140610348944042c030f5881458141d6480e000000c410800c00031180003032202030b180c4103040c00320000c0101e41451800c4100083c104040c030348150407010400384854034481740a45030b40403400c21028104600d86d1280c00c0c803004020907480c03034a15405801f981812410302070401010f00081c0c8070380d01600c14804035950042400026190540d400000f81485c1e00a05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 688264496 1250 688263246 688263281
    0xa0e061209070315090c0632040f1e030311030c0f0607080109090b010504021b0111120f1b0306150d05011523030703060308070b100501210b04020c070603 68
    0x20501d4001c5e101e0808080d03402968000f006190890071103518000c00c090036042d50490460708038240001c0b003a22260400d0400301501c0328a03020410105e0049070b0b004e0141b094009d0035824001042480f0902500d515040600c00144103074100ba103103004251074812a40f142e030b02c407002003000004000f0310900c86950368107480ea0b00c51101205035540c9d210001c04101c0800014410351a164016100c00d0003c15041920000076001590035956040d00d215a004400104090220351070220307180d00c02030480300c0c03044038188003820b40091032401e48003603940c020100124003079580d40c1503404c110f0f00070350102d140c40390040e10b41c00b0000d02303080c415010207a10b040780d40c1e500303d40124032206901d02450480e01212841011480701e41d400144110b081540e03448c0040001141c110140109074010041c8241368946002d090510005075000345040c48910031003a0003402c03002d4940c03c1c11100713404001c6184500140400c0103402210021006c9016102002c01e102b981075100221400324480750 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 688265746 1250 688264496 688264523
    0x2070c0807080c2e0f02011b082509090c050706140619080318031608060a0b0a031101050901020109140309040f020a0507140703020d0c24050a0e0612090703 69
    0x4156a00d01c2e84e078610030420101803019134140b40034600c01807440e03031140004103904031040440c00e549051078002c0e0001c6002d00c004d00100580b00082c09082800b80004d000f401d5044110150880d100f0b882240c06050f01e0f80310a0604511803415075001075409081404054007110b4a0f06036800704403089402541062525003803200310f812240d08031a079200c095803404041c1d0341d80140318000c02c4c0d440c0e1b4062040d8848180c000c6521680d0400406110010b410281040050a400c2c1e8689484051180d81020710034004140c6401c0307084c03461942400c1860b60b8403a444010707800b400d50124040e0844404103141860ba40000c40200500d4800b01c8040220ac164000110100d0203021905000643c050004000141588c0380055443c5115030031120384039035942c0001c24690201008444010004601308029200c065100c084004e091401440200001400425074051606003102b00b00924100300300c0c5403201c1007181c008095400d02c8020502d45070610701c1d80c400c1507200840746249121507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 688266996 1250 688265746 688265779
    0x606090e010b0d080d150806090d09140a0b2110060e010302041802030402031504110906030a0b04060b0109050a08160b0c0a03030b1804060c1103040b03010902070c0807080c 76
    0x200304003610780c010605814118005c0390a4010700c0107000001e021140e03c040801c5495040000c0d81c420314082d4010b18425a52900c0103110107600d40c071180c000503c004003020584d8600780100e094901900641303403580c0c00507001c20069034200e14099100c00c201e101303009000940c0700c2135030203891140d00d8094500e80308400440c01c82c800d41c4035091710742048200e5840f031041250002d5070050b000504440e046010aa89011915800c0e41d0460341c01811744e1074124541400c884941d440b26080340074184a0080d5110205440e50003400107004c0d60761100025550383c0280f0000e0003500000d041e080045485880e810390300d24158020a1045001003c005280b13088401103c00d200d114501070800444c40b581d040c3c2c040c08440303183c00d500440d0140d0000c00700383c80380025413003240a0790b0040b46482c00520090312403064040c40300340301c2d081080b05101d8605410120381c110b6080c850011f995010034123003200106030980020045010303003140056170364000580e201b070400c021546003040d000c1c0d41d00f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 688268246 1250 688266996 688267009
    0x240516030210110f0306040c0e0a090b0301050f010302030c011101060f080304080c15070b07021009050102090906010f0c0b04051014100609030f03030218100906081003170a0c0606090e010b 83
    0x6401c41040070b0800c0000c20f282015023000b50981c5035409d05919482c0c2100000d030005005030080360801359a4114111280f4090150a400096800c444100c1354116004242c50780d18020f5440e0501041e10b101c403800c1d403001d6000701c0c01440038140a040440e161541243c50303070312510440318244140c82250701c0c0307850644d0f004503100080d0f0220a240c01f00f01e80e242c04004000500140560140b10307444031040c83c0c3d500610450501c1140016500c07903c95003044041c2002400070b07410050704200c0407000e01c1d046007050590f59000120b1400310380c0c442c901a40b0700f29101030300c00801410a03800c0d07001c43c03000c0362400d03025100d11b211541505446080846d0060700d180b00190500e600d200c1c0120109001740d0007010450b9014104201d1003100502240000078042c502200184014808000c1d06610003201900401038410f815079503461501e640c0041108458442000100050f9003a451805030209040840d1f1114003402020354500581004020300e503a440182c1d401c241d00e07041d5900d4001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 688269496 1250 688268246 688268257
    0x70b0f1003030804060e010501090902030f0106060516080c160e011e0905181e010b011d0f062206080c030403200307020a031101110724051603021011 66
    0x2016240381903807540e01c04031031541c2c01600036912540c2d181e143c610248421302800b8081d10788002c020840c0c0341c591040c03610348482d86823070000c0ea0749005000e0001a500008032040440944040100710742c1d1800c0040f01849551070f01341d800c2c85420021404200c1001403d02110904001041c950307984500c828014aa0021304c401c080420404c188802c504035408207030002d0900310b0a101803214417070003d15124090300301900842d40d14401e40c01000c000d00030b03059442000e1908100400c2c0d541c13280b0741c42140490025200c1c1c0540b0311f10003699210842612409024115244d8150352010a0002450358a014100001c0c0c907690001b0703a4403040d001201e00032035050782c40c0a802040d102070201005084003501016000802000340507070f86090350140074600440001c92440e08a100241ca03a5040c40c00321240b6403c01c0c0340400480040e842c0d0360500d0322000104003200303a111281160399100c0c81c2ca030840302c0d80f4418954002d00d03500240c08640b0f620200c0003040001d8888182003114040c3c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 688270746 1250 688269496 688269511
    0x6180106080601090605041b0c02010c060b06030703090b0a2d11040f080114041e05100c11010b040c0c030503070c020d0b040204050916060c0c08030417120a0c1b0812070b0f 76
    0x1d103927101005520801840d0307101401050002080d040040000d08983c1c810364841e000242c03581c4c540d8007400148149540c00400003103040044140310072400040d00d40c000c40010b41c1c0c0e52143c44891b106003164111084c0e480e50081050343c1e41d80c450a06611403480c2e8000d19107258600081c0d01400105000281d000707d03041081d562074810750340c40a8603051040e01049882d40100c905950003200d0900581c507201d100c0303449040d40301c0e5061003142e003140d04000303045110f07030f080801800e10b0300d03040141e026159400d40381c0720b41ea036514500c00340c5040600001c001c3d08584565014400d11450b034407640e001cac51084a05000380e1b20340c6041290b40c2c2111845101581c00e00810070040d142c0548000c614403403240c00350308001a9143d030038904540003584020047c0b403d4440b60400c985007404400b00070640c1c14035a41c02d2404e0090b0003404449403200003001e0700c1c01d0f000458040b204141a013002020400200c40705243d0220300c4d10002c1e0817409084400019500110300d40350b00e40105140708165 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 688271996 1250 688270746 688270757
    0xc122104050604170c04020a021506090f0718050a091b09030506070c0204110a0e2d0909010216120e030601030b040b070504030b0403020307121106180106080601090605041b 76
    0x41c420300005129480710309900c58890b0850361785a58132140060700100a02d500a088212807082080c0954840200f41034401c0103034108101c640e2030700000c81c5800081c1443c0c42800210100c00e41a041d030b845070450b6600c980000c900061254003030300810620a40291020300300341e81210203541c03034101c9000041c800d800c42c40003d0103252150009141c0240018070101e99500c41c3c400d0040355a00c144403e0001800c4544041128200791724a0b84031500f03a003444003906410010b40881d090700d107880c2c05100340510000b080d00b60314250155020380c07000c0e400c0480d94050601d03100c00348a040780d0411000c1500d0400010442c038010405138100c81d0020742c00b40f011340c0c0b42d50355040d1201d4020441d0082c404c00b48808404107582410b43c520491007500155620441401c01c0c25003008800460010040c161b902c0c44800100414586d41183c3c085c01c03251401c10341c00040c00e001d400190007015552042c400001802c0c1200d410101c111407058804200500e0310484240c00042c00001c11b070701084 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 688273246 1250 688271996 688271999
    0xc0a110d0906030e070504050c041401050f09040b060415030b040b0609010912020117070309110603061e041b0c120908030a08040515070201150e01260c122104050604 73
    0x14001e4001340c9401500d00309448909441d04006030480320300b940c1c0010264400303c0c0c20f00002c4000a02c00c0041e407400d08100b8205203001d0302c107454034400d1500107400389441c1c1d40700e52140c1e110002510003408044c070001400c0c1c4100e4200400520031b508204e4412818500500c03074504042044507000c4030185e40d8080e1041c14078148a06040396130204904022a050f15501201c0344110350324043e042654010a00d031040d82401c00300002d686002c1803141c4810001d00410741d4034011100c1c04034840260718540c405402000600074241c18000020096042100d507038616402510030a420348a406485203494802078202d40e030010a00507804142d0040090611041c056807001b0390043c0700700115148548101c11203625900103071404400341c2e440340c2c078507058100112582c201816502e00541d10640c903110f0180c032012039407034041589000e41c13591090010418029010f0040d80505058000704041d010595610710301060112170382c01250018122130505400c44d011548001d10701d90809 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 688274496 1250 688273246 688273259
    0x60b130905090307141c1b150902042c01061413020706021204060b0906210c09010305031c020406120b1206010306020306150708030a0c0c0503030c0a110d09 69
    0x80070041d01201c002e2105014643c0090108a90003025001e8403010b80440c16160051919680d40b42d40d1000a0050500062101c8000101c01e00c00050300300a5100180d0700c940d9094005140c0340e44041e421604114400744c5042c4020011203212100095100182200f080c4039804c8403242d00440c0c000d9511452501c52a29280354a0004044030882c010725001d0f080e602c60b4101c1c0c1c020000d0445a2914100f00010b1122520071204050410368042c28640b4264001a00c2440840c0a0a1250480b0351141e400307034000f0006614107800240c4945000c0d42c6a00703140782d5039002828440c4480304144010700c02a032081c02503c0440c0c000d0b03200c0c007032800500d4600d03001a08080290540024210008903400541000131a0007075010360401656030034401c045c401e003090f00d0850b18410841c20044040090b0b022008c0b80d910141426001860103101101100c01403081b1a002d40a4030010062040384001c00c0010101010b1076201e1501003500011269110f02980f442500400c85044040001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 688275746 1250 688274496 688274501
    0x6080402031005040312050106090e0105062b09051006151b1e0b070c020f060901020a1104150315051803070b07051902160504060f1205191401060b1309 67
    0x500c2800c00490506c03825a0b254210b4400742c1c008000075086480030095001805d00c5103000d04826102e041c40c0c00008d0710010205100c0080900362051881902ca1103c07120764443c84140754060107840180c40c00810584c0580528001e0101d0f000405106054150207a801c4921544003c035002404c181c2c40d80340c40103100e102d03e10440e01d10010094510000fa00640c6a40c400c2100c0e031a0010540000e0051007000c41d41c046020b401131608100c0310143e6170b00010b129a807030741d00000e15552200b0103c01300340640001c030060008580ca03514044100072400d8985180c6101c118000c00c0650350b03050320392042e503c1005c50020703d03403c02c0243c1c4002c6014001c0c25a031090481c10400e1900d60711404120300d070b4800c0890200141c1221603c014101d824000d1040203010840b8240a0f15050042c240c20750b01451040d4007090300000c40350410420f0900503101007141142020340e814890703080001001600400c10407165182c4074000c125414a60b05a401d140341690000c20041e05281a0000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 688276996 1250 688275746 688275751
    0x20702130b041407020a03110610051c080a08040317040b06010509280f08010605100f17040f02090708091218130e0609070503340f05030706080402031005 68
    0x10001e844078990034880005560584c0221a5940200300e0141542070041c081c05200b01610748a81198003807291410601c1003403c203680c0116400f11844500649401e007003018203200810702d0030040740741c00c10700750010b100601c106e00a031581c81d5030354809800d410072548200c07002424095a200407805951203038020308151103020700041d507802c1d0003502d0404c994a07d01000c9070720092445040c82480e642140000c0145241002400b1082c02c04e8009800b4134404a00322041040c2a00c81e513070035512500c48143c006580d1225440e445c101380c1071251101e5404501640102d03c0e103808241414852031a4501c07409115000c0c084014440340c44003041d41c03240039585580180041c1c0002030341d95000000104403445030f800a40310302e295001c207041845c000c0c20424240c01c43d0070204126207022803c01001c410000e5904010724010004201303c15400d2580c4000c15a1750078040f0350000008080c0d81a42c07000c804640b00c0f19620403040f6041c500450b00290103402c0590398100c1c0da040d03a0001354 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 688278246 1250 688276996 688276999
    0x140319020f0a18141611031e0a090e060904030e030a080409020304140708190812070914040911060304170a0c06051006020a14030c0a1505010603020702130b 69
    0x10118107000001101e01140350400b4049582c440076010010b0f00d184680d0f05400c0041c1103410062820f10a0f002050045980d40e0381484034040c0090b004100c10300860306000c0c3e400599031880150400d070b0250740c1e001004598082662a44041007050b9540e000501c105402003c00f0180d554980c3c045801e1b00c00100340c01c1e050321841000d00c002582e0140580040c2003008030042c0c903403a060070f00e0f8003050700100c6c54005680001c40103104020001c1000210205419411207410700da0f071030701101c107210304000060707060f500c0028400c403941d124010f201110f07183ca02440102c040541007108803504030034001c1810074003101c40010b40c20505d01959105010710300c0f2a11905203000c06183c1d90740f048000e0b00c00125560303900800c01503184950b54010074804405296a800c15001039030701d0305651700143c081c5680301c3c0c0e00304810508004a07502e0040c054280c1d031038440ea5140c00718840d800b101c0800032444c100000440d03258840d100fa02d65103500104011030b42044001114010700300002840d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 688279496 1250 688278246 688278259
    0x120807050c2d01020f2203030c03350405060f01051c0501060b0a11010e0d1b050a170d0f050c0a08191b080601140405040b06131e14031902 61
    0x120341080280701034100e00f94040e150607640c6c9064182e04281e494001e0301c0440e50902c2810520101c3e601c904010242907240c200b000d0700720540e00c80c3c0d409030080020410410202002940c1081241009450142e0701c00c004031b03102500e80101c020420328003401116040240e42d2000403070380341e084000c5003070140507000000c1d00d83d8030b40d12044110740c015036940000c80c0601040902400d02407180041c1c0302058805003480c450540c80041c442e00301540c245940e10821440001400340c14440240c2182d484a03145508050810701c0748442d40008904211840c5440410401e03001c090080714403c004100c030741445c01080b10001e882c0d44101522074082c00c0541800005c12581500c02c481c03100e552125995a62200480003c14082000b0141d034100814440c02d062511311300300c29101138483c22100418820112000303d02c05016140003800d80540030301c00050980702c5001b03222000c94240d00b03103400c42503e941410488480362100140c1580c01018080c241540c81c51800f02141d2000307140c2c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 688280746 1250 688279496 688279573
    0x60f18051c0c0914061801030b060618040e0f0d03050103150e19051c020c0a0b16021302040806092407051908010f05010e0603160516120807050c 64
    0x4a0f0841d000c4040c00701140e01900180845031404982d1039406002e109032070103181d811a91004001100a010b99010b4040442c0c01c44c1c0e1003200c41c0151101420161080200032550501203549114840400189000c0c0304403035032007031744030307000d83da041c0c81e0042d0b0045142041d03007076240014002e841048820340690b015141c1d000041a070318082c01802103005040000000c2e07181d00382010028100d0081d98041e03807003a0410b403a4031400408582400180584403250031440030441054604000e5000035201c000ca8100903882c4d02a100b540c0605c130450b60190b6442c00c0c9580d440c210041c420b2000480c5603002000740540c11107141c0e010103c0d1400606052413150031001c1000c1c40c1661002007180c807401485200220b00040e002020b092034501107421801d0081481c1e84000b4021681109107174034407940c41402801150328845200504103402c078440e0508100f10410b801d4a500022038a03008a4034480c0f180c400d4401d2000e01402502c6042d50f950b9142c01f00d24039440082050b210308400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 688281996 1250 688280746 688280759
    0x30b0a0603170705060114130c020309030a0605010e0a06030b041104060b0a0807020f01020f090f0d020a0305030a030e0102030f0609040f14010b0a0911190504050a060f18051c0c 78
    0x81110184125002940e120f14061a000741403c2c0160000030a01d82900ca0384c05840d40c03002041e03520315120110010308a4480c20f0201d0640c0304880c504e6402d84901e4007040108010303a4403040c12500b580704000c00304d40f9080c902d01c00f42e601d50311002d00085034100c08600810b80700701400c1800310004100040c4290b4956040c980754201002c0c03280815009810062820f0b01400700c036807060204802107103098800200c8900300d000340d40d40039025005401021030503440fa51048103550740c00030309244480d03030340b0300e0703ca540d0364802080c0c480001e040540000b0a51014002e6900a50000354483c58640d14542440608000104180c4090f5580010b02020444107424014000480000803c020003100d051010359940c0364030055040385031465004030001e03810300791a1030960010901600c40c0c031410080310213008903040950f00201e0740c00001240ba40110002c0d9002c90243c41c1c3c071100c140b41104116070010148509034111101464000d400703542c0c3c84800300307850312400041714056242c50307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 688283246 1250 688281996 688282013
    0x6030204060608061c030f050705010b04051f0e0601200114070504080f1c03020c07090f02040e0a181403270315090c040203060a150909060b09010801030b0a0603 71
    0x1071142d00455141801d00c0254200510f0007417440d00140c5c000003552140d80e5000300040311a21a010400c04c2c040758510400000390002007224200820902550800138510340d258080e208074282c0d10802040000f80801203403c08511402341615100b10700c00c01e04405c604015000400c1744e107595a1440300f40e9a0149a0403010700403466036030743d59119810b202c0c103145401442e5110740095409650b10311400c1004905030321481d241c5103405a110340c0300c8000c040c50712559811280c51281086002c000381a140c1d40604204c41305aa1940c0d010703101c40041e80100e911411000144107c003403034000c04503a40020b1000c6900f0301604403450070114040740140e100390075101d130b45160040b10410080d0b103410450303055003110a40c049005800c00135501550380c0051062140107640101c0041c1c019500d14078001c004250482044c61014407681e0020f01c5030569010b01c1344070515024012070703d2000d0f4000c0d1000303400182c44000c401c1c0d00b0340e280d11b103e18000510a010782605c40d40044006482c0c032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 688284496 1250 688283246 688283249
    0x712060803160c0504020909240a080102030703060e06010e1009051507051516030c230a181a07020406030204020f0a0206252712060e0607020a080c010603020406 71
    0x3080000e04108034a03149420f0f00300741e804240b10b0340c0144152600b0f036031031201c0d640c0c1105003480c3d03150410070500922070609660444070742c1c0c0714208003000604044190000c51250401c1d50341002000e4603a1681d803102d039000d441160000754580b40711007003800c200941c070410924500340391f03100660300c00000f200076110000c10f94000303101040005c20041c040002d02448010714000e5a0607180c00c2400c0c500401c0c18015080c1095101c0c05a070030a9400707400800e4620b03442080210208494140d80f000c25804500c1003c0012500389242064a919401c580c0c181c071510942107141c1100b039048452070b504030b40c0e4260f038029558040000107903200c1c401845289229811140c031800c00e458040e0400304001c01c542c2d200f0309650446000c000c141c003201e8145100034107041c40441d0509045407401d080390359461000040c0ca075000700314440c00003210391406102d0407043c0140701c85c1c0f6110589642c0c05450700720160b448911050001601d14010700102d0700d1880002038001d0341c07a000201650900d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 688285746 1250 688284496 688284517
    0x1e190606030e0c030a02010c02130f02030a0e060708040506070518030102041d071403010b0304051525050f0f09180126010b010c02090a060801060308031f0b030712060803 75
    0x20b070b800c0114003000500900303121001c22806030048100c0f64002801501d02480000e00c241901c61000d400c51349664803000700c0e4808218110348a00d03003414141c004000040f01a10f492242c00001800710340302d850000c1c41540e000e000390500c2c1e1180c0710240c459070045084d00002100f80e030110001ca48092010b400281a24808500b5400c1500010010280040c2841c02045602d170030052036800400120323411140010101030742da40d41c50034210b0a252415000c040d40244000a01001e410a04403055031030040c10f282d0300c2c101c16050016501b91080f0030918002d5181030000641103804c00002c1d21052030068030150001403004841a81c51509030840d030810a80140c1c02c24182c02015581a101d96150008006607071210380044c0c04102d9114000748a144960000b4100321001e07088800100010310090011a4a0b45818920384d0011901035100d040483e07a4141416403244410b030803038201041c91491520368280486003202100b03510103216440d040005000e040820007401003011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 688286996 1250 688285746 688285751
    0x30906010e0603190b0402060721020106050613050d050f0604060509010c090e041101200606041802012001020708221e1716030807030e03061e19060603 67
    0x416408241e0480302910450007a0f201c8400050f03421454020940020f401810b509071544c0c80f0320025075144524007000b0f1504108000e03210a049840c00602c05c0600300382c00034000603440d1010b00942d0300803480e00000d118080001000241042408500340714060000c1e03408140340411401d00d00b02080d0380468090740d1b41c03410030420301402c0c403803880400014600158414134120024201007400340001d49a401035000d20b8141c1d030700500b511000f0340d40310907184840410401115031502000c0714221701850904100c0b44010b1621b004640c041a416190b903050210a1114a000003010306003102d4699800c004540c0800c03082c03805810043e00c2800110740e0030310890554100b80711590b000515140003500018a0f8400540314041952118410411401c842c103920f03614103c5892410350b45100c43c1203021052100c4407000313041c180c1c040d4581c0d00d0302403a64030a1590307a2008076a81101c08298900b41c0a119031115005508100c1640341150780c0722915845001b120705640c0003001295 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 688288246 1250 688286996 688286999
    0x2030a080a0f09050105040b030a09020a14190b03041205092e020706120f09120807140f0712032c0f06090715090e04060b0f091306180803090601 64
    0x551103004101d00ba25a4a09030b5001441d020001c1c009015a0041c40c0324a5404070001c1c112a009038449000142c00032308200d445556101140f025444402d005801107445c003140500080c1580c80f01030460b0301980c1d200f0310f599107945507401c20440007c0a241005010059510f0301d50f1500e40c1c036440084000c1c920034204d600034401c41182c004002c401b80540d0800c102c00c0062a40005480344218525000401c400da00c00f00860010140c0190040038421a1030880003102d074440c0307900744159003945030f64400b200070042400b0329025451980d46141b2081110f00000341604003091501d0b02c03035003804202c200034901002c09203000781c0d00080c3c10b600c40304608a04000704008030b13948000d41101800140c00c142c4100360320b820f43c40c001d50b042140d9440c1501145440f5201c1c0c08000c10150582100605181c42c295002c3e0420b800564403d40f500000b0300e500b482c1500788075000c1c12803414051900c0c1255a030b018050300c0644404076592101d11544d40105a43ca4011482645024040c6c0f100750b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 688289496 1250 688288246 688288267
    0x9060a050708150f180a0605030d140715090b0f040302190201021902180a090c0501090b1e0c010e16060c020603011205100204090e010c02010b1c080702030a08 70
    0x354030040c030038410001c81d207041c400d10401c1c14180d60041d900558800b0012604900443c044800e1704030204030707071140c80040016400d9140d0121080c0d660441c15a0075504007802c0850b030400d02160202080c0d14200002c600151900841819241c4c042002140c4040f10b03450b4480441130442ea00c000340c031811802c0104140c1e050160b140c941c03e070741c0711103001c1040c140c0000f5030703881c0d01d4000030203140700b000303800c2c000d564404140d0f0340a04950340c0781c0420340c0b03003150114000c3c00703800300100c0e10045a0b020108541d030007907010b80260343e080a810380c1000760895a40380000f41404480d220f8202c10030103100200428003580c101010468000c0181070f40c1050407002e5022103a01c210f080007140f901010040e502d01c800c03030381100c94000203035030b01560506003582000070b1008041c031b107140300150010302c110094112000b402088002044008540e610907801d81e0314140302280d0040d4040760030303110380420080790680580907090032418608d00c1da020a1411188640c00c2e180b441c004281d0b850380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 688290746 1250 688289496 688289501
    0xd0f020310050123030c0916081b03070e120d050a110601051f030219200d02060105060f09060d060305060109061208031f030b01061b05070b070804090509060a 70
    0x10350035204104010f41c5403410700912a0700107144459500c014400c2c24a603507608000c200070b20b0300001c0081d400d90a02031044450030041c02601000300e070703a02000070303500c501032000c0041925038a1040351a5544540e41110443c83d40c1a0709030380688080d00ea441e288204101c209020010340d1121176941090041c090142003410b8181507543d4000e000502130394130703031115807803022000c4801030104035010f00060b400f031b0090404044810340740210500250b503020500c5800c203104031410458030007000d0516525005540c4045003d40d000304010406d5041c85e00040c07542c905100000c608000c80304000500f0b507400403d0080230aa10f803e000c0c014002e041c0a900d00400e800301c82003059520300300c03800c00c154890b0400a0b00d900d0002c000a071042074140b040200d400c00501d194820b160302c078600b81300918000c1c0205000110000e00c5030384140c11145641c04090b410130010a03100f807a0a81824003a0701c403088c11942c0e6003081c4400210030340a405010302035100100074290515061104004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 688291996 1250 688290746 688290763
    0x2106010618091e0c050403051506041a0102151e0f07030b090f061e04180b1b0405100203280f050405060702041a1504090e0303010518150d0f0203 64
    0xd42600c3c00580700c84958040350004100120541d0210300d6034540324090342c6030b01450344082e01d01d0050005400c1d441c0151640c0a10600041720204614171349241b511100e8101c541d1704a0160380030105051407d404401d000354441c280c60390350108094142da00c00000b89040c1c0d404600c4444880903c280140c0502401d040c145060742c4002c100c3c5004c030007a540c0083d01030a000c0c002c4070900d0316114044250800c0200c001c001070814459881c0d440c3c0da083ca1402d06c10700a4440110580210300d00312891a5400305082c0320a00311801c15040c41d0803c800c40001c140000300303500c020000483c0f941103d131000c0f041c0e1800e00000500740e22410030050409541c0580900400034200000d0225642c0c0130b0a0701c0d12590190340000724011008070a0550100440d050740d8000c0710080a101081c180c10003c0064441060080c060301e400482d41a680340400e00071654041e542e006d40088900c1c20103046a4004030441e03045021100c1c01d004203c110400003010340d41c3c03014032014002582400c010595 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 688293246 1250 688291996 688292009
    0x616060902150c0d0309081201030515060a0501050a0513030c0605130b120a020c010608120403050708011802091302060403150506010f1b020117090114090f0c2106010618 75
    0x7490102c3c00c0c00700580300c5050302c1c50481030561700c040e15004e000c500c5040e2001c13a6044010080303c1d503103a052042c1ea590702c102451840b03950f40b80000d0420304041c2e2040c02141c030107860b01424041c52480940d05a0001d180703240074885103180000c0032452445404e80208415100c65546100c100800d442c038001681003902c0440040004a08082540070115400380c800074006803103100c4420b0050250400fa4071130b00251042103840c003095884140108201c0788689d0444d11079603035504100b4260340e212003e03107200d0380e041c825903000740c01c007040959803085010340c00780340018040d80051000d42140c1c03c19110503540c81070740300e0511014030a6030f82000c000d081c1070200140d0018001c1941400d400d0003d0320020307000407101164040c1c901200844400c0d0120481864a590741c0d40c024045d4004190384030707008002007000106c0100341d0f108098030101c080c0c288001a081400110100300d1440508204d5091042102520078845507018054981e26510203212109070304c2e103944000e81102 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 688294496 1250 688293246 688293289
    0x703240807030b090f070b090109080613060216120e0109060c050c011d1e030105130305040308030612030d0606030b0f0a03170c0717101b0e0616060902 67
    0x50122050004240040b641c0c01001d880ca0703940c9010032581802521140da102074410041e021130f6904d411000340c00f000c40b00f030741d9042056503110f030045d60714001500c8002c4650301100f000e801044a580041c04920940250b1a0011030540d8a0020b10303444d8040c000c000584c4064000000d60340030031004020407043c6403251403280d258445981f1181d00c1d00b02c0d68140280f54088000490303601007101d841e08070041100c1140c100b244000342c0018405d420f01442075207000006250002125800c528a61305a0350b018140750a55440c1c1c41541c0c00501929803082d00403103107142a84c0d082000308494282010041080d078a010390180c103848545a0141c42840c0d4400921550303125229150f0840c0c0d040301c503a140508448200c5805449105242d007014002c0c2040458001640500c800745000040116441c440805034603008450151080032010000340300c218490f03510521007080011401808103107021040c4c44038400e8485a01400ca03a21a21521004150f1030032442030f683e014001c0000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 688295746 1250 688294496 688294499
    0x16080d1704050d080703060f1e0602030406021c2a0204110301060210021b0313031707080d0b040b0402031f0b0703050a0c0f0c0f082a130e06070324 65
    0x1950f0f100c1c601002503900b00300420300007a1950f8402d0b0810b8000f00100c0f55221300c2d190326013801e20700366106100901da00c100091800915940300004403030072aa4640c0c060151103a0f401501c40c0884170a2010108000385030042c000000e40ca008004800c044e001c842c03908680780c9105010030b866116640c00b010000500c01002030b07c3c3c0200320303112124900c80300141d580d50b0380300010b101c40c02409814003041c0f0001c0780c03190323008012194000030b0303a01456401e07071044183c0c0305200240c0304800c00203103040e500744005d0400305040d401507815900c0080022405829030000314080b60008c8591701203030070700031480c4402242c285c104a0083c041c1c413524940392040a4502604911a100991080011885560051113035100381242055031203031410048aa464a824250b0980b900401c1d10a000303420a00d0408494064100d000800005800107040b01d8502007007010b004840e02c440f1469111441c0181c404014821540326003459100002c1c11450700326001d4034aa4241c0340e220000748801c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 688296996 1250 688295746 688295753
    0x1203140a09050c03013b0a03050703022a010311160606060e0307120813120503041401020d090620030d15050d0f080d020903060403020f0c22020c16080d1704 69
    0x400c4c034400c000300502c501581b03490040100c1c11070300820011401c0c01101041020168060010010140a40d08883c0001c515402200c40c03512030f030030020307103070b48100c01e00300301c19400307600212021500d401c80641012600038954014105445049658503a200c0381400016040861648400025070007022a182041d01c040042260484041d045641c007159031008600031100d010b0140c07119842c982240c1d200d92a1407641c03074000b03001c1e0401c0d02107070b0040740c10603500c0001c109003600c116a50b1403403068a0180140c80300ea8407051130707180c601004035190320060810001000032801d08200001e080035400312003040e90700c0c0e9401052041600840510228882c820402441d50700034806c03c0d614524010324000a10070740e10041c2d054020034080105141d00419222284503d28081e21010f00450381002200d100bd800340b8034080310080c11441c51181e856000c4c2041d007005004a890800102801715040320307455210f00115409070f402d0301c1c20280c1c480c05074001e00c0000320401502c0d08041e41c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 688298246 1250 688296996 688297031
    0xf1409030a0609140a06020c100912030b01020c06070f1104060602071e050a031118061011210a020c010513050409031403010602010603020108090304050d1203140a09050c0301 77
    0xa030180800b0348540c809014000c030078200004d11380000084644091103483d050020f074000c54040215405181c000c81011184c501601030240d902030b03040400514003040907001800d209007854114030500c00b1800c001d0712114024103000c1c0c0a9800034050391b046240441020000c1600c082c001d0b030802c14204951600050248240d88580c0c003080201c0703508110b41220100303141d01c00b80d03100c040040c0010911855190402e418817050300e1082d81340d00804108200c0325419248190013459818600118038810a41103094801d004191115081030f004441151111600107102c450f1001602d01c034010380401141c1c0c034031030080c2005414540d0311844d42d1042d5896219150003280c80e20300071000c06200d500480103070051000c0d0b550302d95840c1c8000a0092100b0701040703020807000808110740b400e001056400700e80f402090440d030b12071a5900ca82248a411003182c0c1855191811003c90b032640020152240c0c5001c0000192a8040c3c14980d141c1010300319910b0081c0d14042c0c0c50076840c1c0548 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 688299496 1250 688298246 688298263
    0x50c1002030a0c03020c030a0614090105071d0a050d060c1701050d0b070507020307030303050702010c050301031e21020d0e0108071d0a03020612060906120318010302040e070f140903 80
    0x7400c015034a202c8500f0140c0c00c004400418079414004d0400b00c8c0204160b65000c100c2004422920aa0039900c0012560032141b080e12041c0100b0700258940a90540500120b00303400b00203800c59005070b9640d03001c034044194000c41114401d0b101d03041d480b001e036400b64a0f025188881040760045515001c0401c1c12247c0303140024040000b20f40000e06880e0050045422855020f42155011076507410020004c1c04296403c2c0015421f12440d0b14020f8494020340b4140d0340c00ca084071a00300c0845404a00c108001c3c00d04031402542c50140c02511805481010000002038010f410220502180105401c0b00282002e0611504000b48062643e0012901c411003810140c0549541c031940c00140742d101da264002035000c5000204a20401c204100701030241c40251a103803040e4030344808006603c5c0c0604894070303050340300f403000c91606501e0f11a01045524181801860640c8600a1001d10001100d0000100c0d01042c0c0c5a807100d0b6020703240e07010042c580342c1124104002a070010791200c000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 688300746 1250 688299496 688299517
    0x62904061409280305060604110d020310120f0501050a0903020d202b05160303020d061d041202011b080603030f0c0601060905010c03080601030f0912020307050c100203 74
    0x2142000d070070307100c40500003510f0020500303015008283e1812981207000500040b200c5000e034201086441c202030090f00101c030085d0b000642008485040e038002908000d2100d580c5001c02c1c000020079010810020f110716003d01100310003d42507081980c2542c201422440040d4900540d002c0880c1e030228002c24030880610f840300b80d00e15034010b98501302561344603401241c0200448011080200c40d6614200c14914254105601e8038034425503081c000c2d14500340c1c0101107100d0500020b84654014000100a0301c800100503440d0f00074000c0030603000781450140a000300038001440140d00580020445c0d900c0248040481c90f085032620658074481c0d001408071581c040754640e5020310540c1c0c0504ea40b0440c05455a0504008a030384181c2840b44001043c0003200106a6501c0350f40c140c8115605034690254030346410b03004500400c89140e40e40581c698030782598000420b0161104484140380d4000e540310b02003800c1050070448141e01c228822039000e001640c4c41134000c801d8070000140c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 688301996 1250 688300746 688300787
    0xb0105040903090305010c05130509010b031f03080f0304030201050a0b2d131b020102033d030b0a0f020c060a0e0a0f080a110c0a050f1306290406 64
    0x7100d280c00d03960380945800081140d400c0182d00c26a040d071180c00350000150740b20040000640d9001807003440d81081c0540310342d5500400014000e070405240700e4401130740012a00401c9035491b11a18016080131120010070f440000900c014158240501c981100e0000342c02c0110f01ca01c1d500050139015940d140500c1903940e40d2111040c01c889001c4008103020190199040240400e03400008000405121380701034002c0862042c01403052081d203229680031301180031000e08010359000c40100c2030740c40350341c400c1d81003080842d0480c4443d01c01c030042d072042d00d800c402420000030b202c05864085441e141e100707105200d005202d80c00000c496802400110001600c441d1012629013042c402240140100000e00b8001c001c011701d200c0142800d111a50711640209004c03640c0c1c035290300c00c3c450a19440003c00d802400149030004911154400013405c085000f1140c011032401e0300c1c2198848130b542d00481c0380048040d500b000341c0714501c05d800085070f840c05041c0744014049006251000c0050714 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 688303246 1250 688301996 688302011
    0xd0e01020a06051503060f1501032a02060f0106020a0503041818150b0103140f0a0f1a0307050105030108070e040c121506230415170d0e0d0b010504 65
    0x24001d001e4001c015421080603c081c0c940201a01c043c021111182d81c02445110f000407a5007180107040c41c080c1c0c02411546030042c00342001100074000da41420014040c840d1300102030841d51407188441c161160300a024586406124032901c40c005a20134810354005448201c0041c001104950680301b40c1001d202c41300d00242011001810301c181c00c0c00d00780140326203000c01c0c40411400c103121440320f10802d219100411004605a4a0310041c090b0054541c50103e41007084910125502110030070300081c05246041015041d10080042031440034141510301155003400e000c0680580320030700b03283d89503500d4640e400d070b59107103a842031100c0d01c00d021380881c0402100090070b100800189080400121082c10105484200804510340c0689004c4000942c80c0a601d044090346101007192a062900350040c8000b40100c0c0c03010020041307400b80e000c80c403001211081e040040811005041c898082c2201503c11010203040511401a140320080055403c040c8141540d009031408107444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 688304496 1250 688303246 688303249
    0x609061003031826011503020906240315150f0a0503040503072f031c03091b060504181a150702090a020c0706030e0a1101090305030705030714010e0d0e 67
    0xd074202e41044e203240418804c01803021030008041003620341c0100c0200010030512070106031181c4580f0000b908004040002407051525060140c96200d404040c0410000720050600c40ca41c412101c2c0c0d80000580d1651700b4160030200818185203c0c28081c013458045110031030031840c007580c5003501c04c00400100080400006205540b040bc0d400751048220303401c0003243c800b4480342c28032400700c5003803003800345450392500043c201001405000e03d8050340f400c45400303c0c044e1004030010307940340340390940701c0b04001070580b00c4c5401841c07540e4480303450f18149421008141044002d001d203990800200c0c0038501c141c07064400501d4405c440e6100007604009a007172040c01141000795004d0742410030010b030b00c44150000c201810081d801c0ea00080d4030350b40c0540884080c81742c3ca400c5540402c40c0758001440c60b924002c00c80e001410455a029036aa55662442c1c6c04590100da1580022990f0342c10132140e0607490011314a80c400a000422008400c191750b0301c840c07240a400c00400030207940d02c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 688305746 1250 688304496 688304537
    0xf2318010e060f07050c0601090609051f03080d2304050c010f08070c0f0b071211040f030602070c0e093d090c170f07080a020d08030601020111030a0b0102060906100303 74
    0x24101c00e00540b020fa49c0d4500000303004081a100c1c22980034200300014407840301c4002400ac3c0c0e4074604003100c48041c01c54407800d040350054485003540b10355498845100c100c1d1200c11800f01c440005280030a0700c1e09241031820452080030090600c04c0c01504801c505802c4041c070f0740c0c84111881c105560000608111000030503039100904150030310428170001c9544070030a61000741c00000c00380021020302d00151014451481140c10f0950100b109000040154005126060003000440c3c200e0362508900c00c404241030703865410a41c0f05550030310002054620b1903c6042115401110f80c05045018000c410000070986003003582d1419801d0800a08039940e4002d82801120180c00142c6903150607640e12120090380301d140b16600c0c0c0000d06540000c2c089140300d901910704208005240da07000e034160800780105040d035480781c2c4590300790707045031010b18440c0000b4071012482808160000e8100000070385032000603013004040005811010074080212640f40ca440c02c00426011800d211 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 688306996 1250 688305746 688305757
    0xb150303071a070f091401050715020a02060109270b2a0409060915170715080402090f010303080606090f060d05180109030f030f2318010e060f0705 65
    0x492603107050081d03030b00c0001181c0248a072109440c3ca100102540c001940c02c200c0500c03852154040c0c041405500e03500c1440a408100c0c462400344180503003d621440c140d8001140300c0005038010801006104d80902500600e007a40000480c4120354401c0141c01602d00c00c0c2c0c1c0604040c0c000d4000c03640d03800f0345500c42d960030240c882c2c04005010000c4000c85d0554454815100603d061400208104107240704000b1111501c401c0440002d1401104085940360741c05080020b000d01503000031650054921409604655501c0304003520301407040242c0d502c0003030108645d4040071001480004c1c2c0100c951504500125151600e41c4210340009400c2100d59040d540c210ba0085a4110aa826500083d01469211455100d075040c6004c07100c0c01c03200741c981c000c0c0000303000c01d00210381d440c040c3d0b12280d06400112004204002c3c40809100c0e01d0b00120400b42c0101058010080085202031142038203200010084c1f1180c0e0f01c6d0890990703911400740070596182050408914075070701400840f007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 688308246 1250 688306996 688307003
    0xc180103180606060f0e040219110f0714150310050103020d0e1203070306051c0803071b1104051006200c0907020109021908100b030321150406030b15030307 69
    0xb003d151100e0000b40300f00100d607066000b0503542a491300c05468a07000303540700445521401000380c100e601b02140d01d80301d4480c2e207601070700558480301c0c980842070240102400b0304e9840c00680b203503510240455076404040c049010b000074010306c0342c404001031070f02080b5030003481e01603101c0c40c41030700c0b0100030044095001520b101c1c25190742d2542ca820b00282d0711811294504004a65590050108101010005000c01d000303469440c3c001800160242da0020700740d00d840200ba051a002903458100000000d45030302c1c2243d06902c20500d0b107030040c640e01c040c000c06010781491400c0c2014029590f10000c030040d0340314201074800c80b108100401000307108001c01d002c0300b07410504000b07070080860701c6040e80100c20f000d071040c0d00400e1160090045401182c02880b0841403043c1000040c1007804181d68180020851480180034110b000e81c00b20a8100c04001a800c00815100302002a80c5655020380e09200040010410b81c0c4841a848812800381c20350b4500c0c04400a030031445502e1004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 688309352 1106 688308246 688308251
    0x607050706050c0933041a070213050f0906070c080a030504020a0305121b0616210207060c08090c060a0c020d08040305150c1801031806 60
    0x3641c0846982e0703003a03013800214030014a0082e54200800e030500116030502040c1c044030a040710791140220300052516181000022500745104828244000041100c00554035070114200c400003480070308000d00d01e80400c00170b00d0081c06a6410b0084c3c0702e42c20000707c169000c2c0c00c2c0402c04541000c400d5040840380039085001d481c00500803604000000f0700040051420820075171300464060b16240c43c0c02c10350141d05403440406200d02e41d641c0c0504240310b103030040100341c0c04c0c01000a140c0b0000001d0000c00ca00720401c4c1466529021a100180003424458554001000c02c025a55200c2254964070032103541c5007611011583d01260410500e1642800b070300c5941c200c40d02c090800c0b04144440c5c3c503031009507040755000352220341082c002600100d00301103281e50700c8030561800d030342414407004038040702c118052169810f041d50781550104011091074060f10080c0d100c0e005 = true := by decide +kernel

theorem cover : BRFrame.Cov 688129496 688309352 := by
  have h0 := BRFrame.cov_init 688129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 688129496 ≤ n) (h2 : n < 688309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
