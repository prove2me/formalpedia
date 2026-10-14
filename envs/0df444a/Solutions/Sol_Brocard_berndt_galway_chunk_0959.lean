-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0959
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:30:22.009986+00:00
-- url     : https://prove2.me/submissions/fb528204-a2aa-429d-a82b-e6ac2c285e52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 172302158 ≤ n < 172482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 172303408 1250 172302158 172302173
    0x4121506050a0f0e0105030613080f1e090f031614030304120b0f0a0905030a050a2304060e0f09070e0d0828031e0b030a0203010504050f011808090607 66
    0xd070080703030744100341c41c00c0800c007041040089001c9070480d0b0308020860b60713200c05040d110402540d00c0301e1801507260310040440da03980001d00c41c10b2414060b4a141c00c00381d00c4000c01107981d1940e084142d1178000b5400c130207841c1c81c1001c6146400110048c0c44900301c1440c90303045038172641c403440704905100c04500c9015036003482039500621050010300804684c80c0f6124109110445051140c1e020b05004214041c04901c075852015500100540c0380c4840351070305465a800c03014a1400b080f9506076000b10800701e443d00e815512101c40c80203502c4904001c409054401500c403624019001219010080e40d00c003124160800003c0c18525800040f02002c103414138505100038000100018042c9603e03100362a5610200300700c06490500c002442c00c0031403d44889151000c21100b000c621188008001d5100f0075a5001c003c08507100314406501090039220304032016603032a004071492149401003802000e42c00c000d5401601c0d02e108040d500c02c0010700841c121903005807004110030080107600c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 172304658 1250 172303408 172303421
    0x204050301020f120c0301030807170f0d0c030506040e1203060d0f030801060842030a03080142090e13020103110c07140d080a09080c0303041215 64
    0x94002d654a402d4040c6044440d405101c120070784d4100352000502c040780500507281600d52040c482880d2100c5920b40c140b00f0184440b041040c1541000360b80c0134007220100804445081c0180429100d8009070081c1c12200300600d028000c030300705513001e00e68100200700d84a84800440d01e864803a103904020034081d00101c1d400070208450032000f10181600040c0450403166542c0d52407503a6945d8158450703000c07024101b071304156605450911a08859420390343c101799140c543d03500785101e49030002403811207900b0003540441d80c00360040c012000b00810b18800c601c030150549042040403540b807501c22244000003035841038402c00d05424039100f003c8400050420b10b00820381c0b03061032850200301c0c00134030300100d02191401d400070510074103160036200c0844e0300b040641192450800c100c440640304803107580e807251203001400d000807084000b42428000d240d4480c003429042000c414a804100003030a480ba0b4004d00040000041e44814010b203698054071030900e883d1078008007409800c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 172305908 1250 172304658 172304669
    0xd0f050a14031201120201092d090b1203120412030207080d020405100804020901051009080f0a020a061e0507050c1e04140103020607080f0f160b0601080f0f0a0204 72
    0x741e5910030054031000000340461020095440d41c0740d036a521115812003c070b6030760007404255400410024051000380c600c80a000d400d4200c0d20001c560000b58100c1502d54000b425200d658640f104050b05000075520300f041407a5000b540340a5140d2007505401000510040001000f0703c545410103200b45c0681d418554400314440d15000c0005041000e50003c2c010203001d091090010a440380c45884c0081c0070b65000380910390544d08141c180503428504800500502423500400510004100522195122200b0280100ca400c51040102c0c0c00502d902c00c004102250740d1704283c10916100c0c059100f03402e41000c0d556030880b8642141481c1d013084113558040290110300070841d0101ca111000740701c04507010008400e0310130055200350000c0c040a90816414440d42d000034070f00d903004001401c81d80f00524100620300070320080961180030b42600005407580c4940400000f2510507030040d6013403c0c041c01ca8a810049031500c680020300040c0d40e100c0440c007040d15024075504640107481c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 172307158 1250 172305908 172305923
    0xc0102041d0c091e0d0807050a0c051206060d1a100306180308010306020702040b0d0f06050a0c05030601030b0a0b040b12090a030212071e050a0c05010e0d0f050a 71
    0x95a401081c529440100110503250822000184804003400100d07400054010800c0c000c510660380c411909503402e188141d00180761000140200b2105d402030036109102d00010076060080749003000ea50b00040d0f1140b4010001080b44480341d080215119920900981c0d13600001000350030140800c00c002d0304a4035000d10098140300c2c100c0005014181524000c440a00040400350507142c001211030801038001150400103100007052074006040141c00248003003419254800019100928110202c030240002c060520800840d805107542c44084c0500c20820b800105c074000d03009100082c40c2904260b540c81103132180c0d0743c43c054004007500214409a403103030344441d8110266409910001e2010b4402400104001c0001030107011840d45030340a04a1031620540e005183d421000c401c4600905404401e14802c8103003001c002401c0c0194014a9061034900f80700c480d03201c0307680000741042120b01070b404c90754a0781148014860790022818140d406e290030701d40d08250000b2401050700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 172308408 1250 172307158 172307167
    0x1f02120c0d020c060a02031204020a030b0c0d150e01050105030601030603081917062101060b070f0b13020f0d03030204091b0f0306050112050a0b030a0b070212030108120309030c0102 80
    0x1100c00100101520019000c503803c10490340d040040302d0250541c0080142d2041214101d070103800507001e42c0051029200c03042003a26995a0b070081101100c5540040d0804242c441080ca0b482c0201c12114a40c90184401642000c254950709041401814140300b400008241036074840e034061030045810000c442d03200c444d07681040c5030201031140510001600c1c0c3d00941c044188401c005030040c07500601c05d801c600ca8440c41089500a2246010a103560714580040e11074100d00040520a03c20400022200464030f00034611076005082c608a8503040d05074040143c070b034625144071150044841c40c40400407450100c0207485550441c801c814244070201401c005d01c11109191210369440f218070108070303c50101c0803144644506400242c018096a069050315071141c0c0d0401b82c0244c000c24030f00c01200100b440c1510035081180e0288103c000c01084650611070a0244102001914590351400d01003a640e08a225020f11045000101250300c0e5203040007180c4442d02c1040c000d5448 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 172309658 1250 172308408 172308427
    0xd0504030e030c0402180108130c0305010c1119020909010b1203030402010f0503091906112b060302132403031106010909030f0c0201020705040e03091203091f0212 72
    0x42546148014003038491081451038520f445d0080d5917160429030740c1110281c15900044038461005450345406400d0810503e01207492082000702070b45c0200c0010417041c070490402004214400c0c10900d244e006a05032800c80d5580f00760b0040070580488a10805498a428045c010b00700c0b007150541c040c1c4180301e03548083c0404405184158000d0301c810b030b2600110710080d41e00b48000c42e515000d6030000091101a00c42400115517014014800059054104811807005502c45282d200c680c0c171042c1800891542d44247c0c10300321150007402071002c54616800708807100804078460304099104d070500c010b103400c0e4285e95a96620480d14400c0c0d91603490030701806a090071001d02099000356400440c190405010b00c020035603056a4000545586170070444000d081701f03070103e04600440c000003d0a0f42c844c02081d03078040d0b240010f150383d81482c5040084042e040340038046190014081e050b50350341c60ad005010f4011124041e051680c58000c805c0f03080c801e001c0080c1c5401c00b07010600350f0b00e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 172310908 1250 172309658 172309667
    0x14161506090e1603120f0215010801050405100209010f12020f040e0f07170403210f14060406140915040f0903030c3011040603020a080f010806010302060f0d050403 72
    0x340c1401e0025a83c3c0c1d40c5000200c0304404500d40005802803084007460446039120b6200722803445001d00c103a0315849100010107071785082c2a44110020b0307454071700380000d0044c103004151005041400c114a03228030000080d1100c004081c1010a000042c100088100c140b40c04842080d02ca00c103205a645440760f607200e003001c40c242e031400c1840b80740000283c0014014480c0200300258414242815070b603d5408032084425000c0701003410110310350b54000100c80d8022030071840319070680481d0310703003030380f07a045884180003407000e071007903040890030408040307601c00e2000c81000070b031152000c81c0e0781c1c2541d64581840c0d000c0701a80240c502030144e5800912076100800702c1d44255424003030095403080484505614481c00f51b001e5400e02512801e086498000010f8003607420f4000c680c1c190f00e840b6501046c0c00c19030107200840e400050006000c5c0e84060010303442180410900e40310350500041ba99101c0d8140030007406100c1c0062454513184000c010b468a026a8090600107807800b890002c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 172312158 1250 172310908 172310921
    0x15030608120a03020c01111e0a05040b0c0a060e0607020111040e0103020d0f08030a0f05060f09070509010306080313060e03030a1b03030617010e010e0a111903020612090705011416150609 82
    0x49440c940c1d26207a07040040808c1143c090700416907801c2d08103824010360301602e50020741c0001103446004d00040c00039509014648003101207002400c1d441c0303170000c1301030f094800441c4c03100c03025001040213004010b1400080e50660b07806865462000c0312601c1d0020406402040151500c4000303c2080303000b403482c3d04801d0150b0180802403007591140d04c00e0180070081445415405000329002640c0c943c0300380302030660319005240120700990385441d43e03030469000c602d04c0e290101040e42c0900c20190044011800440700380c0081d03243c4a041c0c800103140401040c0190041000e1400036024144a83c21250250040c101520300b104500640d01d070003001300c0d0500c03031070550a01d61070300303003615010942c2c407551034110040740745011050017080725000c9101e0202800c0f0000202c0400961a0070000e0140c6a0040305501010b04040351001d1614041e540010b0400c1800101202215410ba041c7c0e89004c1a1103176964500d951440c100c20310640d10050b03c0c003c1c41c42c00c000002c903001c0580048 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 172313408 1250 172312158 172312177
    0x108030406120b01021f0b130b0901060c0b071d040c0e03010c26101d041a04030c0813051c02041103010f0509090a02031615030608120a03020c0111 65
    0x36190341c0b0303001c0e980300140c0300000401400f607080f0038400c000d21042c1342900304107600c508800044509500d00081d9828412143d0303039001c103503100d5100700d140c10441c05807409464a8280541c0780500b40c0d0f242e00d46080018000307000c0168075907050004581065040d15114001401803203a540c840c0c4000340854038640b1800e11a60038910b07441c54403401400001c20900c10b200003961110315940b00c90000707040103041f21600045a1030001050a51038450641c22110a100ea44460900d400d24210700c82601e034004540f60105800e0000180e08411141c9030035520004050b102c01c0203400c20a00c0b8a00c99010a4101040a0501c821400242407038202c15100300c0781080f100409040c6040107000034002d0b6066070b0300010041c0a985041c4440390390040201003140e6980100d035022a040100304091450040d50480040c04000030013103901c1d29070a018074041180c14a044c2c2d00c1981c4600e00840034917000c8000483c02c1045110340c04036100c0c002e586000f84548120b00515000550105048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 172314658 1250 172313408 172313417
    0x50c011d011b0e060915040b030912090120010902130c090f05060a050c070306090501050406050901021908060105091e03210304060b04140a0903120c21020f030108030406 75
    0x10103021038441e10b5002c680d0030090703031000c40410031541404255031000001075808240500c0b882461a80e200040001d0520380d4086034407401c0c203003601c40c036000070a4200000002c085c442e40b0501d90344a40e500030442280d00302200500c104003845801000b00003006500010300c2183c00003510090740103518044090380d1203200c01035440420f00780038800e0b0f01a041d4419010081c8400c440c0c80348001e1f0038420028004d44441640e40e030390310411108819002c5036a039441d90300700300078403603c1d00c1002d80c01142800250b103072481501200821881648000b01840f01e080089000d0341d200b2070a40d0801100903003a500041e00b0031703509009a01101845a103e481884554005600580c4a50726510050040d00d070960f00c3d980e4a03400a0407140710381d19001a81c0e81c802c07241a0111924190040c04540da00280c1644d031410000d2440f005100100500c508006411020507802000d0304042c080c0b0b044621070446a40201341e0181c41b403c54180c00100c804030001c43c011b81c3c003200030802c031402e40e00c8c0d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 172315908 1250 172314658 172314671
    0x20304200a0b07230f0705090a020313060c0504090c05070c06020706050304060506010e130507080106030b0a060305130609030f0e01021f0e280b09010e031603050c011d01 75
    0x1c0100000c0d0300e0044502c010401d00070800007034100c0040d8503080e240c0604010f851452101803901d800c0c401440514540d12806d41044035045c0b00c054260807102080c0294075514001254500c611000d54005041503078842c2c034001202d1041d0103030350150030300520900103c940407100604a4101640596a1803031200000695600005e10740d0201c3c0c900e80c50380e0b401c583d07954541c4802800020052414000d100381d5010990f66035003030600a84010007400070702030a0046c801401444141c01c098203261800060780714070b650380308141003114038515001c02c060341c43c0150860000c4402600814460a0036000d01c201500804e8000d4429200e658200c1c1407490a40126582c19400880480e6400031058480c0c0f001129080300c0310007455107040350911a20140d078041084682d070813805104140340c1c11242004022820941c008803001c0007402440d041d0410b441d160321a5174002d120560b0a141440308150080c0107690444038200000c109106664058a000120050010001d5480d10340d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 172317158 1250 172315908 172315973
    0xa0f080709060503060705131e060206060111190503070f060203160305040c050d050a02120319030207110603071b11010807080702070308030c0715060f08030315090a020409020304 79
    0x2c038a008442c0018010a099110850f050319a68440c0741c80300c04e0001110b6002c1a904140c1075142501d15525030745445503403130130800a0a02e400584005e04100503c442c1107000f80b40003a1410a00408261032460400b1510340145503101d030410040688400383c4500e000c1c0107003940554840d01c01644c2c900121400f80300102c0c01c980003210000d08070108840244920300f00710611824242c8100c00b15002c1000b25000a0701d005640900c41985074000103002142c0c0c0c030002000c491200007406e0640c1040e5595a030b0442c8880081300304c501808011000a03002c83c425a4070a0139120140400e0590380300b1814182c1101d00d194074041d010544940c0414201441214003a01c10403069000d42540390841c0d4070040703076070f1000d401e1280c600000d00001d004282410340851400e5100c41000038181d103891920204060745038021400c43c1c0080c810400e01004642940301090802c6130b00d00110366402151030000e010780d400800d14244040b0401c41008403541c412410000281031141c610000d41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 172318408 1250 172317158 172317161
    0x3011413080703050c01020d0605040c0903030203041518080105160512040605060f0a080f160605040905060a030609050312010b130303210908190201060e04080d0b0a0f080709 77
    0x95450109000900510101003070355100581407991107032400740c3ca4065035480450036a000b00884510b00c40d0b40e000f08002502c2c0030310424180810504000003c04c0c959100a92a8000e070f02c6102d03250500c91700001d40180c402c0740711a04200d01c500d0250842900c400c601e600a100803295141c410b0071600b09103290501401c00d85501c44032100841d42241d480340d031504041e00d0702400c0c0b1600007207204c41c8504590354030030841c030280400c18010a001061000c01d9031a11140314502d0300040c040110921000f588501120196141d10301d01140390780382c400100d56103c03056130001d02030034545081c14080100c00700081c00d0b082c400c080107030302d20b980352110074074a4071801e1480c071124103000c102000024041c8165626000d002d441c40305c034020f14a078450041d240c10120450700104001003118020744540041038040c00c07544002c1003003600b4100b07d007a03203200142c4040c025160100300604c10010540140c1d08694000e0043d4041990b1041c02986c416054014001a4003450a0129070074421f0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 172319658 1250 172318408 172318411
    0x21050709021c02070f080f070501060b0c0606090702160b0316020f0c0f060903070b070b0703021303030e030a1202060a0e03131a0c0105010305030d0c110d03050c1b0c030114 76
    0x10503181e0100300304140301602c003e43c04103d00303e44210900007028040f0f03c0c8400504445107021141d1581d42041c0c1c0707012400c40c0c402d330b0070142e00e10209101000916500068182d070107103041c2e8111038192214201603285c5a11480304030011030300c85a000c5032201c2200c0285024000d84404460544400c21040c0d8940b045114910000e9014000703100982c82e268007003080b007000140c0500c0c5030046c4040440d003402c00d50340040c0b1070700d640001c060041210144175298800c1c0e40d0301e401c40c14103101c081d4240d41860b40d031002a08001407020002074a980521074141e109500400c5040400d03604a80030b0344495040742c0b440b802e94078107071421038482c1000c4120b4414009a09146454506000a41c02c40c503480001c455032403017052110040282091103414040c1d4000d000440d2110490280c01003540c031174540c607034204464104200e004c00d41c006030751085000c1c203040c04181d0f560b0325004a00341d0700417070741d003800c00000205100094a4000c140581500001e600034004806c80c040848600c400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 172320908 1250 172319658 172319677
    0x3040302090f040b0a200c0601062006010302010f03020c06180601151215180515150304022b0c1a0c1b0103060b030f060406090509100b0a2105070902 66
    0xf83c440c00100d0b00307806540032203c1da084003402e400402d0000e406c0303105160042d502c1d820159200078018013a268000d0b0410140481106000e100d95100d20340c034585501040c4802418080b075a04880c0110f800f0b6019101010020800c440052610140001c3d400b0f2080e4161903039406140004189002190003911107404c098895210102400c2c9503100100485100300c131a828405030081542c900985000e00409043c00c4007003200c1c245002145c2800b109444240c0c030074201d9022110b000d072a0041566403081c1c044a010000c90926003840705007681c94492000030b80314101030701041011200f0520141e810034600e941d02c81d403d480c4050864420072440c48100d0740b0007141c60710f0700c200209800c26815410300d00841c015036180c1803258603801c01d848244603c0b40f101b0801c0720130f00b880d100f51390040030a03540900850518090303041c2c41d102a01c1d4034003805901c070744c407104080c0c0b1040c0c001d000412450f0f0040240c088040140130036031440e03803002c03603103030044140010340304240380280d814944 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 172322158 1250 172320908 172320923
    0x60e0c0105180a032f0102010b010e0103180507121a04050a230105160f0206010e13110a03060b090a06150503091606020d020f060c18031e03040302090f04 68
    0x80c0c50b00034816152410010309680007050040202c006000c1c465000c0c0c4118000d400e541c02c02041c403001e904004003940c0c0682c110381c0360420001c0b1a0b80d101c000a0031500c0b0a01307001a4101c52441c5480000c0c9101c00050183c0c4110070300020031b038007152900c03001d4a025070448205012800d01d04000000165400303007007907000040200106072062910f50701e40480d4003507000d0031b0045502a5094440495494000c00504e0a18403020b90b007041141034400c003a40b002d082e180d030610103001d0b40c0c41e80c0545401030607042c03100e1450800c99000b440910040c8010440d10040c0c0d5285401c2e0040c28810384001c0c0106100e00c04103031000340500502d810740301d6814003a480040390707a104a89607000180700342c250384121500d200c20051040e0340000604020fa01402d208242d500b8044d00c3d00101c645900c07602e43c0440100032080000034190345543d0101d0010410100044002074a803190300f0baa00745c40c0441c1d000c01d5808440b0000000c6c801c41e842030314840c010f40c0d14000905010710049902a1910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 172323408 1250 172322158 172322167
    0xa02120c0303041205130e10050405040b0f07030204050d120311030c160804050405101e080304030807061b0302030f01141008100803070506040606140a0e06011416060e0c0105 77
    0x80c041965004c03004c003091a200341480b000503c0000550100ea0055200c03408403400e000501900f40000d40c00741500340c4060013903040a0381c1d10800d03c04010041c41c40d1144400101e88000d1103a0112001020020f2188256842500788501600541c0c1440750110303103070108020b44e00c5218010745e0701c0340d0203442441d8180f081220f410a0400701950003110403a000301300209040d92544920307130041716800741d072007821400c00390214884401216080345007150500c00f0441c45000000701d5060b07035801184e0b69154002d0b894038001400d07600a02400701107440442042035945580070f148694495800681d15981e0380c440042102180e40e41150040714140d15110800c0c002c95410340c0103801c141c0552a06682d800941d400c54000e104125510742084041c4024413100c6e00455010b402d441d241d10005c40d10410000d502c1500a108070380344c0341064400280c50745c0c014403000805a0654910680d02c2508441d09515804c01e08401c2752421302c0d0425414409400165110110742c0c1030b12003034030b407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 172324658 1250 172323408 172323413
    0x503010504240b0901090e0114030c0405012601020706020a120c0513060e030709060602011418030301051908060a02071a060a0b160210030e06071b1e060c02030a02120c030304 77
    0x3d03a0103d10b00364184411050002810450044060300818603a94642501c0c0700180405043c0745070744144038030680c20400107000d60445107403040d09c2e004420080107200c100c80145a40607000340ca001400c0140301040780c0c4c3e039003070300440d503485c6200042804000b2000895015140c174090a052615600070098050004074000c080e600c250150040c00c40351038a80e1000110107a40c007139080301d00140d4450381c03059864541080c0c3d440d0090744006c01c59809424070603845a49001c14845c091003101500220038461001c40c0c1c24001a1110340d0558074030b40f5001e040d81d0065400703081d08840070614294004c05012031341000303500a200052001401d80d2420b1610307007041e0440498a6000001000c02c840165980d030344541d810141070f1000300d11802c2e03c0080c1c9040240041108051080c01013490300b596503a400da5615041d407003110010b9003c102d0080c04600c42171024020051441e04c000d2701051500003001e071088407125803c5819a0800702540111802007441da803185620600c0804c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 172325908 1250 172324658 172324679
    0x609030b130501020c070603150b0405090c03062b0b0703020a0807120f151d070c0308270105010e09030918070c02090c03010305011406180702030f0703050301050424 73
    0x314038000e02c00907042c00260052a03003170007615807204022a82e112455205000f5803101e04005041000c2d00d07c0c10149800082441041c0c01041c8002c00400000000c0d159644c44e0002416640091444449504103240001841c1440401521041d0301000001c44461080c000c6030102c0010384c0c0c61195076241c5c2403003554030910b40034200e15042d0b01d80e00c00f41c01c03110444c442c003152184802103a05220b031801d4654215200300703143d9090032142c46402c1218440d0019000c403150b0f6803500d030990703055442c50112115510740a0911050a064104003451a141500481d040c0c1d0f520000215240e10380009895507403090014068014001d030100b10074404052942662240450501503450315669000803071411048807040c0d40c00d0b0000c80140b0031b10000344500074030601100ca417448282018400146020100300c10040707064044000206042d2092040d6903240d40180c952030307100e1401d46000f800d036400034000e8501a5180010062003885c0038090500302808071580d0b03040403070078041002c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 172327158 1250 172325908 172325941
    0x2e231e0109080d030207020f0105030c03040f11040501030503090307052b05070503070602070306050601050703140901120e03040e0f04020a06050a05071718120606010c02120105040609020a0609030b 87
    0x3418004021400548500140a00350b00c80340656401039072070006204202854280c0344105041103800d10801c440c0c89440c0044a8000d40c02165a64103e0706601e031040c5030030768002071541c11030300b04800042040030000c0a8001031100314140c2d24615110001c3c400c0c0e003400d485560318203080c0c07040c0200c0740c0c2c1a010ba15001c0300d4061810380c0e00c0035468001291512080b68416001070f4000b0108005212040c4191074210500b441d100f850000c058a000f0004c1c060803a461509807000520360682d603004004184901c00e103400d09005e004007101d1000d4132504144a0034910788001c07000038041c4c0744481301d403a2290b0b40c0200f106800303500b0703c1801c4405800800c800018890300f00800c5006c503420310981c0680c2a000d280729940c0b000c542d21415081d121a207400c0c0d000d4224031120b0034580502090181e4812002c2c070701800002c465000046042492a880d051a5481c090a10082c00f49a41000000038000d8480c1031a5595a00c0121440451403201401c005031080204001c06040ca405a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 172328408 1250 172327158 172327219
    0xf0f040b06090a0e010305100c09050f0d06050a0e0c061c0b0d08040306020403062d020c01060e040503030f1303050301060305100320130b030c092e23 66
    0x241c02c100d01003010412090040d0007034100300340c040c401002080010800a0b00c038440051044c420031500e444080c0c0018601e0144a01c610f0f00000e0303100060301c4501c110001e1a410140500c42d0781020b4030071400501c2d0740b0340c100402d80140d49454081c2e0500c9022900600100c6800d034604103020750740d240c01000210586980011072122910104601002900c0998045c140050f0f803180385103050402c072540f004200c40b0b00480403070341100d00040c4103c280c12103615a8009640c50364500000c50052040d1741121405100359000d00c428401d0000246214080340c10800b00552a0011a618460303014440100094000c1006128041c400c0d0041500041102c5110a0349a201d503580c981c4036204007150050200a05200015440c000c2881c81710400419000c110101c1e00001080c4c07502d2107483e0300c0d40030f40d480b00b004c01c0c903802c80320b11021260070032142c2e00c401007103007008818504036843c80b9400300707524003041e860b1482d840a41c288044001c02042e0700004003110b1210407007481120b840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 172329658 1250 172328408 172328419
    0xf070e0a0b27120d03150506030a05090c0a030c1e05090112111c020102010b060c0703030503090f030a050309011a0d030e0f090a09021f1704060e010f060302040b0f0f040b 75
    0x520b9241c642292581e4120000c03800b400d40c0e43c8001c0c030000c00311103542800f2000117500e96000c00640e1110400c9036000200703068042603980c2e50700f038160303c4c02080d0159223404c410079440002c144035100c1603a400f500e54208200c1d80081d920491014109500c0c00b81c03c4d405a440c0004010344240146585605449030100691003c681400900e0541080c00d00d81900405443c8480440d039080c070919491060842e040f50030501e104030019600c08c89800020284400040801c0c4070310020440f03400d03c5009001200d070350703d144400003055608280c031996030960a044c0e0b40548408900305603000c0d4003010f03055181c6640d043d1000c44040c070003c4481608118081c42010160300c48010040c418200034071302050070034482c410301025081c80e0b0591907800100c2c2080b0024141d000000b040c034244c074400c0e43c0b60652101d04009004081840d6500300961038504840c80149041e0080011207008680800a440b002d1080c45500340301849016840000c0c60440e044c3d906d410b80c414009010054074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 172330908 1250 172329658 172329727
    0x11502070f0e090f06090303060105090102010b060f0a08070503040809091e011509060c080d0504140a1203231b0409050114091303140f120f070e0a0b 66
    0x160340103040264101c0c0b07200040210400c03044000400601c0800c1e80b91900421540c43d1880085450340400ba0145040141c0050211190382c801d400041050307000810240c1d60b8164030808141550045040401140084000504450066056a203d107030001065480c03c460b1504000340c6620003032280c0c4040b4041881c02c2e0712601e001d511580a46000300d1110000e0f210300d0000740c00c91f034003a072190042103401c1e0b540c40c000483c00016161820103402e8003061700c0c0ca66142c8a0001540c40241078a580301c0c040000090001001403d0450350003500d04100040c01030314040e200c503000004440d0074040c00b82c08103a420301464104070907030740c0e81c1c0184d41c246500d58000d0015283d082e1701403080000344c14403542003450402c86403500710349441da54229014080d9405840c0d8105800401109100400c2d1031315040440b504841034807401520105151508000c00146070707005840200004a20220320303c0c4a017000030043c8240e0307080c40100c605106e5000e601c805c40300034455004041d80d10040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 172332158 1250 172330908 172330919
    0x112020f03090a2d0609020307051207050f100507120e0d0c1a07050a03140d060305060414120d050c070c0605120f0402090402010318020306011205060c03090601150207 74
    0x30041c6004103984409005280e500e410154540c24414071044105081004030012035500044103094040d4007150204001034503000190030f0014030350225410141e40c02440c8c5ca181c5d0301140c044e003074500407286219061100070a02024014018035400032920801035500821807851142c03032008103615005044454450215402200700b01044035230a82d102030a00c07400c101d82c00d00c91008015802c01505101e440d0700c0c2c03259111034030341000c0c1c1032000011500782c00300b0ba40000ca50380e1401850080c49603965910b0090b40e0f40c01c003242c0a0390a0216121150140d0102003082e03410001144422424128001c03502001008050940c00d6200c1003041003000180401410740300405440d2a019103410040c0407400c1308040081c20400808115410080185d45007040c46411a40a180c00a408203111016115081b48803001070b41c1440b039034000181c003c400341d0503a61210710901c107656150300c806031144064001514482001d030001c0d40144118000c0382000360000c00369204485c4000e0340c03003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 172333408 1250 172332158 172332187
    0x60d1103030409020d0b040c0504050d05191a150901051009080d0f0f020d02100209042d0b010c050c01050306030718020304110906010e1323090f0a11011202 69
    0x280d10540343d40360081080b0220b203000b0321402c06814002e0b01c0a0104d0703101d0305001007162081d401440d11450000084009014003084144083c604806c840000d80046042040c225681401d0706244030705c00c60300040700c14011800c0b910141e80c01600c0200c00d6401c000420080a0780403020100300862603000103200c078170801001009558981b01d0303c4112a52083c018000403d0301c3c40c0d0820f56011013002c411540c0d0000d01d548840d40342000047e00c1b808088001800360030b142d803103004030303010103081d81c120031202c11070400107800880f10404c9104d501800540c0c0a401c0d001c000340030b0b50005560006654029070045a01950050654014907103c2404480050003c5280a0365a90100030071082295050110b024a04111804045031070048002400c0a500b000d08600402420000810b0401307103404c005000e02c4a20040b899082101000200402c0c2c220744102c901d100742e82000000b034801107411700401d82c10001001c2d003480000015601e420114000c017400b80d07400c004189030034044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 172334658 1250 172333408 172333417
    0x61002030c060406020706060b070803041e020607031106070e030c062a0a0308013c1503020702150301030c06080907090501061701090c050715110f070b0717060d110303 74
    0x6040040c0c80d01107605000048600a81141c140c401c0100401d03008181450140c379400360341b1400c02c054428000301c401c1e59142d103822000b034008001013440000c15400109600d8a500c80e0300440c0e549075035108007110901d44480d202d50b0190800c100c00740040c2000c0004080242c001c50000380311186149034420240c1c51490046d4440d00300c41c03542802c1590185456004240ca0341107231480510862b101e030740341c070040c0182e59555032060400301a00d00782800024000c0c9911501000e9000b07189002601a51101108030320840d5454580443c1083c84001d985c1a0f03504680c0f201c1c0c829003801001d41c1ea03190f010384004c03081c2c8644180060450002d001d5103001c1c0003107544180c0c0340910070322125a500301c180c0040c04902d0800c003107410110382c04819600d400e50001c10b912420840c081041004210301d00403140741000001c1d1100c2141000001454500e20413000c1c0f100c10f0342c078180202d40c8408140d1510030140a0840810701320700d007011001c3c060354000c408001004001c240041e00e542e10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 172335908 1250 172334658 172334663
    0x1106030c03090d080f01050f01020a02030105090c130c081315091202010b0d110613090c090602120301030203071206020d0504030e0307050a0506030711030409050106030b1201090b061002030c0604 86
    0x4006604500f88a181c020001e203081109881c140340540c3c01040105000d03480c0036014014000003185c3c400c1121021058001d8001c000d00c0c01d1a02d11140c6072644015400e00600c50400c00c0401c610b0780348104404a0641e94a804d2031351078448051645400c04e0354203a500e42c000d02225110340d03050380306064005205156111041d017204101a003511248444144240c0c1941000e402207003800c1c60f11103110706d0440d400c5580b142c1148145400c3c0f1056000030750300e54079021400300d00941245144c01900c41540840300c0342035664140d0351040c032007404020f4154001c910200403d485100d1202c008510409001d8180082e026001089500840c0c040d030000f501031480000c01d060902c591409017002b0b81e861440a03041c200450200e20001d00501c080190359002c1002d110024001e81d0043e18615100717214030b503581c520083c041c0c5440899030384249900310140715a01307814451081d40c0d50f48000d20580302da48100400c03203039244900c0d2038020740c00b00300b0440c2c501c1141030000620484c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 172337158 1250 172335908 172335931
    0x921030601030b010513050103020a03091b0311030a2609060a030506010908010204032402090307031103060114030a060b01050405180103060507140d090611030f07020f12070609110603 81
    0x18200000500341d803062103507241401000c000000150110303546c843c042d503c00382005a41c03076502c4901100144420b480c080c01c044d9140f030690b10b58490355160b03070049070700802d02c40d00d0800045003055140c110090008040800035455041a0104101e81080c1841240d0f1039909014940300401c666600c00000030000036910740410455603080000c2e030000e025800021401c0c9402c595030103220481d00f91614405541c17055007840e100ca034030b40444282903005401d0b1011030390780b803802d24440e000d0385100b10310a00444001040d00e0104118445030340c030340180102031590315600c030840184a13005c0b40e00e04001d030401011481d5142c1801020040e01e802501c03110640c55418007104840000e0f002c2400c0002801c0f41c00940403003c401e40b03250764071940340003580d40024078054001301301c41750015685101c080100402d0022168006120b041d442c0c0a80c1c950802c0075001c0350301d07840c2d1a6800f192004c418025000465029400710780810b21a2401740510710b01d00001401942003100c031401d400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 172338408 1250 172337158 172337161
    0xc090e0a0b0102061b1e0f2701170f07020a060e0309030f0105040b240307031110030905030d02070c2d06020a020f092d16020f0d08092103 61
    0x3941c1c100111580a10500e171000381050006007800014859001c4641e0b0041c2440848088004031308100c6400d5155589042d41d0f0380c07000c0c0070946600f00c010a00c48c0c20061420031031151540030b5000c070240d03500c0c440408042e5a486500c00f140d9408042c2c0307544c0451060340c8598000905030710075000b0b0112603000968452805004242ca04400402161100d0341000b05110001b0341c81c40b40150800d5900c01c240d440383c1480c07501e0201c2140d80b0301c2c0c41681403054500010610074000d10a0041907415a40b560100c56031703110036030a5a05001d4000e065510400101174203212960103080110310410340e41d1410303661500001c0400089005800c4030120072110980090707100d4441600424150015062503000c94000620103030140d00210301035004440041d00e0100ca0302c0514105403140c0d401c2250011020003810b81c503080448095205060702005c466080d07000042c070a07100000c40e0010445013050301c1c0103c074007c90180c03007204c80f8852104074102c00c80da1004441c0c01d0300c010486890f101d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 172339658 1250 172338408 172338431
    0x607030614010c050318061303032a2013320f060f0609060a080103020306010503190f0317010315110301031509020609040204030b1008010c0807030c090e0a 69
    0x54652407605050002c4002d00c0c60000d4400300c2950480b54003500f40410b42461403000c02d801e44100c519070340f5032202d411b00c003008054020780101c0013600c0c0114441c01c00349011039080c250504800c1d02820b800251003c140ba215081c400443c0900c0e00500120102124100b215050329208001480e40e0034a1309540b8031800701c20389032030a8510b99461031500c035040c441075007103a581021b45042c1c080c2c50354490001c01c94684908980060340040d00312940c0321300001d00109080c3c020301049109028480002400b4a800600010b0007501705449242101d99a6129a200000c602c000c41c14401096264103d45844808a50003036001e92543c100c2207608070160821030b014010004003a0400b400140f01041d030f0050305035880107080c200000e80e01e92a0000901c2c60084416159205000080100801401654aa00454541300c49a8070307152074008240c2130311060303601400010017840004424510a8018108420300f6041681c1c0403038440002c020794007012180448031036107030080102e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 172340908 1250 172339658 172339679
    0x417041d060307240201021312022103180d0206120907060207060519110303070908010b09010e1306020d0f02071101081b0a0504050a030308190e0718090506070306 72
    0x14040c200b00d01600c1e045003049113207601001154035481520010400b600205030003507040742d421404903c04e015403260380b1504c00d10040b000c904203e00610400c0030701c002d40c84051180c544104841e002944c1001103615801c06114030750620b195002284414440c00b5072035080084c203042c04400c00e14885464450401490309400b42c1c041421548105400c0100c80e030300c80d060700d0320400040600941c9454040b000c903114603002e941e810060000200b8004c1c10341d000132180b012560901d000380000b00180f810824140c100740b141d04882002c030740c0012175015803070404800321482010300509040000d6212400c030740143c60600602c80e4000740410034000102c4251070319520900e2304400524110110302d0080d0314075188260707200c4002c94205501405001075030050140501840021a03490400600005058900207400c8032940fa0241580c0c0386401080e0121500038000c105061920401c804010100e100c0118061364580c032480015906008060042c03036140e50100d1410f0805040c3d02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 172342158 1250 172340908 172340911
    0x2030103031d060a051606051f08010b060f070503040317090a0909050a0b09073c38071101030501140904060908090303040312030b0604030503030f0417041d 69
    0x4998100c005840103541c0f41011591002c14900c0c010740c031911402e0b00101c0d000503041004205c1d07414041000a03075041416446003004082e269401060790310440b081c01c07075109042c100d81006e010007802e46a10603000c01000c580b0f01c20740c11a45002e50301e441d0300c15004500b01900d0700c3c180c8005429402441c04045410150a05400401c0822441d50b126943c0e055804401450143c8100000300b0410b030600805008103c00140c0804007600d44110026008503c0b698560075809040013a800c070303c00c00c0c070b010241c4202000b80f200e1481491100e0080d90b154000c02c22003030740c40e4204a0001e524240c00303401c4072407260303807800100a8004005816140160451901800f1f104035607a0b0075034401ca1a150000c3e04410002200917560074220890720403541199090b1000140001c2000300c418280203c200c0740c2e90302080b88da4080020090070348143e01c400707400ca074820303c003040030180f95900c010f8000e407041c00206208030704111020210b03085640805042c082e580c8c1d10103d0b0b00c0440344d80d00e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 172343408 1250 172342158 172342187
    0xe0307032315090d0f0806040b0a08030a03020c0105091f1a0a03060914031c02031302041104030b0105100518042a02010f02070506040b0408070209040f1208010305070506070602090409060203010303 87
    0x6030966110045e0003401c110000344268407031522540c41c0102034880c084108068400d01043da661101e00010241c0139520050b1003d81941c80e20380010b00a01c80410800c00780b05160315644940141d540154000d0b0002c444030041003c004101e48106a5641008100441c0f0a1402044044542c2442c01c404c520420344c14030240c04c2080901040c0c00215070080b8840c490441c0103850352510301f03441610386100038000303411030310301043c00001c141c2c0c180c041e1003281c0c404c40036581e05a032682e0034400350444090150002c0384052140e13068294905006590292001e800001c00384410b81121001c0129011207100c090145030030015032660a0050314800d0710320070420752810441d90364507580e842c0028805005800580d01040c200211401111031542d0007e001500500b42420005d80c5000030180440d840c043e00325401c80e0300c1d409060254103d941150142c80001c1c07034241844802da20246046540b030b81c1c00c00c14a60325944a1141c804214082d09006071a50304518000d0820b84e04103880 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 172344658 1250 172343408 172343417
    0x71b0b01150305011520010501030c2306070b060103090c091b08010302060904200408070e06010e0a091a06070b070311120a09020f09070e030c010e0307032315090d 72
    0x10701c0518180e41544c0d0341141c10f460041c40c2c00c0c6d810340c0303814210107031080d0401c1d055082c41c0001080c40b2800110760181d991500b910a10300100f060240400c4001d20040c41d041502401002c02040f40c0c6110742e507011030103050200d61118a90b41d0b46d0101c0700c00c4d4100c089165a900c070103040c2070074000407074450840e00d810207185a5055800180140c0030304aa0b9a03c01c0340c46512280d44040301105041d61408548461915503440c0c10360591514000e00406100340c812000183c001c0d88180011107010b02c021744610346450810041c04050302c4550201c80d140d02e900e1181c0400c40d10340000400306c10340103d0322131030396007440b800c020107a6841d41139561204900b40022089444a0340d8950780000d20181d0024500c5e107a440440c802c520118001c540c4040840100f081403900800803002200c802c030151003a11001a006442c80ba2583d41c00d160198040d41e41480041c0110000200d90614807003c00600304660200c14901200c008039510310305240018000166001c111040c000d0466040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 172345908 1250 172344658 172344661
    0x110a03120207060b06070501021c020909060f03120706091e050d0809010908040602010203060405010603050907290a02070f0602060103120c02150c0c090f0717071b0b01150305 77
    0x40051055400e11034803011107a0000b030303540030404158400c0200b903902404c00c41d02c0700350758286107000b5004030f03400b61a9108103851210308400300d0701c203d42141c07030000d24094194030b0f28000d02c0b100e4a440d0003040d406128100103143d05103403030805000568410301000c90940003038580b54000308a0400c80840701d202a08044001800100c0e00012002851602c00501d664540e825805000c040c1c2000e070103c00001804199030381e040d00114420281500c081c000741c1d80c0c503207045080300d8086840c030320140c101c3c40080c092a666110250340348140b8012407001c11012840c3c40c0342e25484042d402c030142c0d21508040144051031a0380718014034090010701115803441c4c407881c0d03c00040450724410008648940d40c21036440031030141c0e404205119168480440c800e220f0390303600001c001c0601c6010642d00003002d420b00c43c005980f11b0f290030390740d21460044a0b480080c10f10b034041d01d40c5081c406401d042d070403640e030301d82c020400b440e01418101e00da951500300d9980383e5034900712495040605090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 172347158 1250 172345908 172345913
    0x60f04050f06091507060605090708090c031f020a090506040b0406021e03071103030c0105040303020a031a150a050c0303090a06050c0a0903080913150302030c01180e04140a03030507110a 82
    0x503015a0440071011107171351905a494410010038040c0c0040e0340c00054501444451681b04803a00e114540e60300c11540a012000c04055a030341012702171442d140100d485141c03000ca4541c0142c01001c0850500c10416900c4800154886c1c0003608012440d01001ca4200000f69040086540b96034030075008804154203103d0b8903840f032040880c00f40050000014200340750728208101d9101c03401403402040b03281001e1070300070080d600035003140300000d081c130495060003c4c0a420000090300700600c11040d036000c0d031110010940011f070030082404030600c640301032290705000542c454a9030001404211811346072040883d14090a52100d0740d200340721b1000f07541d4015400b001902d8222144a494421407400640c034010001d00540089007840d8440980c140101d2070441507034800c0302a154070321609001120562004907203040d4555104604018450b0350102d00c40d006406100d07031300010f4803c806090f180510b0400c003100004c2c1d8610422201d65400041c0e840010402c10241602c04401e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 172348408 1250 172347158 172347169
    0x1503030504140604081005040203121317030415020303010602150609060f13090606051809030a180905070c170f34080309010f050c0403060218060f04050f0609 70
    0x140070b400e42030824505081c5042d40c4890640e0014041d8804a400c4450946000400b0b4001075038200d00900c105280d1410001c450000e039825102d2980c101c9548070f140c43d030b1000c10041e02c50500c17000381c0070400c004291140e101e100e020500c000c580040d5641c3d4035240e002440c4c82508031564440b2103440061003080e0345c90380c4000390040070807200d081d80300c011600003822000e04802c1600f0350303500c3c22007011b041202640200c02110400c81e2140440b0510320b1132142100000c55200e0800d4008000300116103006041d180d006506283d003420034141c0310f050f245c0c1103443c103440030004150310920f01c4007040507981083c03481e1403114184034104a4041703c0303c2150300948041182414400d5401505c1500d10500e03500040b03925483d28040c0032003803d00070b80d10781c010759102c855542840e00700b00e01c00946001d00b0b4060301c0182c450a19052440e101d200c002d402c00c1552034480b05c10416600d502c0e1350b400700640000310005882c075546614080c1000300381d000702034125014034003c2c000c030007040d03459 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 172349658 1250 172348408 172348417
    0x110f030a0e060c0c1c0201020c060703171f180b0a0303050a050f0708030403050421050c01080405030c01240e0c070609050307210801060206040b0103021e0d0f0615030305 75
    0x60310300702d48034001d10320803500380340c0c0c503c000603040107044039003180e08951103152500070f030700072380a48803e0b900b000d0078002d091142c440d0240c00300b451114100c0056403c0d44085034001042c0034241265000701101c0700000c9200d0740b200b10328002c510f410b03101940f110302c10342000e840d00311102004c035855640e0250980c01a00c1c80c240a01c400071651041d400410000c07181090360006001d541c0785032a19001d005504540502c00c40c0b2039035003440039000118428940d0095401030000d02c56030241200455aa03400200101d680380001e105032003042e10b090060124013950380100000140c20464054802505a070007000d9060b046010700030403503009000c41d21010782101011582040750f0034401e00d0341c07040b108002c0c45890001180386c441c2401030464240d01d612a40c47d03503c42d03640c4101c201d9a840c000d403405400611a000100010320b0101c81c5a03a42c4450304404040700640a00020200400b10a042c0c810074410300701c000821001c3c0c80342c94101d46481180007022400e689004040b4000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 172350908 1250 172349658 172349687
    0x7080406140702092217040e1b0403080a0e03030309010522030e0402030a060503070b03191b0c0302010605041d0f1501060c0f0b180f0c060906091c03110f030a 70
    0x1200891240180d00c64044c48905c5a00200480b16407800d01090740941d6102d40708486140f4000808501e0400b0242038615002c074210b00014141402e54030b800c402a031000c0d0800081c04001d10041c151074406002440c031400e140d5000155620b07000d210010103c00d8020f2800d0a0a1030b4051000006d402074408150700c0004d803030040e05c0e60349031752000d0300400c0d0300d810495240c443d060000410800890003136104210701030f400301108003048103c8090358503000407903040e1603040810308034051040078107000380c50184c070000c030f82203035100040b608680c80c5010004009600c0102d95400702070400c5003034040c01d2004000c00c2200d9240c4582042024107000d04000c0010290480d024050001d0381c9035603241c2c0280c058691070a203140d00250010141400c020a4015141045040c42c000710340440700c004e01400e0140382c10740c3e80f803c0060680c40710803159800100280303c60322110302040e13100400c51207074482c0c0c0c0e821108414440d01c0c001000d21800010b5208101044030107900c898241000396 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 172352158 1250 172350908 172350931
    0x14100213060804050f010504120e19050d030c1203060914061012090b070c120e0906010309060603050a050a0b0f09120d0b040c030213080615090c0c030708040614070209 74
    0x84951034258141780280c0352001c407940c01d2070709000601c40d0a528241240500d9111801459020424080e4843d40b07203030001c0f40004421401c00541c10001c000c580b080b4840d18203a14201078503a44c40300340ca2482101c0e103002a0703a82340d06100c075500300d105d40c1d4041d480b80160f0324000d02e81718000843c59040345101104104614003441540d5102c1d402421420f580095881d1983c6460b50b401840003800410940700790040746079030700a050248481b402110009400391556545100c0190050500c6603011140130780d454000002094090108458240c030943c00303401c000d0070314100f11a03014000380000355007050007418414884800036145668070b4900c5c0a1036100c42028100c000201449210340d60440c0c20030031000000340d410390052a84c03400801034143c10584940805075684012102c0515000502d402d0070b2551400ea46180e503c0280e019100b4601903c0380303074190442d040414111003441c1c011605002c0583c12415400c6c41000c071032100d5007811003e0300016800341d400f80a030303900748 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 172353408 1250 172352158 172352161
    0x70c060908150c2a070824040b07030c0e090c071112031804060509090c03010c02070b070212211810080609040201110304030b190b010909050c07020904141002130608 73
    0xc0039050703000c040d51130407182950f00d900d0355540c031143c41e98062035070074003000c40100c0d070300c6003070b4400b204041d00030341e0000d080c00d0071942c900c2030540051402d001c1100602c00c003500180c5444d40c0c0d4102642c855121102d040342c84801d503141509018108070b101601c01c0641c0303403030941280800019038242900c4a81c0002c1078210042c0032600810180e004950007007118801c2064010000030304c0c005034802a4020820241f5840c0100d80b102210301525504003020450fa01c00b52601802d8158080c1c04842a680412991603d403401e0705c4004518881009000c07500032202c0340139415001c0800d07800d07210303403000c0801d11000901840009000e144116058000300e01035902c202c0e015011f00aa290880381d46948a05101d1142881141d899080d1031021400c05184a11800b440014220613100d50001500b4a82c1000142100409050511105010304000750303982c46075180c0600d00030b058125545851b009580d00346034031000d0f1192260300402c41c0d08664400c5800040484200386810602e070f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 172354658 1250 172353408 172353457
    0xf02040b2106060f3619060e010605030a05040c0b0c0f100e0d0c05010b0409060c030e010507050412050102091e01090f050312090303070c060908150c 66
    0x60010380120368005071644200d00002200c07103070254507100341d103080398002ea64400c104460104e000c24070641001c0e004120720003202d00902c402c4000c50f0361082080311005504822028040100c50b61000c250318620b81c000003501c1ea208040c041d002e50914480c01e58101840034041c0d200150484424a6031100000c3c1403001c8892504080c081894020359540c00c00c2c0f00095488804040704401c42c001e4501d14080740865208445900250380054000030482080035641c00c0008281a1030b55500c407541682c0c40d540c3c3c0c1c0300d600c40c120b124200000720707802000c030002d040f6003d960000300c560381b6007011302107043d8102003585c2c102d40101c0e01c906c07503c051901d0028060b0291869403600326528a0030400c2c00001030482d424a51006c0e8ac40d00310f42a030724a44056440071b00d200d034035010f4001041c3d144a0140c60700041c43c04074030240c1101e14281070f66a4906041225500480021305103107800d101120050015485c965206900507110341080700300805544104e00c0080070303a401003e101c101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 172355908 1250 172354658 172354661
    0x10f06050a08070e1206040501050a060b03010e06010507031b0812010608060a03021908161a0a0e131814120a021005070201060b04141003020f0d110904020a0201021c06060206040f0204 81
    0x18208885c00c10380e0400d0405142c036502819080d5014040c46041040c0802d42c0c1c00c9003400d0f81d0484905004400c802e8503508019907030743d4000f107016010420800c4030080024030701d030741c04662184510301da031b5a94910085010105a07043c2c0202e403c0210762020700c5560390782c00c0c1550301070740c1d0100ca402405481404c0c140c031400300c05030f02865590240043c0c02c05100569500c690846800c400c3c141c8000b03200d01107100c0641b1844603201c0221703200c00045845410303ca500c00407200384d01b010005420440c03456124030214507440c1124210000b040e10b00b14001c0504c48110651482080c8504100041d14082e4030758080111000c030281d078420010300594402d40001004086201e0019503403505c40c0d6115200ea80c203401218000c107607240820744a80c0c400d100b00c1e00110b440d401c415007401c0101c1042800303800001c84e195264001881880030365030312407005112a50050300010f03682c90705840840021845e0500703940c3c0c03c510303044d1300b000101e8010500d140e125900401c034034144441d5100060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 172357158 1250 172355908 172355929
    0x607050d0f180f03170301051507061517010e011a01140d060b0a020114151207030204020d0e01060f0303020d0f05043c0315180203060a05010f06050a08070e 69
    0x42e6400000500342c0c1c1d1000c01d220070380c0d000d2110341861180402029806110a01c540c0d82c110103500072400f4110480d002504805201314070208440745451401649214550408158801e610107060402002403051b500b1a48040b4002c0c49004890050710245407040340c0308a060010390005031350620618030448620966014040212507101c42c552150b60b0059010324000d9841c248100308035281070340445101300894501c1c4a0040018010302140c24115500c0c0e0400d4030489801000503652400a40140e0049500c0003520654141c1910b0940340d0540c081e030440440481c040c40401d03170104500d081507000e400c1600d002d605810046809201c0d0303030301c42603090291420809018503252407002110300a4090081c4402244580c0098207601d032200800070b00d000004086082e509401455800b080c05c910141048103540229007084421901400e009581d0b034010310803451550000302c003600d603038944542071070611900523003001e01c050108814800382c2241300b00f0710342c0d55080c0035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 172358408 1250 172357158 172357187
    0x507020c1315061e020316020f0d0b180c040e10051f080a11010216090b0402120907080613050714060c010c0906090614040504110c030304030206060405060607050d0f 73
    0x303104203030b90703c0d0010150000c0c440000c030025040d0015040715440013080c0c0d949200444840c03020320765a6400c0044818013050a6070f0454000c05082c40030600480d2028441c56001c2c400f003d190415001340d505000100d82e201c3d126030700c0c00c1c9404a1070f032030024000c20682c5011400040d1a2600c4115081d041150407281280003c28600810708002c045045143d00f80b0440c0340c010820002d02c01640c071401c1c5048590b640410900c000c012103a100d400004489002401c01031a0158440c0605410788044038400541d03440400c0411815070704102d010382c454413a05002c249101d007942d0b5140c032501e4078030030340038490b14184054206694040481c1c0e00316002d04007c10210381446070180c40904940f08035004a401c103800000d14501030b603442a84940f180060914045c1071100700b100810202e011907050450a10000750801001c20081d80958001d400810062804000700402ea80004089a004103001e102d00030000d08009000284040079041c841800031649030200d47d07000080f00103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 172359658 1250 172358408 172358441
    0x6091e0302060a030b040b09010e04060f110f130806040827221109011416080406180b07020a0e040312020316090b03042321040611010507020c13 64
    0x290004260940c1c4950041701c0309603020b20014900380200a009102407050138119042a40020300240a6620518070494000c9001032030b41942c940204041e000140852040c820001c0d20b020f5441260a02000418000c0b00921080c58230741c0d15100c2d00e020300d60b2030040444141840c120603540400c1c0a40240102a09003c5007141c200703500103260703011b800d51060003032504241240c03c506860843d40240c0e030613118800301013002000310b480e07640300040081c41c4983c1d40c40c01800040d002e000a00040a041d5902080f038020350740d21080c1582c40d03911054003010304000b02001620381000403801c890759030b400508141e4488c2416076070710b000108507070600c6100204000307980007488048002c4d446540e503503804180d250b1905001c544402d075409004070a0580d18540d91428100d1007070740b0b42e044401542d070030f2021910503100060602c080c0c105881400704050158550090140b5581c504000083c400c5007800c0001039120481604003500483c1032203c2070000c0449500700203c0d0441e40c3c0302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 172360908 1250 172359658 172359667
    0x61c110909060a051509030a02130e0f0a0f0201141606050a0b030610090e0a1202010b04051f03060f060317030403020c06070302060106120e010e0601050a050102010606091e030206 79
    0x541048540c0450955842a41a50003254490501d10074000503184007a100c130301d420740140c40f410030a070402c82c0c060f41c2c94440c240c400c400607202d801c160415044550070104140c18081c081d941042d03004007545500f60b014990880116022010800c1c00c0c81e020b00b8045041368480840000c184903810746222042c002826090230000c071a481580700c4d00d051401000b20300708003070070076450b54015108076030401d400941c14080c0c8980c907840f000030f8140c07100c21501320120641d00c103080022403191100142c0d56400030440d440c202070003801c1c0d014515140400900c0083e05150314410f19034000036201c1540e80c1181e202c040641c0e0b229001458001c2c07008010003a45446070346150b48111001c80040c010f2300c483c50f03013506190007603441c000d44c19009030486a0030034104a4044600070010032260b6116242c881503804280310314002030004c440078007225810b00050001c4241c99900171030440e89002003c10115a020704010240d0744030201803900310300c100c60600020340c0d8030382019600000004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 172362158 1250 172360908 172360931
    0xa0816121508011e0609020913020c011407080a05100b070b1504090501050103021908070303050c0a02060307020c010807051c050406020f041811130e070c0c0611011406060702061c 79
    0x244413140c500311010080c4000b54540000a069000342c0142941000040c2c105c000b080c1c81b9074000c0c0140030b055100000b40c500d50410111080305098881c0c03c0400c0c0450140504d1050034020305a12404601c0c803c1285071412641940c9446892009084ea00385200030400000304209264401c5a000f8014842d40c015402c0c0280244000c0c4001ca1095801ca29401e421640c00010b02e021a0b40381c1019007141851074500f501d02e0b0f801300600307144c54016080044d0069590001860181145600800c9298003600003d026100050304d08030500070309106a9060029220715140b000710328503404645500ca1345440c038082d0049004180201c0e1004c20085401500e0240c1c500e03081052860501409070010000e000782c0c4189000c04000e8121082c06020320003840800365001072a515086c41c1d011601e031984001c0611035005100012140c035280b0061401c01d016046912038140040300303030750820788005440c9100301c20000b0b0040c040071800300340d40360110448004030141d19130144401d02045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 172363408 1250 172362158 172362191
    0x50901111c170702070b070501060b040b0301052806030e0a171c060303020607200a20031504020f1306060e1f08060103050a020906040305030a081612150801 69
    0x901800d0002503642c11042070041001d219140035110030f801400380c45003000d425130700561000605581541d05ca213800a4942c90001c000c2004220118100d5220b505080030070003040e01e942c180107228000071001e0044002d1403410e030000c44040f410000b440300100c811444c209102c21002610301000d4a604282c50586500200342008105010944d130401e00c400311000ca075068000540160311400004400500a14000d0010101c41800c3d00180c02d81e5001c0300d242c503001400448104c3c29452a641d0484200003000244030b8044000d84600c1440084000b1030b00e03402000a40310f4002044a01100c1d20307410903100d800d0000310014015a80c403040d025104211000b03160f4040c1e03112403010104050300307109540781d031980d513620b00c60540c5a210045002c0e000240c0240b50440d803c01441d00d40303548100c001c00c000c40c40785e03024540700c0d11207000240c0b020100400700d00c40512070310358000506610007032034019030034101000540d003545401d0600040d02590441c0442d0344c642503041c060010348 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 172364658 1250 172363408 172363453
    0xa0203100e16140c0714041107030207032f06030c0c1c0e04060311040c020106080d090306110304030206040807050a0f050606040e010c0504050105091f090e07030c08060105090111 79
    0x42d888401d8507480180303051501c3d1085130b490304c045801c505410f003e43c1182c0c000c4400d619a00810115000e904c110400200784e00091088001d6441400100100101e03102d0742051029945000301280d00300010f031140a615110250784111030000c0001c0c021180801622004402d850488040603100c51401c81c400c03a0010182022424804961580e854203010311801d4950103112050952040750500000d03005e40d940703100070342d5207406022075202c0c3e0410040c45500441d40e51091400d1842c10070b0710407100300d840318442e0901c003081008082034001031410742255000144655441c1182006c90402c004000010203a00b400c2d1001c0050100018440c0c1c0292400c584c100002000180000d088402403442240482c400b8042000258042c9000e000548009070401c9d60400000400c0c0b4824002901c495010844000b400d0001c603801007000e5510200d541010001620074120103041100024030250411000040e6201c80d6441204403a860909a01c11900d1a9003036001d525602c525 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 172365908 1250 172364658 172364701
    0xd06120c050301090305090108040f061505010e040b0303090112020705191104060f1203050c060903070c080a02090f04050c1201020c24040314120a0912030b090a0203100e 75
    0xd00c40400308a5140600c100b080d8143d05850f0240b500c41503000640e0845401442070b40c20a6031000c111020450038003458079a214456801c0600fa4140070002d0a07201031030b44501e024034030300026040d00e43c80c00001c4860000090a01c040001807000f64400a4840d0807001400c5024034001020441c0c88182864000361041c4d030184841052074041c0003c5039154441c21206105500b020411140d0180c1d01e01500c1d4060300e0a1440c0c250643c110a19020013034400381541e42c000640d06080c071000d9000f8201510098003e4240c490240d00040c01080002d0142501074105001150821804101035a51040007a0074810a01242c0b50004e0003500b0003d100302d81030150740c003248202205901c01900c403106d160118611502c031520100e400c012245e520034000b03041045422003a01c04020b03010f01c41d02d440e18021a08421614080c5c202e044045c10b60802c3c141440d03001ea28a0755007980c1942e00c0402c07008016202d41e14914070a40da40207942c0160030001281c42070000e00100362180441c41007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 172367158 1250 172365908 172365923
    0x2060a06090207050d0807030207060203011203080601021501090b06090913061a031b010314150310020f180406050d03030b041406030303040f021809010203100519060c05030d0612 79
    0x5555184040592080e014000c04d01c3c0c02c01d850000d5000e01801800b0b40100d0365203001030820009540b00400c070382c02038200c01c00001040705c14104040c1d1005805074040804c0c4081d0006070000640e58280740b4044c05440c00d10340d164a90b0300c0c0030b5103408041e00c000e240d0050103001c9504140e2030b401c4420386035031800c1d40c0039400c000810642da074048040b5419440050f000700000600490045098201800c00078101600c46203090070500c10f01c1e01c100e00030000840074038402c0e410442014641410540074103041c0b8014410000c01c0103404059032001000065002c942c0c1c0b00c110f000400812064005980c0008102d0b4507a045c541e0591041b120043e041e0390401400f10321900b1140e40140c219003580d49640200f001400103020041c2c4015842e02c041c0c04204101003950a401c89000d049810b200f8a030350120400004070039182c80032008090555610307007081040f043c1d030b0741e00c9405401000140810401101c007040340400464602c0704081c20104a03c0e42ca0700094060b10b1400c04083d2a02c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 172368408 1250 172367158 172367171
    0x1505060a060e0d2004050f16020703110d021f0c050705030a0c1a07020301020a0f0210151e0b071103070e100e06060c011109030d11070b0915040602060a 67
    0xd004a02104141500034929220403c03140e40302035004078030213501441c0c0c0030802e840e100c4944450044034016031084140190030301e4030425050700c0c0022030350324404650084c1c00c104040354071000d000c010902e0a03240f010328058103001064000a101e036000d0100422508113902c0d1591005000450030301c10302c26500c50070359a80c2096a6106005806000c42184031000c00030503001616501040007000715a03420005a40c0010b401c9800418081c4041218601480c403566414000c0034054180304070104021040034080b01ca000c2d001f4010380407020710710015802d01085001c12000103022804407642da9100710b01c0c01803590a1183c80c0e4601902c501ca80119207504110355542c41807404a0020b150350f49010284240d00e0406040c25811407400c0182d8a240d0600b8020788009080d0402500d6072003801c00d05162912104403505020050158040c0c0d04241e03003c40c0c40780890b03c181c181c0d42e480300b151100041641040704c0340b062145000040c002101500814001c4c481e0f0000f40003013062 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 172369658 1250 172368408 172368419
    0x7020d02160902130305060405030909180d110f070b0a030c09080a030f03060e0f10060203040506030a0b0307051801080d0905032104090207060f050603010e0304030314071505060a 79
    0x88000d008051080c030044030701d061002030659400b511620324940080d003041076694176010305069090750309a40c1a000040c1022082c140905002e40080c00790728001c1c0c501e1003100813551280380e03c01c4042c040080040f00d141c0b122000704403c00c02100e0300021744410964940019402c0c0c2d22050203403020030b04000c42810814007920880c01101c01038409440d412165a8049990003103000d617070b00a06a071108045504072024080e070380325a0680c00103410508044010800c1100c00354040800c40d4400c101c180104d480e04019a5000f060035500403c907551072000203400c002035504aa50419802c240c0c510440d5034951660f41214249420b4030142c6c00c00c40011075a138000750148903003552000c40d0900d00100702c4200300e1500b80c450048241415281c1c0b003410142d0380300d150240c170300b180c960309d450790030b5030f01e92003071640104048002304908030103015010348038003580c40041c0510520000003820000588200c4100700d50026410700481b6041c041140203140540c2e200780120300e0705101060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 172370908 1250 172369658 172369663
    0x302030105010c1e14032d07030e0a0902120403080702060c09130617071d01050d0209040311100501091a01052a15040b0703020403200d0f050607020d02 67
    0x141e03501070303650720301d0242c02d03441d410842d0001128807040c0f80040005840890006502082415500000b5541d07556131944c00e10200300c29190280115009014015200103c860481e9609503060030a031744688400300004459158940c09600394900000c1c1d0040c482e1746020307906200764801d856031003660312103040483e520744041303a041c0c4480808111102d82d500d006e18240d0b0881c0001503020400e030340c5800c0038100c00741030f85101601d1540004c4050040344c007040c00b0522401c0484078841001c1d85460001508403034118000380c060b4082070045000e0502c11240024030204220071111144040354144000741000d100c0ca501aa1070804401501c1c2844041c0d0b80c0543c03816034525040000f16981040da00c903125034410485200e04d801e120316031400344001d255007071000f27051058502c0c0030f040414020200a001e40d04051040200b44009001c61590034054200c800681c034880340254046009481100c6000d4052403100941c40d00304070000070b00500c900119425903000074005041070f40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 172372158 1250 172370908 172370911
    0x13020a0801030f0f051e010c020c03070515040905040807060614030c01050a020f06040f03080105010801080d0503072a020f030c06090d081b0705090112050604020108100815040b07030203 82
    0x400204110010000f2504800001c42c0050158650807011070346542c5151a00304c0e94101c10207155151031144504c40340070312a40c41200120300180000049103000262911741a00680d031160703008482d0b003e00503038510140d0300034010a8034100b150342021300f0102c40503001174100b240d040d41001004034490b0940102e1032403404014008100ea410060010346907900003100140840c0314990300340400c3da0081200e075000740c0c0030b060b0f40103120314107003401085004141c22050600c007040b801080310840000c0c03d112484424507046449456030802100d0b030b2008905407226004015500c4080105205c0708140c12610842d8800c5600342030b00c0c1416224040303580e00c40d500070401c2c0007544160070046500c01901781b140703a10f640707000c41c40304030036000b00c030820350000543d80101c0080c8524104012000d014103282841003202207225a2000d642e280000c0c4020304000c02103020a00540e092003005d00503140381003d81e01d03602102c0702502036041049800b030b0744658001001c1400715000c0c1c03084a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 172373408 1250 172372158 172372177
    0x30301140f0114030a0f02090307060507060605040603020108072601080c010207060801051302070606030501110301090506010c0b07050d0902130905060a050f1303050d0203150909070807090e010902090403020c1302 94
    0x5400c550705c0f409213400038051842c0200140b6020091840550740a2100e00058901602e48980303600c402c0c2400801c45065422090180385407200510140c3c1e00701c03060a0344042070f0b1405a14800b9201c140401d980003c0e030b1135840c140400000410500004141740d200f0b140c00307138219020150f55400841c0c101c1c400380700d0581c02c0300e8244025400f1000e2038006100311801504042a419501d070ba4180c210346c0038901820424a0102c0103000303144050246a8001c0424a480f030105500e58842c1c0b40000005400c02041c01000650180041c06940100c9030a540003400414142403144088010b40b1840b282280c141c003070b000000e4448000e40c4a9540141c1010000c000342d652449402c0094210300740342541071101c10311034480c1004060005502c00c154002d001c40c031420600c818000408000303000d0444940041505100c00d0340b0004024040b990420350129588400200e41401003440c0034019400c2607441c02000141500021096140002554640f820790317103504181c0200d00503490719 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 172374658 1250 172373408 172373447
    0x10305161209030e030a030809100903050d180b100f12080f030702030d06080703030e100e0f06040512031306090e0601031e09060501051e030a150e030301140f01 71
    0x3050341400c180d80a446500d2103402c0c0402c03d103a002001914000704da0031b0850004100804001c480c0c2d0042c807074440300c40c0c0c5215062210014540c0d01414a00440c40b070301900c656203241f1001100c0c004083d208a9a421221055142c1004011100501c21038010240705c426040c00000781003c9809884220316080207020341416402203000b050755101070451030452200780208807600c60715100d2680103045a0b40100806440d41c80c028004904a5038514801c07852403c00f0401143c0212035075249070011100c0102000b034080003d0701901903500000d80040031000c00d108000000030043c06d80c414103510f56550300d40d8910b030848645126010b00c00c008403c0c0350129070a540a50003100203081601030002d109601c000b040401c541003500203450080d02c90004211a04101d465440c840c8a1580c0f00380c1d400c0301c440082640c8056071b50700240500b101001c04040d10401e43d02c14a0203502500540b60b032541e40d01c00100b601c800754240140714440206c4840c000751b00441d0640010f038401c0d5031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 172375908 1250 172374658 172374677
    0x20f09040302011514010e040c1d011407060f0605060c0a0308060112020a080a05010501050405030c1509030f0f0d0c0c050603070210020406200a0305121008010c080601030516 77
    0x2400814400544214290764a036401140c4842c010f052000240610300c070802d03400b100c0d61000404c80000e08004038051850320010b001c8041d40505080c4d801903042161003500030756030340100ea54502284402584480108607181040305541009054403001d51041c011143c030303542046020320612000b100c45600421300c0c01e0010707010780040b5a106074141002c49a569604402e0f800ba42e008a55407000189240c080000003d40c070702c40c2902422080c40c00324106410304020035519403c21084500c2140042c25070030600281c00b04468030303034402030151350b00303103809000381a0f41e505444401031160103035687e0011210700c10502c1c4d181998200c040230700d100380303000140046544054034a40840c01010440c843c0c100c00c81c00100000e00032695998869075418074501c1c00c018800401d00c0d00c0742c01401c0c075000072039481001e4070742003c1e5881290206890300c0b1170001003403000350306c120415400c2460381500070f40c00090261043c0000e8070b00744010740d282051040030101e0b40040740c02107002d0700c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 172377158 1250 172375908 172375939
    0xf05120c010e0913020306010e0403110609100216151d060c09040c05070209090c01020127020108070918020306040e010e0a12030914060a1103010605041a0403060207050105070f0c02 80
    0x10007594000b0082c01c05283c4c00181d07a008039050a80036040380520000001c144420540d2209041e07400214450141c552410855005512140781101e5071110b140c02048051701d07440307c00c651400711313940301500c549407031144440d82e0058109510720424075800c00d14850030b10780700869401e219080344c455003894482e882d81000000c15614041200700031051007000c0042e11030381082401441c02c1c3c001403021403a000002425902c0342c0c001039200d140c07810800300c41c000c0d8949400074050b5090074003001c01d540c0c000c01125404c161350702045028440c40c04804240c2901d500440c05114159010b21201c0c001d448110701303071103081c5c131101043c2e0301c5100007402050418101c062807190f5440c002c60f402105071503080403d40c04001c0d52240303400c000f0038028540041d01c2910040242d210b016400c541c980303a000f51860149100b40118901180104c0110325019001c58005d180e01401c11915840e450510500800040f120f06000c01c00d82d1421000042c0078105214149034001c0290461003c0310 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 172378408 1250 172377158 172377169
    0xd0c060903090302031e120a080f130c030606060f03090816050316060e070f1a0d110304081206040501080703030e1804050a05010c05130302120a08040f05120c010e 72
    0x140650400c01d4040002c40145d070248044603d4642041e4107641c1e00d0700b034203a0503043c04211000c0340c1e5201c00810070b001c54130750040c05044e403003070280c090304e40c840d5a29100b035951100d100c1c2d0003c0c1090200c0b42c000c420006290302c0241a560b4941d104020110031035400c3c0c003210a5020050024072061060302d08401444103420203d501c1b40702070b07904040000408148100e00108101e403400d464015520303071502c080151a008251206040500034a0900f4110800308951006202d03804000f45c00800050755400640d01c40040c1038140782c0d2403429040080e1030f50001603245500180c00c1003c26124178013401501d050325a010003509100d851640d05861004c1040000d81c0c021900700c0e8924075914541040f1813045d0300441c098158a002da11b4214219072401e10584180202070241600020440561800b07a80d41503c203034040768980b95075140f40541d2004028480c00c1c002030007155190114001310101c41050f00e50b00011891507024644032a070900d80c03140040c80000385100d152502d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 172379658 1250 172378408 172378421
    0xf0504050714030a200f07030c0f0803070e0108090c09010902160203030a0921030207180e060a0c030605010503010b070f1401090503090a0e06010804151409010b030705030d0c06 78
    0x40d0704092030040c0c0c4242e201001c0380c100301c503d020803541d01c609002c600c00000c1c4c1015440ca001032616860840804113030a001e00511601400b00708901002c0030410504044520758107070024289a1240740885c00206080c42d64a54180041c02807808a03411400000b6402c5024074001c1c030880e0300b0383c24150301000035003010b030030200841501d2801c10007580b1706100a0407280096590302d0702c001d041c0482c003030608081c0151120394002c940000701c04203a020a107113040d0740c00e46008450030781420b20860060b2481d8003e010607030041c030061101c0302401d5444400c40404e45c1d1000d00c8101d03525401501d103400309209594281400700101c00010f04c44850b0348005c580300ba49030600e46840745189a003120000e020444182d480014201054504811000010130b82e4010145283c030780f00700020070305440508020803005986400a4410880340c0000204103c1500d00e0141d525120a190b4081c1c0310b0403480707501a004004010030641008a442c200b01c000c20b480320a101c0c28281e075040000c202c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 172380908 1250 172379658 172379671
    0xa0b010e070c05030d0f06241b02060c030408060f0903121312030b010e06040b12060d05100204050a121a09011b090302100e150d06030c0902030f07050a0e1306080303071d0a0f050405 80
    0x1c27000c3c0c000140d4074080134280b00d01080005584680c01c2c00182440d104002d0003103405544002c081002c00e5900004481254014003506002c0341c4a10382d1200c3d554403088401820741c0d065030310203500c2c1e079495413000180000c01d07030311081e114040c0e00c20701c030441c0301e04e004025a10204000c10081003a81c0250280c010b4009001c49400700403d031900c03030400340580c2030200e00940024040140b0b2401005070b102804550800315100c5613641d442071295843c090740c040748440c141c800105480ca0079488201046145001700ca122010f00400038803100b0f0300d01040380b003000d24114500c5014400e0b07020140c400c03006801c4010340102c07400d101400703402454039441c101c0d485841c044001441605124000d20b48000c02507202d0420300031001d22850000c3c100750412500384410340c182540000b00303041e1a44c1c180e40c0b2828110031046035002419680d00943c515100010910032204d42c0984280400e4903c021100c010b400300c0c00c10004050024815207003124400c1000740a10714081d03111580041e03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 172382158 1250 172380908 172380947
    0xa060b03030c06090d0801050a0f0603090312110c0f0114130f05070f0303020d230d2a08130b04020907030f0c09060e030a0b010e070c05030d0f0624 65
    0x340d00c82c0c2441e00800721413180d038541041845406107a00165207034090001180c80803441420506007035900c041c00e00c40c0c841010380b682207180c2450b026450080102d80800800c0c003c0d515069000001c41d030000c0342e6136080b40f0510900c580909010700c203a40c042c0001e0000d8100d07039150010800076981440c601641c202c403e030484c00000680421043d0000d24103c0d168402d0203144d400e001e42004c18402c100d2060107528400580c55120003204600000f59090b0382030307200c11031b010038217000704022102e03000c03140494a0300d200301e4401801c4681e0116003039911220a42d0751184564004c4040240003804010f583e03011800610780451500d41c0078400b0b160004601482c08245002e0380d10501c40803011403000f0100b40045540024103020f040c5098000f000ca01400d0780c4c0f81003650720140701c2d4140c55014480402e01c000d100382121100744e80c000c2d0440f5251209001c040004100799209565298504400020310f00322407001c03100001d0f595601c101e40060111400d903101c1e00c040300b2090010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 172383408 1250 172382158 172382167
    0x70306090212030c0610060807091a040518060411130504090f1e03030c0f021c051909140d050a02040f1806021306020105060a03060c0e060409020306100807020a060b0303 75
    0xb55002c20180c60841000d038001c1c180c60800414403001c40d80c0a82000080020900400c010b90360002541011140b980106682410f0452066a07080c02240c11044c0d00c0b161000d4070341000b40000180a004001c11102000b0950801844158522400e00c4102104010b0842000b40303103420fa2189000d41d0050f400000610000c2c0c0d144401000381ca1812460181c441c2451000d048e494490000100c82c0c41c20601034404401c2400795441c0905400100b8100c007041c01c104c0114803480035186074161620000b01843c001e03180c080c0802e5003500401030f448814031218411450004141c9000d01e421601038901300246400f4031000e40401484401c0164a50703510103883c500052904403032038000c190050700d5100441901010109641c098800c581c1040288805503a56500c074004483c1d1000e000101500c41980903101098000a00390344102c020400062050480e0003e501c504401c50717290800c0b0180c40c4d03054801050654241c40140c1c882d840e040700080440d0f009520303c00c0c008040b40d040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 172384658 1250 172383408 172383439
    0x1302100521040302031c0c090302120f01050c0408100603110f12190303140702031c0f05070c0303150b09040911030f0a0507060f170a0b0d05060619080703060902 71
    0x20300e5041e02d0031001a44000b46210300702d80050341d08090044c90725000e0100b2803203c0d000034910000740c00060700ca1504481442e9500340c04011207110284080000e10541c0f40c8450504903a8200344121551801512040c01c12400180b0410781070780d603c2407a4401242000e0240302d0710741c902d4120240c01000d074040c07950008070704000b02c0107400c2284d480b0b1820002c1924000301603506c0e101d0003445024400f014401d0954000c01079911081c02604001d45c4000c0c0c0c090703450003a044803810816010f00d060700740020194440200e1010b140291428000000c040f1040c0580c20000e00c42e203000b20f20309100310880c528007030b045006440c1c040c0c494885500410300c0000e040c001400362145140d44080b2040003084002e114040041000c1e080c01620500e41380c40141c40e8907032044468800b25502000505480d030030fa0b100c0c1c2240c1703501070b001813151586440e2165540e4000c0c1e84042c4110b80b68000e14600d000040e41c14001d03113450002030100030345507907034240180280c10000ca070312002200c0b00001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 172385908 1250 172384658 172384717
    0x910050108031e0403020f060a021e21181e0415050a0501050a020a02010c0f050f01090b06040b01020c06160b0f060108010b090f010f050409060f050913021005 70
    0x3801020010710f998407000c0c1568545080c01d035043d40301043c414002040581e0b600c009000701000d040e150180d036004562001c82c10080c90114a042d5403402040300012840005601107441c40b50100003100c101c0e003003c1010313040c0100c0715440801520010892000d0800c0070202116041c4140c4403c2c5a1801c80c0014094880610600d4004840e2040802c240d1500e04800d400815003030a0282ca80740343e0b950000c0d10703026185406818052140c60000402000c0c4042c0c80b500b5420405844000b070b0600d031080d019000749181500c00102d1a00402e10307502c0c1030f21507038441501c16001088034900500921425401030300c43c8414004010090901081095180502c11038155921040c5403030043c002420402040c0c0180c0c9410000b4020f20071075880c2c2c8a00c000303c203842400c02112080301f00c403040b620351040d904200000c2d0f05010000425285841c2444c0544a08954185040c0d1701c034802540949100729003c3d5003c80480e0140d4042c03400742006100006852401809101031140c0c00341 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 172387158 1250 172385908 172385911
    0x3110c06180f030c101103072a170d0b01020d021009080c0102130303021209090619090f15080303060307030831050319050304060f03150306060501020708010e1005091005 75
    0x5215001710007031482d900f4442c480c400c002d4200440032429410301000081202c8100c120800c4e0389070035a03013070a80501020341d6100344154000c1d09140301030100d150251454001e0700345407802e00d060840080706503001144a058045c0194014001052343c03110300005070100e0b407000d846da01010015100260001e0008158401c954603400e051f00d890743c03038001d02e021401d2542c404102401e000c4c0350521350f2280b49960708a2011144044410030f40c0c030300ca0f400040c48c3ea1003000e5152415602079641c00658001d1520030703015071040440242d40da1070058130ba00c01103415960603084102c040c400158a24058032012001c80c0d940100300c10241c045080c80300491705a40040309580000f00b02c145000c01c5403980341c1500d030310b001c0c01e0054250380c0e265403800b03140102400d01400440981d91184240c2c000310a21040c201503625141d501e003010030080910b806428014051088003184540d4140600740c42030310104002e003200603000d250700004180181c104ea4150140221109202e00c6030b00445 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 172388408 1250 172387158 172387177
    0xe190305060103050303180c0f1e0907210203010b03060402130e040308010e150a05010509041401090b012c0904020f03061501020c01210203040602040e070206040303110c06180f03 79
    0x10340d40d9040c041c44120403180a00e08087d080d600c07194907121584c4620910850705807090b1100d952003055000c4c082c400c2c40c0c0b030003056500500ba84042001190380314004030010940c0c28541c495004c40800d40005074802401103105c0c05400700081901400c05134001c06a4030300940500311350f00d0700e403000c0c1004030909640580010702c03004010304c01521581c22864100c25141208042c1c4a40900030694448491040ca8180440407460b98a541c80301e82003001030840d080c0301030b00c6039038690f80104020240b40e016940010900041d903081c0985101400c4031403201c602c50421007200c04d00030003010b400000c1080f0b8202c1046200c041d4240c6003041214020714650015803014009130000a16003100303480c6c01380c104411203000e00d044222454840302c19524004000da983c1d030390703400d110000c0e2003964000a07400750064200400305601184e140d000320302c650740c1400f192422b60603450082c010040842c0e41e035041403022500360704142d0201010319038464184d8072000310f0100658210b0700304401e031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 172389658 1250 172388408 172388413
    0x9061c03031406010f02151803040314010506010807091208070b0408030708062202030c040b0c07030302150c0405120f0d020109110904050d0507150207110913030e19030506010305 79
    0x110700b03026540d8a82030ba4404020b2800d814545c07102e039030003540c0b03440c80040d1034228182c0e6800300b2103a4000c040d540200f406100c0403695035513542e15001e420b610303000d1021030f81c551924001c99083d40c0f00d20305040c040c0a06588030201d640c2081a15400801030071021101c00c0004c00110000550f140602440799004000c00c90300c929010300007400c000002054644198104400700b001c1c8207560094894000c0c44c001d005850783e50b1890f2590140c80345400c02c40c8084000b02d01c41e0b414030400105141584e12075401c4d1860344038512034081c00302000b81c41f941d540c1c48040c0020b01030382c1002899100d10421b4181100e81480951004c3c07402c084000c40c1810050351100084420301c500b410801c0300543d03058469070198a081d4940c0c5072200d20a03545078040010000c2c9000612121003514005441c841404643c2e907106454034020031041e1484080c05a200c010001d49400128010b589960303415448018840c8800005c02c6104590351039800e8103a002c085000c0082981001405c0c00b03503108400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 172390908 1250 172389658 172389671
    0x26011406120706020d0e0d02031501180506030a0f0302030d29010e030c0405181b0108070507050a03050306040f0509150c0430050d0c060606020a1109061c0303 70
    0x500207401908090300c0c007541c0c40030703108000c0741e81c2c0001d16084400342c42c81c15442c090403c5002840c10700d02050041c1d8184110000b015088143d1a030790b50488580031103a0f09101c06041034082a01d0f001c542e0a68150004404900840e0b0580c40700c841c954400e1068038600500304603d41d0803902862981d407a0078a1402100b40b2480700c0c2c246454000009007031000003031441c0c80010380c2d83c510700b0302d403c0c4c0100c0d02c41d80440d800c0c2411031203080103940101e003952800a0304410103001080d4840078a80040d14070b0300413815550150702203c4110360000040c0c0800510f50301c00b03640640c00a0300054003da030f2168007030700c0000c40b441013900501190018000c2c40002c2800205441e2000d00811006013040100700070140d00da1000d00713095004032200c4400c64074140c1404910f406a03140c0644107014551000403000c1e07214041c080d50301d10800c000c21035a40c860f01c080340d9603002450300511441d290b0700311100724904400700561000c001480c51004110403444809254050700c421008281c0b00d51 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 172392158 1250 172390908 172390921
    0x415030e0d02190809180c030f071e110304080102040902040306150e070c030e04021801080f010b09010c0f0503040612050c03060d0b0709080d09050a09020a0801260114 74
    0x1000c0509052071000b00101e24036005090702007000f0394402080075000083e0400703e40c5030780c00840500340c01c0c2443c100191804041e0840703650300c212401201a003500c4000368016006040510245c1045a1640e03000d98112000765800041003404031020322040c04001030b100000d0000344043d02c4007440c090b1719585185401016100f2114007855082d401c4c081c02d010b41c002d6a04c0782d991110302c0d441c10070440000d07802d050f0f03428602d0942c01e07904203000081000300c1e00421980c00408103400e0b695084a6a03404241c000300350000c0c0540d00c070006081040202c658461400300820074026000f04103030311881e43d50b0500c0d651042d84480040b540c04610203055000b00e1082c5584200c5000c54585507203000d10001c0c2c102d92078040000d041250340c4001c904854820030f660302c080c04c103036006c90304103034209000549108440c3c41140c3c4100207180000c11155a1802924400801a02e03401d072240d0805240004501d01c00318008003001d814100000a12030900070442d89440000031b072444c509120 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 172393408 1250 172392158 172392163
    0x4170d0e01050105101e03020706090803070e220c090e040506011703090a05010807030b090109021803011a0d03050f0d020403150e060c090a0905010803090f100c06110415030e 77
    0x5031310040c840d180702d0220603001600302c5240d950701c0100034941c0e80d124554030803c0d0000d00580401a040616104070340c410000c2101c000c42c0250a1900c80c100103058031420001a610310006104406444510149203000c00d0341104080c1c2c0010b00b050480d840c4c903000c84041d80c6908071800d80342580004010084020030003414030207200d41d1800f0b1440c144035440410780840c500d1081b203040100ba807002400203031080d0302041180c0c40007841e2031758035652000148040c0d080f00c803841054411102549405242c14858003200031036a18054410b4103a000410240c3d1010b864140e0900c0002c006954a04114038020f12614002d002c0040e1100c0c118108020311840c00c10008400500d0610100c2009400103002075201e848040151707550301c04140808da40010990145002c241810004603000e003010024240343c001c00e4403603c00800340d01c2c04000c10380302d00e5400c0d6008601648210386c0490000c0c4c000e48010558120b0741441c09070741e0170b07203504d0760039001c071200300000e40d02e421010646205 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 172394658 1250 172393408 172393411
    0x5041d07111c050d02040803130f060509030a02060d151e0e0106020316061d01140c0f0a0309061407020303060109240e0d020405010b0408061012030804170d0e0105 72
    0xc120050900b078611242e840c5401d5603400d00382c0706000300890411500550703501102c0140031108252030700ca031460745000c10040d919002da03480c1c04980c8000410810310800940b00164002801400a50394076020700070140c0c8000c070717807038030b02600d4500002c00006240a444010051220107500c0350203c20030f17030002c203140c94112840040ca104010401e0607400016071340b1009001c01224180181032411000030609001d40d41c4034a20704041c01c0d5448101940031554031301e0301140d141c1303e595841500020503c40d160b03803c1d007414401e01030703104201c0c4603900c0210801e11030040010340c40000294010081e900300d03103940c01640008100030302564020700d01001809034801c5081c5110008110000d040d034000c0f00c510401200e5145100c40d55210840e0440c1903401410030011961070305400601540607010b54000b600c20703240421249804a54000116009282055007003542d55400311800e4001400665100c0300b508060344202102000074440d00f941e551000800041d088125400d4810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 172395908 1250 172394658 172394687
    0xc120a1406070807050a051209150702010c0e03010b030604081b0a0803010602160f1a0f03010b091f230d060602100c030e0a030804030215040f060e030702150a05041d07 74
    0x500f0b10508020f10340200559444006d104230741907075903403100d00c400c0ca0444000010480f440c3e00000f84801c850701035100010aa04a1b91740c1642e0094400170b00d4281c0304011384841d096030140d400600072070020005000810741606901901c0e019446550385071888035079096580d602c00000400c80c55030100b00480c004008140c19600141c60141026140c0006200e480014000350084140b00c0e8103500440703465007045492680c603961180e071b0301441c03074220b400d0950103207030320000120320a910341004a101580558482c10074094040341e137100348081c80d04010307005909000f00e03090715565014039000b0305401c1d0300500c0d03d000500c007402e098900704030392034041c185040d84030301100700d0210f81307100150b4040c01e101c0003e03129413400300d140200180c80074501801c1801403004100315002c0f58031100f405000c05014000380c2d43c40181c0c491003648402580010f011054840d10003150b0050074070800701d410503500b41640c0c1c0c5101e0f15030080107110040c1d00c0140390b0070040c0c12900141035484042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 172397158 1250 172395908 172395917
    0xb0114031519060926070603110c100e150c0d020703110303070e040f200901051204030c051212180309040f05040204110f12090a0c080109060c0503090c120a1406070807 74
    0x51580d0b0031152100b010340101f0b0100f40d03c80c00c840f880388060f003044a42989659045a420b04500504d040081c1400740d18078040380180c200c00c80b008051200024050302ca409400c515160252230040c0c02584514822810b0101c1d090280301030712000d00c0a144540c0305500c54054a40c1aa010803040f2110f008660003400d103881c0420b40703600e000007680da05980440c182c540c2c0d101490401605c8a016079152091407a03500d40402081660000c58170906a103d101142c111805030748001007140540440b00003211081d0700050310503c4284001c06100d02004183c9e850310f01b6800200c3c090724020624120042c1d02c960034002141000d102d14032140d4184140c0c9800e1883c0000510514850109010075103052036010640800051009980803584960b541d24100d640c0e08040c3e01915810000b034400900d00001e500c1180e014200f120f1160207140090455559880104520000c8084d03000965101e04090340700000c07207907442400280403c00007001d16281249000f0000c1c1c0000703200c0802c20 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 172398408 1250 172397158 172397219
    0x150102060604150b07020a09020c0706021b0907050304060e19030e060c06060d110301050a0902100c03090b1b01020c07080601140a03060509010e0109030e03010b01140315190609 78
    0x20b000d43d40e645060f200b4034040c05a07102103900010304c4030003190304142d026901c0001d188410755000034078801111a21b0302a10001503031a044100c02209102116411601020001c1c4c00540700b80000c50f849072240c107000400d40011980c0c180f4044d030840c0f0030b1110150346041d410a041d0485000384c0c10002c11508140341c11981d0441a8803410043c004030b000b40d58072801c4404000741c90703005500208029000308503610344105164042c040f5600c040e40202000100400851b104080005100350035464001c2c14901d0001e40b40401c2d0311048030695081c42210000d040a0f400703000600c0c610900700000c0500e40d06101960382442c406034880c0c0c1070110070204050454641fa900703002200e41002000880d55500c0c1103060141030340005009145d46406041e004040e00004112070a000650080001a880400540e00340707210280c002500d0700f0134400600da4440190303c5010300c1e0b40140140000d514030243c400c6101166400820100380804c5050000c550742c00446045900d107505001c056 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 172399658 1250 172398408 172398431
    0x210050c0a08060a030b0f0a110901080f060a0f0305060609090d140a03020706091a070905130b0a030209010b1801080402010c110319050303090609060421090e150102060604 76
    0x140c40351010030810b12814000041943c2d8902c24100300441d00001c482c4e500b482d101000c0840032004840e420340440c0307000c0c081c600d0644000c060380d01c0b110301a142c0354400d40711000c004105d808000c0c8502d03401a19130030702040c090030004900005503c100001c110b1410700000300040654028500d4003a58401c1c001104c03010b601420084405850700001c586d6152219012406403194801c041c1440b410700c00340100300000080222032030203242c43c0041c1691540b01e0100c403245100d02c40c4581c814000703a001070402100c4d40c0501180030f40200714005050b520742c003181c0d80c42d40c240c0c041c1034140c40204030b0000d2903000c05810540070000746442201490a9400a007000740310721005816014150306541d8070340c170100060f41013110071030340b090300d900c0e403034a04180d4036030007260b00350894001e00010804003c03001a00600840d400056811003403031181c607010806040010a00400004080c0052064285411240035581ca00e40b0f420210b82103400280c508280a001c00340164a0449440300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 172400908 1250 172399658 172399681
    0x1d1501020c0a0e0405151302040605090c0703030506041503051005010503120307180b031003060b0a03020114031b1303050d020a0b011502030c010c03061e0e060f031603050d021005 79
    0x10780f8440c0c44a081652540c0c1001880e0003104c0c0c081d0010703101004240699800c10440300300400b031088409001d541d0721403080c0301407001e080e80c04070b1603080c0522001e800280a5009540e000201402c00030381050590030154441c401343c1e00c16103a50b0001d0f5000003005000f8000c0030b0151000354000c060824403007508508a2100502020030808001c0840c1c41940144c0b801c6001000002541074a90800c0f0b0103001800000784011641c1c246418582c0e00306d8146034601e203049903016120140a0b0080c40a40c440c0750b0b1008245c4054010490450440004200c01504c0421080d407201d904450851800c5440d1207420112803055500042081c400965030b081c0c4641907483c040d445040c0c01c0071100041e855401034103522007007542030000781c642c44c40e41035201c00c007220080041444100750568043c00d880015014005000c4c14500c00103103d03041c2011031001c2500c010301111409401c5401c440f01c8007080d0b80007284e40741c01505d400c009090341040500410301a503c820006418007661410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 172402158 1250 172400908 172400929
    0x61b06140612071a0a0c0204091203061a0d0b0a030b010902031006020a02090a1d03040b03090c010c0327050d0f03080702030a0206160c14010f110c061306061d1501020c 74
    0xc0500d840002d042c485d0350b100f416082d030a84e074040c1084c80019942e281074164401e5208403400000d140503000038101e0a04040898111201c1d03494601c5e101806a00101502440d101207070841c2c200c103800400a8030f103000050003420315540050b00e0341854040410000003692040d42158030000d842c2002d41d542c103454903004800d01c00f0000b1641c41d50803a4040c2d41810205995050102280c00103604002500541c4580c185000361040704081c3c01c010350340300f61500c5018002821540d80312140c00d8450524074015154202007103151541c8100045026003461812114228009024010150001001500026a800603504200407090002d50f03640000349429881603d106135a0099400f81c502150415003117000001480c2c40100c0302400b070b020016080381d18611300100d0000134140c040079104203d8182014040507240c8854044c070003514410251280c03560380030005a400608660320340c5408054546030703164500070490f02044105080e01c541590801040300f120780e5605400031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 172403408 1250 172402158 172402199
    0xc0b0a06090b0d08090d060f06030b060316030b041b2c0a05061e060930030702180612030d060f050901080a0201120b04021303020f1207061b0614061207 67
    0x800006e014201900500000308007045454905007002c0180028041c40702d210780c5e0180c0c1100c0c171440c859801c101109400e48000341402040d80d0105002902039003802004a08010030901c05540710007001b4003031540c142c4101e29540c0300c0800d50300c603072403c0040e260784411334139010022450541c000c54010030ba42002e441c1d039141c9400c041d00032592090180c40002401422010281c0035042610240c88445e180c3d001504001e1068240540d1000041303c1405602420705034071300703013018680404400702406541c4c2c0300540c0d0721420180c180030005424215281c81d400300c3d4040c909041417840c0c1c105038000038025640840140080b010020b1184683c60742840d0840b0410303040c030b241c03000030301c036035812a80e115000082c9440380780d8441510300c058038002c41c0c80f040441890403c20251034000d1031a0b07000c82e0080300c2c042107500e0203251801500700b0182ca02004a55081e81d0b03c1c0100d84508a07403c50705c03d850828850241001820120007540100040c004d0034200220056102084000d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 172404658 1250 172403408 172403419
    0x5010b0a0314061f0918060e0c0304051507020c030a0302031914070b0601020703080c011a0102030c07091806051e012c07030e0d0f0f0e011b030c0b0a06090b0d0809 72
    0x2a8104c1c51044865100034020344600075000624030305104003510051140c1150411103c0c0800c4801c0240c50880703001d591320000074002010803050032000c00b4402440e480030740c09940c0954015860602059040522035409507a580b0005c0d008413403927844c0c1e80200c0c2d0820203410f1082c10040d843c14111410640c003c1003a1099907210780040785040f086410052003104003241c1e01d0542c08054001c50740000c21f94002015074010300c0012a96130046020744145030780111002c200320103182d031180740180f01c00c510316400748140d030700c904066074002c0d5014074804e515a174805200f1112420214050f084d01500d1050011035054007100c1c0d99903280810501420030340104000d1400303a44a81410040d842c00d407112844007000250256850404a00100c0c10540f00c443c1407a1040360500203d9005858081140f42051014002001d42100440074045031783d1003900801c2d4400c2003648100c40c1c412010501c98102110750045e0b90b41c420405025030083c18405000440340b409542c9840c105640 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 172405908 1250 172404658 172404709
    0x4380a090207061805030a0201060b030609040b06030c06070b0f0603030301080601030803060a0f03150617031b031209060106142b150914060307030c060c110405010b0a031406 77
    0x40060044c650f00000b5054960403c0d552810440d011002d0a03c806261f00200301041c1d403818801e4052000300c0d02c007076106c0d0031303c0009070010ba01d2200088c0c0112000c0d00b1a87d4250030350000c2803495000140a0300c000d40080100310030803503100007103984410194059800c5514110b0406c1d80e504041c00002c7c030448001c00000d216407949580c110041c000c0710041119a40c2c0c80c1004e82c40c031440d00010058090170700310007240e007200049062000c0c0c0202c0004615020a01c00000b0745805030042e18181400100030360341d08606614856401001c44101802207545030040180c03286002c890408903071a410701c01c00c21050b214005088680c0000307160100e42e51041c2182c44000c140322a14500444600316000c21503c44541c403900b20405a203448014036212001050341e148124070000303042103041341041c0405071280a00560040c4945407480640300000001010750b10240c210840040022035004846681800381d030701c00c8030140c280e00499050001c0458203500d454640980100440c16 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 172407158 1250 172405908 172405913
    0x6101a0901021e0f031b01050603060106090501031a060d0b1c031e02150405062a030a110d050109020304060b18160917030306031e0604110406030204380a090207 71
    0x2020744c009600c0181600d594011580030310b202d04840b1030394108150f280c81e00158440c01c0c001902d0341030720f0f11340d152048810b03d410011005415248108801c010900c1c1c02090705445540c01340103500486000450240540014840105e00d584d291001c08120480f000d07007c603803c040c400c9440c40d52006940c5100c3d0107901d00b6880c1c00654001000007014502c10402072007404a007090140300041200d42001240c0b185181c0c945d000d015200b2001d01d0b0410200c0c0c604001d03540710101e110003900c4950304144150507200704030703607090780032a00d03150b0001304003c100306607442000c82d440c05c215101e402000c1c44d90b00074601c02e2802844241030031000c4050300d00840c0103102d000c00505804841003828240c85c1042d03500c07504103440c4d090091140c071104e0b4080028004014a03d00d001000400c0d01d50fa60313840d0030b0251040c240d88950401d0784c440380440541c4071805803020303601e032505000b1042d860b101d60640380303500060030342ca01c0042d1002c3d00f000307203503502d440450445490200243e2a036841d0f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 172408408 1250 172407158 172407163
    0x60f06030c091202060a090e090708010612150c031e0501030201030c05070506070c05031603020f0f0d21061205161703040504020711030616031505010509040e070806101a0901021e 79
    0x3030304012468072240d01040b261027000030724038065890340380c024002599142d0501e11080500ca82c01000303007000c0c1c03e110440c0e1045030700062440c0ca161034085402c0150440215449000002c540807454a8a0050041d542c241c00303203050b0340d200d40c41c01515200d0b094032141d4036494054180010000480444824046e0400640d410280c00700d281d03000c2c000c02d9141c041e680b0780d04501d11418501403100344d0710180401250456020545442e2000000141038000030381022140814440c0c41d43d0311b80101d046d040c0800c001d02c81501c140001e11110507141e0759404402c06903880146074004900713007075401d1f12010040c0c074111007040e54007580394019490091210501c8038403540e0544207403400c011800c0d01c0b090481c9650794030754600300304100e01500b10202808a9000c3e071404998100241c11050401e80e12502c07403a401c410a442203180c840b503a8600745136060f5001031580a1181e1f0a101c1611401003608560320504c000628103041100040c0d203a03030000e034207410b0a2000105206201d07030f05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 172409658 1250 172408408 172408427
    0x7060f0b04020d0605031e0312090708121c0b01090510030b060c2b090b2d030a0b120606040905030403061407030f0c14031009060f06030c091202060a 66
    0x74400e64542941c070b01401c0040410b4800c10b44a0b104601503298004017003115100303404001c001035482e004280079030a0005102800e011031741d11401400240c0d040c414441c0100c203420740b000199a50341e0303041c4410301c1c440080e500b0401083c0341c002c02c08926a04500050103ca07400d4030140c042446002081e80109044003440c0d801c00e00004d0380d0348075500003040303c40303c48507860000b101001c0082c3c04040b1800c86144000d01040c038083c014402100b000c3c0c0940b000d643d9844c0c2d40400400221402e46105806007034a5107022000f00c1400a00c0031180154072038510700762241d54005520b526500d075200406003400380199510310050701406028001c4030f002d150002d81c2400514505044c07006214421121000081e01d4800081c959503024002c00f51300000316600c6051052199a200845500240003000c2101c0405000515800e00b030203040000d01e03501d845c0f1324000303240c444c0182c1541c0d03921755103e00300650030409016503800700201201068060310a2519030a4440003134600402d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 172410908 1250 172409658 172409681
    0xa0e101509180f050c1e090f0301021201030c12030e15040b0c1b040203040807030e01120c0c060e03090901061407061109040e0706050a050309012a02060702070b07060f 74
    0x510a488000002c0a421058441c00c045800300100c2c0c0d1881c0001d4400d0240840d10b61110808900c6080e0b1040488060201c02c44000d06558282103401c0000c3e08a034001602d42401c008803400400a115901103c88000e1444114118200c1c0d0183d4000b08141c0130070350500d2003554248007401e130710100401a030340503052626001d655800000319050390356050191410088079030783c003000c98078200ba0082d24015940984480e081030750726501503a240e524030a4060400545200444081c842402004020a259140d2984048a83c20000191011a0043c07071080c2d004000d5860552140c040c0d090440d982450f0603100c10b0001c00d071300700e094407800c0c60290801c1e09242e0725051012280c00142407880007214208281c1d00c128110984410980c4603280101e0418003600070154001d20055601402440000850303090490349102c890058030b8038056070480d948108200d85404100e41074005080780000d0402c00c0c902954048644190803004206070f032901480c65000101f50049101d6a6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 172412158 1250 172410908 172410929
    0x3030628030b010f140102010207020d0210030f0c091a0403050c010c0c080d080a0b040e0606010e03010f1d06012907050f06190b0d0c27020d06050a0e101509 69
    0x1651102507a80c10242400b802e05c0e85003544009010540c01442120103466019009541032401a000c020100f8148410b072018161182e030480b003a91300b184a01d503403400c0d0a4960000701828950075200c4800c021000b81c81c008030801c4248042080054060460307002440c002c070944400749400302900f88154040c18070352080c500c0034a22036400c840035901ca0080c500c820888054400c0400043e20b041080803e9160840c002258140d44207039094107051801800114509135210207000c100c0c0c0c948081200d82201c0740f91451004c0000340222401800d60415846190048680091a41e2604030b16443c418500007206030800a0900c2989484011302c0b0940781c80f843c101210844440d06510000c0300707945010a41c4840345000c0120060050708040d2152070b450801000902c0600c007040728210064070040e10075468110750000745030b10032892030041403962425003406903101d8039401110000034021304100c074404140b4070200840c0c069400700c201302c04650a080e40e400c00aa0480c681d410f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 172413408 1250 172412158 172412161
    0x3030706050112210807120212090c09160923030d2f06161103030109020d0c0e0102030904150b04060306180c020d080a0b060301030f0203010b0303030628030b 70
    0x10040c1c8600f0410a50142c88050b82c00d007040851074604203903112421011504410104d0300281c030901030000d107012107410052a10a04852030b600c07200040780c240445500a04d100d082030708001940d1600000000c41c21004440036000c05003d0100c00c0c09030902c05a07a0018100c40b100d6420941004180054256603654085000c010704000c020441d004600180b080e00b40c0d107824a60400e01c4030b0320481c5010700b4003611142d1071209001c1d603901080040244c5149000c00d000c0d014001180208183c0742c0059039a034201041401380c070041d003a070000703000414a4141890741c022040b00c103504001c46001a2280b0808036588a140281d0815503c04001007400700e8903a42603407080b401d48040103040000303001d1090349201603c0c8243e04110040c0c0096800c1c00368640540b450304d411203024200810b40b2109440814002d0b0000da005481040a00030000b0550600380b00c1c9a4100200b50007642c990b10b02407001c1100c3c0100000b07a0303070608041407000100f40401c3e00c4500302442d030109102015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 172414658 1250 172413408 172413419
    0x4050106110105090f0c010c020402040f080303100509061507170d0c030e01060b0415050c37110f1807055206090b19090c05040b030307060501 63
    0x32602a40080540d40c600f0b800f20f2424440044d100b4900d50901d0002c1c42c040814400440d8100d074605012030308942c00748004034100440c8801e1601400580300250344a1070103050781c50020710554492800f804030082888200e40380c0071003d005100c0d45141d001e40d00d000602e04030034003c0c40d080074010341d1079012401d0503120005400020020b0070704e0b0340502055001500c0307542212024817035040c5118081100f0081090310460482c004001c3d401c001d42015107044090b03003400313105407004284508190003001c2800100005035a5030b800314540c011500e00e82e603a070204004582050304d118950180002602c5d60b518041080c040400303886101081c181145e000e003035038201012040c13100302400240750340701d850002424400207884443c1d0031111010296101081c208000c00b0048000920f040c82c0450038130302031140364a108108000107440e050391800c003038140c090b9840800b00d080601030380205015400040565400b124001441c26103040060b10318442d8160003040b80741001c0c00080d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 172415908 1250 172414658 172414667
    0x2090705031008070518090a050106140109080309031002130305010f0603120813060914160602010b0301090c0b0c1e0106060801050105030f040b0601050f12010503010f0915180204050106 82
    0x585400c1e4103601969481c0c1031041d840e00d04e90700406400c6511446401c0350802e4407030b8205e40241111003540c0b1420040e80760182507034038607084403001482c0800501c0729941e1104000000f001ea442c082e605102449002a886440080b03041076038540208400314900b5000700c1020046920100802070200c2c691948005405c0d2484143c2d01e80210340380708032030b04d8060641b00d44980c0150703184001c0f000c02991000010207024201707803261210303903c11020110042118540c0348140e551842c00c039130301d01070009081d6488000a907019034103007014000029003400e2601c1c02c0e500318031034907902c0e00402c22140e071408800c0d4010100c1040c11002c0003903064010b601207801d4811594034401c0580c0c80300015141c51209445c0c0340e010740140c030001404103c412131001d07000700c0c05140041c5000c0217031408400380e4015042d03596112000380f00411544ca0300f40305004080e800b0b58807e00018040e0b888010f0903203580107000220503225a000ea02ccc03511081302c04107485074018020000c5503160b0000a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 172417158 1250 172415908 172415911
    0x60d020a021609020f03040b0a0204170c1207080a08031807170106090606050904090c0302060a021501170307080309010902030106090e0c01111002090f090702010e0d09031505040f0209070503 84
    0x10050442d5440441c3c01800e07402140c207030782c00d16a102c40c50740d19641d41e03140051900510303980365140d081c800402e8549486094161f19411400200803500360743c020441010741c42c82c41c3c60941d170310503501044261004100490000d0700850f920b5100da4803000c1c01c890a010074085071070280901880840ea084003d89121010003442008005298588041d5805c0354074a02a2001194060201112600d00b40d04840780051040b005401c0705030b035a42c0865043c2d00050640e10140e0804030303810750541e4400c940c55006100d02c00e00142c4800d6076101c025164819000c001d428903400100084800c0d500350060162960f01078000c10100d69540300740d4000300b405405418071030007109000801136100e0203451080441000240c8608031121030260029480051355682000d40040d00200b2540c6044081d4032032080354001040a021311804242800082010303081070040b2036005001140c08052604001c440c20200061241c0741e07401c001c1c0c20107074200c1000790310441140402103207035405800795 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 172418408 1250 172417158 172417183
    0xe16031b080106090b090307150c0b0c030105030f0102041a0309070b030934051c02040603050a0302060105060a0503060114041e06080a0e03091915020106050102060c09030a0b06060d020a02 83
    0xf41e41c0c82e12034100c038485106801c4007c0d4168413008c82403240b1210b40d040408590351600b450441c1e03490980ea60f521002c022190710341c203040080010001c070f040510008401c041c2d040003c62a103410400d2917101503421099070304d40350700c4c0800002c0580070100900750141181c000c190f5102d02d030a00c00503a0f1640f0304c0085a03a40003207031042c40803041840b440d05060168000c94080102e04290600001d19810020050028800a03030030016807524071580e8050341c0581d0281540d2000e504010380340c0903042e0f000e10300980040020030801580070080d07982203002460100b15100762801c0c60303a102e0146402041a04542e0030f0880f150349811981d071401c885083d10750407100d990340b45a01d8120381052140b0909508204000901d51030103030031406a41c107400c1a0b44840d191140c20220080c9555074510f40581e40d03c140911140d070701045000d50140101e045580340203030342e601198907200847d500a10081c41c000c041122aa00d4030159030454030303034000440d280c02c1c0880000b5910a01516003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 172419658 1250 172418408 172418417
    0x2a05090a02360d0510020a050d0c0905010518010521070315061202090d050102040b0309070f050a030623150a050301060b161b060c0b0f010e16031b080106 68
    0x101c048140c00d41c003400c00c980034403040360814255414280001501e040c04100c40c90f0117030401c2600d0340780b0707144040c003071209460399190b45451641c12102c0c2112440c10200d001d0100700329040045a170f00c8000c0702c0304101d08103d0600115010360060321540100c40b502200c0704245880545010303100c610b624400c258a60301809021010941924203144900038140012041c07040000b00c002d16030004c2407108005000c03842402d15641320142280c006400c0043e418600000740a060b034000c1140c000070f45160072074410309510700000141034550900c002001360380c81e90001035034145001400130100d0380240e080255881c116240c4034081507942c5201f0b20400c0449408900c03401c1c1445403030709a41c005a00356140490024440c030441040000458000181c41081d100440c44d8a650750010700454403112196145031600e1200d0500c002e2400300002081c0c001002a441e0076102030742c201004050a10110100c03401c1180070b4056401c3c0b48221000a4511010860f8449401412640107540703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 172420908 1250 172419658 172419697
    0x50a06091a0f071b0b0a09151107111305040602090102070e04050606012d03021c09030e0603060a09051905100f03020910031401050a0b030a2a05090a02 67
    0x305500c0c1c441c402d85020429014000004940901450070040c80c12001c00580c1300c0400c255844000c0c000d41118029005503e0b0081c441c02c208042901e035850b0340c03009806010000e040c20312900075010700c440c05000c0319250268491591194180c160300000884018456450141028000785d440459a40e0052180c82000983c0c604c03a4040e0a0045a109010384626250400110dc01c06100c07102d210b400709084010804182507a40100003580254501688400d00c1501c038041a6044080d42c50410b402c0c41d142d02c00181d480002c8106d4420119900c4e80c60b83c42c1c1c10081000d00075107400c0000b4241c6031606001c9110303118050410003400350f081c14045a6152805202d6014541c0308200702041300010070300041c80d012200990000341d0100c1d42014542e6511354500c00f0f800708000c401039954400c01d020381c0790700d6401094064076003500108850190f5580e140307611000541d0010419081a44560054103004060300042c0401805146c480c104101050000c0d80701c6a00d01c56490361802 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 172422158 1250 172420908 172420943
    0x518060304031707090f090c11031201080607050c101113090209040b040603080d0f15030b04030e03070f0521030a021b2715030f030409050a0218060c030403050a0609 73
    0x5c0c0015248008603001000c0d1410100301c0c0940040f0014006000c001c03035140344141c07800c1001d41070341508451070083c035501d4000705070309111026040c0c501f000382c20001016103c000082061801c0183c1d44000380540c0c4d604c02d0108180103000c0b0070041c1d10001140010b01c50102d802a16102d4030448042000c4030031074040004071061444003d1a20800380107000008a0a611040000c640e269010840400704001011000c1481d0021620714110038241701c00d142e4481c20030b285005d41039004280403428080035240c40026445a14031500080c14114000d041e068890002c82c0012811252501c00b140c40c06515460b032413190b42c0015804074224401441e1024028900b103803400c040049039540c40400c1c00c800ca10080480049480c0d010b048480d6031020040c01740c3c441b2101026540751400e0501030b60581e031300508252001030041c0541d0100d03001e1a2041e0034001e00443e0019601d084100c00e02d800c50180354006440e9000d0380001c1d00602c900d50f0403031600707031f8414080c1009045214 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 172423408 1250 172422158 172422167
    0x2030106080f010f3909030803010314100b01050922021801080a062916080a030b01050304021e030a05160914150f0301140c0a17160518060304031707 66
    0x20494811442040541780f422080214200828145000020140c49844000340c90384281d100b1116280c1041c03040060540500034054540c1c0e880c0001c0c021007070f10b240001c105000f060b400b01d1003480c1c9030aa110603814048241505140c00c0304003552500006403c1100c0c4403c04182035001c180154000703024510f02d481500151104141020040c880911046410400307050010944402c10030503003d1b1800041e46048806216481040d918400b000c00107043c3ea08421748907050010500c10300006a5440508518582001d00e11013a1041c500c40000d00c5c0c00d00b840300c064298001c400005d007140100003c031100381c92565030103202016141400c282d40c41421600c0700d0a005040d00d0010191920b4440740e0990325008001244c12181030142c9010040161006202040f000a0f0354050982120b613181010b842d04008055514050055403582e000c88085401081340004004031011080350040000079000381c0100d841e40742c40d2401400001003c21400c0541850000041000c0d104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 172424658 1250 172423408 172423451
    0x1206040302100506060d090c05030c1203030606090402250c15020d0806010504170a02180f01090b0d06240e0c1b030408031c110306060a080402030106080f010f 70
    0x36a00508a4480c20002c034002800e000e88500c0d40941e0400400200c48464080c0d8400300e800744880300d50103441e003400c01d440c184005480500a100314119002d001f81d0110a582d4070000030388a1b141d980c7c0002002500901c605145860941110703d0480100045080c9555440340b041c1c17000d807052615802052041c42e1402a0540140d0103000744d420b80307074460010540c205406040c054141074841c4100d1154038900c0300551a6940410150302c01d40c41c12041c480700c103002050b10780c1a00e06000c0c190440480050040390400354544550b40141e44070442d440052a40080301002041c510845000c216003507021201d8000040000228822240e41d012a0003019100806407030019400d0b03030103040809031283c0d5440fa000078040060507082c180700070701d50569050340c40019420745081040c11120b8810382240d004605004001c000d0700c40000b19804243d80382050b000d80e45d12440028058416500144280c2c054031140e44800b0350150440054074182003814045038505207410781801c900f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 172425908 1250 172424658 172424663
    0x302010501060309021c0c090c030c09090209090c071a04120e0301050708130602040305010612021801030201020c040b1c1118090a030507031403070e010801050d020d02060d230402120604 82
    0x10b0085040603400504842c601d46e10710a03002aa4219651400c1c501107404070115040400d840b60080b40c00304d640550300000cd0040d00008600382110400440c8542c60000c10030b82c080e0a0010ba1340080c444145950300800700508030721041c13442d01c2c0c40d11800c2c40110034140004200c0c1c0107080c41c501e14060044c50300c40c030000d030750340082075640c43e21010a1440741c1d40207440c542e83c01c01000c80425000c0c080d2401031f00c49400c0d201100440c52062240c5200e052442d00d98200300d203c010700c0141c1e800715200b20720800496000c5488012034002809210000c841206510341e80c60702441048021103043c50807441c111210400900c2480c0007400d41c40c0103c40c0c0d220ba035000010b481000a0044001d003040b035000e40740682555103500311403c1140c3c010382e251004504001e40700d900a43c0d0001803240585410b65620032010312030781c00b082d00310350b054400a100c0c0e00c0109002e521100c403030b4002140070b100c00c86262149842d071080c4078000c58050300d081c2d0050307405100710034901c8000121140104ea = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 172427158 1250 172425908 172425919
    0xf0f0415030509150a09061406010207061106160908011401050109090204030506010b130e07020303040c0b040e0610030b0a09140705090d03050a031d0d08010603110703030e07030212060103030201050106030902 92
    0xf49004c91600140000b0b0124907040d9444a03c0004118607201c1d03206034003c0d01104024078203042d0300180c17030000150712081c200000c050b0303510080300380440c91f02e40188039840e0301a103005003e48182c4003e01c142e000700d8400c0d80b80a010281403082d030002e030340c1200c0c000c1e00e81c00040c0d62038030005c005a21031400007800681c4070b080100807004441d401045014009072060420b43e44600078504213902c19070300c0c01c006a00220500080c420048290002414016060342c40c0500d00114111000320051042c1e00c02d81c0400e600303040c428026001180800b00040c00003001c151540742020003411441c1040240c0002000001e0300180140104c42ca00c0500038542e10512800307540c111840c1d4003a007003000c00c00d901c509101c0000e0000350b040320068904840a020540710303603440248641c805034890000c050409042481001c800d00480e22a190140707800301d01c025140300441d142515035070000f904403900c120f01d64130800000c01e84038142c0f44280d000380701590740c4101c100d068944c071050107580513 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 172428408 1250 172427158 172427173
    0xc040b03120403080d09050111121f050603090a0b10090b0f0109050d0602070c0902070b060d021003020a05190201060807080d05030613090f0503030615070506070e060f0f0415030509 80
    0x6010744c006840c03140c0210001142c000315542d98242543c0e0f034484802e458020205907081180c0782045045c0d8040a030000d5545212000034070700c2254134a80c401d05000d0200000411428031044c05203041494014120441038101b500c0050702d00003040c8142030b1603514102e0102c5145c900071000d13112000c0d0596907031109a0821007000740812002d48215100399081000c3c100240d140d88002c80100b107441001610f0b2921810203003071011000300307094811002522002c0040e580c0d00d100d61918a054580103131030382a841810f8506124040c0c0c0791082c813841c1c100000d0441d41c1500700764161101101905c5185640e89030003507480804185840120320280005007041c100a580aa40b248a00714041000038850310388081c0210080c1c2c05a80076000042000800e007800a001404d5058414460389812400e4951075125000503040e14200135140c2c1ca505102e80d20541901e00200c184600c40b82d5a5295617101c09642e44240b09000e00e01c02c00e546000d00d0320340648030781e510896002c1c000e8442c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 172429658 1250 172428408 172428413
    0x120206150108011d09030c0f0102030609010e090a1401090b040503070c08071203030c0e060d0b09150303030a0c030b090a02041509051c020301110c0703110907020d0804050a0609050c040b03120403 86
    0x107a41c0c0013881e8281d2480140280034012500b048948c190300c03d904001030b40c908040e014000d156105802030440b040941c0b00703000e1900400140c24292a821101f2052444580f500290261485020180c42c1e805000140410303c4000b00007455128410780105085070303a110050f40c0c407481e291140c40d44040c00d1450340d50100b8041d4000551241241c90681e800780c003810300040c02900100e401a54150780c074000024a8202030b000729421402038010030002c28840d9001076682d20000b404101c610342c40e20b07022001d00c2d00a4101e102e9407000140702c0039462421540220080d00107129050b04002c2d0b100c05000784070301450000b400e840c00036204040c0300402c0000990745005509080b40c15659031546a4803214924001c0c00b001c018160140108601e1810800c40b1403034200011407090300e02c072040c00a49600001c1c0c00aa0b01d40c603080c81d84655403241072003400d04101d0a0701500c17081c100328010b0700b0408040750215585500325070070800000c40605040c1c3d91041407600300340d0390301c00704001d202 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 172430908 1250 172429658 172429709
    0x71701030b19020406030f0c090f061107050306090604050601050906130903090510020f070e151c06020310030303200a11120c03070b130803011401030912020615010801 74
    0x1400482e541c5a4000316000032007040c12a801640043c000a070395031900c1c42800c0c02c5000320340a0300c1c05894031840050501d251110052000d201d040140040b81e400294080d201303104810081200030b065485038584480000d44640040324212000e000313800000c40c00346402c6000c1c5029002c0030300394602100112a0340d20003130507210f405a061010420001a60350307034110600000c1700c1c0d0355029107422459049064a4076500e9006944c0e4140b81004121100d40300c48605c051018040b52811010b030459040c0349504601203030054080d5000104100001d080e20f402001204c2c400da0341000000c4041141c1401e01065050380e01c1c60490800070103162511850320600d2411010044d106460007250010a0781e900122828205810200d112800e001c00003804a500941c240705004002e1541c1d0348804131403005003d41e0f000700028030401c1500d64429408862010782c44007443c100030440002c00396898004070391900040012000041140d4864007800303049035100c900384012405d10a22044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 172432158 1250 172430908 172430911
    0x405061305010303020c041116030516060c03050f010b120a0203060a12060501080c0303030c0703051c0f09020f060a0507110111060f060a0906080312180f060f071701030b 75
    0x680c400c82501116111420522440d4001c0d482a00100f200184400a0106450304080e0007000182c0911803801e500c078041007000066941483c120350b135500050300c5c4010030450740e43d02a040d03e1a10399114011070b00350740505c0c0911000c059441c103d0b80d8414042c0c40324414080c1400d0886c1c040e002186a01c00107802030f58011a0042c800c00030180c448a450361650300011042d90903d4031030380100101075040c00841c3c00c00200340c01035840c620f400100030060344a181c8c4002c04214002030407041c43c41c100d075145a00b4104c8048240103000c081c1d1039210240c801c240081e071007000e00d103038469031a00d04030048032180340660702c0b540c2c02c080d50382c2c441c2070544059001d003e05004007032401303214a100a0050522a1f103100d980709580c0c0c03c01c10b00b030007091200b0b6008040300c24a802000d10400e5400030070b8401d100b0070104050007a681d1140e649072100c2da09d40404806100d03c0340090846000403c0681c810030300d0410040140d40c4102044405448411140074a00a0700d0018800320f00c10240a5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 172433408 1250 172432158 172432171
    0x6020307030c08040801110d0c020703030c12020c040c180e010f0302120f060702070e0606030c2203140a15050c0f030903160b010e060a030507050f0319030309140d0e0405 75
    0xa50805031748003030303803400c1d00c0503a40c0400f60a9000640b10740d0f10621841422041d00b120710080c00f0840c15581d014002c3d002480c00503050f00ca5202d41c0740c4440e03100b0000011620800790080c083c2d90b841d0400600708420784141071007030040c28480400d40403200c4138460b0480d0210203030840824916002d0042c1d10030102c5c08500c0364011400015a500010820b95005401c2c0d03030700401c0106c2c501000c0702920500589854072803c020428400e1303018403041500c402d41100c0e032000c040100780d00000c510441c115840246503801c40c015244040d6004204482c2d00c50242c80145c2c1003580840c10542190002c460404044505102048150544501560f070110107807040b2407a1000300c0d121000c800810200c121049045034005021000300408083e40180040d10340d82c603447e040d6a203494548215015241c061a5403055071182603501700030090352104c03c4188440c080b101410000e0180c840789006462900252601e5460184009250401c0c5074840e0303540f11206c0d20308410000075000142c000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 172434658 1250 172433408 172433423
    0xd0315030c030f0c0b0c060a0b1207032913030c1704090203251e05090d050102130602070b0d09030314130b0702010b0904110402120a021e0406020307030c 68
    0x2000140c540815007025601590b00c0e40d801442914243c002000e2540240905000c01c0c4100321980d2000900240c02141c0101c0201e441c00d120004600c54001083c02c048841c0f160020000070311422100049940c034038041c4520b0700036102c001046080d902a01c04001001c0c0c544607910200303118888410001d407003503401890395000b80749a14401d4000b90020b14000b82e00205120103021050f80c2008a90514a600442d15a02e5140a071080c21400d9118441c40d03180310b0394032186807080c2c0803200031200040c00c41c99103a0990070318034000c1d0042d840303c244a40301500d011600301e000046660440d400c00349200e00d000412042d034409441c04060480a144e21400b0442600085050442c841ca1400c0600c00829210707040c900f40104010780309400f56450b02c03003050700c940c4a0403107065110f5000300a4640250b0301c1c0020a00234850348150301000b100c99008e20120442c5600207205a00000700b400140400f20140420b10348039600c1404096803040207404000703801007071a4080719014428 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 172435908 1250 172434658 172434701
    0x405090c0a030804080601060e1e0102011806090c08070e01090c030b18150406120305030603190b040b090d12090203010b0a14010318030c0b0c2703100c020d03 70
    0x32407800100e03600125400301d4041030900c100e06040100b24014441c40c031b4502010b0920202003402000010f9100300d80146425070f0701141c0c1d000b500b0045141704204803402d032148144c1025001403020300b80c01c5600501d07030b5000054598000800c40c06840088030902020703440e1039009001005004201c106241d112283c0c0e2075259141e1081c00c580d0719010301303107408600d0329860b4070002c14090710f40d0b544518940f03841481485401c2c5c80c3d50b403480c1d40c10f0408544d691600c20001e481c10089050800081400000d2081080011344c4464042c82c81103680b1f4030240c46400c041c940391961144c00100007503550845070001c00a5400c241c565900260001071401d403040c01107400000541c104204c22410000c00c0e070903550f45885186040d03425140c2901c00b800d000d42d0006c02e0058000805800307004088003190740c0d0705845084644070b00d65410018041140e240d540c5500300754418401d40300f402408161039030803006010f00d0380d440c1c3c01ca90241500300280c4000350014101c0c24541100041c1601 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 172437158 1250 172435908 172435933
    0xf1b0b0c03010303030b010207081018081909080606100804020d05120306030c04090f030302071e060609050619030308070908152a0901080a2307020606030a0c0302040509 75
    0x1012500515440c0d110a0707480d0b0541c01c000e0705942e0650b456034115407206c03004000d0080003050040c04810100381c08510109030008070003282480d403801a104030800103420300642c080001c0121f60060075220034036216910455540c698908542480d0001819101c41841038400e080c85944548002c207000140e040c540c030b40c0c61502c184071440b41900e060001c18003101386020071030350b40842c10032507081c440e91460b07568801e503000300c03801c00405154020840408000c0500b40090007400103610325000b010450070404040d01c00740c4100d0586519242c0801e0a5081c80c070300d50b1440784680900c18015a103076a80440f0f804100801c0314080151802002c12001d0b41070196800800e0195090401030038009048541d00b4000c00306030441c40304100e401c00c0380505203415035462840900340a840359542c100210040c0010070590f14840d0380b01507000350201c0c40f445d0124040c60f455030071680383c0d0350740c2814541d4442060340040d25250000e8000c00051070079810440d4010505401c3c2c588090100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 172438408 1250 172437158 172437173
    0x8010b0904110d0c1e140901090302060c0307150207020d020d030e0604030c050901062c181303091e0e19112206050a2003041806050a05010f1b 63
    0xd9126008040d01e44505898050740076143c005416013240110000d80b030b0170300002e0143c04000b50240354070031000c140c914507a8018100c00d0000c54001c0c4c5a20356400262003183e40340d034806c5c902114042c400150f210b04c0c0c0405442541c0080754060301e0342c0b00324081502000750585440c1821400c103c6050b402583c25100c3d040900002c520803030160100ba810401009000c56050300000c08011081620f5112003860703400c21030310446088041c001e0001e0b8900480e0b0b01803184085091a483e03490140003015280f001000da003140243d480601d0540c45032448202c0c603000c80081c84407409080300500c56100c400741041d40041020755017161010405e1020015220520490780b514100440c00002043c0c0c070070b458408620600c4402c0c2c0c951030401c1d20141c010b008030110b101c10464040b05204914080307200f404a0300012000b1070b41c460342d80e407a81254400c03103001c4440d012400c0040009075800c0010021090710016110350b19600c1d54103404481c00194601414a14425001a800403e01d0b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 172439658 1250 172438408 172438417
    0x60909060f1c0201090503030a05070f0309080d050c06072c040906050903091e21030c10150509090a0807022704030323040303020309070519080105100608010b090411 73
    0x1074602050025101d0001400d085d00b640d20950090b041081049007c5500404540c0a1341e40001d03c008001c100d820200c440301c1f4950400740b0640315146044020b503800001521640d0410001c40c5c01035604e140d41120350100c102c0300e04109022000080704a00704580983c003004001807c0002c00151680700e102c26180250f07158100d980000540741c00d01d00388000d221819840c0c00c0c407039080c9115100081151000112290196016543c2c1e004c84810814003c441031249101d0454a10b07806990b0264000c04803400070080071a024180018a07040c14074449218802d00e00240140d906140c0b07510300a075200c044100da0240c40c80d90709c103860080383c0c0c1004482c02c4d40990001c5451606250180c212030101c1107403c3c6014541d240c8001c84582d003013615900030b07407500c2c0147e101d4a400008030320385203083e084617078044203040d544102c0e107040c10321400071922801d00901c45616a07890340d40090502d805000002482e100040c050304074044001d1001c1030001d0301c0002c083c1d50607403486a40b03420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 172440908 1250 172439658 172439689
    0x2150301050103050606030f04020f01030e0115050109050d0302030904020901020c1302220305061305010b121f0608070b0f072009090c2107080a12020d0c02060909060f 74
    0x88014080c80d60300d8402c031940000255006861401c5c0b1107074160a03c41d0040c070003403107207500c07a00f04c102c681d11980000301d00e20040c800034071060602541140345401a0f00416000854860000403180741c40304103181d19503055006141b408130241c0601c80654000d8651a06503c41d02c408841540c0322091419030b400610a0011385906c0604403150540400420302040e0080e00b0000f44042800800c0d150340100340c25514a82d420741e80c0c0740c201d000d000e0784180540d0007000040d66511009001c1601007071208150b00d0b400301c0003c100b0300c0c0707011503125006584095108180030b0200d10303040401821280c550421060a165903070307464690b840c03440c0d200301c090340da00300a52590f14288000b03a190000c1100001d41100550040480e1030641683c1480002c1610410900600c400034040302010700502c0068454811040c01e0010354119020002d8006106084643d0140b500c01c54900700c06035401400346140850450811004000161102e0b130f201030115001012075507070345100d890441 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 172442158 1250 172440908 172440949
    0xd170301060305010f03082208100b1201090515040501060905131203060608240d060b03060f011a0309010e0f010f060801060311040c11060408090a05060c0607030e0a02 74
    0x1030412000030b094442c1070303120384922030010006000040c0c03078000f6910118040488012440b00c903440c60021303031080d0743c08184a40604441401b103054590855021418180d4002e080b03100041501400c072502041c000c0c0c2950805000b00740030130154611150828020800443e0142d110310b5124125103081e2040f90b01c000650441404204241c1400c1410710198101000680e00e8020054440b000c024600c1000450034084c000481e0840e504480340c6103030141600401c0a85031920b14010149601da40d4032a00c150030004000e0340c0c2c6142418181e0701b19845000d1004400d003030584140d000948001c80c55501c034208401c888100300804c0d00f9901c440d000204074111401d109100711016904000807590408000780085280d100e11403600100c161800194080061800c9a0482805101003054015441400103105000000e4000d81904464484107079980f03c080200910581c1039101c001d4210400185940b4040d070b0194288a078260241d68203003019500040c40314140301f40c000b400f0b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 172443408 1250 172442158 172442161
    0xc060e090c190c1209141e06160c0e040605010503070f050402030a24150906080c09120a030905150304200a050a0308030a0f0203091c12050411031011180d1703 70
    0x1b0803801d1089a000c08013510031010443c0060200031001050910700c60140c03000281c0c004820b1a1008034001d0290040b40002c3e40b00d4944e694030707600e114190703000d54009041c14000f1407140703408500d41c401c0b21320400901008620384002e00003e074000405414000350f80d48101c02000401040c040c0700702c00e19902000b48282001f8085805515200e6000d0400c43c80340c03001e11986800c4031807203400a44046096032a5038850b00010101002010040d4081c000e501541c02010381000c051001c0e00c20442d81002d610001e171009604600046030b02070500000441444440c007803480404416210140c0f86144d5207840310041514103600e9441115034030000001c0110140b014800c4908407881484203501d507080c0185400c1d03803002c140c500e55586081d21190311812031f01a602c0e00c0000103413010144050f10307040c10084003071913105204034044d01480c0d58582c00040b2610803020304103008131030340b070a003181ca50002c0c2e600f41ea00c611a41c0c002d040f080c0c4c2c0001203071290707001e440e03030200103c2e01503030f079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 172444658 1250 172443408 172443419
    0x13080a02011b020c010e0d0c0b0a0507050c01020a08030c0715110715060302010f212901030903091707080f010203010815010b0406080703020706090c060e090c190c1209 74
    0xa104060b40d1100442d0009a03c0d544546e92040014482e07007821240c0000142c0242085e48644509501c92a448480020b03100300d0707a90004041c0040350b024106541103011100016a15080700e1100142034100400003d00389a2540300500001401410480c002061002c2c200c41190030100078010f07180404910001000f2518400100d02d14503124203109191075640041c0980410040c02c0041c17200d41007814034080203402c814415a0f5044000b8400c00300300c0d100c203400010240344581029a01c01741c07101c00d954002e00071081116450f5840070422886c055450340d112000d00100c040500400d20002100e14041100d00b6050408100041e41d0b94504289546015401020000010101c40c010042003a402050340e0443d00c40d428a01c40903900d20784224000d00c200d07038008006514080c2c1003010700c0000c8038054103940c01c40c2c03a48140c241c140410010342240807240c01400500030409118080e18555604d070214001d82843d040d080300c143c0c3e4206840f0009c81c4084001030054808100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 172445908 1250 172444658 172444691
    0x20a09061403031903020721050d2703051606240609030f0305031b0304030207080d050c031603020a0206030a0c03110306010519091706090c0a050a030b13080a0201 72
    0x6402012401140350240210802c01084071300e04c00c01d001c0c5640480c0490074890758001070011000c01004c0e034840113400a40c0a000c40c1c00410150310750311b2402c20706506465008110364446940f000c0c18006041183d07408446ca6071007044018800381c0081111030008101e4001d0b4210101c0c3c141d05141e000c0703503450400c59046042d40c481010000c010608001140d6040601c400490b014501079070359955040340003581c51010010042d0030007000040000b0f040e4003164501c103441c0380100f61403c0445000301101d00e4051084810000e800030001c2ca04081c00d154603160b1154400d0040d034150114a40001d034154004961121540d0b444000c0c643e071039513040c85251820280c420b0414103500303000c00020550b000d00e1a110320441849000c8402003400f80d4440310052804131070000c00300081c01503030707078640f1403d8410910501c6142c0d5180054500481d42c2c80a9500281000b59494074546612544a8020748040500d400e8440d800380880c04040040c00c10788119000401d41202d21100c441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 172447158 1250 172445908 172445939
    0x30d0623040b010c06051321030506011d040207051009030507030306060810090b01110d0c0506010b04060804080a050c011503020102061308030c0f0f0c0a1209140913020a0906 77
    0x2441a45402c158400700da8201000e02200d540017900064a41c0d102688114104001100501000c50003001483c54410314542c0581c0101542d90501150f1103050055507405107450200560740c4423065051542d0500768058941240904d00711403250701da0300c0c80a02111030302ca500341d0010b000060340600741074060198100a000314a016201d500c0d20b40815601c1035035500504901070b4440032005500d0307114002c21403059100700c055800041d510038015240b6000e10208407107034000d05000103068030103502540d046400580786c846551b5501e41c1c507500b0a83c05800300b00300340817003482081c81c4e0078000d200e4000d00140030381144c0801e500758000680b90403c003c021100c480d61211a180000e0034001c2680e4000410803401511092024030081c0d050140741401941508041000161048000b5a161320036018400b81018100b45801c00c9403400214015184010709803000903140342070180c0943e41c400402030300810034045540c0055800700840c0d00c58040c85032a4981404008a00380c07805 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 172448408 1250 172447158 172447229
    0x2091518011419060206040f29100605090f010809120c071403010c020d0e040f1e05010506181012020c06090d02011512020a0b0c010603030206070305011214030d06 72
    0x2c010f1503c1d206009664240c0108020120041c4104a80c10404000320304151104029120001c061a40400f680c4040b4100c40c0e20b040180600000540e0718001c0044485084001e054940d0b20721071840155250782024000d954188242044c1c039020410310f00207040c1c10811680500b0416207041000c0f41c85440c008041803090749001003404500f500026544550281400e000440043d030200003401801844032111401d41003038540c030b841c103a03400d000d9001198041c00402c4280d0300d4009110341790155903d030308203a03500300b0140c880d00e14040f500104004402c0c900098a40740b085070740b0042e41c026441c94546070f880394003440340c441d1080c4080c00c0c25a03880d100801510144540c2401e1500c054464130500ca12036111040640d241c3c41d0b04000a00309110185944070003080e2a0381c000c10f038500c0240c0050280c07001084d541846405014100c2c0d280c4001004081c00d6911044001604085040c0d0548000c20a5607e80340c00c9028410051803034945803013140404000c1300c8180c50040c00301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 172449658 1250 172448408 172448449
    0xc010305011d070504090606020304030209070305190f020412230c0a2105030703020a03090618060518120703021c0c0b0f07020414071803020915180114 67
    0x1444803580d01d000b0010420a1003840b00500c3e114020300b6145489140c100751102c500700381c400302d0b416800100410413248251000c1403141c0d2403d0040301255002d0311483d0001030f065001e141110f02c80c1d0080810250040f40043ca41640d420110250030707484e020464a01c00da40c24842c0c1141e801d401740008a103952805401038200540000303040215034019440401a0f0005c8000790300300150500000a03888001c8a5072603210b810041d40d600502481100001c040706008103000d0b02c1114403003603040d2144e00d940340050400c0c01c1982c5c0e41d00600e0940010f070a0b2034060380b2903555241120042e000106010b0110f032070450040c00703c000c0600b9400e01ea075800300158880041c00c18691101182d800010f16070300c0706c0360307969124003038800c2c0c8002a61260070059540c09800032100d01a006a04a0b20f84640901c4241003402d0b9a01ca10300c4080e41c40081e00c4005034004400c041080d07000c917001820550008880110280301100030382040f20f800c0c5110070b40c68421306003c564441c141000661 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 172450908 1250 172449658 172449661
    0x60a06030b0a021305100302130f05100c1a011503060803120403111903030204060f0c030905090c0f03010b0403061104030f020f12030d0b280504020702030f070b0c0c010305 76
    0x103464081481c041e1101160541c00910515000141340960002c0d1000821150601d440c205005010b500603036040004100150700c00118071284552a44c21210701600c103950b420821501503c581e2802842541c1e11644101059910201140c03554003034140d04030010030100c07544100900702d0b00c0f650000c40c1560300810a00201b42c41c07a00d401035200360b05203080c802129117250300b60300b0030703654060694142c000400d05208140d0035401030800e8403030950340c00130241c05156080b1034501c042000680403407042c07403062109040c488800c5a101030b0352140701c0e01d480070411826003903038800d03030064a0401c40070906204010603400713440b0003110295807450400f402d42e120703000307501d03140700c0d0080c40ba041580c101074030358a669205004d00303050082030780d885680d2071459002401c0445001440b41209000c0c00b80381c00b0040c441306070310401d443d80003840103082606100c000e5006250680e414031601e0461400354504200500c080c040c80c003012503d40d07000398801d80c42c11081882e01c1d414141090b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 172452158 1250 172450908 172450913
    0x1504050702010621020f210a05100b0a03020d0b07031b02010203041a01150c05010b1e0f03120909060a05041503030e0d080306060a0c0618050f120304020d030318060e060a0603 77
    0x1840001580801c843d5142d40d800880e1044000c0401f0070500b034100d00034580300d281400030105800300c83c0303640814140104110102040055042800000d40c445000100d640c080b1fa0b80fa2001940007410303050001e0b1500740072181d0f0ba0421000407080c1c0050790000108010000a00c03001c000840c1100c03101d00340c55042c0707440681000221065041080001c2c5200b07002c0c442c0035007009918500107441c11690b00b0481c400298070080304241d4034011981c0201e0b81100342000281d448081da40340032980d0500b4240000c20014443c0504000c0c1c0c010344032180800c003030b50303248a00c5040c0d1280a03072800b02103142d480c01900150003001c1a078803811901d00c90300c002c69001d80449a00c0381040318507594401000b04141c0d502d005003a00903010500c2c0c02c1503658214091001484050700490448030281485000b8aa841f00111400041d600d400c1c0007140c0107007410000180340e07a01c40d080c0070078010b0040120320f00505d45213000703403140d640300c4038510001c0409000c515041003007a0300604c0b00c1030541c4c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 172453408 1250 172452158 172452169
    0x303060f01080c16060e060f0405030a030b030f0d0509010f0905010903020108041a01080303240a05060903030c010203070c12020a0b07050d0609020301081b09010602060708150405070201062102 85
    0x4032040c0c1840240d00000e83c18822040445828106002002d9810003203400c0820040c0040044c88060740710301400301e1814183c94500b98801c5900c5001540b030b05521081c2100075101c07141c070003034040c85540e250300039806007400005001507055036403940310b904400c0010400e400d0030720314000780880c240c028006640c0c010701e0f5409681d02820885202d44036860002000c0586003101d0b04980c803d40000708900d0008030003140142e003680071043c0000000c1e807010420300c100c0348045500c010102c00810050401c04003038807943c40002c3c181c170305041921115a099a0003110641d0000e800d080051042007403500c03850740d00c0d10b01440107001840c11079440d0488150040d160405109021500e060044072540007000034084e9030301c0039902c95030b60310446583c030201c3c2e114040c1c8425020701d201e28281885501c1c18121442e41d80249810340b038840742038943c560017421040c01c0d6403d079114039030903071128011103004181d140d00000d2811326000d003480550701b481c80c01003041070000f00700d5809a03441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 172454658 1250 172453408 172453429
    0x70302060412050904020703021f0b1c050c0907020114070305280b031501090e060f07110a020a1410030209011d0604090501121403160b04030c0209010b1308030306 72
    0x1000810321508a0543d100d000708141c059200d800042d9540800d80c9c080f0300b800300420203500300480d40070413000c0d00083d2a046240381d50482c030f03003054060000c145051a501e0340c0d8003910540c0c4a10009002099550340d0031114000940c2d1642180d048d82ca80c840341c41a4000b81134070342003202d030814840300c81c100020392a800400b1809500300c114025a01d901c10504450024102c80c4036601c40481004180070911810424620b4082c54071f00c05480800c0c0b10f44603003541158404181d687c02c5050b103e0000c25585800144201d94040340184c131280224009404207800030540d1503080b504101c28401340007032040030180140315000c2140d07003200c92541810040d80000c2d07805402d050105089000740e0341b00004032402c01e4000184140c40c5a682c01c020750068180c00c00d840e0001810300d503a0301c5a5000815440d01c820400c4000c00c0424250700d40041c8245008403085003da0001440ca180a8004408806000803580d110030012039803a001440c40300d0140d030651400c80005114074071b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 172455908 1250 172454658 172454663
    0xf09070804021302040620070503030405010f09090207080c0c0a0503071214060c0310060509030706050f160b0601121119110102130e01060305040c03110301090501050a0504060b060703020604 84
    0x24a080807030115941ca01448110303808a440071900c503a56100f004010b103a007040b07954941001402c40e49182e840c0031410300c05030381001d130040d890980ba1800440d1401c6051141c03804000b5140000b04605a05000a0449500501c100368641d1040081142040e03418600d03d4444c3c281c0c044204140d032004201c0354121211140780c00c3e0290180d04102e088081403141200881c081c1c0c0c0100040709810314080d6001d01d1481d482c40100c5a1100c40c1680c1520a240a036981944254000c000c06c40c0714100918a002381c0c00e121a08040e00c02000300c45421582200f00c0e007204a0000300311003035074007107025402c0c4000c0000038045e40d51000c503450b003580702c0d4181840918400c002c54140c0c01d400340004200700c003400c2000719030787d243c40c11320158801114003604043c104a9400040c4062190081b180200c0d0442c2506607003c0c41c3d6510000b4110300110025050354903005000042202803052a00c14020003102085a140c580791807003ca80d1144045441000144807580100e680001e00131350155 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 172457158 1250 172455908 172455917
    0x4020901051302130306060303090b071a0a06050618090a110f1b0f0a0510060b1b121305030606060a020307110114040320040c02030d050618090604110f0907 69
    0x3826020340b00079200390044160b4419030120004104080341e40301c0c1c02184d00070b954035000c054941c00046600c0c49040c0020b0110907005a40301e41c0325107180030a5410411200e0000f440d40e03074400100303005800a405062018081440010312030810400213640240002002c201018a000c044081405680076101344180089680c0221440b903804000a41c2851411030341b003100ba840d82c1c1941c88400c1c0400300c4450044144a010080950241c0004d960034504101c3c1440c1007001a800c041021313240406292054001e07a0f0060550304000300101e515034051400028144801e061a1481c044c005030b002d03e00411807843c010317502200382c0d80d44960244d44003001d910b01e0070040703407102c40c4003403540301003200003400004101c440d0490040a84102500c001d0000b4114108401c44a2000109015820030000384024504507400b0660011000308621040020041d0500b80350000b2079840050343d0000e41804107108000088041c0300a04882c0528200c4100c0c010406800707010300070381c0c1440b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 172458408 1250 172457158 172457179
    0x3011b140903010213140409030804021003061a0903012307180e010909060e011b12060e1501140a0e04020901111006050a08031e13090c03060501030605090402090105 73
    0x122000d4119409003400034000e40d1512020b03034940341140002e00c038000b100c0800380c81001090426025200107160551503030f80595541e5024044c03507024500314170080654504000c107c1c00003c400a642c018035264115856603441800e040c00c4884259150003c12900310316840ea40c102102c006610101c1c62501d450140d4101038a50360344a1140c0000e03044418100000c2044c580680c0121410350145905002d40c0e1044400503080740c1040490002107040d06c1e500d4642c0c1409900c1c110032403020790000040c415610800045500c100343c840020318409020519002c0d80c2c031000300c2074030b4515501c3d01454941d0b416070240c079000e0200010390080fa004105818140e016800c1d1240b4a5518026124801d50020120000700081d008680c420300348101c0c085661200003040c2c1d45041e21000303085000024581c10403009402c10481035202606132100403c406a07640110a8940c016490109585041000141c05d07170702d40d6000b10380122124420080940d030340583c082d045500660342c40056 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 172459658 1250 172458408 172458437
    0x50108010b0a0e13060b130e0709060e030c03010509030307020d0503090c0d0312090f02120a02030307060902041517120304050d03050a0b1507050105012414091206070e03011b 77
    0x8404040d80d213400c2460314000050351000c0070f004006404d0558490041c141c1c0b581d620000d04070040e154540000c0e1050000e01c03400b0b01802c0b40019141009084174040c5514100081c29a00110352175800e54202000740500d59404004a141440c03480c00d0141c210f1904001e00e558554001c0c0046200d50783c005940b0b0107150003081e0b0622540d05090b024000caa8490900014950300d05204034060368941001628030000030a041c10700c0e5600502440c90002161100c40c040c0a80390703400c0c1c0e0300640c0c0e0346030b00740700101c04024040200010380c00001da02e80d1500490b401c140c0302106080c81d0035800c00400c4005103002c00d040003280c8450400113001d4071601800c0005000d41114640c1046a0500c00750301004548064040d051245000344441c2c0e80b1201c031880044080412165030000c0819900580d501440100103481e1a2412041c200f400c2c5900007007844021a030600765030340190050140f41a032081402c040c414065000b072107940700a50b10010007826283c2c0c814100021075014510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 172460908 1250 172459658 172459669
    0x121a030d0c0303150902031e01050f040911040212100e0115050a201b1c02090c16061a01211509020a02010b1e061806131707050108010b0a0e 62
    0x4540225090145440c3e891700c5c2000700070b61090307a03014035680d20407800c0c01e451103120184038140c501c06080395038000489414003001d08100c803401c83d000c03140e07990454001d031034500c050103242000d041c01740707540d080440501d03c0540305500000741540030b0708018010840c3c3c0da021403140c04214039085030b540e071881d0002c40c6c0e040a0240c0e01c05c0c01c007442d41001c1c0c10a40d4001307400300c019403141555600749102d1000300503508100c80e01c00c004680c9007104110251a01c00007040c1c1c04035940100918243c0302c00201038468607000d800700c417210707954150a65001503040000a4414007030030a001001c0301c1c204845010303100016085002500c456104260122080100c4020b081d030750001d6413100c06031364010740640a00003d40340503503e801031a20745042070309541403509101900b07080c45e1a03400803400f013014085c140501d410581c00c00580920514004510000b803032017107000c0a0303410600480b24240340c40380d4002410841c0c0e48006201b40180442200c0f9903560909002a0509038680402c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 172462158 1250 172460908 172460921
    0x40c110a0c0515030603150712050c0a03060e100b0c030c0303010b180d032001060e041202010c0c0c090203040305071e021003020f0d05150a180c0f021504020402090301020703121a030d0c0303 84
    0x5043d5401e01050168080b042c2f00508a08003c5440a00c01640c690440c0e84800784100c44443c20703120101c41c10000f001c1c1d01c0004000c40307413000d01564900100102040c1ca194401e03440700c3c0740210001100c44220034040c00d0740d07071030000486814420745003684004107a2070340703041045183d00d1594886a4400c5003540030800a0101d00340c451a24075250130494002108000020095401c0115000b0014440c1d2000d01d507803a8440c03003854045080c601050000e4000030001c80900004100402c0401c1d405852111040d40c0c203c0f0103440f409141c41030060480c00d615010040c98014020413407040c88020a548982c0b800040000c3c0990740c0031040340e159560b1242e40c81c1c0280d140580802d51440c814a014481e070341000050041c115900004c840c11600c203000d20006800401211025000d0000300d2600030b8002040582052901000a400caa1042100320f0209c1c400c01b0a01039040502e0182c00300014101c4100c103650450000031944032190070208030200702e1f020003070004045c0641c0c0601d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 172463408 1250 172462158 172462187
    0x606090a0e0f06041505010501080103030809100207050c030c330706020a0f09140a0605030a0902040f0b0a05040b030307080a05120109061d070509040c110a0c05150306031507 77
    0x9075054011002d5050300e440d41540c041c1d800030100400da03041e03e100b40c0100c1c0c0c104e460694030382c00c05030719644085900c070354040d10b13000d101d0041002d440740710005030000e45030a0303001e04c4c0544407c0c0c003ca000c1500c0e1681070156203018640741d10070344610344a607001e6000c0b200c81da07080c86e00000d04032040455540c0300d108002042c00f4070101d038003503040d035100b00303405210b9101c0e440b841c14007501c3d140307080c1411075010300d06a8841081103090011301d225070302641d0400d44400d8003240c4e02505a001906568050076420300c400c0e500c002e500301900c0c00038070b188001c0a081e82c08100394181400841d4070780c41a150007074655040044c6100402d03100c5c10480d208181c96084440c1c1a58490051101512aa1045110f40f40500c400103160592260200b4055210358442e1445c10100400b0f0201400d9012a0202030007004500c081c1021005d1003401c008500c10b00c1c0791711a41c1c0c100310402c0283c0d2020b600c0750410140c01c0c010400a6100050108003901103480c070740c007841d40c03240310440300c078211500c69 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 172464658 1250 172463408 172463413
    0xf070f120302030402210a03030c17010801020c0c06031506072904150c0e01030b012d02061e0a1a0d03020708060903070c030206070c0e07081f080606090a0e 69
    0x1500c0c49645540598003030782c03003240d4001c4400d0390355290188543d904071107100301c4e401070454140000d0007544800b10309217417030030101c84001c110300121a100d0000d9011802e541d40016000c12386100600c401009803004848450440c204080c03104016030170025058040c030300c00554041880700040d400354000c0c0b00c125138030107a1030411001c406010710a0707400700d0701070704400354012070080b4502030140303088000d0766011407040d410070046000e0f0002d098414188030343d820200c2d0110072100c848808220403660b070b080503a14240002850001c00030842e0f000310660a401e00031298808040c25008003c0c401e0100e00d50040c803001001c01c42000d021281c1c045929014101050340211b4664216091601580c200e6598140c450762240b060b0140100854613040f0140014903191b000340c40c0c00c41c051140e010b000740c0c030f90038100071400040c0c45030404201d1080030031401d03045440044c2031280200c185080c06a161585580d91800041d02c02440b55158500140004005038810490b0036100001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 172465908 1250 172464658 172464683
    0xb190b09012702040b03272b0c02090c090a0f090510051c15091407080c040207110409050c15040914011a0307050c07141002120f070f 59
    0x400050504420303080d4012590051019400310302d0074070a03203080780e8058035160324607903c0f200766010201e8072400606441c00080d01c99210400108002400c0c92500e1400008502680089007070300300218401004224185122030016140c0300d43c426000003600d440305444000110000d103080c00305800c0010412003882002804111641000b80141480c009401c0d145881d801800f1b00c1e40007070701d03038030348644880c2440100003044988260390070301090301d0014a1614959a241c103c0072498440c070300d80e40c045001030011003001d100b850b4140740e003143c0441c0b800c400c82d55101880000240349034071550740c4455200600c101440003a041003c0101031102c012500c101400307070b0390460f028030102c0c01d19101c4070301d1084a649031010305031640d41c2810851080421000442e6601c020450f0ac2048414096010013040401005010707002107092110740d0b092010501004a00c10b400990442d4022000055120603220448040c04904114990341c0e82282c28845d505105046005221141c01e25 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 172467158 1250 172465908 172465919
    0x901140c04150c0c140d1b060f0f020a0b0c07060501030c0f0501090302062a070902030a11130605090111070b2a061513090308180a0b190b0901 63
    0x40200240c03191070940b041511044441203a9600d000d81000b000c0e50f0844c0b205010b45442e0321602d414203100200310074040c5541c1d65440f000441003810b200d0f2001204441840115049641d0a130503d01360301c4c001202c80c0180ea0000d55401c00c07100040c0800580c04d01007201e10424000b142d4070721341c11031424045940d5034076025150720550301c02c49008242240340401c9661080c181481102e800a01072420301e1406150611003400c508070958044c0c600103000720030240c090001c00001c101001d80140c0703c0c9002511801520006034807190746840c100410505281c46128203001e45e4082c1c41e020340c5030044c800061740c000250003102e4609210b81c401c00540200c8800007080059403011080aa03000d54540144a45e0500800301d40c081c0c00400000f140d80c00a03003d1a50304403001810082c16801e000240412102504801e80c00503038904200f08100000e0441d8119000615008103410f000c1c94031410303903c20018143c9100e103448070000000120403504640c4981400030801180c959491 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 172468408 1250 172467158 172467181
    0xb0d020603130b01060507030504140111070609080d051c0b1306032010020d050a030207150f050f07050a08090a0c060206190513141015081b01020c09090114 69
    0x9010843d44880d4035000030804038070030001e0302c2d011640340d1030b8281024202014040d03440f100090702410007251401d0b400450004000c004024007003a100c13440103a042c0040740f070800580901090a020b001c0100000100e0303a00b0039411b0007884130300c0010345004150001040d81901905120700107007014000710038014000c20076009005c106441c0a50903980d0000d104402050030300b2080560000500c035444503000703038024980c004403454010302e04102641c0ea07100f840000c0b09000006075541c603031408400348522a06400c00c05440348001d0610b48406d0042a034407c890607a0b00300981030011814181040002024441d44aa0105000d94441400a503510001c5424040702111481e002d10002d0040c030400b4041c1c0d02c02d400e014200d040c603446140c0449801001d140852103004120b0709000018030071290f4005041000d0380c1980e241c0740c800d5182480d440e82a0071300d0303460400c081c0388076a0001284010004241c81446581e6205e9100d14010a0b442d91580c0d00c4034400c40822025580e00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 172469658 1250 172468408 172468441
    0x140a030b0c09030708010507050909090a05030a0906020c0321070c050402030108150705030411010f1e0503010f0803030108030405041d06090d031a031e0c04060b1305030d050d0b0d020603 82
    0x640854444c29503401d1918280c40082d40d082c1d010480c10403440d4094246540c485601140100491b03446012507501c071451035010003410000604114406e1002540c180300044000714202c004000414980252502080f14884050984440010010100040002c800c00140001403045440c1c2d03035251310035520340d00712000c1c91901036004000103480318003038000e581c0110342002c4107003031003803864005443c101031807e001d40500c500c0240e100324451240d8550085440760780c1c2c8840d141e5244c031046541c1100103401041090f0400e10040c0b208903000000d8400302c601c2201d0108001c40e03204a403081f0070071070101d00c3d0038a0081208101c002c000010304104130420a0f501000310385119120020b0b8940c101766813643c10b1300302c1d028003d4607051069050b8861007800e07080c0c503504449480024100c070307903561240d01001c42c0402d01e02402c1522401c2840109400d50180055a00d00e090007050703440f4500070200c14564490140b07a507074581c05030044203664007800b156500e0034800e0000d00448030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 172470908 1250 172469658 172469677
    0x601120e0f0c0604030f03030902040b040516080601020d02031218030a0309030914030d0e06160f06050106030b030307080703030b040c0e0a0911180301151d0a0204030804140a030b0c 80
    0x203040100702e503505040c801c6804581d0020412100c1c920b041d46c049002d03084c0c03110709030707485500c42d04241d516a0300c6108080c090008062445000900ca020180003000c00400b018150b4009403200d0035850307000301c00c80b078100c4400d00f0348582c1e0b5620b5280000154107060312010700c1d84000b00d42003004039015400398440c40c1c0a52103030300c04681e80b419003031031125010154a425804c52103000c42001d009904040704a00014925418a5100e4040c0840c0d10040c0b08261400d40621100f00c1c10b00910b80300e80c6000d82481d1a05011100384080441d44c0d038480c3c0d4074028080d03240040c118050611079441041c3c1c1e104002c005001c0d00d0b286500081443c1c000c81c0d0140c0c8101c10446000421031004d104110980503445115400c09a1805c0c0501c0300898041a031900342d52941c030345200e2000060049006010480721602028480b0104044010300051100c00581d20400041c000301d40254281c408848180cac0c07242106124034404a030100505502c001d001c05940802d20000c0d80000000e40080310 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 172472158 1250 172470908 172470913
    0x504080d0b03070f090c0e100906080609040f03230d020406032d0209030313060c0311070806010b07050c152113020409050a0503070305280909050601120e0f 69
    0x304100c1c1055152042403240000318800c8290030030030702e8000d4100c44840005814490322210201300800d00b9100320381010000124001014001c4c1da0b002181590810f80c250750481c41803426540f159400b440f801d41c06400d00c11040002110046050078107601d00310010071240e190407401c50a000a50003501942c3e021905044101501c0c0b4660070000100c80391100b00c02210741c142c0e0401c40005e40c4840d072100e0b054001042500c0b0507072002800c110080c06140c0e01d4440794205810700801c0b1101002c903605050308202e40401c03261000042d141d056503480d030802991410300349400c514040c2c1d4030f09403903000b00301c0130101c0310716402e003501a104111a105502c41808a5004134240c030100c1224204080007400040340050300307083d44070107203003407240c411605541105e03181c59203540c0121004400141c0c000800c4401142c2c15046c0300502048141195810f104019002d04607c6090048644072030340c5000140250703114060400050710b120b4810415591340300a65a1100e00311040750003240f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 172473408 1250 172472158 172472171
    0xe1b04080a0201120911041d0102040b07260301091107050a0b07110106051c1a04080415080606070201030b01180605070c05010c1a090307020909060601030518030a0c0c03060504080d 80
    0x500300c030b01032620071503480142403e900c217046c4108801000001070075100d8440e06000e1040d001424402400501000c1e20f00d60344030305041c500b034001003031010881e6500b0b844441c0b0134045041c81c3c0043d02e05541030f1050208034910f0380c1228a1082c000d04030003414601c104603c00b0140403003d04024000c2c2217a648a843c5808030300c03402402d032071081c801d0681020301c2d900014045d0380780340400d84083c0d01c01d0300341141400021108108624041d0b81c00d42e5000c80004003040b03070b00c00071511004640c034681400002481c2100004441e4010340740060305040d15011012400c1e84610045d0003e1001041d0000c1d20a481d01030041440e040b034402240c0410386950089100c1d030092040c00102c7d54405100341480c0c42014840c0c10314440500a1a820310081c8048001a564802090310a20034403000f4481440c1003000103054035006405010580a10700e410180180c001c0121118070720141022130324018545810f40c15a4000e40c07001d05014038120034042000100002013561080f07001091105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 172474658 1250 172473408 172473437
    0x2090909030307090b09061207200105040b18011401080d03051f0302060d110403081909060e06070311010905030c1b01050a30020306010906080606040e1b04080a0201 73
    0x40c2d21065840c4000302d80d1034002000480050fa006003044030b40a000142030088104000300c910070140d03648000705010100ca414013440519030300c010086000001d010034245610b03051070786003000c2d000440c403d491510400c120744007500900d0940c0741c007a5501ca03071980d650408070b4940400e1500030340044d0900c07001c501c1c00d0018090070303a440402000035180e41441c0d5801c000d0b590b4040c10f2940101d54682c80102038031845030002e000151b00400031556a50251000100c481e9901c8001c601401003e203418803110394003030650b9000c0e08060711106d5880e9840c4c03d050760341c0b02c203105090a5179070030142e0300810442c000c0f01912051403080200d0b95050325041070311481110760321800307002410600042c0d0095104103102141190801000003c4440c41c0b600145602545d5101c0318900d0380020600015503031010080000308001e190140341e5041c4840059924420b40c030403032542407610b0012605a440c00c036185c0a100322507840382c65a44c5d0356040025220207000c01c0a90210708815039101c003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 172475908 1250 172474658 172474663
    0x20c0915040b03010506100305070903050d02101d0d031d031803120315060304030c1208010e06010e030c13060e040506041106030402010215041403071103070b0a08010b0a180902090909 81
    0x982c20047c28210200121503040b0002c1200604400400c90003000010201c0e41c00e028240030f03902564060b04030005850305000c02c1c0d803800ca03c51652504449030341c0d4044400403039806884402c0e4a00407032803446005800c1503440024a402c1008e000008080890003e000c0c04000d0803003081d42503c0c00527070304141c01801d500084610207007240404e42005803d2410310b0085078068403d0414400101e4903854165065440c1c594820214084400600503050041c0007540d204c0003d00c0e241e6901815030340442e8990000019003801009414440584090f041e00000040d2000011150341850325080c1030f0b6842d142580d0644030a07001c00d90038449800d00350216407245406030014030540c00070160000a60700000d10a8038008845038403e001ca101c10b00040034103501030104070100000040c101401e0400661244240103420031a000d85540c0000c0c0c0c01d07045030796088101e13031262400c81059900340418500c0d00343d5800c01000201b000e42e515409428954800d0b2841c00c2c85941c0e822490341d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 172477158 1250 172475908 172475911
    0xa060c020303030403080405120304050c0a081902060f0c060903070c0503010908121b130602010e0708150a270b06120c1309050708010617030304030906030b01020c0915040b030105 79
    0x307400d038100b00002000700c0d0103510180c0e0010301c07440c11030302a0212089070802ca5001514201d410390010f200b0a062868280c0b00c04020b024240080c00f4110401e401d8490740181c0d40000900480c00480e4600561403800240c44030540d00c41c0c1510a50701e07208103030a460f60b01c1000121154807400c4c2010a05040500c00c000c0c3c85503109070054074040381c2200c08481e1110041c900e011202c245142c0f01018400390019209847c0c8882c0d025003c03e080000117400d41314400364400769580241c1040020100020b4426031880d8009058262038030b441d410903010708124a0b04481c01c44c0701128554811040e108003544090154428071880d443e4003007080707058005800044569840038854103090301d481c100303d824117555031900080c000c866966030303400c0000c903911581c400d943d64481000400d0040c88503a03001500728000d1469850300b039801070561031182c0112400c040d640c0703100c035090343d000708402c1e420302d1001402c95050f85441e05a88065925604445000d00d081548500762410b0500034103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 172478408 1250 172477158 172477163
    0x10c2106050d03110f070306050108070501170708100812030115020c010e0111070509040605060319051b01050d050a1b02071202060d02090612150a030210180b180a060c 74
    0x15050000070307141100c07034013a2410b410300d060151000740b01842c076042000d0b80045205140104580d85041d860314105202c80d4040d03410700080d0303e8003803000d000c03034071520360300c00f0481c1400e090a4031158800c801d50725003a0010100340c40743c94010101e041403400598104d490710303c9018a0064030b500202d8603101d40009090204d107044440454035805001c40a0340c02810f581210b08181d83ca40c0010030000c0e00b17850079144140da071020710806040901141810140201709034407251056960a40d9942141300c10b94030310101441c11140680c440e000700e8140c00c0a003031051216052241200004000304c45d0311810643c600500c008802c0e0006c139a580440c0d00740714280c000700d5042d80034411640d01880b0641300c913680c01c210b000700d81da603000c014081644142e01c0e019424980740081d401e4020071080c0d00c81c82a044d4000c1000144c0ea440080020345020786402c00c6568132500c00680350f40201d401960361403c0c0411084602c0160301400c4141c010701305c0d40c861803039590703e405807031074106400c01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 172479658 1250 172478408 172478419
    0x204150e0a0f06210f140d0504090f02030f0117070510050a0f0e060d1503120f080705070c030f0201110d0e0f0607050d080912040312080f0610030e0f010c210605 71
    0xf0300d0042140c000302c411440d40030701b846003089080e01514a0501c1e04d04003d103804a8030100c3d082c80055518450440c00100c000c0c8210b00d0b60901d17940f1100c04210500c0303a541842c6034000c113032600d20f1003407011f07074000c00000c0d101350f10191034581d01400507003040113410300103442802e41c01e654a20a240c510492007000c3c00c468609004420302c03034041e05e010502007039000941e120001c001240b001d40b17904140380d1a40c50100039414664001d00301e10000e007204080080c24010400402c004a641c1003c89501c000f0309024586184010f030b0703584060000421060080c5011480802d81012400003008821908a20816070300c400f0480140160107016100da8000e06010703081901500d034003034215510b001101c0d0100e40088144030140d21540003100d0700d169803046200b0142c0c104101a40000c60110b20306242c0c078280010482c0c3c0f079840030302502095180d8a040c80703040d50504c0b1000601c074a18009200c0c11034800809490001054403004c0e1084002020882ea00309500c10102600e4000780b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 172480908 1250 172479658 172479719
    0x151a010309030c020a0905010e01092003040213140a0b01020a0b2a030103050c13021912020909040b010302090f25260105040e07060207030204150e0a0f06 68
    0x110020149104102c05010103150741c40056500d0410754001048004070100312517041c00c040844403101039100082c0b25081000001348003443c2d45801600c107412074006610396a8a0000402c05840f0b00c4440a060f40303468481681c045140421610404d00d0920602c0307488448e50049a88600b5400041d04107010b400c08a650b83c2603444103800c9904100c0001d03d4500000281002c0ca81d0080c0c0c0100c03920b5201500d002c5060070200320040d044140c800b0214100b81840020100104010105004100c01000180e0030f41207903505070740021780060a240458580b030307d003008600d0001e01041e40700e4080100010600564948600e00c03940304224009410300d0b10034030011145200d600c0700c1043c025000c2c05c140d02000680303800c4244a0000c1a000f001d075251038280412141011000c00c0c40b80c0080c00f09001c103175000030394801165410343d000103d0b081090310400f0444d400c0d0b000502941809020b2010103140d0382c00c04c4a0707100700c000040041940d5192001c41030910014281100b150a90 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 172482014 1106 172480908 172480961
    0x1090503210702040221100b040513050a0f0e06011a0c190305191d0306070906050d0902100f080604090209010303200607020d02100b031e030d140415 66
    0x41007035262504100c003141090004801100350bc40e141c2d800328018041e03960002000030f40183c400c00c07003602c0b90300c405070b1918428420382c524007111048219420f43c008003114071508240d4020403000703034030200c003191584900d07d0079001c0c8403052001414080b01d01003c44024480350787c4148c100c5906900002c159030b017120700c15000e940b203e0200041e0f1500201440103403006402c0080d1501c21840e6018040c0107281002904020001c0e402c040d1940c0000718220200580c0e05c802e0417a59585040c00111010710b0000f81d48612003800410110703005500423013086110b00d001510034034203100c1d81c0d480c2410586d144001a8011070f03c4802403a810702c0f95000760709070740800b4003001e010700e00026500c01003004500504440306420034000c041c200100c481100107170000340b1034144400800c181106085405640c20320b00015442c2d0f06c1e01d0244101030380132602140700d0380081103c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 172302158 172482014 := by
  have h0 := BRFrame.cov_init 172302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 172302158 ≤ n) (h2 : n < 172482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
