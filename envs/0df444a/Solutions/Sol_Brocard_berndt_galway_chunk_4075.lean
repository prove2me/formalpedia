-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4075
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:46.393414+00:00
-- url     : https://prove2.me/submissions/6c9131d6-e38d-4405-80b1-c77c9d9194d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 732733812 ≤ n < 732913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 732735062 1250 732733812 732733831
    0x90d1404051c120c030f050f0d0f0608010f0f14090c060304031205070504231c1e060501031712240a0b030a060e091015170d12090b 58
    0x4038158207001d181d00e0700c0d02c0558030440c031083d42e00d840d030001000b5089280b030071130001d000d000c0d04615540c414000d03913510303072900180f0034640408109144000c0000c0c0740d00c00d80d42e585030900021508420f00c26240388804081001c281510040d04031412a4854407010300000310503018401120000148041200c1054402c1a6a500c8904099440c001d0000780003034001c0c2010108030030310354000042e104641402d07c0310400001800740f0f08080104002c08560444c1c1c0113042c2c2c186600f0411010028540104100d0451281b4191000580c81d810302c02582c0301501c410040081058400400d0a0128107002c014103050928031481d488040150451100000e000c9202226642c810074070303100118000c103211005592010202d10303580088030440c5205190540004000d0801c4034154410400304000c0c0290000d1042c41c04010020aa51140388100d0744202065200341d5103644120401a040180301c0c40a00400c028250040703503400c031402c28204034480c00010340c0c908075140c1058494 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 732736312 1250 732735062 732735079
    0x7030c020d120504031a0f150d150218030d02030f0f0f16150c12110408030c1c2a05010b060f042405040b09130c08090d140405 56
    0x14000108044400d100241c02156442c400340e0300e16400030003c008903485103025044c0780050581c42a440407080b03a01c007144004040c0002c0c80a0242c0380d8032109007500400c100034840701034648a50302d0001e0340e00405407aa000279005a81c0404200051401e54100c00a00002444100c000d460b4040e861002d0071510000c1007140c031210402055401000400760060f071203540c03c0c2e040c0c0003000183d50060360405401e03010400b219442c2d000b440040340c00ca880d00a1a200440a158010000c201360104501c0c1c1c02d11011070000010310003080c0c251048801030a1894180c084032a50003901d070b01e11030071b0107096282201242445419031400300364003d070040501c0200e0410038003402160a42582c040d000184440c000303481c030000361056510411400503c1c000280c01c0a00c1c50741000381181c00700300203204c2000a070400900a1101080160050182d004a48e4540081d02d400400c1400825590b00030482c548108011084001280d0b282441c2010a00c00d00c42c10944114040c60317000e000704 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 732737562 1250 732736312 732736337
    0xd060e090106031a060607060c02060a0e010b0609060c010603141c0504050109140307050901091d28060e0a03091e0326040b0c01090215070b0f0411090f09010e01110703 74
    0x41c40d050301c20b003e40003801800281e2745883c2c003c1d1509021140da1030301d0781c0340a20341e611310b000c1440b40d000c0110300981858604403410042010540107d80d803a20f01d99212400400043c3c24446030110401c01c0c1c90040c50500e2808400d03001961400143d102041030034441000543c3e40507010108490001c0000c0b0017568044000c2030600c05541c1206030080c0c50040002031007401544064180e44080c11001e0600c0e611804860302c522107941c0968a0120392900703004181c49481d000708481e0311420740082c091000344d40a50400c452040c0980100b80e821504000417080041c90100c00b010882c0c810303400a05542d2040030303101c90540c040003c014405c0300354140f04c0210088034080c7c40c100c0302940d164032510204a003e44541d9004a00a10304403802c0091480c185099440e4158084988000c90b61500485054118020010381c0e41c034825405405840d2104400d1030301604030303072030207551910b0041c1c0d00d1401d444120000680503071600c424610400303d2002900c805030b9142c5000003010703c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 732738812 1250 732737562 732737569
    0x402120a0515011e1a03090f060703020318150a050705090301020f040303090b131806120c031e0203060f0709050303040801060e0c070206070312020d020d060e090106031a06 76
    0x20a140180540301e00881c402c80b2200b0070360360340d040b11a01da1148459099206113080c09020f5486a24402801120200d0480f072681d005913511103461804c980700796482d112820700e800416611903001c2076000040c0061a074100601a000180e040d00404480103040c070601c1d205400101042c030303100e588001180c0e10903c01c000b1110f030703104000c1c02992590356030301407001070313900c144000c0b40400c000c050b000800c001c005050307940c030704803007000c890400d4136006c440c2000c00344c2c140285110603954030300407500e01d00041440d4161800b40c61109070540c114900507500c0e0150240741c8194000304444100140d41c00101c0b030750f010800300101442c9840703100042d030711200c00c0e4200d42c0d03043c0004940810f1210055008804403110650001000e44070000c050400d40b0990b40080d400031001c1000c203001c6802803c00003070f0100b00c10001803400d2aa0f40c03515040760885c80070614400c0e1510310030810761002142e8581c025401c1002000500d2a541c0d030104505611000d0040500d008800910700343d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 732740062 1250 732738812 732738823
    0x11090106020d211122151107052106090714010c02031501030f0b16050403060b1503010909110f060318100903081f060503060d06150b0309060f0f040212 67
    0x1078100020302c10030004490780a513039000b0031000700b0740340c0280081c0b1650582400d042400c42e5000040034a5420b101d04041714122000714165000740b10782d1500080c0da4495803c0c01456031403205140e02903060400c411400d001c1c0280813207901d503021000c280f100811610016071080c0c0242003584840c03207144003190801c3c03001c0601110700b04036140000207011402c80f01d81001ca01c1046800026a201c001c1d10304043c0c09055400c00140c0e050106000080c02540210000301c402030a28070010070200088a1a0b84242c01601c909600c452000c0d040146400050031051021518800d0041c0c001c008200386000c020312500c1100f17490003500103505003e000f170400140d120402803202c01850b04000c1e192940c160342e442010040ca0401700e03e103154441c1c0356010360b020303540d80d00d241d0b48500080103046042e41200342e800964a50300d40c072029140c113600c48010405141c4180e240d103402070f029810894010071400350071129808104540f10b581c4280380c4c0c49503046580300d09081b00c044030246040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 732741312 1250 732740062 732740117
    0x1b0705030102030703020c0706030c050a0309050309040504080a0e030a081905070602070f0c0b2109120c0604020117040b040f1403030708102c06011e0503010311090106020d 76
    0x1944000f080c00440355042e0010002c10a910081303d081c00d07a501c400700e007150228404000003403828401c00c02c0291090b00080701e09406030080300d080149180014003111000e0b5007c0752049000124900c0140d00085140d08070032044015040b090626240c048161040d1800e003007142c00300164074206517001d20152081d10703801040031910340034245051103040341030354400d442e242da440c00c000524001c050116030350440501c0c0d030940f403000e100c0e002a11031107016203406030602908071900f140b4022030014181c507824010044c2030a082500014040300003040d1500c0145180d4000c01c0049259105503c0c0c0241e40310510070010607240c180001c02c0c00d01e40f2070785c2d00345010001c10b0001d100d50224000c1d010302100c607505800c10f59182c080302c2492080501200d100030202202c0d03a802e00007102c100e503110740d040c1030541c0d80c0400c815031087d10b50030080140003c104041300520504c00e06800c0c915110500395034842c119410f02c50080d5403032a104000e80c00b000826040d1800c42c00c030080c0d02c040030303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 732742562 1250 732741312 732741319
    0x6040e07031203090203070e0108100b0f060f1b070506161506080f10021c050408040e0103030207080111040b220503010203011241010e15060112111b0705 68
    0x81c01c03403400300140540181c1c51300b42d120740710b07250020a14a0829014504940c4024002c0108145001e41c0001610b152240c003644441c1d401e50b82c103019241c1c500141121140890300701d035606507d922404001c17402d507440501c56400003400380499180c000c00c80c0d40070184450f01c501c910500d454032080c1480c1c4203c241c403542e404d1200000c1e0349040010602c042880d80015103100450701008501240210a5055500220b050000030703d6001030b886560854054680d043c40c0607141c482c440840007007079100300c00580c1b1191007080024403c0c4119414002400c882614007480c1001d0301500f4000c6040c80102c40a81d80e05c80e0b2500021710140c031004120107002951290f03500c2040b43d4081c451705800740e0b200181265402c0c0c0b04241c00e095001d901c201c10000041e41c20fa10005030000300c2009885501542d680c502d000e400401c01c00540070104e903060a030f000589403031400100000d1003c202550340500300f05190080c0c3c1048019150070521592480104000c0100c0d0700b4508015517210581 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 732743812 1250 732742562 732742583
    0x6090207060c08071d0f0f0303030f0117030901080a270605012d0e06030a152705070504150308070c0e180a1e060c0e1f0806040e0703 59
    0x8018035904188081030707450f01c1c0d58205a4030503e05544011030070f5034494088207a000e03159018036214000351682d0b4006420a00c0144ca6280400c0ca1035000359130a150030f9815000400405509249440b15149154040c50038400001e0000c1e00118020705540e08482d00e465055042ca28030250350104e24184a07404d005e02c29207420800f00030308080c0901030005400000c11541d5440c8140070b100c200c02c10440b403200c020729101c102001e020740a810541d06001d0010281d000c81ea03450081c0d803006051100010758403a0b20311300d0f42100c0048040d00602c000070140a10080359001c0398440131940c06413004640404480d00520800d84035800007810150080340c0e52007400030004040c03040c1d03500c07040240d00c0c2d600c80b02d003a406203102c140c503102440d61203004281d00146030714603c4441c1c4c82104074001c0c2c2c0b0340c0180da04c1d60252070041106078000b80c170004004100d850300ca103401000640145a400d00c900002c0360003072003a08000c1c25640215211084000b014100f0045030b00115040020f011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 732745062 1250 732743812 732743827
    0x712231009030816020307120c020a09060f060f050306120c030d03050a06061b06110d020d09050d0e03190507330f050931020903190c0315060902 64
    0x4004004000e0150001840140060080c00c5500103113030241c2626002035041910b0347d80c070401c120551001007000c10800c4880e903001600c0301c140e0300c40070345080940424002c0c10a6103805041005911602c20814880b040d02c0d0700e0760308103049903040a0250342d03643d116016481941d24000400d0701068140c40b841c1d405880c12503150303024900843d00700005100c2141d803070a089440700e04429034104122000d01107680042c806501c145d1000300385000040c1429100803408040f41c04c0000f15a0b2783d01e403181c0440003000424015942540c0090510b00c5d101109040407070b07a2031401c0500c05c16085a5440032000703200040180c1ca00809000840c0e41c104100c0046510300f444200d05004407128864450000751400b80c50351203030100b00740e40c07147c4c2000506020040401a410050f10308035100d85800d08c3d0300c004406002414580320308025079103004c0e10060502c3d00b000c030003803103407058902c10f070900000303459002d96412a40c0009000c40e138180d0608401d4002c203060783c0010005031000a026 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 732746312 1250 732745062 732745093
    0xc07170a0903080f070203070f1a0c250819150c1806020705090a0212151c05012f0306190e250302030f0a18060908030414071223 57
    0x1e00d01c2034407d4050702d84680d80c41c210b141036000540194010032100503090110400340c04007901031504014122002030b0443e00003400d00000004030815a182c1030750060003003030703010804403202101c0c150340f001c0d500178103884540c1c401c101c1c1f85c5451641612900b0440e0340300c0c458955080d0000d00384002c0f01f2078540d580c40c0a903a500062040b1070040d008400001d5868595100b695141e5058031014050b503590080c2001c0039250b1141c209034070504414030080d455465540b000c95640c0300c2c04c00051006041401001c906103504448807045c04038800c030303541c1000b0a6080ea500503d081e82e8401c61100c0c0c10030b1034441612035402c102c0340204900104120341100c00d19112038440b007400b01d0095561481d03004c0f01a0b01c01101e1006034500d140c2c0105000080705e078029200211f4070300704040c1c00101c5070740d464248c4580c940e007581d0311840803050100340032481650303034015200c0b10010951646070154510316089621009400740b141741454900003162000540400c64030f0009544e0445000c0c01e44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 732747562 1250 732746312 732746317
    0x2070512010929010503030a02070504050615070c0f050a050f06070201031b0c1709010e10030f020c0717010213171c051c05010815150a0308070303050c07170a0903080f 74
    0x182100841440f00004503420301204135141d11801d0350241c85d005061400f88006801c02a1080703404c0001c2c45070316008070150b81c010b042210700c68120303101d001c0e161880e010700c520055003105106262140007007020750340d481d40c40410207000760b80d8251a03000c03600041e80100b60070948000000340d801c0860b10f41590000c1d841103902c3c4164624254668070b101e840321039000d0010002d0116454100858003407074120303500895100145404110700c002e03121060241c1e00440b480080c00c0c0c2c0044400d0020524070006000c00c110300300d0086050100144600c600e03001240310b642c0342d43c1d20441c12841140d81c244508440103a100c480300c5042c01c50b03484000d040c1d5200c0002c0b441d540c0c0c241160b40c50000441d02445040b0703444038000b454070001e50160820b10703100103010000c0200e0586280070107034698924000c0114000c41400303465409a06004e016200000d140c0240100e00f0480c280000e11080706041c4407107010007450303413030f01c603a0242518001c20703640019010f5a0702085c0c407001030740032030700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 732748812 1250 732747562 732747623
    0x40e151c150603021003020318030c0c0a170d0f05090301061511010b0906041e0e03070507090e0a08070519080c0f0303090a120903080301090501031110020705120109 73
    0x4000701e000704284400070494070b0034000207611200302440c100d1a43c1c465000ba50304458540c4011052261354040340c1e1656110040c08005600070a1b01e240d428035006c903055005010f02415800710248615000707449802e4542e400d000c0c024000c0c100c84059114105540c00080e015008001490301c0d07680790b0304140d100c002a0000500c0001c2a01d190039010302811808041c0a07000b074106484100c04c210160154541c01000d80c6181ea1403110416400d000d05010000c0c600e028507a60369690038014100781e941d4010001050602d01580004140059046021034216200a07220b0100c0d280480c140707440300c1c0401402601c0c80301e00505000d600c0c4010302000104408541003110450b10013a100d000c04c48401625800090404000c11148116150214a0380c0b4045171440d41740d5a6000c000c3d042a0440e17810f240c2d503070006001704042402502141e08045401d107050000d44a0000c0d0740700c986000310350240000500000c01094250402c102403648004980d4050a01c01c0c0c229510003543c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 732750062 1250 732748812 732748823
    0x2030f0109090203060a0b01030207050604230d0806060a140c01050a150807170102070507080105070801120f030c06060506220608010b040b130909051e0c0105040e151c 74
    0x10000190a5100c1c464102d031158080d024000c1540c540c0c9605c4010050740070524141034080100000040c018030429114038800c2105000034106c0c4140300106810134007001141303030310001072500a01d400c011807550000c03049508940d2040d03a110115015690384000c02c5011902184601020314103400c13080c810400c0d10b408002584c01c03142800c03c0c400c81031080f1205034000c06030911050340d0400010303210401d5200058035000c0b03d50798003441c01200f50302c4142165503400a21040c0c0e0b43c40f9044600410f00100a020010181e0321100c0110301e4054004081c4011004260700b00701d60b80d0082d10040000410445d100c4c007801130102500d908d03070418a0000c0541d1800800e09a0140c0710a5050300d2a000e802c0c5e0805081035444d0107641e200012821802e2802e48001030064034501401c52524801d0015180216500710920052150707407003031152030341010b00e2119440c0d0f449410390341110510840c110054995240b035101441d07421691035040742c030084111441c0300340326070320101940c0b01e031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 732751312 1250 732750062 732750091
    0x11701090c0e042f19030503070f0605010f03020a0e0a480905100c021e030f0a021e041b09150813030c0302031b0d1202030907050103090c0b0c010203 66
    0x3000005440744045400a1107241040c0c0c004245c18580102d840841e140100200240d40304c2e01d0309491500005070850f4a002100031140801c10a801031500500c503814290300094107681c0014000c420030302916450000c3c0d0400180075018a13080400034081d150403026440b10f61404602006501503072400c11468811180f08020900d85c0c00090460400d40c2e42a10a03420300c02007103001086004c02c1810808000c88a8000d41c0d55203051040c0039640040326016524860141401e0009003612000660041260040980c48461080c144100700c0c00003505045200e10004c1e0040074000d224807182200f4464080d5080d8001e910743c02a160340002d0311185c00300300c020480d242002111103040d0f43c07103140310400000f80110340d0759030070074840d0060300c1c145606504074400c04012106140b5490340301c1424810441c2d0020030810121038444015859460a4524a50340380038030300c189070400d503483d00503074107114030403604802405d00180b2041da10350786180628003030b4100340c0d08082c1c6403018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 732752562 1250 732751312 732751343
    0xa080f0c030a0c050909030408030a0c02040e0a0302060a0b18040f06050f15010f0504080303100312020a081207020102041211010818100c0e041104090c1403011701090c0e04 76
    0x615000d1055014120030212030410051140052006d0f1800c03065200a00021a088200744090604000d480d91400200116030040106890000f01e403008141c02110740a40400c2e408034030903511103100c1d680801d142680001252410260741c0c1c090f03245810b40028482040036102e08014514001c5000b801140c03076141034101896800d5402200e1042c1d248104a03c5500035089031141d480d281c20701d00d0505580c0c4503080e046a00c11900107081c003004190520400030708101c4000c1c24a00fa100400200c645941d41e54002c0c4034015040c140428100e00017204240b007501128041c00d141c900100284c00107207030440d9840307038000700d490200f50494009a0507042c0d41000414461010b40148491501c0718094070041400c101007404100c80d04010100c3d6460300e0160303010958055031a50b86e16490b01d01aa0110f030001801c2800300030a5021181c014411041542c3c15188115280200c0078440ca401038018010390200401c0085e004000041130080048010321960143c90001e43c042d01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 732753812 1250 732752562 732752569
    0x22109010f0519030b240307030e01060509010b07150b0609010e041b05120105032a0301150815010504051005011103040e041208070c03082409040b070f03060503030d02070f020a080f0c 81
    0x145186c403821044030520002e22031600c640c10a904d00c212a0000184c40b075155008220110f00c01d0b0041c003240c040c0010400200b101408a40d8940c0c070030341800304000c42843c070004507144640f908407030400400301d854045680e201d51060b21481041201a208800308880240c03040d00301131403070800b46640400019241c1800f0032410109045171180074292005191030003001e0300704035000798240d941c0300346120f0102d402c0086480070f0200c1c44014070008080e410010b036a25070503080203004038140401e10010300c030031b03582070300c20784d00f09080500d802644190030500d18011a0f00031400c007800f141c1803200380900070918402c2d002081e17940300700e00d40d114101519000f50400009002400780300009807840d400c558651545444131803154003490000740015807410381a541a195081b0790340074003003101c0e00500b034004041e11604052182a240c040000c1e200d01079103010180103038000601e4000c210140e2040401e030383c1d0040c0030002c01a201c50170640c0e502c8501c2110f07815482942001107052a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 732755062 1250 732753812 732753859
    0x60f090b0703050d02070c080606100c020609042f0d180f0212150c04140d050a062a03050603060a0209090402040e2803022109010f0519030b 62
    0x40100c0c00c024070303050340c555044410f40c0c0418611030030103609100840c0051381d11003854004103090780c024040c0c0c1c281a01004400d0400310120024032100000000040c4c6a24007038440d03444003150300150740074000d5a2900311582000041c07080141081100350160310a001500700004040e00800c04d25038080801e0340400244607014060207000a0074500618150000c2078034900320074241c56209000c0303440d501e40c4d4401924818101e50340807409000201038050301d000e075100e04440d011040001a04d84585a0041c004050306558481d40d420300c0401030000e00c0c0c0d0300302400301000401441c4030080200100804d450481c841c0c0210008280a03d459000740c4000107802000855251642e508000003040300307425501e1035018444c0d01d100058400d201e80034041f0780c5030340c1d4100700a66038070380242031204d031503180b88a01e0132800500035011840f10940d612035000707007042c0303c111587c288103646c58002e5405480d6604110070b443c6501540c1078200c2c208045050711800c1c2140e082c42e1102c034111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 732756312 1250 732755062 732755069
    0xc060106090b1e041503020306040f020a1403040501090f140c060c030d0e010b0405042009040f062c0d18050d02010f050409020307081503061006050d24060f09 70
    0x510082c094103042d100c201904a00c1c0c500c5280100f85400e60325100300f4401a140103055020a5002c230411100741030034003a24002c601107200841c60483d14500c0500340488a5250742140e15010000034100007007580070400d4181c00403030703000311055546404411014112010700c0b0030300424009801505114044e14800700c0d400c00903500f040c2040304010700a04054040301980c0d9214610b070b6030755843c0c0e4801c460107a402411406800e440075006000b0003103031400c805019151000810000c144801c03554a103542d405140454100c1c199206c81e151100741c1c103900042241040c076000c004201c000341294081302207440f45203034054a48014207520b4298441c140d00222610f00080043d0300c10f64801c0701082590510b00d0070162186074010881e0402c480c1e540c0070800b8a82030054410207545e007051025001ca0081615241810911006a42c03900c580c0701401004241e0703078000e403043c0d04410a1075140d0006001c0ca030240e200c820610075440d10903080481c20b030b94021200f0600c528101c1064 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 732757562 1250 732756312 732756329
    0x30e0111030d020715230702030708030406020304020f1f0e0a03080a1b06020f04050f120703061a0915150c1207170703030c0810050a0506031008120c06010609 70
    0x10106910b40400180d80031140880d1920300c41c1c0101c01e00c64105124440c01c15060002c42e1071070241e0a0800b10b01808003400380425980306008100004001400b141d078090b60141001da01d82d2103d102080000d848584140d90005128494004418003d10003241c00c00d150354845110b0703038120f414410440700300d00014181040801c0600341043c007038582c43c110445454002244004aa00d400041313802c040d442d045082c00028040100746440400305140e4681107401e02005880080081c2e030301c201c648801403003a40c5450804a24402230450441094409042c0e80e9a034640690f07000501203021580c1485030b626108070b0407030107142c0402d0310510381034079006003410424410600c45030340058900715040218000c40c0d212520400e070107040f100e442501e012400712180c5101810700c503801071041240b07035800da400300042d07511860361b1012103c041e90602d075207850702c1c41541100038083e041003400d44112440d103032030451140000c1403071030010007d0b2030a03a40c80304012100801903104281a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 732758812 1250 732757562 732757567
    0x30a0e090123120a0c0306020d0f02031905062b290a0b0a050d080a02011a01020a032f031b0d08040b07030e0105090a0309080a0b010b0304080408031204030e011103 72
    0x481c107150350f18003d00603600f012204088065039070745035034001d5034104451641d0040b43c4041d040a190007541c806485005e82942140703811088064910080203000d80c1180d01c03803002c11215240c034964500d00d0031070200b90610a8440300c4043e000301e01c2200f0100d0360440302d204400411200002902054101e00385031511035141d81d02c2010182900003400740e405602140d0004090b6241c54600e6000c0e48180144d0384c03681e94002c406421540310361a032006040c20b69180350ba00b41e13800f00b050382c2d01c0f07540b60801924021a440c01090b42060400440b250035100c50051555624004040c2807154140440c405108035203940e0303d0303116000c480c3c650001c2181100414002070329145041d0b408841c0d85400201501c00c04506802d584081e501120590820640b00040c1544841c055003d04003440045c1070b01c0c1d07610b64500c1c200c1441403003603150104012000c2010884c100c07045400900c6032501301e9880b1500c42e00c500041c01710503141200131510105902b841c65003e04081440186080c0c00f860 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 732760062 1250 732758812 732758879
    0x2e060809070b07150b030105040f050105070e0114130b041202150c06010504090f020901060801140603010806061c06140106030e06090601090b0a1a070302060106050309190303020705030a0e0901 85
    0x84c24a00390300800f820440e02e400301c00f102a14240301e030a100301d000c0e4811a00686035404c00c103084440207001c079810803140d1007941141ea41c105503462880c02c00009265510800d100014035000c0b50ba0300191500c3c00002800a04e41445417810160507000700c482400704801c0b2255560540310b40116590b0541040e40100554a0240e02a43d0318a014007010580d00c00590f00090241c20240c00500104843c8001400200c01601080c2c02c9440203a94403880c40d414200b04590b01c15005080500c5030030703408010305540014503240c403503155014406008c104003003c80f41d11603030401d00903500043e1134450340d4100080c0010707005010340301d80b5020f40050707402c001c00d40c000752400e030300c840d500a034014030005401080e005595024420121515441d4800d0703240c000e04180c0103070310000c01c0040601c18416803078804910340e80c0c0106c0d1003d00e0010500c4914040d400307400340000141281c0000701c2c0c026410742d000792001d004031004640a0703141d6038035a461290400311780800e940c841064044050b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 732761312 1250 732760062 732760073
    0xf0f060503131e0507060c030914030c03120901020c0609060306041116050c040e0d082a032d0c0403060b060f0c0f280201082e060809070b07 62
    0x41d5000050050034000c0c10000d07489240102040c2c845040204600d80221000c0c40814059107000c0d0a80c1e140045080e13005885c018007151182c020807440a00c640c0c0c00820f15030b41002194503e200c0a000d85084402043d85018240c100f40425405401041c0c84420343d45442c2d41100e01b041001405d450841d100c80e01400010840700e6144200d03020200a0b420001912603c0d0080c4244200f0040c560041d600040c4400d80b4241000d0341c82c10740c000503484003407076001000c2560180800781d101c0c0c2c0c00460341c0c20030310b13007140c0b0b54141c245c003d40008240800c090400440409003003410994009008220303c070a6880c0320111900c1e8000b5809000030300003e07005412210032114010309003402d0040302c6041b01c00d2039001000e0180c2c5640302d60101c028001050040058500c01e116002c5441d9400c03035101e036801000558003c1c10032204100294504208100404c81c040c018450300510002000c200d400080e03a60140390040742c092000100740c5c8200298040c15106c80c011414100325031990750 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 732762562 1250 732761312 732761317
    0x7090e150301091e0c0b030c121306020403031d031f09020301150608250503070e0d1a090f071a091201051005040c020f120903010b0901031202070f0f0605 68
    0x345506549492400c004908682403c1155000700000c4c501c42c0d00151900c600302048551081c442c0c04010320800c2402d420302d506072000d190307006a11441e03903501d000441c0d44200d4080b4008012500c007050101c14154400007444d0402011950441025583c00805603188a1040050400d000800004003011481e4220000e1144042d001260150643c10303000c02e03200d0150000b00020b0000000c2148070500f0001e80c00e00c03600765411607007072440d2a51004080b4800104440207210403a1103e02c0d450312003c0c5942034254124028030b50415154109003541107017903c004500f8491061b21507880440820014111034110b13101003036821a841c8005090f402c80c00043d58010782e040d071404171050b007e020b014464074954000708085410310080108840090f041d43c411940a40c00c000f40e01c1c80005030004d035052841c42181d031500f60200c00207000d8040309882c250810306c070784000002c0080e4091620740440c0039400340c910706603d594080701c00a2152240c0711400d511544100302c0640200300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 732763812 1250 732762562 732762601
    0xb0a0227150705210a02150402150a0f02060603070e0f180615011706030606010305330405060909150c0d0513110604050109050411280807090e 63
    0x405022928259080d0300542084200303442c5500700000c0c0d04104c1109045031555034403a00c2c001d50030000c5c030810096a070300b00064119600034218000c10f00355920b840c0c05c0140505900d0f135040d52042420300040055010483e11000744c414040481c40600d800300308402600c1880c17414010b03903540e010710b6800001d0007601d1070724005592400f900c0d215009019480c82481301c0550f9a00340207125000500501c2c03461380750086404242c0a00c401030340d01242658100c00246404101d03901d400040f0507100c011041403600400a01c00d410460748184048800120300803101040156501e809002480701d003120240b003103410690010800400000c8a241c01c0b616204101d0305020000d003101c0115401613405490320214501544100011a00c034140300c002d064130030900382840d100c00a032481446005483c03080f074441c0700303810000c0d99600030386540701d514150752481c20f0001205a07540842540d08040000d1041d4002a0964003e40c0310000f10b5072081d118003429039540c2003004441b80c002c034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 732765062 1250 732763812 732763819
    0x22080304060219022503030806010305150406060f0e040c020c12030903060124090e070509180c03040203100b0102060a050703150305011b02010615080402010c0c09090b0a0227 77
    0x2220f0407040410601404040c2400c0d0014150151a2800345e01221076411140e4160000680240002544078040e030760080e101b82004645a00c8240a9007102460044143d81051400c1c3c0c0008496500170511801104141c07181211110400240825140e50010000259000490f9201d1070b0030407050f04a40100810192414406503100103810f04400f03074043d0490080120503200b08a0151103124070341000c07070404040b41490140e11203282900103018405220b00480c001c0015200e4079048044c0a90306a80310100e4a0401c040e040c00360000c0e1001d0303001c0e1103103943c8e40180340841e119134400c0c064140c00034030395960381080c0000075110082900c8101a01c0d0b07014541030352034001c09600554468800800c0f5211078806010402044440c004116810202e00300f041c43c0c41205071054050041c50801d03a50380d5a400140d520604400f40141030024a0701e0008403039a00750303c0f80002500c41c0032510b203135490b00b54121080c2c0c000d4610b101d062280e100e4031203000e640c440181840000c00034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 732766312 1250 732765062 732765067
    0x1020c1e0a08070b0414030d0c170d2a26060f1e0103050a0b180a0b12010b030705040c080a0b120a030c0c061803031103040b071109220803040602 64
    0x40311103038100160f640c0b00c01081c580101d024400c44e840c40d0821200200160000c1c0307001014103000400714000600082d020041541000d200b0343c01200c00c40c0c0d1315520640050296104011a02d454420740c02c0c07644403903444521300345404074419036007020920000b956440e480c440e800b030310341c0c010040500002e5000d060455a039245858442ca0341e040b0001003011010720800c40c0001409584006004410300c034a0720011107895551071605c40340e113103810000c0b03651940d1803008000081152030203096102030791700201040c1c04815000805505419020b07900b450340d545080c0f2065406203182080403c3c0e192000550314181030340111136084004000d000c410f5402c0307c80600b4065083c0003500002c41d80300320f407000d10142c000e20a0003014145052104d4651084054503802018003000b010020004010300f4000b008200b07507000b80c044003031455038803402490441d80000054035004c6c0a00700389000290300840600b0400d08140007000e24100100380e0395210081a40000c000710340140e402e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 732767562 1250 732766312 732766319
    0x9030102130602010f1406100809010204031a0106090e0c0405013f150803030c070f2f0103060f0b071509080301060801090e0a110102150c041401020c1e0a 68
    0x110140c0000030b00706900005140440c0c241d61505851401c00c0080c202a24402482000d46500e20304100c10007040c906601242c60700f28065019202d0b9610240134031030308010b118603000205410f64100c9a00b512403d04440d13482001c1680c0200c2100c031110f144a042c003040015502900c420814020f40010000d01c1c0e0110611000300001d10780700042144403600703800f041d80040b510581e1500e4105210403850189030640381035403440004e0486510102c040344280801a5071123100c20b50640c031070001c0710344045581c04440100c0328419840c02c0110010080c4c0800d5009101d0304042e01d520f0b42511035814244a8050940d90100d41e003103400650380b21811209043d5071140700c041512038484175a403035150203001003001c54103811100e12035241c90301a80e0450000141c00c080715603c81d452000d48203882005130308007403440401802c1d002220f4200031590341113a00138819108600440f10803a4454001203030f44000b2122040d800c0091910800c0e8019188085400e56580003070501060985 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 732768812 1250 732767562 732767587
    0x10c0203030c0726160506070f0b04051014160815030102041409061008040605060609120601050306090307171e0a020703151109040b0303130303110c030604120509030102 75
    0x50351294201c200101001c540119030300040e4503940f03007010005d2030f42080b40c42c101580c540c007601c81c8030310801000541004000c12808006900d079000f00d0340c059186020b0910343e4541e1510355040e0052403810484e100020f140740c1100740039450801c0c840711614143c041c1940e94401c080c01540e900c0c00340d81c448400d203540900091000c0c01001d0300c500c1000d12020280850190040c01441c0300d00c0d424450003151a038886080c079401600800007080030748400011480c20b2251a500f590031011030050082e02200010f00c1038102d40041e02100c1080d40c480c00c9079500c034000c074403008005a0702d4200198030328110304090406903402c90401078842c820614840415802003492502680180c41d04200703014409a07a1002c400340800184402c80703103031910250b02d11803110741a20490b5a4603421416450410607602c2c403055544803903190039141e040c0034083c0504002e03850410311451f40e85030035500340800e03018000c0368006107a6402c0d41e6018400e03211500f080710416015942481012120103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 732770062 1250 732768812 732768823
    0xd050a02090a0606080a090501060f0f18021e0d0f050117061006052706071202160f05040f1e090c0503190f0f0203030304030905120a1122050a060e0709080a02010c0203030c 76
    0x100380140f41c1c501c40c5071003745c2e0100013036441c203224070301e205202c0400900020b0030300c52003100c040e1460035510210b9095141c0280301e0301800c240c00501c4c02001054103001216840314600c4c051048070400d503a60101d036940002c43d070261000103081400424110220307203900a0714800941c040b1540702c0c0c8410013161503030f042000301343d4001210341032a203070766a0140400c0410041c0b030301910003401e052403000084440b440c8142400b4a9135152144290741e2103600c1013083c0803140714941c0c40c1c00b450025600180a01c010240c40c6c402c2c0780040000c56240004110407d554002034040300c104840e190f007104903041c132074281d8030b0f402140c0802005175000e000652145201c0e40318401e01c0c60514007803040134501d501c104241c0b0341c031036140c0e400411040c401042d1041c40c121010310b040380d40ca03070202e0507096003840c10079881401c1106010303c40030301d03801c0f000a490031402c008205542d0307944200c0ba03205c07045c4110403150b00500120805035215600300f250300c90018040301e03d04086447d00905e0031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 732771312 1250 732770062 732770069
    0x60c01110304151b052d1e070213050702030403051606080903070308010b0a021e060a0b060717031308071202070503030406080f04050a020d050a02090a0606080a090501060f 76
    0x31000400c20041101c0600c1e090440c035040745040042203a012800c8408010825000040c80804075001515016054a200000c45c81c98a5811a94022041c000e030340c0d001840800a81803a8040380510036000343c080c0c0394100d0b002041c0c1d01c3c071501c090420300f00800f0094608800c40c042000080046103080054001e80d2282c100042c1c02c0915022004002071805450a0300e2230308100481004242e0100815040d590024075260340ca00300c0d0881a407922507400034403101c101941c01c0c61440d540d80429954072442da816024003142441c4001c0180d2440303908001440c2d0310b102c001d400c81101c0d001d00a542d0010030454441560829a11000e281e40c000701c404075600190486602240c40d03052011200421041e80210304044c20204081c104150040074000c040d85100002001d0010400c00d246440d50050701d40c44a4020500b07101d030302c40d00c14180590107028040d003c5104805a032007002e0071944160f98424050b103406100da006003450000039035041d0b490341310215101c019000c002009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 732772562 1250 732771312 732771341
    0x30412030c0c050109081e1608010501171c0e0105070618020102070905072003040f0810060501090317130f08010b1201150e0c0d02160302010b1002030405040b060c01 73
    0x4140c1c0e2404081030600c075088030f41008080c40c03007000390b040c000a503041c3e58800a102200d555110603000d41c035103030350b0701c1c1c0001d140c200300200025081d2046d0702140c162140045000b103041c09203858030f0350380e46180c01102039028210840c2140d462190700042e800200501d0002d15007611a00c0e00001d507241e1421302a601030117400444110341e0108030100080240c00000c0c8010302e00a0300180030355803a1036615150301000d800846040074241304a401919003030440d641c8440c0c50b852a60b50b03444032954a1801103141180101d840c0d0700910040c42125446490300d4070300002510700030f2071034004020b000c0e044649848003180d40c0c0541c41080024100e500000298031002c4020452409515100a001645000c100c0440265005e80003800d548a07240310146a880309842220940320781c2c106c3d0840244085183c000200b520a140c9100601940c0240400c9a1000402440321034640400c000343e0310820040060381040d4000c4018120002c106900b0303c1c2e80500c886003954000c0c0e51307401c1d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 732773812 1250 732772562 732772577
    0x50d02090610033902071412070504023103020303040b0a1808010e0d0302120129030a1a01110c010e0a05090910060b04061b1e1a07050c06040206070503041203 70
    0x1d03c290740c107000e84c401070980e1004020b6186883c24401410050047d0303240240304101c0400c04034441000030300b00400001d8800c6544031104540c0000d2403081441c4498183c80041400444901724111803003629001000b962900d85452800d000c2540100348000610003449464108101c05407402d0004083c1131001152681c02c403070440b81010110f008001c1494414881540440000c0c0515415580c0844030b01810000c8030400540d4440341c0c03076068544d240d00100300140300056401c00707020440d06002000d40d035070030000155509000b0b000080941e5000c0c0100c42c500e907125100d04211100d001d400b86003055261004228100d804840c0300200c0d901044103c0200c40d4107208440c02440b502d40c10310300303290030b100c4001c00c2d603025052114500b9001d03013040000d00c88481080702d5100000c581a200c0c40a0034501420444018521031307010342d0180c8000342c8624000c1c4115640e8240c44405000d4a59a070b908200f0941c1000d4400c0e00c90344800c1c80f0100b407940c440700c0d0b0071f080b541c020349031240d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 732775062 1250 732773812 732773891
    0x1a01060e270709150302040f0e0703110f13060806010507020d032318010c0b07030c030b0a060806030111040f030b090f010c050318160326030c13050d0209061003 71
    0x204d900f400c40321101c101417040008220034103050341c41c203050711914032070500e81c0c1d1200740044006d81040144001410b0700040c400d03800c1402c460082c07420160b003450740400c00380e94123000e580c44401100d0683c0810400c10141c001131600c007444101d40d61090130000103e0759941555032040c0090f0b010005184000070b80c5800c902c610750200c1380314072000d28081a10002d070740c3d500c90507030002619074000d254072001c032085207074001e401540c01954043d12002d142551508010000a0300303640641c0694030300b0745411a14184002101c0039a04c210b0014040c070340c50340d0303552403100000420880041c00b40d00544004824280207007403c0d040d9a83c0c40640b6403c00b94944060b80741c0b2880001440e0780500c04585450648400c0141103d0b044081192600c40d04140564480c22100b00c00380e841c07000000300210f102c10a800707890f844c540201035511280c0c840003409184400f9010180d84a071703c1d10000740d21032030101400c08210600e071030041030f100314450140d6402a001540702420944142034603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 732776312 1250 732775062 732775079
    0x30d0e0f0d050a05032d010e07090305120f0d02030106230703020d0e0f120622080d0e0a1a07080f10060e0613030b041a01060e270709 59
    0x10400d21403100090807200125010150440c821005100144200803002400d1982241c038140e414006541003652030210406100210790002d004200a8104000114000e0b80c8112005c400380c0e94000020008800c003022540708940203070328000c100d04d5007003020004d0a00940055802000c03140c641c0102c242c082070344110051002c40c8103d1504005201c0e56000ca903002810907411415410107001500e06240441c80c1800031800b1290480d00803107040c034401c0b00c0010543e2013001c0d03540210017500941c100d400051910440041c000030828018003840d250b030b40c0d00c410300c5500180111002116950788050400c80e240c424880c2036100c610801c400ca9800c4208240e0001e006982c000062030710710403003a4816202c0c000d1008200030608282030540790324088401c014000e110000f41c1d00e07a42d06c1d20b07a068a030129021944808503000d02901507130392a0f135060681c0c00c603480d000b640d201c071941441485040d4601a00401d0b81800724980000d030001d4115000e5445079540181050a0480c2e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 732777562 1250 732776312 732776323
    0x307090b07030806011b0f030809060106051809070e03060c0a08070305220203102d0501050a0603050604020706020c01050f060a0b070f060b0307151101231008030d0e 73
    0x51000c1500c1008800d0019900c00102584940c0901740b40e0382c015110092042240c022a400800c41141c05a0401c20b25411640880c45015180c045030407980c0c8070325040f981d90040056010124035581c01611803071811010703155000f807a86ca01854846c42d0800001e02d071100513115203801000000d07052079516404140d80303500035014202802241840c2d503544030a1810b400c0f20008004c808440c000455505002a1030511072606050228950400c040000c0d4032000414810702440305c09d15034101c2041d4060b8034103d44008140014a0340b41403000d5018101c014030b201d41c081d40c00c005110000b41148054040182d503400002124a0301c203a0070703051404003030303c41c500c81c80c44203008205000000c41103e88055001c0101004034a2620303080c00640002e5803c45d92501401c03501244c0b02c4003131810001480ad403990396111480b500c1c0f4000e402c07551040c1e190400500300303004034400415041182a0008188070461364030a960303821850940d0854861540019111424101c00344000c00c0b6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 732778812 1250 732777562 732777569
    0x31e0a1e050a0b0a050c090d02040b041506030e07080d09060f0203070b040b06010810300c030b09060a060f03060c0e0d080d110c0a021c05030403030215010905100b0d0b1203030709 79
    0x540e00c1c5401e600c1c1d000035000c1d1020400c0207104548401d070be0109500c07190010050107a562280c600955221030001d00940030345402e8212600c83d41d2000141000f001514074030714466038541d0203000c1d0030604120343e0101c1400700300703055204c20400e60000030307206503026108600a10030606681031038000100b4405014008046d66084c2000902a0071141d044a181a1100416140426030242000c00310f5500040700600440fa00305400001d001e45102058858641001034840740d642d03c0c151001100d2060042c08154039803040148005151540b00442e0701c581801d0400000030342c400020324076031760840116000c4070003198080c610012070040c400c1950a0030404c9052860400381c065584800f414003900c20100203030f02041805240b1800040d80c1e401909132541c8944a0a0295407104031030200c3e450707100c10b03200026a042003841313043c0c018020001e203041c41074a02550745049400c0003813910456a03940d40c0740c0d802992420541144288010040c54891400c2c0e00c0c0608040462361 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 732780062 1250 732778812 732778831
    0x190e040503040f241b02120a110306040c0b090103091b06030b01020c03102c010c08070f170405100617010609110d02130b0c010209031e0a1e050a0b0a05 67
    0xa82004041c3e0342d09222016204441c9004901c852042c03135980d418140200d0040d402045135100c20b487c0d0700001c9480e0001e540100c8000b00900980300915a0b00c580c12200644028220f203003d21150b140c0d03100800c10040145030214010780c882d00c480da000c0c428000452180304440000700580e0380c160084a03880c01090014016440250001c01d4031203281d84400130019945002a2000d107040051050740e000794968610814240089079034000d103081e403414800700781d60500003680d591240d880e44000e0b4040e07030b80702c040c40400f20f89549500701004c0c000306d91a0059501e114040286440b03100000c01940340c0a8080d40c2d40c1000b92400c45085800c07925586040141080c91100402d044030680700380030400682d00c004002d079181000b0f840d500001040b200015558001d008150054031f02001e00700e090702c0704400d4000110030310080c21110440c00e504a6240c034000720702c080341c4402c04445218000c5500080c0d42d940c1c1801c0050b6610115481d40c092020710070b154010348100d030f6020a502 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 732781312 1250 732780062 732780089
    0x705120a020a2003061b180d0827030606150c010902220e0d08160509030709020415080403080a0906060312050703110303090a11030a150b01030e011802190e040503040f 74
    0x289003840c8a1081031141d40107d03202007013580c0c3e2512242c507260a034a4115102503101e00c5509000c001d050000c400f4000c2001000409000f140340c0480e40e107010390801043c5a00c4046441001e1001da0400a680c02c2255a620780c1d44000d078861b004206c406100030424504400c40114072001255078081e0ba000039544002c1d002c6414940003c0501e07002009140901181c0380d07002c03800c0764a0304c43d2090a40c0c00d80503d490001d000c14080d0083c1068903030b0051103802004074440d003100c91100440d03000c0c0000f81e43c01c01044c0391807510b6018080481c011200070450300c0e01c94645c2c407070305c0103482d0781030000800c0010141c00703256004528603190701064010354034600700144d204e0341d194030301c84014240250811140402f40e400308020704890b075100f082c580400600800a078000c00c640c0800d54081390400c070a41311101018854100024034071190300c040c1540359024020380700011001c60080920f0424081752500c07080d0078491189106000465807982041d29600d88540250700c0710b04641c495 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 732782562 1250 732781312 732781351
    0x30d09141507062c0307030804082d07020a080a05030301051017090106060929030408160c0302031507020a03030c02010609110910050705120a020a200306 68
    0x5424500c03155100445525406842065000001d8840c0310342c001c01141c680401c0502e492102c1245208a4510548108640c150a11659120700c108139004000a21490000d40010108406092000c9101040742c41c2000e040c8030180c40c2541380440c07440c0d103140210f26901180b4040e407142c0082c1c4000c00152040d0840703543c400f903681c04103009551107045c0c8031a81611030351182905090140c0c0c404403031442814046c1c42d80303008045d18041c5a001a11005002c100387c5c01c0442e0750804104540400d0700015101c1d040402d4a03000540110b6a500c001c12071443c400c186c81d07020740d0700e050181184c01005da14502c10186001c49180c04020403d04000800c2180c94000c03521002c0580c1608010070030600e07102041340145002d03080f00c515145052144140b80204030098001c1000c01d4804044006100c1c90548150080d06c00090040d8490724000441840e04800362485000c103004907192040c03e6501d000700d184011503203200032002e100d00e800540c6400c100d102d03003000812250403412060b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 732783812 1250 732782562 732782579
    0xb0a02040b1b0115031110050c0a03030f1113150c030804080306030f030a051806090d12030b09040b07080f070e28080601050108150112111b0606030d09 67
    0x880301c2d440d4070024042c2501828140030f4221910f0b00c00c082800014070394803403620f0481c510711881058041d90750009070100b0079009a0480c0c40c040e804800a181e414121750302100a420815810480c0d99101d0403140d6a001c0407001178001071120020087c2c656003040d0381450000f004204180c20030242011130008203410183c40c0d6086600a5001035a954802001c24a4040210711004492000046420405500202a00c0300c06025102403904607618000c0042c540500c004080e0321507440c01105000451910607545840001d05000c203049510f60002024010200c8081d254840d88904010400354007800d0203a001e00841018102401e294400400000c42044020300418940510305442c0000300a0341402481c2c0303101c981001038540350929100d078028854039020034107890101c3c1500c0c001491800038004180e5403001c0075404c81048501400b01c0301121118210b00b040b500840b20302c6600d07829442c5031200024102070a011042c1f40c03034100c11003064410410508824890000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 732785062 1250 732783812 732783817
    0x9030c15040803070e0d0c06050c010e01090c15120501080a0c05031b09070504050316090506150d1d1006030b061210020c1501290a0f1119050303040b0a02040b 70
    0x1040345000d815040c1c0040200c6c480c000d12860140107a50b1013540002d030203a00500418000c54424000e0000030a4080010b007602c5814000820040d44c00109000f0b80345040aa200c0303100e954038004104071a05c14001e42117403000c0c1c000442d01e0700300101c0e0100f40009501d035600209410703001020386203030035103083e000d00e015000703443d1250b11600c0218901c1481403058a02604004040c6c64030600007110f503255242641c450018250b0400340026039a02d4451022400284110035061600c0b440400c0c040c001d0126941c42c289007607207910f120008100c20041c1e104210764440c400203031b0600311300b000301c074854005204912402d203409540b40040800720b80c0620385400d40c0d5000d81c44180440409040c1524004421741950f000e030300010f0820041c1c07005a03140c005414280c010010f1094a15855206100c2100003140c0e00c0d40070401140e22505039500d980c0d490307400b9104460031005824400051088050f2540d80c404010b000074070102d810a00c0e00b0150707a800440c81d003031404a540c0140d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 732786312 1250 732785062 732785071
    0x812010e010e0f070c111f0804140604030c110a2c0a0506010212090a1a121b03040b100803030115080105040603210504050d06141501140f040e09030c15040803 70
    0x10f46842d0014078040d1079200d00500d101a81200c07c2000c9034003484000d003103450440b410744101214507000c0c940280f02082d910300640d0540d8410342d40b4442c0f13403181c070708201d81185c501390888803100000613a460170b01c000d01d94400b52103480c65906840146452003000340a410718071194540300921010b6070b00018001c2d106c4070703003c4146460700d01707150000d00140001c1e0302541203080406210881c051000c00203150403903501c2800e2185441d03841c0007403080002e105da42c09001404101041c0864607034402a54411040040521126100e0980a096810a9100070354031b4425003142100305403c0175199000d0706042d607040000d54a943c4584001d00c9000a801440503032003d0340640707092180d01124058200500908001c1e162450a400200105142c00908556510125140b00d1141c032088106900c140d64074840504081481d0b2950340c819402c04100b5241000000380351105900b049114103040790196841d00d10314001d0b2410041402c500c088010789950410002030f1000d815a07400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 732787562 1250 732786312 732786323
    0x90118092c15071101020f0310080d0c15020304020f03120a0207140915120a0c090b090417030a02070c141002030309070e07030e010f200a02070e040812010e010e0f070c 74
    0xc04c035007003200d40e00900c545058101801000020419034846151031740302100d94920407078805000951084990138a0082d000386603102d03c4505c0c0040700441e40155800074002005078049000781c1e000a480c11480320080c03075200e1004117400a051b07405210b0400100320703e420505e140d821450002e50210001406044121014110304040d40c0300d0003d1262103084180840c0c540704040c0c2050780d00e4034124031130341240b241010301c04005800c00c10341c5280120b034005001e02c515280809082c443e600010304111400c0ea0a0140e640481e120700c1051004020f044810b0050901030414130103803503041c0c0840070942d4410400d01c80080d01c0002c0d14011070b00038540840c002d40320369900700c014180e04140b61002d0341c2054000c0b4000d25440e0700c1400800c0300307441460300310b04002203400f4460140d00c040001503000080200902e040b404c80310341d80648a003a0b42860040c20860750742400400313070440766041c0c030300f017006218100c4c100e5840d0b600326924404410346e520309048014116114081d0040c031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 732788812 1250 732787562 732787577
    0x120f0519030e10020111031f061d0111010b0616151503120507020603010e06040c0e1c06020d05100614071e1403040801090204140408090118092c1507 66
    0x203c1d64400e6022001042d02c00789140d5682c00d20000102040441c1d1501d510001c04440001803020300824012521014035071218601001c048010360f10089407c00142d515526000d20010310754502d002041091070310031605003403805500305031030300f1800016000c000700c1c030b04082c9004000c2c0103060394003183c3e071140408902e400d03214421a40382c080c0e000006e402110100c00031840e8480342900b01e2040c001500e0030003054001000c2103603000c41017044241c11091080280400300b503041c18040109004442c054900b1080390402012200111a910442014140140242513101920240780741600b0107280c1000e030581c031801e500340030f4001c0c2c0c569042c00c9021001c081104101d01c00f030030000c841003503d03101d96031600740501820103500c04a104da440e090740b502d454004150180d01031604100c9288c1071001540045d03450302004881c2030808e500c0c040d80010202007034050051540c450240d221010f0400100014500d040300d4080701d080d0b00f08190041e400c2d1030320305895030702c40f14a160140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 732790062 1250 732788812 732788839
    0x303090f0f05060c0c18060f03060408030a020a0e0607030e03060c0316030c0c060509010b01020c0414060402070c030b01031203110a270305150702160e07030b0604120f0519030e 78
    0xe03c5d0103002500e1a4000e07810b042c0f03040074543c2d100307210fa1003002d055035490091002e1108141d150402107070f005100074021301c0450f1a00401394040d150350106070400055255000d000600d00760040b541c00c40004048041e14406030800303200850b0040c445511042c02d609281171240c0d402c000c80e809130410560364503040f1f04002c1c802c0c07103074500580d0050f900b00300c1400c200203814044c008605a050140c03140c0d00a13010141840d2045010410001460308000c0e15441e00b000082d6210407800c0d501c1452001010012580d0808807900031880343c00c0708012103500301000340540769021005807030b03008288001c80d000c2c0d030400442254491030098080012040c0f003601145003020b03400c081c107141304880a190905280c0410f40e8018040e5400712000700040c2010200c0210241c050f46000c0711030b0340041a4001d0107a0170841040c9802001035050a840e007030751014903809901c2c10382c2c90968000a0700103100060101e1170749440110380400c10500da548001e4104c060500c0220300030510058038a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 732791312 1250 732790062 732790087
    0x504030c05010509150c1b030d0c060b01140f030604050721050406020c0d0e040f020c19030201020712030b041b09030201051e07030804030f080601090b2109070303090f0f0506 77
    0x5c0001d2540c00680a45814050250f280d03a12503503d148501078005407815581403600240d0110710401c1a5a182503002c0103035140390144c072101c58014103011010329207a802d5a203002c06400d9500c040720245450346000c0e0100300c240c0394041e141a041c0100c42003038420003188144848000b5400c010085020703203452602c80c4c02845211201d03241e0780180364131940c00c00e40c816220101000100d6060082c40e0341c600401040b886841e02c0158a80c1c041100c0b14010b1038040d1200300d825000c1c0c0001800c280e001e440346041c40c1008480b00000030b94601c1c4c1000580f905101d160b00c0707003079800e0f0b10600c084100c0c54090513104060002a041c40004500700810100400900307501e070308000552034a40c1001c0c0f4025010100940d4210f01042c0801c4151020522440c0c03082c0c41800142e6a42c4621032410440d440d0b95400b020080001882d40c240b091195105000c8250141620600400c465861800d000b0f000c10010b07080400540c602d280104050903100b0281401d4400c1290030954404400858 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 732792562 1250 732791312 732791329
    0x150d031803150605090a111207020f010f0501061101090b0c070c0906080c01080112080301050907030b04050c0405030d050301052119030e10170a0c2003190504030c05010509 76
    0xc02c520391000780320320140d18a40101003194803c1e5602d400c241c440c4000b02040c0c400300c03000b10034a00c20500a48500e04400c00f040f541200c0b90b40180c983e50801c00001a00351200064a050403c1c0c40f0300c01001207590104403200007643c0c05000700720260455860b075061000107412441c1210000c2421b005000801c205c1030005c110840c001c0048982d10350305107850380381311900203000c540c484d80000342003101100e408900c41c0c2e001c40c03000d00e90380c03c1c24100542114007410003010980e40300700c0741044e0703201d07480380a0194030402440f9856914100070103107030401c240800b0003080400d000422158813012041070b0b0540c41000b08071030800c03118481515181d1314503002e1000c050b0603d034441c01d05810209a44290b101501c1050407011134490590311487c2c6002e02e2132103a41d03c840004c06104903540f01c0020140c440c640400680354000e6400300d200070082321000c540e000001e1518200521460708507030300e10f517821b100d82000d1443d10303143c408034040d105180c180300c070014441d46141e485514 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 732793812 1250 732792562 732792569
    0x1909030c0327090c03060815060112090f0609050c03430e061503010b0d0902060d060311090a06060207030318050913020a0501391712150d0318 63
    0x910002007a42c0d50280c1024004d50075403540130a280500c00b0402540c0071401c1c0c909202094180320300c980300c85004442c1044507140a44009031343c0c100c2030000802c503080e1040711a001b030001240e11001c03810a14208894449201d00c654010342c41511007100781e583c1d8040034100c02e44010f49200f0080d2520b6990401180800c441080a144c08210075410003603c07805a60180d948000f20120200c030300c0610710080c02110000b800500140702c07107503602c0d040082801d1001c4c01c41411300c0b120110040959a60381c1046849110103522480740382061f4116030341c8104030706814043c49140c200060345486c00380c0070240404c41000070b43c1500100100e0714034001c1c1000b514000f0245030281040d01c40407024a0201d21660b5400c00020b031642c86a08030240c110114074944074001107103019001014020a07c54201c1400d040e0507501003130044421184498540d41d000365a0131214811450715040148081c012020141e02040c07551a0143c1014180307905080206018001c0307904105400855070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 732795062 1250 732793812 732793877
    0x3040302070501091505090f0612070f1d1002120301060512090706050712050403051c02060a2d090203070b210f0406090212101a0303031b0a23031909030c03 69
    0x1a4602b080d0055150300c030301c544003640d20308080194100c003c5034290700601d0002e80039940365181410929200040c10700c0c0d84158011a8045407074486500310320b030801d90004010880100c0c1c000e0001524140c0a40d02c2250703607014102303803420104040d0150040310300242c00b0803100b10035865103a015a04440145810008680c0302d80840365500011001c4c04040c03d006008071710224000c044c04e8050302c4000c1404001526802c1c0508410030098004583d0b038140c0f0b5038903045a2409030b2401d03c00a80500043d10710b0f03d079604403001d040e01030140c0fa00e01d4a24406146400c00c906140742c1058240c00551010f400328161801e8000104041c1586032045d2081c003603070203900408400d940c82004641c802c2ea0355801906440000c0540380c1c001114840c00b00300c150810244101c1c101c00041401240d00e08141a1107030121004900455240c0042000c003c0000113200405284140300001a02c502d5003c0c4603c8200765001051f901c8201d07001800d00020034481d410703c5080583c541840c0341c580 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 732796312 1250 732795062 732795067
    0xe01050c0f060610020d0206040206090409080d0609061211011803140f0f0a050715031401080f060c0a1b151404060c1403070f0203090d0803040302070501091505090f06 74
    0x10064880b0825611a40700388569004103070110b002007260a88818150061b0925583e160203000c55640240c1c855503110742d03900042c00026005d074002c0c100341925210000740341c5007800b000c1d004440d480d400c880c1d0b04814100070315000071240c4a500f10021005c2c41e02a1a0302c0703400340c00f541c0070502c54000402c14a00f40c100c0030100707403000030000f1000071040c007103c8042078030000e456280d02110a0161070b035003010034107010b00c0400001003141e2801510340040e000003e03001e6100c03034040a8211502d5500308080c40d030300380310b0100511031f0070010448240d840c10706c130718401030000c41c10995100214817031110800c003406010450740036a04c0c2011030900c4a59180e00440c1e43c801340c00c0ba01200c0d05072070078560071042445a84049100106803010601d5500da13810242c0d40d481c03825646c4402c5110800c07541ea02c50b19240e02507440c95101e00442622824507180107424403010340c002504100000e002003191041c00c2e0407090420400d8100f20383d031014502d001c59040c0d01a01504c94119400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 732797562 1250 732796312 732796333
    0x2031315120203191d1908040905090a05070e060a0303260c09030f03030705030c03090106080d0c0303140c04050f06070c1d07050906070b09160314010c1e0e01050c 72
    0x310185408070b10004e0004010f1803540e0350030351034440c2801e0280c0500340c1c4094081180e44100014403900c0c2c50003403585c01d00301a965141c2c0c038155902203c1003002500301119210420800b0071092002e4214182c030188546410404504139000c0761001804100428a0f15030600c940c8146140080700305403100b114601e400401c0100c079511030088503003c0d01c00c54050031448a40481900c0c01024160307110392554541a07184101600040c005095035582c4000000d2461802c200303400d01c1c41626207820904c1203d84c1400707801c40d22440f141e01c421000a5040003505c6425408550030748a0031030380c0c501d00c202e001c00458254018503400400400480a0200b0001d840002c800039115500900c0c00843d0340311172084400f0701400040a03003107002445001c00003661426042d41c813454450071242c0001410312501190320b8181c0c01aa03a20004041070125441e081c09001108011030034040780e45403840c480b00105007081c410323030b0742000300040c069000c0b41c1c490b404031988940140129112280b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 732798812 1250 732797562 732797581
    0x110f06070207050612150a080307120318020d080f0f160507080d081512060406090605150603011505090604080706031409100504060e0a0605060a0602031315120203 72
    0x2020380300d010251041c0c103000105850074200703c9401903500c05050040e51070f4124100c603a00e45880300300f0b600000d003a0012802d804100086d200040c09450303010040c80441c00c0280494644004884000303141078003000142c0c603150b0001200c1540302c800d042d80c50312039031520011130090740007082c1c03900310002d5a410005001c102101500780980c7c2507070301d5580d071140c0c82607681544450080214001500043c2c1c11000703d02c1d40e0702000c001074070602d00e94402d00c0312a828100119800c4034016074500311242488041d10039980c1c0191042e070100c4501e030f100e5001404601051040301d0040029014504070380317203e04180c41c0c0714200030f41003649a6444011444e160402401600c001030b140c40003032240649401541400b80543c080602041e042440107080a00750041003070716929103468600b5145002001541110742c002d010014407418402c0c10081c1c80b07007059001c201154024001c0c415843c0c00000050100d400462542c54501c501e403100b91800b002c0302101d0308201c0c0c03003c81005500c05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 732800062 1250 732798812 732798823
    0x90d021f0207150f020a03110106032f010f0e06090f09070c050606060711060304030c0212070f1205074110021506130e100605100528110f 61
    0x1001580e0040070460760307510071130f403800c0000003000040e405040c040020901502c00c00000d9181c040011426607187c1d2640c0c40030040000c1051410200a80741e055031414859a4240140d000d182118100c064040700030b00c510100d03c00c0c0ca11940d000140485159510080b1840107078028107454103a01e17000e40042c100e4140700409881d1402540000364030b903c2d05d01e00311100035601c807510124940f404010f10201d07800090040b001d2140340304103c00580e5801d080031304104404002000e40508003007400b04102c05a84c072000c1e00644882d981000101e011404906458915802c49607441a42c501910428190241186101c445482110b44003d626000000c1c00d58156000300c0520401340c001c980d0703113604040c1d0109040d82080450013a00e0701d5000b119008803400c0340469101011015681480c00300c0d21b07054041c0e50340714004c1195040501b03183c1c6890764141000e604248044014401040b81d942038080030080088000c00c005025040d0801d2000300d44045030200d191001c607150303445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 732801312 1250 732800062 732800069
    0x1a0405270912040b0a05120103081309050103260d09080d050106050307021b120f030301050f0a0b0a050304080720090109020f041203050c0d0e04050f040206090d021f0207 75
    0x92034903400944401c0d00054025018850411050315040ca48810840b50f9000b03019010104407080040300500785c0c07031419aa000c0c600806069948403000e11034100c00d4242c69024138241781c10903004001051041c111400780074034001040342c005807a4584209940304400201c0801d62418400c0302c00d0103800c0e0040c0c5502010a0b4080000d07903241e40c01030310b040c003089401e40300507440480d40090300b40c1c009514091510000d00514214181820280d043c280c4404608680d5030010004200328036010640d0f8140700e40903640d2507011814400d6407600e921030400a4024000d00002040401107a08205e41c413182d000408290100309505200b400c2501d09a403a5124100720000440e502840e4401c6841d040c00d41e1407030346c1c6030500e8030035051510b5102100075401d020307040c80310703038035507a401e0010160700c03805030f95001d0f8541148070800044460203001c5c10003114a144c104401a1200e82c210744e403101040710351141d0003116200160920340709581202c150016501d504007003035000200c10096 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 732802562 1250 732801312 732801379
    0x30c0f12092a0f050406180903020c0604030b0f0105010e03030d050417040e04020a090b03210c06010608070f02010218190812040911181003020403082b0b06041a0405 73
    0x4403036a1300c04200959105015030310b0380144d10036000350382c0b28080d4004c416061090058a10280c40c08000030001d8105a000b910140d902c8810800e40d00102807459014002c242001c0c01b003e04034101003507a900844081005880e55100800e0030700c41130300100e41c0c80d6009a0300540c0e507280c5811064100040907034040f4040c510a15012580c00464008d943d02028041c00400b0094807901d225910000c010030895801d0f841040074112850007800031a02a000a459070b10082c144100002c00f0104c081c203100b802c40e441031140c080c5258018081041142c01250700520300c2070f0511141c60a00d0703036544551114400c0b15542d808500340c134406030044550300d03a010042000c0311610a42d40b81319600194841c2e6101c1c10591596180c24031282c22940c80524005041946a0399540100c0c1d0003d024600d0303024884000424a00d00480281040c1000300402d12164040e1008201c050055000c0c1046004100d0300046d100c4204070152401004010001c0319035480c0c0103584c030150703105010503029 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 732803812 1250 732802562 732802589
    0x3020c10030f0b15090f06091225030203031b030c0709150f03020603010302060309030c060a2a0212160b0f07260403210c0f030c0f12092a 61
    0x103d451300701340c100030034100705106504c2e00240710100511107101c0c1c0c6005038071200c1404070311802d8842d400340a07500d40d40304000380613603510070b400c2c061448500f5107039480c40da02d032003801e00050310080152207010301d040e071040b400107600c0041242103004504040000d8420a03c0c0040d0261040d0050700b500b0100c440c41e802d420391100400325100409000c0603403c02d004000400040c14010019503000000304203480c100b050610f6003505010055501007105511180c07407540074011220544102840301102110001c140f110107900c1d0207000325809004480032683d09000c1e01e030b84d0440c4e4240d035840f40c0b52080c5032030441c1d40a41d8039a0265207000006100b0400f4500802000c029040c031103000944000c2550341715a02200c0d08014004c048100141c15101081a44d101b030007502e40745503c4e13480b000030000302100000e08441c4080c00ca40208106413100d140542c0c0c2000c1590001c00d441100420000d80d5810180a661080c00d001207041402021803440d1000010040c016240584100403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 732805062 1250 732803812 732803831
    0xf0d1b09150908121305060c01090512090102060f090c040c05180402090105040b03040305040e04030503040501320c0c0f060103050c0f01080606071b0b0a0e0411070201080403020c10030f 82
    0x102c1400950250102a510640c06a01d40b020f40c28054420103840f41d80d840300b0b1540f9140032410320303000b6102000e51380c0e44540c1000b003009424030090f90a03012a607622410400306a0000b9600d0001a0040c103651050307102140100c0000d005901281c1c1026109008048405400810b180c1c800b503d800c241442c1a0b408080c146020700860710b281c88169540c50600f8200040a50154000b0300101d040c4502008005248520468003e1140c1d001e0380f04c00d920f915190801a0a4441e4001310300c00c80c1d80507440d0140122000249888d1132052010551940da070b0b100401e50310341c81000c5c101c1c90036108044030600d940c0c03000203806060b244510300b0340d0b001c0303074180c024416106103100f03d0070b010a42c100000340440c00c0180103440441e015454100003141c400031552000106600300050a560000340c0e0b514454200e509080c01110541e42049045990f0707480d03942502840c44002d04118400c404101854030820103000c100100034000588421940409001428006030709060142482203e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 732806312 1250 732805062 732805067
    0x70302060c03011a13270f05060604060c060f02070c080d0206070e060913050114040e0304080a0210020f060f0a0c030b031c030e061e011a0f0d1b0915 66
    0x143c2c12202105120b181e800340309081e001468100a04a0081c4620090001401894214481c02d04600700180d1030401e0301c02c0c48200282d40e550f1080941041c1002d040c04100d8861108072022201603160100a1581d1840c248014000e05240c00880071300201da800203000d0511401003c480781c08045030260b841b940d4059031034140488140380442c03905140d1003201d04016001b415042c00080003d1040c1d00714000100480b2000c0c0c110b400c043c007607011541c00324181132040c0314190301802c1c000c41c1803e02c2c01c0c003e280d5450402e90004c2c01070509004241442d0f00030440e40c400114071034241c0301d440c41d07d1003809003400f00c1102c8882c40035040c02050b070340d914002c0c803402a01d81009806059005041d203880004401c02c0007400d4200f585c1d500c2503080801703081c0025030103900c142140342e404a412403003645101406812500c104c5e40600c02c0154441c4880044404400c1011540c54440d03c08000030802040408500710311060420f110b14416035000d05007030103136058200394156808035000c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 732807562 1250 732806312 732806317
    0x2010f0e28080c192304050f1605070203030304110d1a070e0a05010f181802030114040b10080408070b1f0603060f0b18033a0c02100210050c070302060c 67
    0x118209021024828880c0380d12602c8070b800c8803044174250007150b80ea40000301d001c69000710748045400c0c1100092040703245460844420080c81450810304008803500069100d22021b000282079580c3c803070003042c098a036a0300d6901c589400400c441c03100c0c4445001040314032811501480000d1000c0d4a154036860080545c01c02e940701a51030303060061154109550351200107e0820740c20610440000d114003001a230021009480640561039514114440c1120355216488510443c14403400c411592103550203d0041d030303418a400325240d1954203120302c25120300306019101c8010501040588400c01c41c43e000c90f500c0010580240b541d4524048081301c1003405084541c03140c6800c10041085444050309042d02a03030300707050508d4003090000c0c0c074241a09182c0b100341c81c103442d520400d00d400d06450024049121a64158460b6002c0c0e00420200101c50300a2051b41c0340c44c0041c06040c82001440300c1d030803600804210505080ca240303081a04076000071401845081c0c0061000c180c078500307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 732808812 1250 732807562 732807589
    0x302010510150305071106160809070e0c030a090b010e01170a05030f090402040806100e0708190c0509130204080c01054003080d0509060402010f0e28080c 68
    0x2d4260080c8450004601410000d444e0034200829040d580400c0b160030300685010300040e181c8000030200b031441c0a004008005c03c7d00c4003d401c000820003d601541d156030343d00043e000391155072039075903e42d14070040003014006443c4404d0b00001007190800e81900301d040e0381d502d100310b0220081540b40b040d6964501c0c00f0041c02ea802c1030280100c0d5080d1a005068203101c010300143c00c0c00e884142e400e190240403601e4003505000420b00f0000349004086081d0088250714083c0858079004814081031036150308198070a03555400380c1c01d1007522a5080e1221600c0081c00001c0d21b0f445568294040d41090194402e18090115061540c0d800340c4122004188e1422260011012040ca240d001024042d0690203400340034504035a101c400b00c031010061440703110041e403102d6000898804651004210005030343c0100103210246c3c5e045021540001c09603d0a10f100140740707804141c8034100d030892014013240103611124081415095842641c0e1004120760b200651901001104082200c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 732810062 1250 732808812 732808829
    0x108010b0d0320010e15090a030e090a02120f071d010e04020c0102040b041d06040603020105120718090b09060a0302150d060b0f130b0f0426030f070302010510 70
    0x100000a40500489100c1c03292040c0c0759040c10090b102c02d1420341d1200515200361b500004a50164007840c800c80503000800301c4000c0410340c2e950354010700f0015440907218800c0140c0000100c5042103901142c4014601070710342c070400d04194401d5811028151543c00200d440602e0080003040c58258801c6c80c01416900c040300d08030f0030800d200003075100e6500641c2654007044041030740300b02400208010f242070320f809030588481650b00d022408014007000e12450a241c4104003507a4848241c8003da03558180001d421303101c04100381c6d0308503200900e2f00c19220030302c2c0c00000c081c1c0305540007144150b02a1214159030340e40c0f004124840c01280402580103180c454000303d8000e070308024144415400c4c1002950a44800c1c02c450a80c1041110503d82600000e4004440d0031705415500202017a0f0046403c0c2112140c10146a006500820307200c1050500343c080e40a0704110b25403188005c2d003090f07a54800513944440c8640d0310002050303000d5070034400414a500408100715045035201d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 732811312 1250 732810062 732810079
    0x2010c09052209020d0f0c030311010203070e04150e19050f0112241505040c0201090206181f0203130f0f0603050403020a061514010c23120703020c04050108010b 71
    0x3403101d2802030070000d8090f178002c0c505240f15000950b18134000c9042c01e00a4110000300b81c598a401000c1c050701c01e0b40001240d005000b40810075401a0351803101503c11200880c294a100511400f40c0e141c5a0200e40001c440314280401d001659400100d91008160140300a64840c0900316012000b84600e0b02c480e1400d03150403000c6010744029004840542d89250117013511a0403803402c0e201a40301d1020f0300c00640348200050b240c940300d20750603076006000034801440c85400099081c002c001c0790b06652400603603204000d9860210600f44030000c6000302e0030580d03c0c0c1d04000e6598010040070415005041030200c3d440303200b0444d1201f20781e01d140002495030304081d0118003801010300201e00b0b510481244c400000d105d4020158000817001040c58901c0c6003440039844429019006c0d4140202c10b0089030202d0720700b100c1c040622010000c2c4041019100c00c01a1074040041d818486524012864000305940410722a4200384215024011070762650415400c0710000034000e941328801c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 732812562 1250 732811312 732811369
    0x917340b07091a0a0905040b0f1216080c1011030304060c030b121b01140f0a091505030912040b0d05250e04151a0919030302010c0905 59
    0x680040e0341d80102903180004055603194910340c4070000a0505100d4800041005452198411070728401068119028072946032203070f010130401161425510b0207181d014140c200c0844041200240c1e08104c0300405035215902e504054030b8402c6100710520811201d961040b1403407162101c2c0c0c180b0400c8402031403541c1c80303958406005040c804091000c0c96100e210068a0f99208141e120510341021301400350405081e4903000003405804c251030500045903c002c50142c5403606031481c641583c0b0350291b8903100140107440c005290344c8088c2d000b90b205441c505070140d104014500990a4400700d4002d0120611800000d004501401c04810400c0c05080d4a200d8180c10079604030101c048a8072149929400309444840000c00070703404201c41042d83c01080c24244240241100c102c100ea120361030800258100ca5500c0c1b507e60084601d011030444040d50310200d07260081c815814100c0106603491801a010784605614100402c0e002500018035090006030403003202850301408112800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 732813812 1250 732812562 732812573
    0x10b0307140315090903090306161b06060803070f12020106030809192409050409121112070b0601020d030c020c22050c04050a0f05010801050f04091734 67
    0x14000151844071240780049500c07800ca8145c016549613000d10f80e10b00350a000d151402c1c0c805014401601c00e0081c01c03110495003c3d9050034030041d8842e00c840b611a0a003400c0018005070780001c04180000110300040250b44c00041000704e120341030040e565290b41c5c50680c01c17160a8071005e82680400c0102080c20326007200d020084912141c960b208050b204c51014100f6030040e1340462620703104520305003544d604550300800901c403c5030103111304035042c5e541090003411301a100060000a606401c0d01c0001440b41e000c54000d6003580a841d900d0600f03190303401907400d0310b6090160045445080c00d4030f2207070250b04c00c028010780003410a0a181d41c140714400d010710140c510794141558000c0c6039100d0070300804ac080c0700c13030165180e00c56045c10700300f0040750102d174801502000720480c00c2202e66003002d5a10304541080324503a108500d90000300e0b01508812100a0400b03d45110300d1001d061000c0151414000c00d14001324034001204405c030b00b00350001e00d1010248152900000005c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 732815062 1250 732813812 732813817
    0x20d0912030c021807020c040f110405010f270302130911061305031c1b0c03060b04020702100804030305010605070b0c2b0501030b1e060d060b0d060b09010b030714 72
    0xf8809030030013088640c8600100782902c0241c500b02c0042c2c10a0b404004940343c00c1c001c482c030600c4415001c001e007071060000b1030110700c224402d00e41440300c2c48104070500c1c3e0240c8446000303401400c0c10b0340d040c51604031009400c0c0e0183c2c007040b48a105020b54400c0411a9441012000c682c0032031482116026441040016080100c0e2603040d55003c41000c1110748082c080000c03450b505407401c0c1e032424003a960250042080c0d0b0355100040010754800400714880700140c2084a800000c0060b02c40301c1100418003030300c164000690015a01103494203903035408920544641e010303030b904110990300d8a4040f58144103684000d085681d400e0f000c1227003299000c004207110243e4241a904100301008554810042c401501d0581d0340d80783e00401c1071020400c00c06a202200c059024991401002d03800aa08400b6000e54080c510700000c1c5010005664401700d00b5007401443c000000d18141f40800240032103059036401032040d40700000d001035030341d001d40c0c3c000c0000341c0f503c4022005560107801d458 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 732816312 1250 732815062 732815087
    0x806040212010f06060309060608060c1606060506070b0405010609110a080603030409060b12070e06040320030715260714070b040803150a080c0f0103021b06010303020d091203 77
    0x955031600403c0f8005841d01c07410000b0202505c000c1103100306800c004048070099441100613420210421124540030300442d01881d2140000d40801c0b44641803940040105821003078100c0303000601c2c3c00600414001300b80c4520b02c00c00007480659140c1400a050300c0c0c540b817100d2107540e4240b042504860040c400c1d42d0b80010701904580c14541d48a164605850f190341c000d0a100380005104001051a001041c4e405007190804808040020010840501c42d621001c0c2841d2981c00780380300307072130200d8100070094440102250040d1b52100002074011000c1c080e89004101014002e0200c1164580364185809240f9403070300c1e180d510300205440c030070800d24090b80c078201d08001d0080018900000030340113900800344d103034607440d00c0b05e00c101c1d009040d24a82d0f0701c610a80c50040208040002d81102000015190016104404001a4083d0040300085101041c1d1406121101000019428100da01030307400c40d1407035882608241d401c2004c0d4082c4140f41e031420740103140400e005102c0c1c0b09a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 732817562 1250 732816312 732816349
    0x705060a0b0a23130207020a06030b0a051203070605070203030a0e1c081306060303020c0a0504050f150d060911030d0c0c05100c120e01030f0e0a060e0c18040308070302030108060402 80
    0x50030311040050103d00d42c50222609076517000c42c1d40f80540c200108084090440741c2010011501440005206494603100f2240f15010349104807400c5d420038002d031442194841014803290030311101c065161b400407a4041d80083c9084505d00104400080b0460503240e0400b1210048041050880f51044010a28084440c84080ba440055010300c58500114040e0303010700300120f080c004001401c07906a00c294403d500300030034012143d062810594200d50407104803030351600140f010680d14103008002804091500c14004184406600d5400c42c4e05000c4050b11410a0400000d0300c090803507244c0644405510740c400c0c852070500204003a041096810881c40e00806640e4400810405a031480c00046c85400000346030350b00340c0240420174034406002e00c070b8100c9a146403070344d600440d20007502c05515020207020090041c0802180c40c04050108030703000c42ca0f032800380b100c003000742c404800160050f000590980d21134400e4074140c4011201516440d03c4070740130404a0003640b06c07034601 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 732818812 1250 732817562 732817619
    0xf261204052812081512120706020904050603160306090c0506040605130b0a0c0f020f0901080a110616030e18100f0510090621110705060a0b0a 63
    0x200140101c44105810507416941000030103076152180c00e2180ba040958240a00780040c0311018420340798911811400b5a0841511008241b07800c0c640810340c1e240485d10800080d00300705010003134000f08403e900644090200340c540d078040c55591603202180f1020361089100c14400580e46400034640700f4090111510301039180d100054890340b0551220300483c3d00055914614028450b0440051140c1010076041240e003460160082903a044018844272100c1d41c4e50f4110f503200414240204409008110745603194120207550324030414068038030743c0091101e847c0524002d4200d07101130341d8920103064035a41c0d550f410b8070881c04c661001303603014a100c1c0300c0f04881c141c540c84d8584281650b2496003261460070b0355600e19407526400c0203000707060f10711141d0b0400d82c1104039501183c091345041c284c4403054014400e1039110310360038150200e0414126002c0030103264040c1c0709e014010405d0baa210b4449490a40403160800741030f0ba044881240b040041c0d040c3c0c00d0240035003d010480703554 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 732820062 1250 732818812 732818833
    0xe0f04080a1416020111060403090b0a050c03131d0105031e0102070f0605012c0c0a0203040f0b130819080310051c03021203070210091505040f26120405 67
    0xc0d5803c42081c0c2000c01d0041542c21081d9070740700052480000e00030001c4c144c203051035200103001540301d001d0800c49801c000748100501c3c2c410300449011200c130001f0740743c881c004201a10403040700c030702c18140c80300c07102c071103402440303185400090403224024004c0c40306108040000b410140d0300e001642c40d9540c01d001c2c0c400030403241401000410300c6000000781d5581407000c0c8440d00b11142241117100342d08640e04c24a54000b20050b19004105244015100c4601000032440d610903500005840d60012030005600d500c1301c0007415003201242c0302c007008980c640400320f43e81e1040800c10f84500341b0921900003c114050000c1d50080d0080c0144c2600035200d4000c80c04200c1200511082e000d040c1c88440e042c940d052040401080e43c5001c000c0c503500704288000c1d95001200c42c0e120440c1c3c0e85a44102c10004402003680001152031010f200600d4281420700705c055110314240c610400c18107004841424a20022003840014007896081440484840740c10040042040780c0501c100084c92 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 732821312 1250 732820062 732820097
    0xd090911070f060c1112040e0c0903030a03020309060c0c030a230f091009230301090c090b0a1a0708130b0301030818040605061204110a1206060e0f04080a 68
    0x940c400d074050350307020402886113800100305da090b03070301c3c07004994100b86000c0d1030a07000c0000700e404880120480301c1c0180c50b500d8025401d4480c040c0c00550501c800655610305030340540195104221a0b0240caa441e51128207110701c601c0760080054030b68004005000101e8020303400851741e941200c02240d410016030240c0600b50340a4624030500500119072154185041aa480e0b40c4050038030341020424602442d030000b4000321030a9008800e0070001292071a10b096102c02611900101054841562400f1000080011003d80c0380182c54034640070445000c050002c0201d801d00d03030445440d14445850b0b00386641c10442c207296000403a1900010030002c4040514081c500a06845941c1da0180c1030a010400710703d991680160700f0306100700003075074803102581e5420385901c1416995940d14540381114603c094800c2d0341c858140f2601040040c00d882a22075000d22802003008450f445101001045404940c68503a2078280000030780000d41c200702510740303d2142e0074001511308a2822a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 732822562 1250 732821312 732821333
    0x150b03100e0712170c01150e041a01030c090c2304050a09090c060c082106240301050427030804060c0503160315030206121501020d09091107 62
    0x2400c40d80c0d51540c0455503140c0e824006080142896403180352800101c0d40d03151000c4070540d00580f10308402098058200d007081d00120609a518080c941c2c04c5901d0f1404900c1c030042c02d40d01a2a04416a1103444800d4064007403030b41a2500020200e0021745000748200c00342100010801c00c1100c0d28140e240509000c034a00b0500701d40301c010031034446040905000e040d00856000342d1417681004040c05c00316240171100340c00e80319145400100300d03400e418100c0311407082c02420906500300304007015040411200707190207410221000c42c01c800154000c0c10b0a40101c1c0c10400b0210410401000f40307117442d030f104011543e405d4002c7c646041000b02c2e90007401d0740401c41600442d082034100300030444e5500c1490015115410501d0960401c5140d000014120010040506554030703440e011031829894039000840c1d00030b10282d5200d184448850407100203a80444c0c0544003000108815030010984580c42d02d49030381c410790201d03d000100b4000c1c1801d51031929002908200e64408074010307151 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 732823812 1250 732822562 732822583
    0xa0b012120030f0a0305070b0703021b1e012c010e0d02071a070f02010c0212010e0c13050603030324100f0206011e0b0304060204080a051b0d08030103150b03 69
    0x1808140752039414103141c1807220078205090650000f880050010360024280e40e0403a402c190454400e41e540682500284184c80d001d181c0601d01050255520400043c3c07000321026020743c00011440d40a0a1401e031012a40e09003903000030420308a8541220b120950f0b00d0100810010844192402405050411003854080140c016281c140580c22100c03050081c280122451070745000c50baa00c2e06907001080110090411845107880c03c190b40d24000141401d5400900070880c00c4940800c031651284240c4505000341011141e2081e00403d5209551080d9006000783d40f550b40c0324848107100d034226201c0090a003d580001524035151110701c5000002c480d251112112414003010f40380c8101640080304160868000103810720040380c03400100c03201d4a283d180c59445034a0224081d0045401a91396841555154000e20000090405141c810b41440140c50b046600c00c0c4000c07101145c50282c0f441c502000108000740354181c55a480b03480e4038400081501e04c00000a040072501704 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 732825062 1250 732823812 732823853
    0xe0f0d031106060303040b03010603051b191b0f0b0a0e070b040302130507021c14180a1d0c160c06030c020c0d02030a0609080409050906010311030a0b0121 68
    0x1581074007618204880c9030440b608400842c01c0c64a4900a1011480140604000c040c0c64002103002d030b010b403030070a001100c1e90b00921034855440d0b10984000c500da19400b04001842e5109501d002041100d03850b084a8000340340b504c0c098140d8403aa02c4d0044080c00440c040c0ea901c4501700c0c0c044e0340034080c01024103980072120765564554010800715400b142c1901080c03511700700074000e48030380004c0c3c24082d04180d0700542da070340a40404140d4107030703131009517001c0a88000218000402c080e504100d02003603080300e08248442d2180c042a240801e16110b4040340c104a40224650541450241849504501c4d03610100100c40e521510b981945500c001c0c082a00c600d943c1d030700c2d55010b01030b64001c980140c60390607000355940c00090351600d0b07800340500616901e07524481031107200380c04c0700e01402c40311406202d142400c941c42d82c0d075441c0034481503c80f070140c511103542e10300c0c010544c0890300c0d80000300c1c3c1e5200d034240005000204c2600d103404c0500414100d070075002881f1004111003003c0c110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 732826312 1250 732825062 732825077
    0x50a061b0f06090308090105060109060f1107090203181b0d0623060108011401090506030703110a020f100c0c0605070516081905070317070c0606080a020114040b09010e0f0d03 77
    0xc4c83c01070124000a003944015034104401c00c115030764400d990a040741c12602e000e00050000c140d00f900c180c06034100c0d002c3c1c18080c262001c102848140c0041d03000e04000750740c40450322030040c0040c0c0c41e00c00000050f00d845200a201048514000c0c00b164141d030b020f84800125050449144941c082601c0004541c00c80d402e001c1016079a040000280100030540d030b001c0d41c01d1884000200007070141d0090030f02c146004000714502c140b203a80024407a030444000203a403003040110180d550380013041580341c81e110340701c0f0b2003d07018000e005502d000e0480c1e031140d1824441640d900c2700a01340092110f41000320900001304052a1140d03a41d10f203500441400ea40d44800c010b0101e0760320f0381600040288402000b00500003075010510318550003e0410006007500c800800301d80c0c403c1710000250070982011000b0400c03007400314100d00124801d8071221070039440c200e103441c0303103010f184074083c0001001c1c000300704594001e211388100c460006140b241051502000a08003010391740043d03000603002e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 732827562 1250 732826312 732826331
    0xa1806030903030b060310050d050f0109140609120702120f06101a03071b110306070807021603150903050f0c150705030c16050f100c021006050a061b0f06 68
    0x14484c240b008041512010300c2c42c40d00941e010307111007282c480c0900603050041440140a010711980b0321481c480740092003250658285018102c146d40039906d1680a1603011400e40f00001902034080200106290308203845c0b50201301600c202c0ac0690f800c00d005100b03040742c02640034043c8038072501c04500280d450760704100400004117001650080500300c104148411140c02000d25101103040042829000b220340c6814074640e8030018040341c03d48540c40c00d0000081e00281d4142c0f00b04141c1c0c0c200c1d07101c1071811f4590312800340203100181550f041c617861540c0d2024640c0000302518042d0802c1c13031a05d5070008aa0003503034840721481c40d140d0401c262440000034280380c85074119843d49461415800d282840000d07030302c5455a882e0744443c4062005080002c1402040141440714040e00c007520135940d001d0b40500038000c04030005010350ba42800100d5182d01c41c21041e00c40141c20b500800d81820b005032461100c0a540a84000480b2400e20008540c008454000d910402012400350740 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 732828812 1250 732827562 732827567
    0x140d0c05041401030204030803060f130e01050f06012f01020f03010f050a1e1203030603140c19031502030916082d0303063a1509170a1806030903 64
    0x10304840d4541010b00400c807c00128a200050b0703600030604581041d400401040050080b17010094802501030070150132004036081036000d00e01c20005801c450034541d03a12001107400c585404184210b8640000740d000d08850100702030320702d602d2007a000600c0c01702c00811340e00c1d10341c00c05d034003903216518030b20401d21081c06c102c8809402440b40c14584500d07a20711300c00b1141e0000080c05000c40c1d03d402c6084210070325100390424001035400c0192403800e508000302c601c0d2540c91345c1c2d895034010340041c035414100702180d9400300104c035004180c0030944096001d0b190041e600181040181b840756420700d24042880312000001001414014142103d40c1d20202040000b020080c038141468034480c04400100802260360002c01100d003070f40c0314201c0700351100ea07402c6007031211a08424203413a214030f0544a2141e00f0f07000c40c010320a800580c0b501e0310400040d500e000000501480402503140300e0000d01601400850009080c440b1410307064074821111900a503200c90b001a07140c1820809064 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 732830062 1250 732828812 732828839
    0xb13060b0d0f060b03011503020405090114041a0f09151c050f12070204050601021e0c03071401021c0c02040504121805091302060403020621090d0906140d0c0504 71
    0x80700240710f040d1410003200340c180014800c5402000703045982c80b041c1841380c0e0468024003402800c08ca07103961281c1181900d9100c510f229030049140010380940c2d511807080d04c4681800042506040100580c140318446e80090400f03d070f030f02d10003000c8036070550b01c6014441ca0100401002404d0343c5160030000d10b041d28400c000640d0303810407000e03900c50003c184200c84100d82c060f10042810307190840100d00c1c280d80146040c5a03129009000240c0315008181405401c0702207049070764042d1550008001c6201500d810307800350340070b001c40c03240c0c1c0c860607002003090707544500f04810400840c0e000325003903d108460031615010b407031103046082d50b0444911001054801e01c0c4030308081c1000d011480c52078015044002407000040d4220465445a003114003455001d44415180e42c1c1210001d00c0400019180c44644002040021520b00700003d01c045608019601d51406918080d020b5900d05071640ca410315070351007008010b0180043d8091b03006040c01170350343c40d59075900d0400c441a860 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 732831312 1250 732830062 732830081
    0x218071106100308090d1109070908071d0f0709090207050a031d030d110106090e070504050106080c160f080a0f0206060a03110907020a0f06021215060d0b13060b0d 72
    0x1032050303002c00c2c400b0891000964101980030340d4410403031205410202d1000703114412039507001000750100407900e07038024074520071580079004035004151203000101c505a240c81401d10126040340c00909004980b41d1030541025050400200e066110709100c4240d80c002081076959510484005040591202444051502440e42d81c0351600540c00060303110510b403441c2c1010420700480c003610300c0f0340070b5105000600e10980304002c0000443c0c0c802ea1500c203540f240398400c43c60a400014080e010b040003a214804805901d443c1591288210306080c50000c001d85803042c040286c01c0c00581c8076401018000d0540d143c0c03d080c0120000300902e0100001c04c81c0d0700603486840100300095106003101e00c00c0b60100c82c900b840c1d80e10000228a40010010702070007800d066541e4106100d003a9009109181c003410a100c481e0791880010102500440f46c0e00d80c0007401000040c1d43c9099a511103a914140100440401004e4280f844103880e100d4020700400840028030004400e010312654051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 732832562 1250 732831312 732831331
    0x1d12100209150c0d080403090f030b01140105090d06090606030b1e01090b030a0204050606362706040b03070902040929130f1b020f010908090d0218071106 68
    0x10882928500c94803413180d124030a06100083c0d001c83d0400d4000c4800a01070000402c0300e2800941e2410420305d0007a003031003808100b038040c0c1c1041c0781d2544607104940032a0006068600b4200540d501e100040452000945106a0701c040100000c0c1000100d140645504400b22500d008000d44640001406034040b00f03015242800341c1800c0d450115140d4855501120006999a41c860203e502e903ca203071120351910314110078000180c0c130951405d12110400c8060a20462008010311a150004d441c98041c44449140b03040101c1458404059010b0300151000c15005041700c0428a0b040e0f958100d560700d107402140502c05000a84180e540e011640b412000030386155003d50700e01001c0c50050603024504006082d12040303050780108074120315490707040005424040c140385910109483c1e201c01030003031840800e03075200140501e2a00075042032046160050143c10004425078504007282c002d00500b00040480e801304040521480e82610f881c1d00104a031a00182015802800c401d01c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 732833812 1250 732832562 732832567
    0x30e060603150a110702040f0c1403240102240a0b011403070e01020f1009031209030f08090f1b0f10080705181207061e1d1210020915 59
    0x340000b03035400d10760b04821601c0d8001000e90b0000c9914903540305480d0082c0d01725003080002c0703481110561106001d00c03160b907502c001a00c0601903000d0a80700c00e0340c0a0103010800802070110340540e1510315400724050040340c940b80303450590b0300740300c1400c0721218066401c0b08041100381805030186041d841800d10700280030441e107105450040c00b0261040d010440c040d1038a071101c2e402007002410500340c03c800c48451041502909010f48001c5600b20000b1344c0c3c40258a03070750405070207010041c0b035050311400075408941c24100c9100000801025043c841d0401d8800440000c3c4800e0045100055035100142d070a06e060001c2c0c01109081c5601070754099055500340d561002c00e07240c2001151800903034506c41e00c203059035101d01803140c0f0355110390a442401c40180c0b0014001c1e040b00c2050b29804001070168190540245d03400e0618000f20b1003100350601036603640203860b500c085008200caa0a02561071015150000d54111040748c154001201000382c600712002e1400f08040c40121031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 732835062 1250 732833812 732833833
    0x11250b0a02070b0d1e020a0f05070f171b100b060406360608180106150507050307052d0c0604060e0d05010f0c1b020325050d03030e060603 61
    0xd540c2c81d25403040800d0803401242c041c0024005420200e06a805851030030050450415600020352082140e900843d004101c10750200d401142650392083d0065104051642c840d00c1f400004034002c5442d9001702010002d00ca480781c4005c4c019a86191300d48000c08828840e00c0d5110100e800140d20345104000a020400c20294020104105503505010840030109100da00032001004881c120b07080b000c102d4804240300380d102ca0703000e100340c0b07139908003841f03031400c04410384e080b42c907240215040040348140c03050b13a190140c03004000303040c442c40460b840c06105444a0b81818506950102c00c0503d05042d52404402d40500d22118403024002d400d40b00b149034001403040c46107106820074041803040ca002941c0d540c40044030055082402442140030103501c08000b0f00031200840702017103600c945407410754403084040c20800e40c003500420100d09861040703460958482c100d50030b0349400e00800300300350f200c1551048845110f41c0740420b0030421044900c0c105440103040c02d0081e405a10b466 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 732836312 1250 732835062 732835067
    0x31b010b0609150c0f07091a0a0803091203090909060402090a0606051b011b020106050406080111071b0f06020a0b090105060306160504092f0a05030406020a11250b0a 73
    0x20103010701c3c540003865890b840611118113002c101e10b0403404502074030000250b040126040780402c00c01008907144160400d030104424400317640502c51641e031044c46a05070606001d14015000301494044900700f400d484000350030041e0403111018650450014041142403549800d90081800d12040c01040d06040b40200720380140d622580c0d085504025010080d5400e6200c4c0c000c0c011080000d5640501c80c10010780642014880d041c0101e00e81318001501d0007040c80f40b03050300c031194802c1528200d12a2140a01a80c0900717080c03c0c0c0d1802740f1070014042d01c80c140c00381c00408680d0058441031500b410a80b1220f040103080f100940d042c0010040b107640d0105440d0703404010941811900c1000640445580c040c90300301000c40c82c40e25600300f610001c104c1542c8048442c2c40c0c080b03034010074a10000c1003540503007050900420400d0002c40d002842da034004c5c3c0510440f034545110052101c0300da540c82c0c01040c0420858403480a83d9414a4502c82c0c14030802a003200006c4900d00500d02e00300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 732837562 1250 732836312 732836329
    0x16170f0d02191d0d03360b070503030105040b040e07081b011e0f050c160321080103030c021801120c05090108070501140f0c03130e040309030f060b03031b010b0609 72
    0x81340300e12001c0d500001018040c03030140c1035681840150740031901500b00251078000c100d840761143c1c1003a02100281400d80042210902a4040e020b9411640b90506020203480ea052030907501c5500c4088450003030404100c03000040103001c00820b03c028550050184900300005118100150586556076212131944c103450492481c0c0392004c015010034500300c886000e5095560060f000342e100c1d007400411130a81040a890250141408101c008801840c2010783d040b40c1001003803411004101203809600401141c2d400642040e07040c0400c01c00007070503024260880220039134250444000d010503a50041d014200a45000c0341e1941000c4503940d4481003845118100680320080c205290301d4a0b003a12080c21010103229261700d50410101d8607a0005090322609010b61000080c45224900c3e00030302464241c4c9a440440b400c40d00c3d40c1d00c5c170401c03071141600c013076849071950801520700308000c003012002494601c2841030406426400c1d65502412148204010301c5413000340d513108140c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 732838812 1250 732837562 732837617
    0x1050609060d0e06012c011a0c070f0620010e0712060e060c04051905010906110c0d030806030115030b06060714060c0a030e0316170f0d0219 62
    0x1d2180e240c20b218a01c0703001402601032080001d0040c1c0340005010005d890041a0481c04030340100a644040780d10030b00c1d4404244a6400310034440704082e0041c1d82004003c0954920080603034502c1602ca448820714241154080070000307280f01d0940000c0303048011050500c4203202c00038003041e40389503120380d0382d03460078091415100150803003c0f04010b1a540410070080e1301c2015a01285481c0c02c02c610107401c0303445a507004901c40c01c06180f0580200c0c1250081c0c0f0786c140c4542401c1030030010104c6010002c500c06000603c103800c0801c520f541c8014040000c02e1080e650049545084024942951080f820401c010099080b050001480d000e001380ea0101d0285c070b842d45c9480b2981400c0345000a080f180e95254000e4030144044805e005008041d00380d80d5440901403407060701021a964800e4081c0058800c0d80d05180b1000101e201d01401c0d26106120030f41e90801e44403066207a810703031056401c402d0440e400641000741034810f440c0d400030340c00603003803048070140b103045c0c2503c15a84161 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 732840062 1250 732838812 732838819
    0x20a0b04081c06030605042a030f0305040914010503070501020102400306050f1021080904020a05040312020d05040b03090114070203090102161d060a27050703020301050609 76
    0x55030041450300d15205180038042c1d802d0900c2115130f0381c202a0010882580d003940d00f41115000088200e40e0324408040c03d464000e010800a40745445181222a0070320080781005010400001c0d400800e02036204a030201d80400c001551402c0200b514041c2d0a41c0114196401400007051003503881d2800150401004441c01c440e640e03940010512560f9441002003051021101100340400307a44014451020070001d001d00361600d00841041c0f000ea0303c0b40b500f10224001f003003040000899004111144070710201c82c00c107000300300014140d0700030103100c10000710046020000d0100640320810311529500107043c00941c0303594010607902c01c82c016502042400408180344c54002d43c0900e03a1102c00161101072410200030080d200d500c980c080f02c0c010300c103240f105204c02864107680402c4400301e884250060840d030200c05980c0c1c10040010b070380041c203000c00140081c01d5100307a04c3c41d0743c100c485c0e0360b41c0826400642000c45a000d0904d40030588140300500c0642c5624044a00d2650b044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 732841312 1250 732840062 732840067
    0x301110a0c0804030b012c01030c180605030d0507051b09061e03071205010c0329011b03020d1106090304181e0b040b030a231608060a0606020a0b0408 66
    0xb03007444251482203070b00080010049100019828680141308215102c0449001040110221404440c00c8003800068100d01c80300000b001015420800c402110920700d401181e11507548000a040403809907690740440d00000d424810040203100c41d580c03445101425100e070704441408200031a00c01010075000f2500c00c1c196049001800843d2601041d005044880981c3c9594010190580c9400204c680b0343c00d141a00d1912402802030b07410140c5c01b8000d241070944028820b20302c900c40310030300301d0501144c64a4110300f130000f54498442c40340070750001d1440f80d8a54000030036064001c2010b80480c2c021206005041601004031001c0303d00085041c8141414516500c00404000d83c801480d085549941c907598860340c2c122030020780b81110108244810f12043c10740f82c6002c4e00c1c004182040c02400303007209070050144403003803500c14000c45400e00c145102c0d4103c84126074001e9034460780607004115000c030746801b40c44040d004034030141c6100b80315651b170488030341b00180005002070800b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 732842562 1250 732841312 732841337
    0x3180b071106090a0b090a060e0705150a02150a020d0501030b0618040515040c090e0c0405011508042d2f01021005070e0d1a132f1f09050301110a 64
    0x420040b034100b500603008001c1c17413046142c119a80c0070640b04860240780307800400022550a13305803800400142c000d09080d4a44c1c94425103013002c010a0290f00c1030b4240682c08143e401442101e020b5442802c0403440c0b070510340c0400c00c2000400203050100c50b120020000024004078564003002d00030040d050181d101d610f03114940c0038894020110483c5000c01640b00c00c00001141000ca00054904212590700e50340342081e101c161001c240040750101001c500010381c08203041c004800d50313001c3e131048107071004048051821f82034002c3d1280055000e0222110f4048171a83c650380780070b0780d14840071002d050300203511211900f1405070079590307501c002006a030007440c0b81a603812009044403025103040c0b900090a0341030712040518031000c01d0004100e849104240048a50004500d034030a80c00404105103c002e20011000e844100c0610180b0f81d0721740000340824041c25102016000d9420100101000d036260b004601c60780c1403010034041140d40d00120b035105540c0340303008541800c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 732843812 1250 732842562 732842581
    0x121504060b0a14040905270309030a0201050c0c0d0321021c09022b0c080706301e1a0a120c170102040e070c080d0203060103180b071106090a0b 63
    0x44d13600c09803d4034213010030400052202c81e00e13803a80c12040c603609031954105900c200e50b240509408241c240e0b100c43c4c8070802542c0500e0142c0b50780d100400458006c0c58001001c00c014a174001c0c1c044010503402c00c0d002c10703030307001c4207018001e401101d90003103051120781002c218000b600c18041d007a01550f07800c400e105548482d8580c52041c903010300c44400c40030070229980c1c0c000c020507105a4060340710744000b04900401060b0070080750029500c4028800f6a48132031145051704c0380ca10b000e02d03005400901007154840c000c3e031001403c90b00c090441080c6854851040d161036800b07560716103454080c070300d40d01d0307403164018010782d10303c0d100a10740a089072a000100180d01d41000300300d404e01c7d58112000ca02c05400410a503403040c0c07138039012500c8406c3d003520441314841c80105036200601181e1185085540a16444070301498003040512301c1c41709507035a01d62a21002da4141009004004000e9046100302c00d00d60b03003e500406113450b2040c0d0650f00d40d071444e0300007403245029901050410f40c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 732845062 1250 732843812 732843817
    0x709110a110c12030a090807033f02030406081f1809021e0a0501110a1b05060c0f010605012a0203011104060e01090e040b0f0603070b121504060b0a14 66
    0x42c020340810125590a11141d0740e80e0001c0704c240c00025006c18010407140d80100d080b2080b44d50000c4249952420440c2c020040c00c00820394524196401055048440070020403041d1800d55801440c1c4c0c80e0304008004101e0500103001d140c1c40080307190a0300003011010220400c941c062841d11501240d0301150300043c0007170303143c040e501a40c224841c990340740105240c401c03004c0044610401031640c0350015200c01c00100340074400394001d0108080070a007494405100712254108507421540c644001170484e80203000c1410b5941d021211036a00d01100340b203444050300090034080003084d990145c10401c81c656003090082502d040c0c0200d03085440940105810182c03e5080c1c6468030741f100030041c4104180c4610740e0004100823000981000e039030500038091500041c0c120311302e547c4c684040740c0340000540702d542c0503c64000d002552070840000341c1030040400c081c42000382000c00c40000c102aa000f0014800e07440d10744100082601300003203926030141400d1015160200344108122070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 732846312 1250 732845062 732845083
    0x7090902090906210106060503100503010608030f1e030109140a181704050409080a120b010e090612061501030e010204120f030302040f0909050d0201060f1215060803030402030709110a11 82
    0x40d800e106c0d0103c1c01036080070196100700e43e8010100d200a40e80e03000c0509032481d82c0b0130314500340c20070000d038000e003d4804000c02ea55400b141e142c0c51410050b003001c041540c401d81c00500c419644020307a1503a114200555a0014034410f024483c840035407000304001d0b164484001e0107140a003400a0308500c110080d80c0082c41c008104000300201c6040401841d40404400000220b0700707005040e00300360a1180640e42074060f0745c4d0a0740006007d0a01c600d1071006419183e1110180c2c21812401c1c004000c00c61160780000722007041e940e5404000f4013601c00904000c000c5900501090014800d10350801003038540019004031301c84c3c1da0707013400c1d4000e104540103442c07241000e800116481c0c0f00781d084000c20510810454001d1007000c18200e08035441c5015925684503804030811050108080030400c0500403400044061030311208502104d9265200340126000442004254a810b0100300014040c184081c0030ba01c0c4180917140041c458400342100b8030000203040c2510003c10000034500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 732847562 1250 732846312 732846379
    0x14060a090c172e0b07080a030f09060c180e16140a030204030312021602010815060d06060215090309011803060903020703060b03030c070b0f2107090902090906 70
    0x103d0404107002480d000018041c079481c500c018144070200c003121000708089a03140024641444829951b0010320b5000e0044070702095141c0d10310005040d0745101e0b001c140352150100240f800041100a0001100d0600091701d802d950101040003260108520b41c0c04462039241010804902d01c090307403000744070501007a04082c0410b12414054142c0d0050040d24004c1d181d9400004660100f50164400c60380044030f00402504a503006500804070150000c0202d282d01c0074200c60800462655000403c1c2c0700741e41c985801003002180d4041c0055280c102d1a02c1802007503150600c41c0c80d076030380b0031080c0341410007000000d000b0701da0520024450285a10a00603c4000c68508000b581c40031a03020950b0607a1801d6440c80032480c0c0001200c11200750301c00908022803a04002c6d01c420780222603042c240307841c104400389000900c090b184441c1c0012512001480c100355100070204006074100030170807441000300c54110381c3c07001042035220b4003c4441e800c500303542100d414130ac0540007100366007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 732848812 1250 732847562 732847607
    0xc0603270a0510050a0e0309010f0e0415030204050105090601020616020705220522150609020a050a080702071406071511090415060903150212040b040614060a090c 72
    0x300b240c00f1800500c0e5202500041c0041d44415400200b210a42003843c00294020458100f0039400b4901414101c1140c0c00c0ca0360220000d00041401d42d01c0410030300200030f20510302231045282610805001d03010030741d0094038a15003940042c0d42c808020744116061402141d450154620800089002c0c0c0030161481c02107000d40654070301c001000c01160920141000000b41800617406c034582280b045404034584035050580301c076007c410200e03200c400d50075103424010941464a000810b480e44090b5505656405840c0004081c924040c0002d01150403110007003200c804003241c2c0d15600d98045071545e999106a03c0c000003641c418a0818010070309142d221b811a01042d0007910000c3c070140d60501c07102140c41c0c245200c003c600e01840e004500040014804542c4d00c2c24051440750340c008005184c250500400d5290101c225411151039622208200400900f400b82a00c0c15144e200246061304200c0d0001e13032481e03401e02610300020b569080e0130010520880702c2201c01c2298203080c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 732850062 1250 732848812 732848833
    0x7030204090c06110d092d060c0b150f01050307050705010e0f0d03020c151801050f180307031d0103141602012007060c0e061602030f0c060327 63
    0x110720380ca66204000202e5841104d00c40c2c01500807400b4040714800365500c1d03002a04200c0e420303c0700403441c0d65003000b44c44428005152200c4c41c0c103e41001d0b20700c0c0c0d203440f11208140c0c5021000c500300105050010340501c014420785803510b5441000c072100900785142c4036580c508044900e8082c281002e426503007015002c3c5030050000c201102107a01d82c04c150b40c600c001d80e102c10b0f8160303c0780030300150050340050155540001c1c1400780c203800c0701c4940385180821403500d51070b50954038280d41c0224114103417028041c1c09002c02003004050001c04c8080d44c01d11100b501c0c050800800f4040c03600075401a454070b41c03502d038070a0b407004041d4103603210070b041581061016003042c4070050b00140090740c03034240e80d4400302c01c0a281d000c100c4207840300b170107282c8be40994406018264507084041030041c00d0000c0c1a0a6a82201400c103444e1000040c9002c1142c81c0101031a162524a50000d90f400044244105456001c2240c2e07010005105211041b10f410110080343c09900300103c4460089101c50b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 732851312 1250 732850062 732850073
    0x906030b1512150d050c0d050c030a03080105100e0609010c240b03160e15040227040b0613120503090303040b0a09050414060d0c05310207080304140703020409 70
    0x901071851400e9000d60400c2e8074082c0b203440040400041e1030782d480702c0a01e11b05440c1070346440080a11a20640d000f02c11180c01113460466652022000719940b44014001402d003102e08007860802c510300b80b006021100d010441c54454104d0361410061103142000504c00c07111841c440c880c400c1092903105541094a0314000c0980124141c401d0140c2c0b00e540c80030f400399030b00c80741c1540e00741a0fa50019444a459031901d180c8403086154000c1e80030f11502c00003100d441c1d03440b45070800c684200c0c07000301c1402003000202c594019040f84907100901010b90400c01c00c100e0602600c42880e4100b880c0d009600f8603d103180a0400a644e05100000b0046024100c60003d40301c0f002e241d444003440c03141c40d00100700035904e40d050b460300403040f0f1f100011203524101460710800c0f40110314044090707407128041030307401d80b6400c094000b44600e0110040340b02020301c900029805010000c6007096103d50f2810340c14800a04003800d81c4e10b0300c8100140c00384003403110308001c0d40d00820411450400e494a03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 732852562 1250 732851312 732851347
    0xe0a1b020c04060906150f0c200316081903020106050301150f090501031e150c110d05040b1801090b030708060a050402090d021306030b130b090d0906030b15 69
    0x1c040c02103040c181c00140c51040390040304261031a90100701d40ca0602684111002249044201c040142c1c2441000100c4c3d0384028160281100c0085452019110424103203001110b8491607160700800c0c001b000040c00228220340d080c8000300c101d10341008142401c03405441190001d5034154a440880d0344044104107004080301e1900f054100200da9510b070070000ca070000d01c4060f1400b00c02e4031122211945035058050a03030301c600085070a500c1211403800c11141e00d8002c14010461402c0c0302066030a04001c80b41d50000b5910300240b4050130720740805000c0c041e80258001101c0802c54984540c2c0c011000403028007041c2c00ca0585a291014004081840039103170540600c0c006d0360007150b0703801c0038000c5403c0d45601801400f41c1d07103403d82c207000b42003c4d0031030084510340c1d482c40d0120004e03800c001114018806403001041011b070350b0800010041c009001e103040ba92081001c1102c080c1c1003440b0390700319415130500248a60031000440e8560094020728400310800141480c80303401e80815 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 732853812 1250 732852562 732852583
    0x60315161116080105072613060e06220f08090301140c19090b03060910090e060a0c0e010c080307140304050d08010801020a1403040f0210020321040209010e0a1b02 72
    0x912168862546c2901c0303002420084003908403038621301849080a020a850300b0440305002000c0c54a915200c00c400c4a44412000f0742c6c50b00b00d0401d2040c080000b0300c2c40c18412040880141c000040c1e9604d601d0322611215000f0032240300415600c3c5607540a500188180140d084a40c40d580341c80013003140310758082e0300294032050820842c0c0c901d503442030f0001c1c4152465560160302c0d41c0c603060104407803040014248110240042b40c08a003803086401021246407103040100064101015000f00755002000702c1010803c0f202040c0160307aa01605606200da042030907183d4a4a4540080300c0c0240c15047c0174200142c004280f000300a4000750586040394030f07603183c600c00d9072a001100d00340d2158400f031500281400030302d020700e51310b104000c1d81c01500ca03018021652429601003804e6101120403100035810105580e50701007a2048002031f850b1405040f0090343c6001d03400601007070010301440c00c1d450402000200c1d2700031164000107581d04541112805c80c40c0d540340003952a8022035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 732855062 1250 732853812 732853829
    0xa090e0c042c06010e180c062704050601020606061c060b19140f0a120906020c0706050c0604060c030b03070e240a06050c0a08040807050108060315161116 68
    0x9111070341002040081c141e8115444a030303455259a10341c0d840400001010306d00a0150740e08007605030745c5d01002007211300c92a00710703540c1c03140036103c1d44070304000300120707050003542000d040184030b0fa4040b4030070b5441441107418640310711182141004042c100e2104020b802c0c502640402c8011004c07016211910400110700d482c90700c150b10413a4030104003000662802c0080c0003090040d00d5580c05420100e002e480c044241c4041c1d819405d0681d40c48500680d202507001603101d0024005114a001909150803c5850480c4206550791f8a590007400174244641d64002644250700c05d4001001d403c00050480c1e500d517448103102246c0700070a0303950118041000c180c00b2002007030f22803003655a010043c6800c00440c0340c031009503100e910031102800d0b02d02404c110900000c1004025101a0081c10003c1400b9400e002c0050000341d8054001031180d8400301079510b990340f2460340c2940c02080c008035400651003a01051b20090a01018010140100c0c0c940890700c19071500030302c08542040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 732856312 1250 732855062 732855131
    0x19060c030207170f0705150108010e0703030221041d07030509070b1207180b0403060506040b131e0e01090b0f010506071403070f0b160801050a090e0c04 67
    0x809030100e20500c8001030050161034030b5020340c659003501500000b10505295460268903a5803036051010300c1000e01c00741c969540c01401004000d208035401d00031482c0003011400cac25501c0103581d6000f03004401e41c071180041c0403900d0001e4041d042e2801800d01148405481c2c1281810343c000340b000700d42c00c10001e0300d080d0000e0300c44400002e000045505940005113041c81480100c20b070000020208412700c500f103d0049a050b01d4840d40400408120441e1500c99055140640940b0006080c0c64800da041805881207941c99856141c10402c101d0800240d1a98181600c041891039100142d2810716003071180d4030f010b9064204104151217076942c0d2401e607030340d00e0304607032212028003e580e00407030305004240006804910b0102c0c0d1032014001c490402e095950b865001076a044021240440211705000070f122140c54603244810903814032010315030600003c1542800d0300e01c1040902d0380c44158075141d142c2e00340002a40b018020b0000e01076061400c0d03091014030900c411408a05914 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 732857562 1250 732856312 732856331
    0x20d0c0314091903081e01030c031b0e070e241206060703050901110a15060810090503091e0a0306020403050607030b06030106033801031109090402011803051906 71
    0x304a08000c020184005080554141c400b1245c411005000001c2003003d8992249400d070751809040c0214401c0c980c10312007900b140b0785000d281c2d250041401c502803a0a04c18000440001070140d400f52940c40c201041b05904c000086c2c0340d0030341410b0385101e01c0240f2420003001034490014440b05c00c0c0d4041c2d400d0706480b50005d11a80e445080c0010780000d0b02030003d05400d44c810a1102004200442140c01441036a100c61808141c4035003501c5e08540e65010030001c1b54010301a00e9020695550200000952604d545849201d22108203204484014030840c1000101c800c03000741c81c0300644000c01c815141c1c0741401c002d50141c0021b5a280c421440000d842604c00d0041500f811400b5244d04c0c21640303000c40603000380c20b00490a0f0740d4500101c8072102c980c4243d08a140100d144544586951078050340007400711032801c2d1004418000400080c40640c035002c03100d540081c0d080c40d03d035025441e000201d008108040d003009116001c2c00100303d1250041e1031004076080e00908040120000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 732858812 1250 732857562 732857581
    0x50109050a030f02210706020a020a0509090a06020a020313080c0a081603020415050306070306061407031d190e092e0e01110a030e070e0714090103020d0c0314 70
    0x809120041c00c1a008804a20050410004020303200844082140305c1241183c0075500307040e1160010b80c01a071011028000b5850315a134000c004083c10340310790045e400c15806a517240e550900010302400c1c0c0019614850504c20800ca40c2040c07a08036119004031b8460092b940c5550a11000501c00e81d0407000104038000b0118804800242c60b10320f81e10458990360034800a05101485c440308074401c4440010070b0b89086c403134070b07114807170b01e90340004c0207401d050014020a960001e64003d514080c0700400000790041034170130043e0304d518084506540c0f14400540c009100c1d800c030b084140700d158000550300c03480013a420300400000d8161001140314042210f041c2800380c059042c541211000c011454095600c044c1c010300c4d00c4000800d052000c0600b4882a074030620f01c8000107640d070703c40c40302004000d01000000d00501c1085035282d0401a80040009034680c0105801c50b100207130182c1aa030190307044650110035008203002c0d007440700901800915854500c1e040c018800030000d0320031031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 732860062 1250 732858812 732858829
    0x11508070e0628050901030615061d1c0515100e0601090b0a0e2706030105040b040219030b10090e0c010f0c02040f020c07230906010c26030105010905 66
    0x21000e40044120701146039a90394601d80c01c4410f40101218980c007050b00e4035030b071540034046c601540011442000710300500074160030390340c0580200044400c005020341003e011802d1403130012142044901c001040e15691070303c00344001041c500c00e2403070b20301d4400484400c2c0c40c0720355002c5031f405141c281d80d80c5014540700b83c00c9408074000780c42010240048510341016112101141c80d0030000890b86101141d2038840c98146000395803610b401c81c21640c5c0e406007080745d00200079002400350341080da07240d12020ba00500020b11801d03c08031842d140c0c80f0440241c0c1c0055030400d013031030001c1c14841000049043e0900a641c2423b0400c084840354030000520b4516011044e96840100744a00c58100ca10b203040c010102d90003130700d480d01c50009610178006060803405071005811201c5c90240c806001ca005084c91a005540041600c811592481300441e841607082c07c2044036142d582c40d040160301d8400c46d1000300030001d141c070082e45820b01c00c0a54107035402030304d0740e08605407948100301080303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 732861312 1250 732860062 732860071
    0x51903050405040e010b12030c0c04090b0c0f0705010f06060f0c0308192c0106050a0f26033903091201020403020303030702151e0621011508070e 64
    0x3041000208501e0400b5404403c08008100c000506080c0160000b03009890056502c0365541c000b19911815007424440241c020104481c2004480b50981d0b5000b1420002042c0002c0c01002240d180b890318102c40445014903800b400030400d141c041c0301841d008040502901d00000d4945031140b218074090029405c8558154440e40d0b9540d489001c952440139964001c0101035444084e803840010304020070a46034000c0d4540c07414480c070344001c03007801c5589d643d1105200c0c802800082003e4890381c20000c0c01e98100c801c0040440f0302008500780c6041410301c40940034880026946090f1a001c1d1540301c11003298404401110003811804084100b00a05407215400401a0040a00e006200c0304488207450001505295490700040d00f160000c44101c400343c5c10040040650740c50085845500000009005403900040383e508586602d005281d28051a0700c031803034040003c0c104125170060b9500000901000d4110401d180300c070082407144c16180c1c49003030b1021448201a0032103070b108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 732862562 1250 732861312 732861317
    0xc0e040b010b030915060301320a061d0403030209060f130e16030b03070f0602060a2d0902040e01020f04030614090c010c03030609020a0e19030c05042403050109051903 74
    0x5841d5480007094480d00a040a070b85590788992054030001240c0901d0118010031909c102d45448000721000080d000408000c03482e0b103824028080e03407198400c1200392500c00200d40711160b03034620b801c1e0002c2c4121940e96034010008940c05520b250014000d0271549181c0c0c03021140666a4044106c40200503a4604043e1402201c1220750521a03445080304520003012551440e9550b40f030f60707007006c0d1103821210060700481d04116208a540c05014204092646124034010002503604490000d525141c2c242c44e44900c518000e48d560b6400c801a240d400900171591118164940344080c1c0c05407200721a102d003810081e00e941d14000303038040c1c4290306040c00340c02d0305c01e451310044607a002a900101c091550319980800d98a0745440030f010740d0702c00b544550791008072410030013047c0300000b400081c0210303004e9014400141088684421540309841c04105803e270401801c00d59082205c0010b0716101c42d0318000305005054001d040d0143c0510b050f11603080c01c1d151012402204140050301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 732863812 1250 732862562 732862573
    0x13051315120602040e04080c0d0e0102120c0c040606030e010b01030504020a03060207020612070c110d110603090102040306050408071a07021902130509161401020c0d020d0c0e040b010b0309 83
    0x20085032140048841403141c90b005280c15102d10981300c11000543d81a10b42080118400c003c181c001c01030700c0c1c0d911507542040ea202d11000c3c00007c2d600c84071341104000e0010b011844c4007002c8010010b00010480040044c4502c0d9100c4400a00400340c502001d840e660030582c0004480d40207208440c000c0f50040d06151500342103031100c0001c0d6014810881e0007081c1001403512103c44550041d000c2d110590303a400d10340e080341c10160484c0341c0181489204101c0b00c2c10f4030700002c01d040c0c8840d50118043d20015280c6e07a43c0e884103402401182c0c8043e00c1e160800c010802004014001030010511442d0000809100a002074594030030450700400580e000c619042e00032150840c02404082c802850703840380c403581c5040c81080c1d0300f040d958a00e040d48028101601c0342390170b0340f61130042c0810781c40080a468944000075901c1d840c2541036130141c811840d10200795101c0e01e00c060030898000d041607450540d6202da511182000b01ca09940401c0b22800101c0c8035240002102e02400c0450001c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 732865062 1250 732863812 732863819
    0xe1c0306121e0503070807080a021b09040201081531060303050a030b0f0d030f08060102160b030429010303020d020106030206030601032d0b01110606010203030f0a020d0213051315 79
    0xd45005071040c103a80501c401d02550b00017403200710080107d1446030340d060340c41ea0a81c000103490042036100d00011070383c084006541a03251280f94562158091a222038592a0744164a1255440701d0301207804c41004c0408075240c80440c11203040111400121400300f00401e00c81d0303c02c94003540001400100d080050a190300d20980002c024400014840c90441340b000d000501d2020700c0010031000300f40c40e031051a02883c1c11a0a451340300c0028005003da001414081080300c0c01d1074010400780c408080003003402d10211440d4900300b88006162648a5602010071925008003440118010301c1045540004d440c410b004400031254040c008500395200c050054018103411382d049012508450100c244105584d542c0e262034200b400c40c00150140d50600041550341d41c1c001e100c4c003580c010024082d0351b076400021298013118241260f1915240c03c04250080d1103008517001d1020b0021403000140b038161842c0c0700c12920110303000741070389048034000c00540c0c284141b2403085440300d034401c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 732866312 1250 732865062 732865103
    0x93d05090f0118150611100905100c0c0212152802070206090a0906090605030309060409020f13060e1f090302011d041103150a14060a030e1c030612 65
    0x160b00420b9942ca0200d55401110300620398041c02d40e22090000e00342c800c00e03840700706d4103110302c102481010a0030301460070345440d003039a10002e4101d00d0718403e0703880c4141101a4419010100b241d94020540e0161126150585590700014460030780200005008181a4400c203281d0b10402060100102e0b2481c005000440c001d412003041a40c100c1003c02521406541c2c14841030058400c200c0c00281c40c50a0910107806c0f603039140c01c00c80c06603104008103225079403900161811203110241c050390780e01114610808034005e0320130019411000b1200440e04c1500f2483d00081d2082c242d03032078103505900c00010364a40110100000c00304007004070920140d403041100a40503205103514108070b010520200701241e4840d4110454072802106101c4000842104403450b840110f030380d03131390141c03d003a10b6046211501881c144102c2000441e820000c2c000d41003103032014a18020394202c150241658080d0341c614411140000c2c0c949071010401e5002c803086000c08030340200304c0302c145080c050f510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 732867562 1250 732866312 732866339
    0x140a1a19051909050a0e0115081c090f091b0504030f030806031c0206061201020c071e0306020a1101060e07051b0106080d120501050d080306093d05090f01 68
    0x9408440302a0b01d010803106258060786025a9040000140c405411b450081c00c640c0c0b140039a002d4030b00c2d0b9403030070800d1010001d10107102c01461031440d0040c83e01e501c0240c988115036170040740c64100a61002460344015408071441c111a0000350100c0310413500101c800d44242c1c0001000043c5000440d00842d01c01ca42071940140098201c41c2d032201d401c2c0c0c900d0030240707035044508016880203082040c60309000c0f4003031090b42c003d040254113006d201c01409071264868000c0c03100d0003d06a60041000104038490b0008580080085541c0c0040c120001c207080c2d01e0900c11020b540c24690001100801c860100348905580d60f80c05082034510134070340400d4a0122900203281d0342360480130a0b030741014071010303490b0001500d5175105c88250f402c1c40b800341c680503402144a690082e840b1000b10b400300b42100c2d4460390844181000d036840021109d41541040351115801c620111000340fa00c40e07202c03403c002041e05980e40700c0c100d0341e1001002200700e0100d5040017030140c018010840d11103030420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 732868812 1250 732867562 732867589
    0x3021c020d0e03031005030f030703090501120f02030c03061c080409021605070803070c0617040206090310050a0b120609033405100e0a05071503140a1a1905 69
    0x140801c000003002c4845285820640c3c20380104801a02c2c10811450108130400d0800e220704084c0d4204a00744d24090007181441c841c039414085840305190360301295511940c00c40b003071540115224181041160a0780e00200c0d0900d00802109850102102d1036804403900c50307510005041ca42401c010300b04001c3d403c180718100011202c1010000040d01c180030b050b000e45085001151150201c5c00c00c20241401688007034244401982c2180e11210003200d07582c1e1094058468031755698401c4080b07894004031008034840146800140024450190030040f0340040031100c1d0106031401c103060580300c84040c0d40000c9030354400c000929504100c02c40581c100c1311809140c14280342c182007030080032420f41500f120150054485040158130703603c00c403451603c00f1002000f507000b0a40d19103584003850b000360f01c280c03070903100592034440c400d0700580e580e02541c024a4040d81000745420001d031101c14040b6000909282011f08141400c8083c40c42c500b0400c1c003080f0101d868101446599028080e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 732870062 1250 732868812 732868837
    0x151015050a120207170f0d050a0504030e0604060906230c070303120209010e0906210a032d0c1b0b04140103021e0f090d03020d02010c0f121e14010602060703021c02 72
    0x146a07c0d403451031242d24819100320202040f0740c5030526004154008051820703100d1a0180720511945a001e0f10002c1902c0450504101060a1a038002c16500c45e50000d254030000c00620070f05240004070b06034080303a1203520340b01c440118141f8140164014011000d00241c240c1c0084541407800070001904000302809940701d4600030750241690082d0743c40b000d0805e03800840c40004040c3c1c05180500c05c0c0c0c0300006480f0034500403501881d100050790300c801040188440c920b2060006014503568034050030212030200b156903260020303c6802921503c121038226020200b46e41d4000c0c000c072600d50941c004200320b5100905a08085030f04810009424030405006095407510354490314030955000e0380003002c0000000c5002400d6401400c1040c003004040c01e1032207002600304a2408400300450b4000c2402e041d5001000e031580c1c0756001105c001d904025014940d6040580d8460585503154281c0d0269a982e420036402c3c0d124202c07072000c50019103200000d030900c03294064840c054058 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 732871312 1250 732870062 732870067
    0x1e030b0a0f0303200703080414011707020a150212070518040f05090d03140c0c01231609030c05060d0b130615020a05151015050a120207170f 62
    0x210603911189101e41c000310045002c425000803124620f43c070407881215880000d0091909541e00e20203140a20320802135500e0f048240d00d00e0300c1c0e00401c2040707051a072030020700855140031100250345511140c82610302c07883c049070045401304180200c5803841040b0112054986920760b08860329800450444024a04007405a03d103170303124040ca00000d030260401007464100a00d4040c10510600c48e082c0c05d06d8030b0582d00800d0403540c2c810003a0b0020400e642c0d191134030040004540540011101c0e07541e9030780c10b6042601650340d15001140038034420744c00e10030300032000f00c02919540603e0001502c4101b0b81c0c0010042850b040c0001c245180710304001241040c2c540011070380f0405034140d111406519070000f44070704800c01e8000700b01d400c418801050703074400340d4855a4840c4814409100921584000645042009548031006246000b14404140c480040081a90b08a0f1103004d0010703000f4445c10000c0e00d100e000703a94038a074201d4200c0c0540c40804844520540c08804440c580d43c405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 732872562 1250 732871312 732871319
    0x5150d0f050d1805040b150309030903060c12010609181a040513140c01050904150b0a080a1d031b0c101d04182d030c02101e030b0a 58
    0xa10080d1000d00c032540f22000956100007040542c40a80c0c1c10060083d803a01e022500d0702c1e03541c0c240c0c240684490300a40390343d0740c0750203444c20f0440c881c0c807010b15090308c1a1010700180c0c6824100805109491414841a41e600ea400854400070b0501c14103107909000170810700526101d600204211070559001c00165500380b01107000d0b108100c40525292881c10a0740c0248901041d10401c000b40c00c5025040400b5864000390030307801815415030090756106503044160b0200d054a40113017040750109907e85408003402031a118084032407089550034030008040c000b215010b200320541018016600340341c003044420406521140350b0420b0382c071802d0442c142540794066000c038217002990312803200702d4001981e10b070340c09109506680584e141c0380100301c80d9144540311501466004500b015150f44103000680c0c020720805d0403412003501c400b2141c00f050307006030302600d11034800e981081c2400340a40c8141c070702e50000c50545c0d00303003d003030600507d20500c00d42c400d40c81d603003008100481d0f040d02d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 732873812 1250 732872562 732872573
    0x30d111306050a110102162006030c0d0606020a0b0a02071109091e07060f0f0c02150d0c08191503060603230304120308130b101805150d0f 61
    0x654000000702e0300000740c0002c00c9034809a0a80038042d110000c0d032138041404c081c00385c2c0d801c0d0035070080d12585240c100d4800d0b102c000884086803402c020500d0784c41f81820003410b00c880d40221009014035142c4800000c44900114204c100c240e004006412269142542000030758071136182180c841b18940c540e8610b664801810074041d100c0440245124020080c00411501b100740d1062010750004504100040c0c1c8007030904030110062901e09424009840d0681c1c40c076207101d000a600c00c82251010558018003c041c0214100e415801c0c0200350401c81c1c2075400740c40680d4055403030726000c0e565007040285500a42e1690909007201182d05540340c46d401700321042c681080380e006a00304450b843c03002c0c4440701200350a480e40051841e1034070f03140d848900380a0003000281400172160000c0d000700c00e801030001034103401c02000c1c892032600340380ea00306200f42030140c0016050074518104452075648907103840340c1c000403059034810046504100000444140403902090300d14440000140f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 732875062 1250 732873812 732873847
    0x1d06010e0703180c03060b2d061309090807031205060a05060306030f01091401061d0f060607050a030f080c0c0615220e07051002062806081f0509030d11 67
    0x40c040c006c00605402030400300701c078213a0b40e0a004016503a1860807180030300d038550340c0b021042038202d42d41642e52081c0c00c2407402c3d1807820b9000c02e140c0d615100903007007800411030040038110311994800b0041515a905607044503c140e50b4160002160741d07042c01642862401140c000b1170080440310000008880726080d80e0144204030b035524404070440418000c240a017001401000c04450850b1010501d11106244018000f01e840d03440c2c480424080c0d05c54504496500b60004d0541d0020013203810040c02d01503611005d07500040d400703c0000c001400140c103a680300d003041d01c0a0311098440345480c0421104400d509680103203c403129202c102095402e4020070480414049a8018860005410402c00c0e40c0040d01860a440c51000c60582c0818083d6210040085000d51810300c0b94001005001c4440c035044990701e40500414a06000140303072003803000000c1400340703603e48100114142d50003500c010303505030301c1031000764000c1c41a50007103401c0d0009014550700b0055010340c04070028 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 732876312 1250 732875062 732875069
    0x908090604180f0e060a0902010314010b0315030d020309150f07050f1236060408030d0e01090804050913050d08040303050f0403020d050c0a0b07031d06010e0703180c 73
    0x1d195010b4601001d0001d000c2c0340e019410b080c00c00c01a0001ca110b265840e60b100501441405640b0785000085a02039444940b160207088495a82903840e0b0f072001004e0350095641c410030702e00038050600685000900622454038079809141448142c405104c4108203852013640079503020f00c204056808220050f11605c1d000382e000300032001d04811180c0c03c24101160540464000704440404190004003410991075a0103150b0b0100101c1c1c02c0c1404112082a0340030b9000800040009a4000000241101142c0c00704100081c8407518407140c00c072584000002c00c10f40d0701348410000c500d00241c001394007000800d04071405080d1656401d0900b24046441008521003038180424160700d8070031540d0042000070411500e08080e18080c1d660946c03909602c0070070038002402003800c039051104410300f03940100c02c0c0a15081070319001d030182200312105185014040740e030201060b40000e01c0d13812550b0044000001e40c80e0144101d01401024030300c1e43d01c1c110074143c0440003648803100390000303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 732877562 1250 732876312 732876329
    0xe060c010207030f090b0f0a0c1b08010c020a020907111e031207180306020a11030d060311181f030803040f0209060d0c180b0307080d08070f120908090604 68
    0x9901c003d240c05403003010031410400801544d41001c2c096407544c0030444403d12114103500361078041402080b504907010180003002030143c1490b00c0c00b11400d0303d60301c3d410f44034058000d01141c2030902c412651401d4068020f948041402c02182c140784c042c18601101e04004019a030b00c0e40e00808001ca407d500c03180309418603a00000d1820301c420244890039030004560f1806003400c070414481441e001d909400064401640000d0040340240101710403040b50b8010380a8944a502e030a505100034607007407006031400224811071644526045242280220040b15601e5650b114655141039210484600c2000050040c2022000c43c3c070728000365201d01d1054074440380180e5a4070610003d00d4000c2d00c8917014008500b50580000d2441d600c0078156206c6c0004032204002222006005d40049c0010503010f010b036160106030080c001c102c049044850307032a80c80d21502d86d45000c54604503502c0e0320400240e4403c0405803103c41641052801c14011400d141c00c10b840100011429171082c1d108446 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 732878812 1250 732877562 732877567
    0x305031b010b37030b09060a05060405010b1b033006060a050d0507050d020408030910180b070804150c050d05070b070503100315060f08030309070303110f01090b091902010905060a0e060c0102 84
    0x2300d02442d0050550120302035070b00f8081945032400351403031030284003500d131031030010b14542891401c420000e40d801620b006403004e42c504e011518905c0543c84002c40751101c0004400060b4547c10802c0840e00c03080c81a0765841d01c0d2100c0c1c4203801c8000d041c041c0c0001c0c01c014040080351014070890000e840900703c42c0700607540d1508042d04000b4220701141449040c1310841070f03554403140301c001e10351081321a481540b41c0d42c0c140528080c40d2511660b041941400407480d80c0550441d40005840031a603c079404440c0350080d070500c281d8103400f80c20070040401d1184000280311500c0381c2e015540001800c4000400b142d2241c5d40c8603950300c02200c650dc8a41d0750b0b00001c0106115000c40080100a1180a1840c504000c0d07002a2652018000903007031004110070015103400030000c00418450520003000081150314215038810815510305205204528948507019108203840c0181b80d4141c540030303212031400b0188699030300b00d042513000784444141091025202e110050000543d41c80006a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 732880062 1250 732878812 732878821
    0xc180910020a0f0e01020d051801021f050906010b121801090b01091b11120901170f04060509061003021e0a1503110a080105010c0c0305031b010b37030b0906 69
    0x610b116600030f00a41154002c2c20507c0150707802a040340c07a408032104041791004802d81c01030b4507103441c50710b0800003101c0d8025011140722041c0e100c0ea005210480981741c2d130b039984060138041390003803000070300c9001100d2000c100c10003508018055602c41290000c1401c1d901500c5440102e0401da100107055900c2da1501c01041030510320440761607005090011211140b4014140e64084078a01c1404403440000c200610381e0082c3c4c5048189407240009111615107000b9250f800401039604179a15030074031004c2101d00c0070110b0b02c01c0c8621022030303006950714170359005c020020100322030540314845490041c041d41d40360001e05e1005440b40e580c591f135144441d200b0041c00c40c1c00721520b611031082d0500856a800b60310444903411120240f80010703140809042144d90054954030041c680e200010310300815805600c0d02c4e9030400074501c020841e810b4440140500c18030490318581079040451200c00c09086110b0f02d11821002c14051648115140c0d1345605d070102c070550380442c45520490401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 732881312 1250 732880062 732880067
    0x40f0203090c0f060c06061504050901080f19151d0f06010e0a0902030d1833090b0409110f04081c030c090501030c020c030303071d030c180910020a0f 66
    0x4a030f02c0c156100c0b45401c40310814642c50303e801034449842038101e00d000d0720381010114140ca02500d07000b42140e0880d41c0d20290070759100d0586101c2c1c0124050245500c6c1100401c1c215903101503042203107140c078040e540ca09030009103901c4200101040710070200c010740101c01c10026600000c2e0000a01d803075410050110070100f0020000320142d130420490500585001c602d404010f0002d080105000019541e0380c003610340300341c0006c0c4521528032801554181401d02c1110310314851461100044008803017141c00881501824542120420040112034840d50107200c83c4101000901d0414640c1020601547c0c000d62003041903500c00c03a0001c64a24151b480d6000d03224083c1020000f180041030301400389001442098145682c46a00ca64001e00a014521080fa801829a41d44e840d001d4800750840011694250f0740403107000c02600c06041c001450880c00e01d004060601015840800f107142060040c40c0c03440c10700900f000311010036401d00103001c0101e081e40700c1180a40051400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 732882562 1250 732881312 732881329
    0x140a050702040b0a0b0405090408070f060b0f04050709121506060507021906020607030506060714061f050604090b0102240609060108060d0b060a030503040906150507110f040f0203090c 81
    0x3c0c0d900c20901c0010400000e8a04d0084808441043e50354280d5a07542e030419920b01e000f012409040c076007003040c0d0f1004104c1103500c0b111800e142111811302c0309030a8000d004c1100c004581550100d00c00704000d0203044c07008842c28032074600c107041c0d02c0004002e5008035402c0c2d503816402040411808500c1c2c408618002d0501181c800d10300c40010b00245c9400c50080d55600058618410702d903492010451544551040b07404a6800c2700d9240070050a800b2515540e0708202c5d41107810f400c054841015040451442c0700840324020101d508090034100b014006000c1902064103500c14501004010750796102c12503047c825034141d0f04a14640b4600340314010300c00604ea2410803403120304005075a65410620b0854680213440400f89035913580100701c100003c2d0b0000b400305c3c44085000103c1e0f82c3c0c5904100103a802403946104013024225080d1081c1c05503020041a004007048214581d041c0300409454010000b0004129400461000c8080fa8000d98907248580c0001030300d004c1c4c50600002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 732883812 1250 732882562 732882581
    0x50108250303050a0512070908010e070621021c0501030512030403081305010b2d1507240207080c0d0905010903020f030c10020f120906030403030507140a05070204 72
    0x4444000103905080510840140001400c0c0a030100d2041c040510482c2611074032880d40c007800806042000b4054424841c0d4401c4071519030911400c1c2000302008949501180c40607110444038460481d003411460510003416130300c10758280f1460880710078401010b22000d11036980002c0c1941541400c40c00e04084000d0750484140030400c0c440080d9100d0441070703005000140d590032085192034100d0160507550544d0b680070000303400e07110b4400d02e40c0c05039440c0c8071600002c4e9120b030368800f8180b1002e2040009881030b200414000304010900b50b141c482405010140c3c2c104a2141c040c1c86c0c42c00300e80103a80d0640345010041047c41391104100110704c1982c0c258104441c8440c0b826000801240050000074081d03900501d107244103442c10001064140401030460b05060580c5800a54940c01c403101442c0900c079039590440031440301421281c011101500c99481c50340c9a44064000e0714010740b01d002001b04c1d0b00611000f010040d8043c120307602450f07035055a614050300422058804405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 732885062 1250 732883812 732883843
    0x3080f0108120a0e031501092f03040206130305070b040314070b030703090807080301030f0c0902040602030304030f0e0a0f0611010605030a030e06040f0e010609090903022518050108 80
    0xc2c618000b520740c04080c0c03510f015083c603000d0f05011081000c282401d41907460250303403030f03060000880c0903c2c1c0e030341081500800c941042c807284030816016126648441040078000d241c00c0020a0243c01d00200500380c0320807810f40b04032199600c0d42c4240c60410143c0c80340344480b80214081c020040ca441c000b03c17402400000a114550403c500780e4541e1001414235030516964154010800c0440425983d0560700300420980340d40c3c1d60306014101e40c0e480ca80840b840500300e035000c07400d0102c501c2510b040e140350394001c0d41507a880d9a801d4601500d00541e5906100c403d561620300c95450710b480f1406065145800c2140601d00000a4415070f0544c00404142e4142042484242c4000981134501c0760585402c0d6421404140441c10740d100d15006410307a46411300780030400c82e40e07000311613048070401d0b912801c10546c1c52140f0011241c1140300140160002c01010fa034401a0440201c1d8500c40001c0e00c1c150155200070f860f034030013504003030184030644890041240840c140318107008440c564 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 732886312 1250 732885062 732885073
    0x7030b0a050a020a0f080a06030503120106020d18030b0402060903060a090519080304020613050d0f0b0c121906080109050a0b010602060c1903020f0d020d05010501030b0a06080a090204050403080f0108 88
    0x14801515029400c03070301601b0810040c00182e1b940910750046030003583c0220030b40fa640c044181704c00962081c240070f08001743c840c6922141401c0d00c0703003ca504440512282d00d102642c116620072080d0200a041640c1c85031060009695560f420704c1340d103001d206013601c0001c1d51051031070130600704154004070480030040381144101084038074048a60140e4111803580d03440c003c0018159090009402c8550400c070609400d40070420350a001032a05400b40c400594542d443c07000302d100d40d00c62610b9505450194034080780011801e1042d10240c40411034001c16140c2c2c0b030340f10490031070760026000e4501e94054144a02403211340c544550151100384003500035480c0a21240c9502c0c0302c2d64041c0b803c6940c1d40e981c4403400c18130a03070540d08401402d416040d550545903203080003a400141e10b050541d85000000909503000c3d02c580c0d00040c1021b05640c003000d00d003031000e40d018071000781002e100c2a1a1235440700103075541e10a0314452403003074540c84002d0a0100d00030640d004160400d0420754040e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 732887562 1250 732886312 732886327
    0x30604200d023c0109030605130615080f1c0509030c030d09090e0c06160c361a19210507090504231501060807032306040506011107030b0a050a02 64
    0x21038170a05030390b04507001242d251039044055a1903c000b10000e040c4a25000090f69003420225000c0d0840300a40119246501080340c0b11391543c00c10202e281d02e41240c02c154040c2640500040c2c0303030300500181540d00003084000030a04001c40d0810701030001d9880d640c20300070075885120301c1a1420b5030400508001c1c0c0d259000c00c6003440b5004030810071541845001c03042218628076900500300503103a6400c0e22129902c032040415455001c0da086105800e400c84080349940f00d900500c60009411441c0c0605040500404261005400ca2070b2280003001061140240303801c0000480e40d1a0740038640754003070802c0d60800a25410025100b03080c40c0c10b0002064045c000c414410012000440c5160443c1000700c0c504a02542c00a000d8120070340000707030240c1c05c250400c1c45516191810700c00c44452004900862120003145280780c00032038086a060b0400d94480c41d44454103060580100440c40995450200654802c072005101d003007c1007801c00e40780c014035420001540e81982030010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 732888812 1250 732887562 732887567
    0x60302041202010507020a090207051c020f0a1218030f02190311040513050607020a0c050a0e010e0a0e030c030702040f06030f02090403120608011a030604200d023c01 73
    0x10090000c0d0411402180c085c0665560103030704802000d440b04110354640c2d0310302d800381d1900000b001c070540d034200c0711307a445002e2400170490a071104103540283c80f0b0780d8405c4d924550100750022008023041140a10285940035050008020354012404584c00d0a40c0e80304018003800d03011403008030002002c00410000b8071400b0024007403d0103c601049a90302c1c80240c00b485192610050617a110300c2c010b0100b15900414a84601030240482c8100d03582c440c0305101124406214400700c009498004121095030842c100703130040b000c92004192140380709011441d68200040030140b80e00002030000c21850a403054100c030340e8550310180040c43c44c5031515042e0040340d00700640a06140c1000404040c81086400c070700c1141c2000c200011519107906900070054100b2464a0041d50790240403245400100c4078031481d4810600c41d0340c55060b80d01d0fa150301d800c6034007417500009203044e180d005030f85a02c4054014400c0c000c820030310f00d0b044c8061040e048424010600404001c1c00f4400d17507031b43e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 732890062 1250 732888812 732888839
    0x41d0a1b091712030c0d05010f060c0f1e03211514010e0909010c080a15030f08040b07150f1406010513030c03050a120905090f060103140a051006030204 67
    0x601c00c04031101c240304180c02543c10688201c41d4408000000020401d80d010f1100c05004802c940020801451380c840054400c20150341c0200e070040381c1840105000203540c44082c40400c0d02c0b0f01c034142d25038410f03120301e10780044100780200d01161101d0816a40c0300c412250280c03111880e0f10707080c00707049081c2c007140c1000c603001c0c0600406260035880c0c000c03c60340182c01c204c0c0820300c094800b8140e80341a9821500902a155081c40040c0401002c0ba11351004c81c00f4880740140d001d0300c034845a0307140d9556001d00c00804e04085032400340602c000034481c90300d00040c00034280640c080d96107440c1c2d948030007411900340440d6948440d141605142c0c4405400080030351001d020f08166645030804040032142000c0c6134001450324580103404020010049041107003584556500304040440200554210145015a64000140300c0000c0c3c83d03101e0a2000c01d8103c60107040005070b0700c404030142212024102c0788002d515031500c2c28403403001c007a030b1001c100400d024901181440d0074a95034100c0d06 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 732891312 1250 732890062 732890069
    0x804030509121e07060e010c020f120a1202031806030f0414070305030c10150803030a05070324030302100207080f0315130b0108100302010c17041d0a1b09 68
    0x54268800701007240100708160621200050150f540c02800400b40356524240750040c0000140e00314030860455016000300d5001c542d0003040342d41404204403c2c0703c0d00b0a030784800503183d48a2030303060710080f070000b0324002c80a12855000d1a581c40100004400c440f140d090802c0c0582010420402c4007100c4401c0907070442e80c0004a0740000c114901181e180410b16003000e4200d0000084806c0201e0000481d8003840725650000d21052060740751000f81c41d0050f00c242051900f080000849181c1d19900c41d0354020306608000441d68a044440006410080d6440d81c614032000400d109242d01000803044c000c03d010380c198035042090355481c10501564910240480c4003001241e800f6405444405004602821091451000041c040c002c0d0660301100c5000c60300380c201046650384054002da040c0c0350103031520140748940d991080d8402911710054543d8180500c400304114200c05040c024003e141c40f0412590b042040d080411a10300c0402e00d0420600c1c481080841600a66282c00b00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 732892562 1250 732891312 732891319
    0x61b09050d030305062b0c051f052a150109110a20010c020d09060c0201080f060f191a07051504080c1515100e06090609030f0d08070804030509 63
    0x86486085c08500400f19101c40c072041e01441c01c06514008505e800001c000e1400f0300448030002e5078034001c3c401000c140800359800a55a007001182603801034004144001d21901c2700c2e055a0000c22840000880b031880d142129040f0914400c0540b5800481e6405015140d10400035603c980a41003881d00c1406600c009104814446803000718801d010180c0d901004002440494003180c030007500c0b0703880c080c0d500c008601211710118103144910380b0300c4211941030716100303c01d49512800da400544001e155903400f10840c1140803c90710741000c2802000c0384c1c20281a0300c42d041450340c00ba00c10781d280d42d8906411042c0001004a81e00049036a03440b11444140300694803903041081d2240b081d0701d8126100e110310103d071129032141610503445041c000810070800d501801c00c000700000301e0900100054002c10703a038a000d1030401c00401c40501d0061000d407030090303c040840d0802102c00030303150140d0411650155556000441c0c10b901040c4e42c0b82c8002c0c1842d00780e802070030342d00504460030701 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 732893812 1250 732892562 732892571
    0x40603090614071d15070308240a06200109050102090a0e16030902060c0f070e070c1709030c0405010b070201181d0411180103030207060306050303091302070f061b09050d0303 77
    0x190312119007a60170800e138148101d0343c94003039003800b4003a81400d56280803880c0481c01c1001e0180172403510b82034083e400410080310549804002c0341e000b0301100e03a10380d84240304c00245000c40002d2240943c210301c160300158a540b0003004004024050341e1042240f8002da80802c4280c08100b00c41e2166030001e800c000030700c022a0b0020039168010130b101911140704500090013960030009607401180d8030300b081103600c1e507102c070742c01c82d28810700203401410901d200d6000038054050f42e010b4844501c0140c220303034800501000150584001782d000d440003500009000d8103650340091030f220200120703003842218034904580c410058192185003010a40c0300c1000c2010004950b1642e0002d82005100d00307140c0204076080002c070802031000b10098494030304000303405d60080c013416085542c024080c60600c8400c0090100c442110190050030035801c0008400181c004140005454061540090280e2031860030a8000c80b035408400107200c0e84490412a81c0e550b18581a501542b5180114 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 732895062 1250 732893812 732893867
    0x91e060f0609090c0909090c101407021011031c0b06040303022e0203040b060316260304080f030d0c090e0c0c011401090c0210150e0c040b04060309061407 68
    0x2042e600500140340d1b400342241041c0068600001140141030500301e0780c009901e11f01181c2601c080d400d0304204124000140b00755030161030310b0301d004003201c1500d040040780715817818400b605503407042c1c0240407002c14009003102c00321040c0c401e03a810350105403049403a00c0e040d507d01a59031001c48102600354078411284a0302440a40980200003a0461096480e4105880c0503130f140c403011030704e60380a84034042c1c1002c0160110301d2020100c030007014000134600c0c4188201082c800e011392001c640e40c40f04000014940200308980e0744040c45a90143d82c9400309082020240c441000c610010003040c50070601020100f010043e03005801c0c024030580d140829010b560141a11980084414009000010b007100c0d541e0052190109a070b402d07180400c0b640d100c50300031034101d00c000b000c1140c07500c8010f0200400c0030340c220f90004a4010198100360741c0c0c00408030154055080320000903190201030741000303003034000d4800c154080c0500000900d00507000510200300c1104103080c0e40c400182c1113 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 732896312 1250 732895062 732895081
    0x903061b170a091b0618150c03050918010e07030524030a02040c090f080307110603040c03060606021006140325090f051f080607030c030b091e060f060909 68
    0x40307000c0356000310350b9224102c1c409031090b81c142241c4101000300306510501e11031b880d81001c403401034030041d03400c04100005091040319130326580c440c03c0341070010030005860300c0d42e18403115038048000f900078100c0c55814082c03080c03545203014168400f45030910003841204060034500501440e80311440c43d0700c0d284004006803070002c404201030341043c42d000807001c0c0654401e00d008156041080c0900d50a0743c4c4141307036603691190395400340818400d10519210b40c5000c4008540060160340c8400c0003545070380301c61040b240240d000b580960b11540350f49a002106000760300003400030300404505411050046600e41c4101d0b100c0300420280101c5c200c01b0100c03034070f5560001e420311003030130401c0486007441040144030130380e07030013007902010000358212200712040b0400b510681000b51115031503500064021b06401505c18041c50b41b1000d200e95291150480103219041c0466061034445100c8072081401314080c141600031004900907540a413a20011500c02030000d58001c203180d541d40ca10b9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 732897562 1250 732896312 732896321
    0x6070807030309082b0518100203040c0b0301090207061a03190203010f11070c0b04120b060310111c3c0e07090509010c0903021215070903061b170a 65
    0xc00d1034910f955411005c60041c1c4001c00000b0176404200035200d40300701d21980700d0a44414241540700e03080c0c001d16080c2076006103400ca4802d0664004541d280e00b15662150400d0300501101c0340d0108031581030045038015080140058220240c0c10107442d0046a1600ea2170380300e210402d400340705000c046403001d41c043d010703c40c880745003003004203070759040d0401561140d10191115998400c010405512a034121f408480d0920b8840c041e08410365a900034140d0000c0c4003a80c0341c02911040c0596455500a402150401c181d10941e212015401001b840088060019100d071510020b400c0038a11000e004406c0b10105c9840c08158000002503050480d4030381c00c0c100082e0900c503100b40e0803000000e126040e10001241448240e4a036084a4201c40b005400c0ca400106245010405030401c412252041442c003030540302c14680740c8805013107008054070010f0000766951800c00c00d1140324030982d403c0d0840704494403240004032074010300f4000b061201000c0340b1a84000305040c2142a480b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 732898812 1250 732897562 732897577
    0x100506040f060f0c0204051305060c0301061e0c0501020f030a0e0d02120904090c0f080f0c1e0f09070e030d020a020d060b0d050f0706301113090f0b0607080703030908 73
    0x105000c641751000308908c00f500012003c0701d80344541e0003c201d8048038072003500d051711040d41c3c03107071048410f2509040c070543c11132604906020740145070700c01042007030005200003d00400304990320308140c0a22402c445400e024807213030743c01500001c1d15607540070608110b003501c8111816260200c80000034014142a03800400c00e120250b40090560980fa002d00308440120007618480b2150040c4540c8075040105002c1e030040031070755003c450041048400b4039280b00a004002031006060209443d0082a1045004602a504015500e180c1000702d445140039034805031030002c40c41c0d404642003000440000308060344914911030f2680318000030424080d003000446582410324001c140c3c030b40790b15000d6000000d4900c803500d420340e8608080c03600340e041c480e10354044c00d00c40c8444603001400a00d484240e80c079001c20010b2500d250100c1d14002801c60101b00040c403403c46840042180c56051134240110740030704c003850220ba44001507a40950f013606010422001c585040301c030780d206400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 732900062 1250 732898812 732898819
    0x41109091008060610080c0d11030f010f090c230c070b091e010f110106080f010f05130c0b0d20271302160204020f03100506040f060f0c02 61
    0xc0800419042030100d0504036100341080e00c0c1591039100a1141500119101c0b2000c00e00c3c00c80401c002c410352000400c020038500d50001040b0054440c1521181d0040c1c0d0480b04c4c250094006000d501c2130300c4144801403030f1908040280031031141029251411000294030072484500d00c001c5241800e05c1154450800b00e8146c0b15542d0700c800031340146420401d60540286a0102c3c4030414068083c04e10004c40c80503114020803464800c01203440150301011642a5521403200107030b4903c04110805000c09644008140c2030100038094007140c1004000d030f211868804500f4011440a100034015903100700d12031aa42c81e054000c40014020031100200c17100f050b06d118005820b40040a0860b030714105c907868800141c188452200b5020524401d0340c000100060850403101c598000e1a5070f010302d0791f1401d519056500040d040381c0005540d049400d00000070044550006c0310103d001d04030440d800e0742083d090a14524150003030340110820300c11700364680303161240907005c403850382035004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 732901312 1250 732900062 732900079
    0x91515031603060501080102070b190e0607050c012f1b0a08090906010207030b07111501030c0f0e040309051012090809010e0603090604030305180d0305011502010e0c041109 76
    0x107540c1c100a001c80c40c4029078415213024004228200c0c18004c0300d1400b50050340079451a03c441e00500c07030780d901100e61150415a00d8107074044880081c40401d01c03486440d1907040c0c44010500f040c909680b42c0c02c3e48031142c065680034540610305401f060076039010005002a85840351b03042510405118661400c00310300c114010101042040801000b60348425181c1071007a480b00e03001682c1d16221804020100300f809400035030864400c0d01ca01d04014840002ca0701c00c40568851140c41d49000e80060382c40140b030003000c0c060105201c400e0401001e140320302e0903a501d410381300144220300500442d485520030401940354180310707801a0b0103c1801c0c420800485140d40ba1040050380543c245030301040703807200101c15520b0818281c0c0d12035508030001c0c0c8140d0782d941d9400c8005190091003001070488076080074005c2c16080007113038042c2c0c4607a02c0004055041004141c00b01822440c03500c2161706284001d07292942c04074602c411940181d40c0403484201d66404c04c01c55008000001d500318032131 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 732902562 1250 732901312 732901333
    0x8030403170c0306280902031f080c0306060907141b03280302090603041205040e0a0e07240e0a0b0a090515070b040f02060d0c0e010f020609151503 65
    0x407480154001c950494441d1107a821030740d001c10000e045540782d00c5c0c0040c04200204540d982c19001998005859211400359809040440c010350140b500700031140d90203049010190b0504020039501b100b1f00702c0301d9500610703200c0c5004144a078040000d5000410115803648000b900e122852070f00041c8000340d0f41c0740c003041c0e0003492665905c400e2100714600b001125a680501034421a109031f0b074040e004074070b035075110388075100740d180f41100100c00c124081100240b440c000350001c5001d011500c0012500070864a40103241020b140c2218210300009200501d00c2c602039030041110785c549041c14840c0e002864006080c514103070740174464400000072890042a4400220710548500710368030800c0f0001e25044040034068140d0003020021040041808500a640700d452098401004145096000c2c03003c0c1090310802502c0401140c248512100f2540c4c00000e6419141c040e40b00504051518001095580f10411842e0b4494018500800c0300301c201d44a404110030000303812110f00412 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 732903812 1250 732902562 732902581
    0xe010e04090803040614010b07030e190f1e0b0712021c0f081005100507050a0602070f1a070f031e111317030307121b0f020c09040c030803040317 64
    0x481d400c03a401d504d044101206c07104003c03140e034141c500a03c0d0703450404130f0355a805d4440c0942418242d6106035420464140028080b0440005c0d0080710300c4e402d15070b0b1800003a0307044d83c0089014035900d6803c045050180c40c204206840d01c05401c40318a408045400c407040e42481d4604034040c40b20261281e9605a8541001200c982462142c0d01d060710b40d5603e1804803460680c5000d803990044504500400e42c2d40305402a002c11801841903030a800343c0b40d40e40710f00300c1e030001008485010081641c4010f205065880c400301d8005ca28120202e1318040b0401051b8000d803950001c02d240c1d030390300700074501800240c4c00c00c0d222034a9030040101400501c1c410005030070200c0002090b0780400e50125040084204941c0c8603c040700003141191140e40090740c481d1b900c15540c8140c1c0f9a07039502d500d65009805480941d901454650540031090040d0080c1007020301800d141c02000244113200000e0040a00c01003101d80141005860303403200e1808440e90000341d0002c0414074285814010b0550 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 732905062 1250 732903812 732903817
    0x60902030d0203090a14060706020c070e0703090b060103050601120f06080a1b050a03031e0509031605040518100f02070203030703020d0207091109010305060a17060a051b03070e010e040908 83
    0x400c079031491703080b6038403018400141c58140081d508400f060040000065464000d020703407070081010f441843c0d49400685904140c2111020000394460251405000036036601940040c000e19060003507252500028005952034459021a25921100c2038180389513503000310003030400d110507983c407200203041030b4600444404e4408041103816000152a00d4105510341c1283c1d0702d034842803890081c079003014900052802e0400180f00040283d40c007c0d94062100e00c600001c0b8020000100d41440c0901080b11401040380d1103040d058041e00720031f001c000680110741c3c0c0903510081010b200d1465090040c0c00342010003901131202107200000c245e00400c0c00104c0101035403c8511903a5141c0c0482c1c01e4841410b48106400703070811402449500c40c0d00855480f8002a0881d10311540d40e5400c1d00c088051407242c880f00303400c90028082903120500500d6080010120520130980304070036011958400503200200b484611462541d059004210814000d00002e108010720950360900c00f0182e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 732906312 1250 732905062 732905077
    0xa030302031504090515060d0209010303030e0d0908070b070f08030c07150b132d0f060503030f04150306090c0801031a09061306020c100b0a06020f0d0309060902030d0203 75
    0x2e69819002882c504061048200c0030303401c00c2c020200380b4a21802c0900f5594050075894003c08000c08d440c0168880034010341c004c601c26940040d4000d4202101d43c14200c00b40004010020308080130414114006000f0064651003000b082d5989020315243d9118000004000c10394000401003040d003800d403401808020303000c0c80e40340c01019249005001280c0180d10525401100c840a06a10484985c001c00341d5100e801d4407030025980c4a103840740c1440340300c0181181c0715180c08041105101c1d0740200d00017460117600035420700384082c002c5005400f450290403140542412a01c504c24803980041d001000c0c544400c100019000380020080d540c01d01094038420710440003410001c8070b05001754495280080600220b88801c61101d4500c040740c2c1c07041c0e0300541c080c0000a0220014064061880c1380142d0020f4864056400d001d0f07580525400303202550440800050601c1020880c1d503030426543c44c3c00510706001d46080b400910f54090069014811480900342007600000106602d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 732907562 1250 732906312 732906331
    0x90e03040302090c1e0c0c0316090b0a030507031e0f050d0914090601050309100e01061e0e0112032105190b010507080705030403050a0503040f21020f0102010b030a03030203 76
    0x996110480d05090b4032503042c3c8651005070101da20a0100c801201a006d503101400640302c0d802072240c0064a4400d510b8001a00202c0d504010044030325584204440145c0c00c0c0c0b483c0c0d01881c0307543c8030340786c43e030f41d9a200c06019101042003402008048520f90a08554450071141d40da80050810594035000000c800c004102131300008104400090f031003402d05a8014000c0103d41d942000442e91a0406400c0c01e501e8400d07d24201c0c2000301e180a010f903042400400060010b18240d0b52444101c0e03011040340d054500c40e0760074044924842480b0307040d04c43c0c96042c08040501440e00725507102a0360035101041110010802070801160096400707000005402c0c121082001c84c0c007400c41d124072900601040b810441c940c0040d8840016140d40d50240c400c1c0c80c02d0682d00e0300d070b81e0708020302541300319559000003c0c14090700b0056014040a0540c2c0170103c0381c042200030140418281d40780c8080d1045410009000c4240c0c401d411111180b8000303002d503150200341e480c0181c080c0d00b0640d403244a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 732908812 1250 732907562 732907579
    0x110703031406041a28080109020f0609010210050417070b0f0a1116060603290c04030c05010c14011b02010e0c100503041106040312020610030b01060513090e03040302 73
    0x10145481c2c05480092810301d24880c503001020740400ca400c9032141e8560000004020705d42c031513a2480884039009144000010800c01205c0c41041818204c0c0400c50344100300902a50841c2d03640042d4801800906200000303103600d03282010f0840000c200e021180ca4000002c46004020003000424040c5040c150000740c0707915000042d005a0344407c483d80a140c200f406000e8089007588002941c860191000180720b0b9120f4270f0740940c06500d240e03c0d000c80c0d10360001a52107a0700003010103522010031180d4a04207820340d03592070800060780c80383d41e04000760101c11009100c00140000e0480d1032800080110b0000b1500640301100340c1c85400b00036528003507210504940c00308000000c0540107101250b500b4001174141d45903000a0401e888110304030340e58900c0b58503070310014000307140a042c1d04030450b81c0442c4024030b8504024000d014110004204000084080941a064448604202c0d440c0d00c4410b0711584041e1666100108a03030404d84207038910b0a020009005490084c0c55804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 732910062 1250 732908812 732908821
    0x20c091e0f04020907210914060c0c030d0b010e0d0c1401170c0a17010b041a0a080402010302030603010e150f1803160f0203010c1101050106260702011107030314 71
    0x15500340111400f94109055800082010b4404c441c041005003030130605400505240c0058021552860012030320f21402688000114004000c083e070311400c2108180c2c50050080c0256499001d081c5081e043d481d160b0300d20390510fa0090310302040705000a41100000700b40343c00d0005001c1ca00f440b890024605540004182d07511039a007e5214458210740b40c55031751580340840199502002c03503402040892146201c542052202c2c030b90003403410082841d1510306020403194095500d000c80034900317400b0400f0508154000f140c06600a4090a0041e16640ca080120740908801242080c0e240505802401c01d8030301108150b000f4881c3d0060800580d03600030131211120001c0d13644c0304803684240064600c050002c401e40d0003451040000c0740030030010382d021900703480c2103201010110b0391030001068440001d1040500401c1d030382c502591001d6038001c4e00809501e2498140185164440010350450b000750030410154020304440c5680300d502d824010300074010310701008003900c158804207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 732911312 1250 732910062 732910081
    0x7060f0902010e0303160b09030405061b070510121508011508010c1106011707090e0307031815030e070f08030c0c010f2f121c14011203020c091e 64
    0xf2152940e000300c8400c03000585d0341f01c1505612000702000041c0c401088082030f140c0320074001c0e003044580c0c0d2404101c840d04d0106160306004254000c103021341d00715000000025808440609010b0074040001002d000450b5569070359161900038100a40c01c288882140d070681520242c100c80039030000304488070380703910111150a0f4403150101d8be80d2041005020440c0c02c0c0c22003542250701d0000712040a03a03514203a20a035000b40e80210039680010a00c513060642000100603030100400c513601d0303401d00f014620aa220f45140021040595881c60184101410041ca1015051034104901590341da0030b04d0969a80c8004148451402038031442c04040d40140e003010220411515001d9200307800c1003038444209100070900214506c10848bc0c1d02140c1d050200340320b102c9006842c5642c4408003591546128404c080d00e00503180740ca525400303050905481c10f41560010207640c0d20b940b0356824128030b0441160700c640d511203030700c1c414489410a600030741c4c4003040381881d60003016034903803984 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 732912562 1250 732911312 732911317
    0x9060e06040803030402100302071203050402120a15020703031d031b0c06030408070203160608010f171e070f0b12012309060102120301030b1b031003031407060f0902010e0303 77
    0x2c940b40b50740103001182c018604514041140003591030014200000ca403900f0704200264071284010a9850051005500f040c8c0c07424000c688940c07009048152066071003030484500300d01c8903400c042e40030840004061080d04801c00c04103000383d0b014440442c1d5000c0c9a1264801c0d101211040440b0201c1c1250160129103030581c0f400003001c803815a911034840103c0ea034000941240c1c18050224424bc03240d08500c20b00025241c0ba42c0e9182a541c1810788900c013001803038001000750441d0f900b0303803100c000000555041d881c0c008200c0d09000c1d10003844003071a0003c2a0440303c0d40608130a0040742d000e0080e0050003807035200300740e18009a6030301d00c0c0190019030011050010320100a5494183d81040c00c074854200f40184104c622401000c020b18071550000e8108650101c0840180036014554106120803500080b182600d9800d00c40c82d0020602c40c0c512004041c80003100c01d130010103000400780c4100b5a041507040c400411a5003140009100c1c0070422070108440f9040c13480f02e814000305 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 732913669 1107 732912562 732912569
    0x302070905070c020d120306170309031e03071b0801021209010c140d090302010f1814031e070c03170316020312181c09060e0604 57
    0x3000020707240003510402c10419080e1840d07001d60360b040410700e0520b6100c0c00d4a1009200100c00350060842680b1081e40300514a9246468020200003002e01220880649400f0160900300c2c3d1904190b1408130f000590041c032034000001c3e00d50b0350410507101c1c25201207000310b80e544400f5007a80c1c0310101001043c0c05400c180801c00000f4001d40481c1683c0341003c0c0c043c19441e40325507500e4081c100c0103c4500381c0b01e15181041c036000b907005902c0107079400da0034000740341107103280c204c00e0b40610821240300300c0340c0340301030040f01000c0180c0e00014904465272080c0440301141081c540c10009042d603041102100000005403c81034100d01c8801c000c0440e500ca180c8491113007070350103a0807446019504100318030070103030301980d900d039611400c15103130104250401d00c001403800203c8402420001c000f04c220241c2d182e00440c001e07040b01c0d226500d51a1407607496003801000d000364030 = true := by decide +kernel

theorem cover : BRFrame.Cov 732733812 732913669 := by
  have h0 := BRFrame.cov_init 732733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 732733812 ≤ n) (h2 : n < 732913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
